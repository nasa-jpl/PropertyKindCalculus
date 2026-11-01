/-
`paradigm.tape_straight_line` — **one program, N printers**: the backend-neutral straight-line
program every emitter prints, its denotation, and the one theorem that the program generated from a
recorded tape denotes exactly as the tape interpreter does — stated once, for every backend.

THE TRICK. Before this module each emitter (`genBody` for CUDA/C, `genBodyJulia` for Julia) walked
the tape itself and wrote text, so "the emitted kernel computes what `evalTape` computes" was a
claim per backend about strings, and only the rendering tables (`cExpr`/`jlExpr` have an expression
wherever `cOp` has a value) were theorems. Now every emitter is factored as `print ∘ genSL`:

  * `genSL : Tape Float → Array LutTable → Except String SLProg` is the ONLY function that reads the
    tape. It produces a straight-line program — one `SLExpr` per node, in node order: a read of a
    named input, an exact literal, an alphabet operation on earlier slots, or a table fetch;
  * `SLExpr.denote`/`run` give the program its meaning in Lean `Float`, with the same scalar ops
    `cOp` uses (`BinOp.eval`/`UnOp.eval` are `cOp`'s clauses, `cOp_eval`);
  * `genSL_denotes` is the theorem: if `genSL` produces a program, `evalTapeT` succeeds and returns
    exactly `run env prog` — slot for slot, every node;
  * a backend is a *printer*, a total function `SLExpr → String` (`printC`, `printJulia`). A printer
    cannot read the tape, so it cannot introduce an input, a literal or an operation the program —
    hence the tape, hence the sealed hypergraph — does not have. What a backend must still be trusted
    for shrinks to "the printed text means, in the host language, what `denote` means": a statement
    about a dozen fixed syntactic forms, not about any kernel.

WHY IT IS A PROOF-ENGINEERING WIN. The denotation theorem is proved once and inherited by every
printer, present and future, with no proof per backend; the per-backend rendering tables become
corollaries (`jlExpr_isOk_eq_cExpr` over the whole alphabet, not case by case); and the argument-list
and literal clauses of the capstone — a literal appears in the emitted body for exactly the baked
leaves, an input read for exactly the named leaves — are theorems about the program, in both
directions (`genSL_lit_iff`, `genSL_input_iff`) instead of a reading of a generator. A new target (Fortran, MLIR, …) is a printer: a
few lines, the same theorem.

WHAT IS AND IS NOT CLAIMED. `genSL_denotes` is a theorem about Lean `Float` — binary64 — and the
program. It says nothing about a host: that the host's `+` is IEEE binary64 addition round-to-nearest,
that its `exp` is glibc's/libdevice's/`Base.Math`'s, that its compiler does not contract `a*b + c`,
and (CUDA) that `float` is a round-to-nearest narrowing of the double program, remain the trusted base
each printer names and the parity executables (`julia_parity`, the landing stubs) measure.

The table-extended interpreter (`cOpT`/`evalTapeT`) lives here, between `paradigm.tape_eval` and
`paradigm.tape_codegen`, because the program's `fetch` form denotes as `LutTable.refFetch`.

A `module` file: imports the reference interpreter and the lookup-table carrier.
-/

module

public import PropertyKindCalculus.Torch.Paradigm.TapeEval
public import PropertyKindCalculus.Torch.Paradigm.LutCarrier

@[expose] public section Blanket

open Runtime.Autograd (Tape Node)
open PropertyKindCalculus.Paradigm (LutTable lutNodeName?)

namespace PropertyKindCalculus.Paradigm.TapeCodegen

/-! ### The table-extended interpreter

`paradigm.lut_carrier`'s `lutFetch` records nodes named `lutfetch:<table>` with parents
`[layerId, uId]`. `cOpT`/`evalTapeT` extend the reference interpreter with that one case —
the fp64 `LutTable.refFetch` — resolving the table by the name baked into the node. `evalTape`
itself is untouched, and `evalTapeT` with no tables *is* `evalTape` (`cOpT` falls back to `cOp`,
including for unknown tables, so the two agree error-for-error) — every existing
`evalTape`-denotation proof is unaffected. -/

/-- `cOp` extended with the `lutfetch:<table>` alphabet entry: the fetch node re-interprets as
`LutTable.refFetch` (fp64 reference). An unresolvable table name falls through to `cOp`'s
standard unsupported-op error, so `cOpT (fun _ => none) = cOp` pointwise. -/
def cOpT (tables : String → Option LutTable) (nm : String) (args : List Float) :
    Except String Float :=
  match lutNodeName? nm with
  | some tn =>
      match tables tn, args with
      | some tbl, [l, u] => .ok (tbl.refFetch l u)
      | some _, _ => .error s!"tape_codegen: lutfetch `{tn}` expects [layer, u] (arity {args.length})"
      | none, _ => cOp nm args
  | none => cOp nm args

/-- `evalTape` with the table-extended alphabet (`cOpT`). The deployed megakernel's fp64
denotation when the recorded DAG contains `lutfetch` nodes. -/
def evalTapeT (tables : String → Option LutTable) (env : String → Float) (t : Tape Float) :
    Except String (Array Float) := do
  let mut vals : Array Float := Array.mkEmpty t.nodes.size
  for n in t.nodes do
    let v ← (
      if n.parents.isEmpty then
        match n.name with
        | some nm => pure (env nm)
        | none    => pure (nodeScalar n)
      else
        match n.name with
        | some nm => cOpT tables nm ((n.parents.map (fun p => vals.getD p 0.0)).toList)
        | none    => .error "tape_codegen: op node with no op name")
    vals := vals.push v
  pure vals

/-- With no tables, the extended alphabet degenerates to `cOp` — including on `lutfetch:*`
names, where the fallback reproduces `cOp`'s error. -/
theorem cOpT_none (nm : String) (args : List Float) : cOpT (fun _ => none) nm args = cOp nm args := by
  unfold cOpT
  cases lutNodeName? nm <;> rfl

/-- With no tables, `evalTapeT` *is* `evalTape` — the extension is conservative, so every
existing `evalTape`-denotation proof transfers verbatim. -/
theorem evalTapeT_none (env : String → Float) (t : Tape Float) :
    evalTapeT (fun _ => none) env t = evalTape env t := by
  unfold evalTapeT evalTape
  simp only [cOpT_none]
  rfl

/-- On a non-`lutfetch` name the extended alphabet is `cOp`. -/
theorem cOpT_of_lutNodeName?_none (tables : String → Option LutTable) {nm : String}
    (h : lutNodeName? nm = none) (args : List Float) : cOpT tables nm args = cOp nm args := by
  simp only [cOpT, h]

namespace SL

/-! ### The alphabet, as data

`cOp` matches on op-name strings; the program carries the operation as a constructor, so a
printer is total and the denotation lemma is one `cases`. `ofName?` is the parser `genSL` uses,
`name` its inverse (`name_ofName?`), and `eval` is `cOp`'s clause for that op (`cOp_eval`). -/

/-- The binary alphabet `add sub mul div min max`. -/
inductive BinOp where
  | add | sub | mul | div | min | max
deriving DecidableEq, Repr

/-- The unary alphabet `exp log sqrt abs`. -/
inductive UnOp where
  | exp | log | sqrt | abs
deriving DecidableEq, Repr

def BinOp.name : BinOp → String
  | .add => "add" | .sub => "sub" | .mul => "mul" | .div => "div" | .min => "min" | .max => "max"

def UnOp.name : UnOp → String
  | .exp => "exp" | .log => "log" | .sqrt => "sqrt" | .abs => "abs"

def BinOp.ofName? : String → Option BinOp
  | "add" => some .add | "sub" => some .sub | "mul" => some .mul
  | "div" => some .div | "min" => some .min | "max" => some .max
  | _ => none

def UnOp.ofName? : String → Option UnOp
  | "exp" => some .exp | "log" => some .log | "sqrt" => some .sqrt | "abs" => some .abs
  | _ => none

/-- The scalar semantics of a binary op — `cOp`'s clause. `min`/`max` are Lean's
`minOfLe`/`maxOfLe` (`if x ≤ y then x else y`), NaN included. -/
def BinOp.eval : BinOp → Float → Float → Float
  | .add, a, b => a + b
  | .sub, a, b => a - b
  | .mul, a, b => a * b
  | .div, a, b => a / b
  | .min, a, b => Min.min a b
  | .max, a, b => Max.max a b

def UnOp.eval : UnOp → Float → Float
  | .exp, a => Float.exp a
  | .log, a => Float.log a
  | .sqrt, a => Float.sqrt a
  | .abs, a => Float.abs a

theorem BinOp.name_ofName? {nm : String} {o : BinOp} (h : BinOp.ofName? nm = some o) :
    o.name = nm := by
  unfold BinOp.ofName? at h
  split at h <;> cases h <;> rfl

theorem UnOp.name_ofName? {nm : String} {o : UnOp} (h : UnOp.ofName? nm = some o) :
    o.name = nm := by
  unfold UnOp.ofName? at h
  split at h <;> cases h <;> rfl

/-- `eval` is `cOp` on the op's name — the interpreter's alphabet, constructor by constructor. -/
theorem BinOp.cOp_eval (o : BinOp) (x y : Float) : cOp o.name [x, y] = .ok (o.eval x y) := by
  cases o <;> rfl

theorem UnOp.cOp_eval (o : UnOp) (x : Float) : cOp o.name [x] = .ok (o.eval x) := by
  cases o <;> rfl

/-! ### The straight-line program -/

/-- One line of the straight-line program — what slot `i` of the emitted kernel holds. Slots are
tape node ids; an operation's operands are earlier slots. -/
inductive SLExpr where
  /-- A read of the named input `nm` at the current pixel (a named tape leaf). -/
  | input (nm : String)
  /-- An exact literal (an unnamed tape leaf's stored scalar). -/
  | lit (x : Float)
  /-- A binary alphabet op on slots `a`, `b`. -/
  | bin (o : BinOp) (a b : Nat)
  /-- A unary alphabet op on slot `a`. -/
  | un (o : UnOp) (a : Nat)
  /-- A lookup-table fetch into `tbl` at layer slot `layer`, coordinate slot `u`. -/
  | fetch (tbl : LutTable) (layer u : Nat)

/-- A straight-line program: slot `i` holds `prog[i]`. -/
abbrev SLProg := Array SLExpr

/-- The meaning of one line against the slots computed so far (`vals`) and the input
environment `env`. Total: an out-of-range slot reads `0.0`, as `evalTape`'s `getD` does. -/
def SLExpr.denote (env : String → Float) (vals : Array Float) : SLExpr → Float
  | .input nm => env nm
  | .lit x => x
  | .bin o a b => o.eval (vals.getD a 0.0) (vals.getD b 0.0)
  | .un o a => o.eval (vals.getD a 0.0)
  | .fetch tbl l u => tbl.refFetch (vals.getD l 0.0) (vals.getD u 0.0)

/-- Run the program: the slot values, in order. Total — a program is straight-line code. -/
def run (env : String → Float) (prog : SLProg) : Array Float :=
  prog.foldl (fun vals e => vals.push (e.denote env vals)) #[]

/-! ### Generating the program from a tape -/

/-- The op line for a named op node: the alphabet op on the parent slots, or the interpreter's
unsupported-op error (same text as `cOp`'s, so a rejection reads the same everywhere). -/
def mkOp (nm : String) (ps : List Nat) : Except String SLExpr :=
  match ps with
  | [a, b] =>
      match BinOp.ofName? nm with
      | some o => .ok (.bin o a b)
      | none => .error s!"tape_codegen: unsupported op `{nm}` (arity {ps.length})"
  | [a] =>
      match UnOp.ofName? nm with
      | some o => .ok (.un o a)
      | none => .error s!"tape_codegen: unsupported op `{nm}` (arity {ps.length})"
  | _ => .error s!"tape_codegen: unsupported op `{nm}` (arity {ps.length})"

/-- The program line for tape node `n` at id `i`: a named leaf is an input read, an unnamed leaf
a literal, a `lutfetch:<table>` node a fetch into the resolved table, any other named op node an
alphabet op. The failure cases are the generators' (`genBody`, `genBodyJulia`), verbatim. -/
def nodeSL (tbls : Array LutTable) (i : Nat) (n : Node Float) : Except String SLExpr :=
  if n.parents.isEmpty then
    match n.name with
    | some nm => .ok (.input nm)
    | none => .ok (.lit (nodeScalar n))
  else
    match n.name with
    | some nm =>
        match lutNodeName? nm with
        | some tn =>
            match tbls.find? (·.name == tn), n.parents.toList with
            | some tbl, [l, u] => .ok (.fetch tbl l u)
            | some _, _ =>
                .error s!"tape_codegen: lutfetch node {i} expects parents [layer, u] (got {n.parents.size})"
            | none, _ => .error s!"tape_codegen: lutfetch node {i} references unknown table `{tn}`"
        | none => mkOp nm n.parents.toList
    | none => .error s!"tape_codegen: op node {i} has no op name"

/-- **The one tape reader.** The straight-line program of a tape: one line per node, in id
order. Every emitter is a printer of this. -/
def genSL (t : Tape Float) (tbls : Array LutTable) : Except String SLProg :=
  t.nodes.zipIdx.mapM fun p => nodeSL tbls p.2 p.1

/-! ### `evalTapeT` as a fold -/

/-- The loop body of `evalTapeT`, one node at a time. -/
def stepValT (tables : String → Option LutTable) (env : String → Float)
    (vals : Array Float) (n : Node Float) : Except String Float :=
  if n.parents.isEmpty then
    match n.name with
    | some nm => pure (env nm)
    | none => pure (nodeScalar n)
  else
    match n.name with
    | some nm => cOpT tables nm ((n.parents.map (fun p => vals.getD p 0.0)).toList)
    | none => .error "tape_codegen: op node with no op name"

theorem evalTapeT_eq_foldlM (tables : String → Option LutTable) (env : String → Float)
    (t : Tape Float) :
    evalTapeT tables env t
      = t.nodes.foldlM
          (fun vals n => (stepValT tables env vals n).map (fun v => vals.push v)) #[] := by
  unfold evalTapeT stepValT
  simp only [Array.mkEmpty_eq, bind_pure_comp, Array.forIn_yield_eq_foldlM, bind_pure]
  rfl

/-! ### The denotation theorem -/

/-- The resolved table array and the interpreter's table function agree: a name resolves to the
same table (or to none) on both sides. `tablesOf` is the canonical instance. -/
def TablesAgree (tbls : Array LutTable) (tables : String → Option LutTable) : Prop :=
  ∀ tn, tables tn = tbls.find? (·.name == tn)

/-- The interpreter's table function induced by a resolved table array. -/
def tablesOf (tbls : Array LutTable) : String → Option LutTable := fun tn => tbls.find? (·.name == tn)

theorem tablesAgree_tablesOf (tbls : Array LutTable) : TablesAgree tbls (tablesOf tbls) :=
  fun _ => rfl

theorem tablesAgree_empty : TablesAgree #[] (fun _ => none) := fun _ => rfl

/-- An op line denotes as `cOp` interprets the node: `mkOp` succeeds only on the alphabet, where
`eval` is `cOp`'s clause. -/
theorem mkOp_denote (env : String → Float) (vals : Array Float) {nm : String} {ps : List Nat}
    {e : SLExpr} (h : mkOp nm ps = .ok e) :
    cOp nm (ps.map (fun p => vals.getD p 0.0)) = .ok (e.denote env vals) := by
  unfold mkOp at h
  split at h
  · split at h
    · rename_i o ho
      cases h
      have hn := BinOp.name_ofName? ho
      subst hn
      simp [SLExpr.denote, BinOp.cOp_eval]
    · cases h
  · split at h
    · rename_i o ho
      cases h
      have hn := UnOp.name_ofName? ho
      subst hn
      simp [SLExpr.denote, UnOp.cOp_eval]
    · cases h
  · cases h

/-- **Node law.** The program line `nodeSL` produces for a node denotes exactly what the
interpreter's step computes for that node against the same slots. -/
theorem nodeSL_denote {tbls : Array LutTable} {tables : String → Option LutTable}
    (hT : TablesAgree tbls tables) (env : String → Float) (vals : Array Float)
    {i : Nat} {n : Node Float} {e : SLExpr} (h : nodeSL tbls i n = .ok e) :
    stepValT tables env vals n = .ok (e.denote env vals) := by
  unfold nodeSL at h
  unfold stepValT
  by_cases hp : n.parents.isEmpty = true
  · rw [ite_eq_left hp] at h ⊢
    cases hname : n.name with
    | some nm => simp only [hname] at h ⊢; cases h; rfl
    | none => simp only [hname] at h ⊢; cases h; rfl
  · rw [ite_eq_right hp] at h ⊢
    cases hname : n.name with
    | none => simp only [hname] at h; cases h
    | some nm =>
      simp only [hname] at h ⊢
      cases htn : lutNodeName? nm with
      | none =>
        simp only [htn] at h
        rw [cOpT_of_lutNodeName?_none tables htn, Array.toList_map]
        exact mkOp_denote env vals h
      | some tn =>
        simp only [htn] at h
        cases hfind : tbls.find? (·.name == tn) with
        | none => simp only [hfind] at h; cases h
        | some tbl =>
          simp only [hfind] at h
          cases hpar : n.parents.toList with
          | nil => simp only [hpar] at h; cases h
          | cons l rest =>
            cases rest with
            | nil => simp only [hpar] at h; cases h
            | cons u rest2 =>
              cases rest2 with
              | cons _ _ => simp only [hpar] at h; cases h
              | nil =>
                simp only [hpar] at h
                cases h
                simp only [cOpT, htn, hT tn, hfind, Array.toList_map, hpar, List.map_cons,
                  List.map_nil, SLExpr.denote]

/-- The fold over a node sublist, against the program lines `mapM` produced for it. -/
theorem foldlM_run_aux {tbls : Array LutTable} {tables : String → Option LutTable}
    (hT : TablesAgree tbls tables) (env : String → Float) :
    ∀ (l : List (Node Float)) (i : Nat) (prog : List SLExpr) (vals : Array Float),
      (l.zipIdx i).mapM (fun p => nodeSL tbls p.2 p.1) = .ok prog →
      l.foldlM (fun vals n => (stepValT tables env vals n).map (fun v => vals.push v)) vals
        = .ok (prog.foldl (fun vals e => vals.push (e.denote env vals)) vals) := by
  intro l
  induction l with
  | nil =>
    intro i prog vals h
    simp only [List.zipIdx_nil, List.mapM_nil] at h
    have hp : prog = [] := by injection h with h; exact h.symm
    subst hp
    rfl
  | cons hd tl ih =>
    intro i prog vals h
    rw [List.zipIdx_cons, List.mapM_cons] at h
    cases hhd : nodeSL tbls i hd with
    | error e =>
      rw [hhd] at h
      simp [bind, Except.bind] at h
    | ok e =>
      rw [hhd] at h
      cases hrest : (tl.zipIdx (i + 1)).mapM (fun p => nodeSL tbls p.2 p.1) with
      | error e' =>
        rw [hrest] at h
        simp [bind, Except.bind] at h
      | ok es =>
        rw [hrest] at h
        simp only [bind, Except.bind, pure, Except.pure] at h
        have hp : prog = e :: es := by injection h with h; exact h.symm
        subst hp
        rw [List.foldlM_cons, nodeSL_denote hT env vals hhd]
        simp only [Except.map, bind, Except.bind, List.foldl_cons]
        exact ih (i + 1) es _ hrest

/-- **The denotation theorem — one program, every backend.** If `genSL` produces a program for a
tape, the table-extended interpreter succeeds on that tape and returns exactly the program's run:
slot `i` of the emitted kernel denotes node `i` of the tape, for every node. Stated against any
table function that agrees with the resolved tables (`TablesAgree`); `genSL_denotes_tablesOf` and
`genSL_denotes_noTables` are its two canonical instances. -/
theorem genSL_denotes {tbls : Array LutTable} {tables : String → Option LutTable}
    (hT : TablesAgree tbls tables) (env : String → Float) {t : Tape Float} {prog : SLProg}
    (h : genSL t tbls = .ok prog) :
    evalTapeT tables env t = .ok (run env prog) := by
  unfold genSL at h
  have h' : (t.nodes.toList.zipIdx 0).mapM (fun p => nodeSL tbls p.2 p.1) = .ok prog.toList := by
    rw [← Array.toList_zipIdx, ← Array.toList_mapM, h]; rfl
  rw [evalTapeT_eq_foldlM, ← Array.foldlM_toList,
    foldlM_run_aux hT env t.nodes.toList 0 prog.toList #[] h']
  unfold run
  rw [Array.foldl_toList]

theorem genSL_denotes_tablesOf (tbls : Array LutTable) (env : String → Float) {t : Tape Float}
    {prog : SLProg} (h : genSL t tbls = .ok prog) :
    evalTapeT (tablesOf tbls) env t = .ok (run env prog) :=
  genSL_denotes (tablesAgree_tablesOf tbls) env h

/-- The table-free instance: the program of a pure-arithmetic tape runs as `evalTape`. -/
theorem genSL_denotes_noTables (env : String → Float) {t : Tape Float} {prog : SLProg}
    (h : genSL t #[] = .ok prog) : evalTape env t = .ok (run env prog) := by
  rw [← evalTapeT_none]
  exact genSL_denotes tablesAgree_empty env h

/-! ### What the program's lines are — the argument-list and literal clauses as theorems

`genSL` produces a literal exactly at an unnamed leaf (with that leaf's stored scalar) and an input
read exactly at a named leaf (with that leaf's name): no literal and no input is in the emitted
body that is not in the tape — the "no naked number" clause, about the program a printer prints
rather than about the generator. -/

/-- `mapM` over `Except`, read at an index: a produced element comes from the input element at the
same index. -/
theorem mapM_ok_getElem? {α β : Type} {f : α → Except String β} :
    ∀ {l : List α} {l' : List β}, l.mapM f = .ok l' →
      ∀ (i : Nat) (y : β), l'[i]? = some y → ∃ x, l[i]? = some x ∧ f x = .ok y := by
  intro l
  induction l with
  | nil =>
    intro l' h i y hy
    simp only [List.mapM_nil] at h
    have hl : l' = [] := by injection h with h; exact h.symm
    subst hl
    simp at hy
  | cons hd tl ih =>
    intro l' h i y hy
    rw [List.mapM_cons] at h
    cases hhd : f hd with
    | error e => rw [hhd] at h; simp [bind, Except.bind] at h
    | ok b =>
      rw [hhd] at h
      cases hrest : tl.mapM f with
      | error e => rw [hrest] at h; simp [bind, Except.bind] at h
      | ok bs =>
        rw [hrest] at h
        simp only [bind, Except.bind, pure, Except.pure] at h
        have hl : l' = b :: bs := by injection h with h; exact h.symm
        subst hl
        cases i with
        | zero =>
          simp only [List.getElem?_cons_zero, Option.some.injEq] at hy
          subst hy
          exact ⟨hd, rfl, hhd⟩
        | succ k =>
          simp only [List.getElem?_cons_succ] at hy
          obtain ⟨x, hx, hfx⟩ := ih hrest k y hy
          exact ⟨x, by simpa using hx, hfx⟩

/-- Slot `i` of the program is `nodeSL` of node `i` of the tape. -/
theorem genSL_getElem? {t : Tape Float} {tbls : Array LutTable} {prog : SLProg}
    (h : genSL t tbls = .ok prog) {i : Nat} {e : SLExpr} (hi : prog[i]? = some e) :
    ∃ n, t.getNode? i = some n ∧ nodeSL tbls i n = .ok e := by
  unfold genSL at h
  have h' : (t.nodes.toList.zipIdx 0).mapM (fun p => nodeSL tbls p.2 p.1) = .ok prog.toList := by
    rw [← Array.toList_zipIdx, ← Array.toList_mapM, h]; rfl
  rw [← Array.getElem?_toList] at hi
  obtain ⟨p, hp, hpe⟩ := mapM_ok_getElem? h' i e hi
  rw [List.getElem?_zipIdx] at hp
  cases hn : t.nodes.toList[i]? with
  | none => rw [hn] at hp; simp at hp
  | some n =>
    rw [hn] at hp
    simp only [Option.map_some, Option.some.injEq] at hp
    subst hp
    refine ⟨n, ?_, by simpa using hpe⟩
    rw [Tape.getNode?, ← Array.getElem?_toList]; exact hn

/-- **The literal clause.** A literal in the program is an unnamed leaf of the tape, and is that
leaf's stored scalar. -/
theorem genSL_lit {t : Tape Float} {tbls : Array LutTable} {prog : SLProg}
    (h : genSL t tbls = .ok prog) {i : Nat} {x : Float} (hi : prog[i]? = some (.lit x)) :
    ∃ n, t.getNode? i = some n ∧ n.parents.isEmpty = true ∧ n.name = none ∧ nodeScalar n = x := by
  obtain ⟨n, hn, he⟩ := genSL_getElem? h hi
  refine ⟨n, hn, ?_⟩
  unfold nodeSL at he
  split at he
  · rename_i hp
    split at he
    · cases he
    · rename_i hnm
      cases he
      exact ⟨hp, hnm, rfl⟩
  · split at he
    · split at he
      · split at he <;> cases he
      · unfold mkOp at he
        split at he
        · split at he <;> cases he
        · split at he <;> cases he
        · cases he
    · cases he

/-- **The argument-list clause.** An input read in the program is a named leaf of the tape, with
that leaf's name — so the emitted kernel's argument list is the tape's named leaves, nothing else. -/
theorem genSL_input {t : Tape Float} {tbls : Array LutTable} {prog : SLProg}
    (h : genSL t tbls = .ok prog) {i : Nat} {nm : String} (hi : prog[i]? = some (.input nm)) :
    ∃ n, t.getNode? i = some n ∧ n.parents.isEmpty = true ∧ n.name = some nm := by
  obtain ⟨n, hn, he⟩ := genSL_getElem? h hi
  refine ⟨n, hn, ?_⟩
  unfold nodeSL at he
  split at he
  · rename_i hp
    split at he
    · rename_i hnm
      cases he
      exact ⟨hp, hnm⟩
    · cases he
  · split at he
    · split at he
      · split at he <;> cases he
      · unfold mkOp at he
        split at he
        · split at he <;> cases he
        · split at he <;> cases he
        · cases he
    · cases he

/-! The converses: a leaf of the tape *is* a literal or an input read of the program at the same
slot, so each clause is an equivalence (`genSL_lit_iff`, `genSL_input_iff`). -/

/-- `mapM` over `Except`, read at an index, the other way: every input element produced the element
at the same index. -/
theorem mapM_ok_getElem?_of {α β : Type} {f : α → Except String β} :
    ∀ {l : List α} {l' : List β}, l.mapM f = .ok l' →
      ∀ (i : Nat) (x : α), l[i]? = some x → ∃ y, l'[i]? = some y ∧ f x = .ok y := by
  intro l
  induction l with
  | nil =>
    intro l' h i x hx
    simp at hx
  | cons hd tl ih =>
    intro l' h i x hx
    rw [List.mapM_cons] at h
    cases hhd : f hd with
    | error e => rw [hhd] at h; simp [bind, Except.bind] at h
    | ok b =>
      rw [hhd] at h
      cases hrest : tl.mapM f with
      | error e => rw [hrest] at h; simp [bind, Except.bind] at h
      | ok bs =>
        rw [hrest] at h
        simp only [bind, Except.bind, pure, Except.pure] at h
        have hl : l' = b :: bs := by injection h with h; exact h.symm
        subst hl
        cases i with
        | zero =>
          simp only [List.getElem?_cons_zero, Option.some.injEq] at hx
          subst hx
          exact ⟨b, rfl, hhd⟩
        | succ k =>
          simp only [List.getElem?_cons_succ] at hx
          obtain ⟨y, hy, hfy⟩ := ih hrest k x hx
          exact ⟨y, by simpa using hy, hfy⟩

/-- Node `i` of the tape is printed at slot `i` of the program, as `nodeSL` of that node. -/
theorem genSL_getElem?_of_node {t : Tape Float} {tbls : Array LutTable} {prog : SLProg}
    (h : genSL t tbls = .ok prog) {i : Nat} {n : Node Float} (hn : t.getNode? i = some n) :
    ∃ e, prog[i]? = some e ∧ nodeSL tbls i n = .ok e := by
  unfold genSL at h
  have h' : (t.nodes.toList.zipIdx 0).mapM (fun p => nodeSL tbls p.2 p.1) = .ok prog.toList := by
    rw [← Array.toList_zipIdx, ← Array.toList_mapM, h]; rfl
  have hn' : (t.nodes.toList.zipIdx 0)[i]? = some (n, i) := by
    rw [List.getElem?_zipIdx, Array.getElem?_toList]
    rw [Tape.getNode?] at hn
    simp [hn]
  obtain ⟨e, he, hne⟩ := mapM_ok_getElem?_of h' i (n, i) hn'
  exact ⟨e, by rw [← Array.getElem?_toList]; exact he, hne⟩

/-- An unnamed leaf of the tape is a literal of the program at its slot, with its stored scalar. -/
theorem genSL_lit_of_leaf {t : Tape Float} {tbls : Array LutTable} {prog : SLProg}
    (h : genSL t tbls = .ok prog) {i : Nat} {n : Node Float} (hn : t.getNode? i = some n)
    (hp : n.parents.isEmpty = true) (hnm : n.name = none) :
    prog[i]? = some (.lit (nodeScalar n)) := by
  obtain ⟨e, he, hne⟩ := genSL_getElem?_of_node h hn
  unfold nodeSL at hne
  rw [ite_eq_left hp, hnm] at hne
  cases hne
  exact he

/-- A named leaf of the tape is an input read of the program at its slot, with its name. -/
theorem genSL_input_of_leaf {t : Tape Float} {tbls : Array LutTable} {prog : SLProg}
    (h : genSL t tbls = .ok prog) {i : Nat} {n : Node Float} (hn : t.getNode? i = some n)
    (hp : n.parents.isEmpty = true) {nm : String} (hnm : n.name = some nm) :
    prog[i]? = some (.input nm) := by
  obtain ⟨e, he, hne⟩ := genSL_getElem?_of_node h hn
  unfold nodeSL at hne
  rw [ite_eq_left hp, hnm] at hne
  cases hne
  exact he

/-- **The literal clause, as an equivalence.** Slot `i` of the program is the literal `x` iff node
`i` of the tape is an unnamed leaf storing `x`. -/
theorem genSL_lit_iff {t : Tape Float} {tbls : Array LutTable} {prog : SLProg}
    (h : genSL t tbls = .ok prog) (i : Nat) (x : Float) :
    prog[i]? = some (.lit x) ↔
      ∃ n, t.getNode? i = some n ∧ n.parents.isEmpty = true ∧ n.name = none ∧ nodeScalar n = x :=
  ⟨genSL_lit h, fun ⟨_n, hn, hp, hnm, hx⟩ => hx ▸ genSL_lit_of_leaf h hn hp hnm⟩

/-- **The argument-list clause, as an equivalence.** Slot `i` of the program reads the input `nm`
iff node `i` of the tape is the leaf named `nm`. -/
theorem genSL_input_iff {t : Tape Float} {tbls : Array LutTable} {prog : SLProg}
    (h : genSL t tbls = .ok prog) (i : Nat) (nm : String) :
    prog[i]? = some (.input nm) ↔
      ∃ n, t.getNode? i = some n ∧ n.parents.isEmpty = true ∧ n.name = some nm :=
  ⟨genSL_input h, fun ⟨_n, hn, hp, hnm⟩ => genSL_input_of_leaf h hn hp hnm⟩

end SL

end PropertyKindCalculus.Paradigm.TapeCodegen

end Blanket
