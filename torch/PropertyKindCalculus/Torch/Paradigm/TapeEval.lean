/-
`paradigm.tape_eval` — **the tape's forward denotation** (`evalTape`), its computational tape
graph (`ofTape`), and the value characterisation the cone lemma and the megakernel codegen rest on.

`evalTape env t` re-evaluates a recorded tape at `Float` with the SAME scalar op-semantics the
emitted CUDA/C kernel uses (`+ − × ÷`, the `≤`-ternaries for `min`/`max` — Lean's `minOfLe`/`maxOfLe`, NaN included — `expf`/`logf`/`sqrtf`): named leaves read
from `env`, constant leaves keep their stored value, an op node applies its scalar to its parents'
values. It is the denotation the codegen (`paradigm.tape_codegen`) must match, the CPU-side
bit-exact validator, and — by tape forward-value faithfulness (`paradigm.tape_parity`) — equal at
`Float` to the source `[NumCarrier α]` kernel.

Beside it: `WF`, the tape build invariant (every parent precedes its node); `stepVal`, the loop
body, with `evalTape_eq_foldlM` reformulating the `for` loop as an `Except`-monadic left fold;
`evalTape_node_value`, the invariant that a successful run assigns to every slot exactly what
`stepVal` computes there against the final array; and `ofTape`, the projection of a tape onto the
prelude-only `TapeGraph` the capstone chapter's bisimulation is stated over. The cone lemma —
evaluation at a node reads only the leaves in that node's backward cone — is
`paradigm.tape_seal`, which needs the graph library's reachability and therefore Mathlib; this
module stays Mathlib-free so the codegen can import it alone.

A `module` file: imports the tape carrier and the CSE pass.
-/

module

public import PropertyKindCalculus.Torch.Paradigm.TapeCarrier
public import PropertyKindCalculus.Torch.Paradigm.TapeCse
public import PropertyKindCalculus.Paradigm.TapeGraph

@[expose] public section Blanket

open Spec TorchLean
open Runtime.Autograd (Tape Node TapeM)
open PropertyKindCalculus.Paradigm (TapeBuilder NumCarrier TapeGraph TapeVertex)

namespace PropertyKindCalculus.Paradigm.TapeCodegen

/-! ### Reading a tape node -/

/-- The scalar constant a node stores as its forward value (a scalar tape node holds one `Float`;
the same accessor `paradigm.tape_cse.nodeKey` uses). -/
def nodeScalar (n : Node Float) : Float := (TorchLean.Storage.toArray n.value.tensor.buffer).toList.headD 0.0

/-- A leaf has no parents; it is a graph **input** (a named leaf) or a **constant** (an unnamed
`TapeBuilder.const` leaf). An op node has ≥1 parent and carries the op name. -/
def isLeaf (n : Node Float) : Bool := n.parents.isEmpty

/-! ### The generated-kernel semantics — a Float reference interpreter

`evalTape env t` evaluates the recorded DAG at `Float` with the SAME scalar op-semantics the emitted
CUDA/C kernel uses. Named leaves read from `env`; const leaves keep their stored value. This is the
denotation the codegen must match, and at `Float` it equals the original `[NumCarrier α]` kernel by
tape faithfulness (`paradigm.tape_parity`). It doubles as the CPU-side bit-exact validator (no CUDA
toolchain needed) and the semantic anchor for the codegen-faithfulness proof. -/
def cOp (nm : String) (args : List Float) : Except String Float :=
  match nm, args with
  | "add",  [a, b] => .ok (a + b)
  | "sub",  [a, b] => .ok (a - b)
  | "mul",  [a, b] => .ok (a * b)
  | "div",  [a, b] => .ok (a / b)
  | "min",  [a, b] => .ok (Min.min a b)   -- (a <= b ? a : b), Lean's minOfLe
  | "max",  [a, b] => .ok (Max.max a b)   -- (a <= b ? b : a), Lean's maxOfLe
  | "exp",  [a]    => .ok (Float.exp a)   -- expf
  | "log",  [a]    => .ok (Float.log a)   -- logf
  | "sqrt", [a]    => .ok (Float.sqrt a)  -- sqrtf
  | "abs",  [a]    => .ok (Float.abs a)   -- fabsf
  | _, _ => .error s!"tape_codegen: unsupported op `{nm}` (arity {args.length})"

def evalTape (env : String → Float) (t : Tape Float) : Except String (Array Float) := do
  let mut vals : Array Float := Array.mkEmpty t.nodes.size
  for n in t.nodes do
    let v ← (
      if n.parents.isEmpty then
        match n.name with
        | some nm => pure (env nm)
        | none    => pure (nodeScalar n)
      else
        match n.name with
        | some nm => cOp nm ((n.parents.map (fun p => vals.getD p 0.0)).toList)
        | none    => .error "tape_codegen: op node with no op name")
    vals := vals.push v
  pure vals

/-! ### The tape build invariant -/

/-- A recorded tape is **well-formed** when every node's parents are strictly earlier ids (the usual
tape build invariant: every op appends after its operands). Every tape a `[NumCarrier]` kernel records
is well-formed by construction. -/
def WF (t : Tape Float) : Prop :=
  ∀ id nd, t.getNode? id = some nd → ∀ p ∈ nd.parents, p < id

theorem wf_of_bounded (t : Tape Float)
    (h : ∀ id, (hid : id < t.size) → ∀ p ∈ (t.nodes[id]'hid).parents, p < id) : WF t := by
  intro id nd hnd p hp
  rw [Tape.getNode?] at hnd
  obtain ⟨hid, heq⟩ := Array.getElem?_eq_some_iff.mp hnd
  exact h id hid p (by rw [heq]; exact hp)

/-! ### `evalTape` as a fold, and its one-node append law

`evalTape` is a `for`-loop building a value array. To reason about it we reformulate it as an
`Except`-monadic left fold over the nodes and prove that extending a tape by one node extends its
value array by one `stepVal`. -/

/-- The loop body of `evalTape`, one node at a time. -/
def stepVal (env : String → Float) (vals : Array Float) (n : Node Float) : Except String Float :=
  if n.parents.isEmpty then
    match n.name with
    | some nm => pure (env nm)
    | none => pure (nodeScalar n)
  else
    match n.name with
    | some nm => cOp nm ((n.parents.map (fun p => vals.getD p 0.0)).toList)
    | none => .error "tape_codegen: op node with no op name"

theorem evalTape_eq_foldlM (env : String → Float) (t : Tape Float) :
    evalTape env t
      = t.nodes.foldlM (fun vals n => (stepVal env vals n).map (fun v => vals.push v)) #[] := by
  unfold evalTape stepVal
  simp only [Array.mkEmpty_eq, bind_pure_comp, Array.forIn_yield_eq_foldlM, bind_pure]
  rfl

/-- The empty tape evaluates to the empty value array. -/
theorem evalTape_empty (env : String → Float) : evalTape env (Tape.empty : Tape Float) = .ok #[] := by
  rw [evalTape_eq_foldlM]; rfl

/-- **Append law for `evalTape`.** Extending a tape by one node extends its value array by
evaluating that node against the already-computed values. -/
theorem evalTape_addNode (env : String → Float) (t : Tape Float) (n : Node Float) :
    evalTape env (t.addNode n).1
      = (evalTape env t) >>= fun vals => (stepVal env vals n).map (fun v => vals.push v) := by
  rw [evalTape_eq_foldlM env (t.addNode n).1, evalTape_eq_foldlM env t]
  simp only [Tape.addNode, Array.foldlM_push]

theorem getD_push_size (vals : Array Float) (x : Float) :
    (vals.push x).getD vals.size 0.0 = x := by simp

theorem getD_push_lt (vals : Array Float) (x : Float) (i : Nat) (h : i < vals.size) :
    (vals.push x).getD i 0.0 = vals.getD i 0.0 := by
  simp [Array.getElem?_push_lt h, Array.getElem?_eq_getElem h]

/-! ### The `evalTape` value-characterisation (a `foldlM` invariant) -/

/-- Pushing a fresh value onto the value array does not change `stepVal` of a node whose parents are all
already in range — the interpreter reads `vals.getD p 0` only at parent indices, and `getD` below the
array size is push-invariant. -/
theorem stepVal_push_stable (env : String → Float) (acc : Array Float) (v : Float) (nd : Node Float)
    (hp : ∀ p ∈ nd.parents, p < acc.size) :
    stepVal env (acc.push v) nd = stepVal env acc nd := by
  unfold stepVal
  by_cases he : nd.parents.isEmpty = true
  · simp only [he, ite_true]
  · simp only [ite_eq_right he]
    cases hn : nd.name with
    | none => rfl
    | some nm =>
      simp only
      congr 1
      exact congrArg Array.toList (Array.map_congr_left (fun p hp' => getD_push_lt acc v p (hp p hp')))

/-- **The `foldlM` invariant, over a node sublist with an id offset `s`.** If the fold over `l` (the
nodes at ids `s, s+1, …`) succeeds, then every processed id's value is exactly what `stepVal` computes
there against the final array — the local recurrence strong induction consumes. Well-formedness (parents
precede children) is what makes each slot's `stepVal` stable as later slots are appended. Proved by list
induction because core has no `Array.foldlM_induction`. -/
theorem foldlM_stepVal_spec (env : String → Float) (t : Tape Float) (hwf : WF t) :
    ∀ (l : List (Node Float)) (s : Nat) (acc out : Array Float),
      acc.size = s →
      (∀ i (hi : i < l.length), t.getNode? (s + i) = some l[i]) →
      (∀ id, id < s → ∀ nd, t.getNode? id = some nd → stepVal env acc nd = .ok (acc.getD id 0.0)) →
      List.foldlM (fun vals n => (stepVal env vals n).map (fun v => vals.push v)) acc l = .ok out →
      out.size = s + l.length ∧
      (∀ id, id < s + l.length → ∀ nd, t.getNode? id = some nd →
        stepVal env out nd = .ok (out.getD id 0.0)) := by
  intro l
  induction l with
  | nil =>
    intro s acc out hsz _ hproc hrun
    rw [List.foldlM_nil] at hrun
    have hout : out = acc := by injection hrun with h; exact h.symm
    subst hout
    exact ⟨by simpa using hsz, by simpa using hproc⟩
  | cons hd tl ih =>
    intro s acc out hsz hget hproc hrun
    rw [List.foldlM_cons] at hrun
    have hhd : t.getNode? s = some hd := by have := hget 0 (by simp); simpa using this
    have hhd_par : ∀ p ∈ hd.parents, p < s := hwf s hd hhd
    cases hsv : stepVal env acc hd with
    | error e =>
        rw [hsv] at hrun
        simp [Except.map, bind, Except.bind] at hrun
    | ok v =>
        rw [hsv] at hrun
        simp only [Except.map, bind, Except.bind] at hrun
        have hsz' : (acc.push v).size = s + 1 := by rw [Array.size_push, hsz]
        have hproc' : ∀ id, id < s + 1 → ∀ nd, t.getNode? id = some nd →
            stepVal env (acc.push v) nd = .ok ((acc.push v).getD id 0.0) := by
          intro id hid nd hnd
          rcases Nat.lt_succ_iff_lt_or_eq.mp hid with hlt | heq
          · have hnd_par : ∀ p ∈ nd.parents, p < acc.size := by
              intro p hp; have := hwf id nd hnd p hp; omega
            rw [stepVal_push_stable env acc v nd hnd_par, hproc id hlt nd hnd,
              getD_push_lt acc v id (by rw [hsz]; exact hlt)]
          · subst heq
            have hnne : nd = hd := by
              have h2 : some nd = some hd := hnd.symm.trans hhd
              rwa [Option.some.injEq] at h2
            subst hnne
            have hnd_par : ∀ p ∈ nd.parents, p < acc.size := by
              intro p hp; rw [hsz]; exact hhd_par p hp
            rw [stepVal_push_stable env acc v nd hnd_par, hsv, ← hsz, getD_push_size]
        have hget' : ∀ i (hi : i < tl.length), t.getNode? ((s + 1) + i) = some tl[i] := by
          intro i hi
          have hlt1 : i + 1 < (hd :: tl).length := by simp only [List.length_cons]; omega
          have hidx : s + (i + 1) = (s + 1) + i := by omega
          have key := hget (i + 1) hlt1
          rw [List.getElem_cons_succ] at key
          exact hidx ▸ key
        obtain ⟨ho1, ho2⟩ := ih (s + 1) (acc.push v) out hsz' hget' hproc' hrun
        refine ⟨?_, ?_⟩
        · simp only [List.length_cons]; omega
        · intro id hid nd hnd
          simp only [List.length_cons] at hid
          exact ho2 id (by omega) nd hnd

/-- **`evalTape` node-value characterisation.** A successful `evalTape` run assigns to slot `id` exactly
the value `stepVal` computes for node `id` against the final array (specialisation of the invariant at
offset `0`). -/
theorem evalTape_node_value (env : String → Float) (t : Tape Float) (hwf : WF t)
    (vals : Array Float) (hv : evalTape env t = .ok vals) :
    vals.size = t.size ∧
    ∀ id nd, t.getNode? id = some nd → stepVal env vals nd = .ok (vals.getD id 0.0) := by
  rw [evalTape_eq_foldlM, ← Array.foldlM_toList] at hv
  have hget0 : ∀ i (hi : i < t.nodes.toList.length), t.getNode? (0 + i) = some t.nodes.toList[i] := by
    intro i hi
    rw [Nat.zero_add]
    have hi' : i < t.nodes.size := by rw [← Array.length_toList]; exact hi
    simp only [Tape.getNode?]
    rw [Array.getElem_toList hi']
    exact Array.getElem?_eq_getElem hi'
  obtain ⟨hsz, hproc⟩ := foldlM_stepVal_spec env t hwf t.nodes.toList 0 #[] vals
    (by simp) hget0 (by intro id hid; exact absurd hid (Nat.not_lt_zero id)) hv
  rw [Nat.zero_add, Array.length_toList] at hsz hproc
  refine ⟨hsz, ?_⟩
  intro id nd hnd
  have hid : id < t.nodes.size := by
    have hnd' := hnd
    rw [Tape.getNode?] at hnd'
    obtain ⟨hlt, _⟩ := Array.getElem?_eq_some_iff.mp hnd'
    exact hlt
  exact hproc id hid nd hnd

/-! ### The computational tape graph of a tape -/

/-- **The computational tape graph of a tape**: each node's name and parents, in tape order, with
values and backward rules forgotten. The object the capstone chapter's kind-transporting weak
bisimulation is stated over (`Paradigm.TapeGraph`, `Graph.Bisimulation`). -/
def ofTape (t : Tape Float) : TapeGraph :=
  ⟨t.nodes.toList.map fun n => ⟨n.name, n.parents.toList⟩⟩

theorem ofTape_size (t : Tape Float) : (ofTape t).size = t.size := by
  simp [ofTape, TapeGraph.size, Tape.size]

theorem ofTape_vertex? (t : Tape Float) (v : Nat) :
    (ofTape t).vertex? v = (t.getNode? v).map fun n => ⟨n.name, n.parents.toList⟩ := by
  simp [ofTape, TapeGraph.vertex?, Tape.getNode?, List.getElem?_map, Array.getElem?_toList]

theorem ofTape_parents (t : Tape Float) (v : Nat) (n : Node Float) (h : t.getNode? v = some n) :
    (ofTape t).parents v = n.parents.toList := by
  simp [TapeGraph.parents, ofTape_vertex?, h]

theorem ofTape_parents_of_none (t : Tape Float) (v : Nat) (h : t.getNode? v = none) :
    (ofTape t).parents v = [] := by
  simp [TapeGraph.parents, ofTape_vertex?, h]

theorem ofTape_name? (t : Tape Float) (v : Nat) (n : Node Float) (h : t.getNode? v = some n) :
    (ofTape t).name? v = n.name := by
  simp [TapeGraph.name?, ofTape_vertex?, h]

/-- A well-formed tape's graph is ordered: every parent precedes its vertex. -/
theorem ofTape_ordered (t : Tape Float) (hwf : WF t) : (ofTape t).ordered = true := by
  simp only [TapeGraph.ordered, List.all_eq_true, List.mem_range]
  intro v _
  cases h : t.getNode? v with
  | none => simp [ofTape_parents_of_none t v h]
  | some n =>
    rw [ofTape_parents t v n h]
    exact fun p hp => decide_eq_true (hwf v n h p (Array.mem_def.mpr hp))

end PropertyKindCalculus.Paradigm.TapeCodegen

end Blanket
