/-
`examples.tape_codegen_lut_end_to_end` — **the table-extended kernel is faithful for ALL
inputs**: the `∀`-environment Faithful bridge for `evalTapeT`, completing the `LutInterp`
vocabulary extension's proof story (`examples.tape_codegen_lut` carries the per-op step law
`cOpT_lutfetch` and the computational single-pixel `#guard`s; this module lifts them).

`examples.tape_codegen_end_to_end` proves, via the compositional bridge `Faithful`, that a
recorded `[NumCarrier]` kernel re-interpreted by `evalTape` computes the source kernel at EVERY
input environment. A model that also fetches (`[LutInterp α]`) records `lutfetch:<table>` nodes,
which only the table-extended interpreter `evalTapeT` understands — so the bridge must be lifted
to `evalTapeT`. `FaithfulT` below is that lift, word for word `Faithful` with `evalTapeT tables`
in place of `evalTape`:

* the fold reformulation and one-node append law transfer verbatim (`evalTapeT_addNode`);
* every arithmetic op preserves `FaithfulT` through the unchanged base alphabet
  (`cOpT_base`: on a non-`lutfetch` name, `cOpT` defers to `cOp`);
* the one genuinely new step is **`FaithfulT_lutfetch`**: the recording instance's action
  (`TapeBuilder.lutFetchM`) appends one node that stores the elementwise `refFetch` of its
  parents (recorder half) AND re-interprets under `cOpT` to `refFetch` of the parents'
  re-interpreted floats (codegen half, by `cOpT_lutfetch`) — for every environment;
* the capstone `lut_kernel_faithful` chains these over the exact fixture
  `examples.tape_codegen_lut` records: the recorded mixed arithmetic+fetch tape, re-interpreted
  by `evalTapeT` at ANY environment, computes the `[NumCarrier]+[LutInterp]` source model there —
  `#guard lutEvalFaithful`'s single pixel, promoted to all inputs.

EXACTNESS SPLIT (inherited): everything here is the point-mode fp64 semantics
(`LutTable.refFetch`); hardware-filtered deployments remain tolerance-only by construction.
-/
import PropertyKindCalculus.Examples.TapeCodegenLut
import PropertyKindCalculus.Examples.TapeCodegenEndToEnd

open Spec TorchLean TorchLean.Tensor
open Runtime.Autograd (Tape Node TapeM)
open PropertyKindCalculus.Paradigm (TapeBuilder NumCarrier LutTable LutInterp lutNodeName?)
open PropertyKindCalculus.Paradigm.TapeParity
open PropertyKindCalculus.Paradigm.TapeFaithful
open PropertyKindCalculus.Paradigm.TapeCodegen
open PropertyKindCalculus.Examples.TapeCodegenEndToEnd
  (getD_push_size getD_push_lt tapeAdd_addNode tapeSub_addNode tapeMul_addNode)
open PropertyKindCalculus.Examples.TapeCodegenLut
  (demoLut lutModel inLeafV envLayer envU envBias demoTables cOpT_lutfetch)

namespace PropertyKindCalculus.Examples.TapeCodegenLutEndToEnd

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

abbrev S : Shape := Shape.scalar
abbrev TB := TapeBuilder S
abbrev T := Tensor Float S

/-! ## `evalTapeT` as a fold, and its one-node append law — the `evalTape` reformulation
(`examples.tape_codegen_end_to_end`), transferred verbatim to the table-extended interpreter. -/

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

/-- The empty tape evaluates to the empty value array. -/
theorem evalTapeT_empty (tables : String → Option LutTable) (env : String → Float) :
    evalTapeT tables env (Tape.empty : Tape Float) = .ok #[] := by
  rw [evalTapeT_eq_foldlM]; rfl

/-- **Append law for `evalTapeT`.** Extending a tape by one node extends its value array by
evaluating that node against the already-computed values. -/
theorem evalTapeT_addNode (tables : String → Option LutTable) (env : String → Float)
    (t : Tape Float) (n : Node Float) :
    evalTapeT tables env (t.addNode n).1
      = (evalTapeT tables env t) >>= fun vals =>
          (stepValT tables env vals n).map (fun v => vals.push v) := by
  rw [evalTapeT_eq_foldlM tables env (t.addNode n).1, evalTapeT_eq_foldlM tables env t]
  simp only [Tape.addNode, Array.foldlM_push]

/-- On any non-`lutfetch` op name the extended alphabet defers to the base `cOp` — this is what
feeds the arithmetic `FaithfulT` instances below. -/
theorem cOpT_base (tables : String → Option LutTable) {nm : String}
    (h : lutNodeName? nm = none) (args : List Float) :
    cOpT tables nm args = cOp nm args := by
  simp only [cOpT, h]

/-! ## The bridge predicate, lifted -/

/-- **Codegen faithfulness of a builder under the table-extended interpreter** — word for word
`examples.tape_codegen_end_to_end`'s `Faithful`, with `evalTapeT tables` in place of `evalTape`:
running `b` stores the tensor `v` (recorder half) and makes the generated kernel, re-interpreted
by `evalTapeT` at `env`, assign the float `x` to the result node, preserving every earlier
slot. -/
def FaithfulT (tables : String → Option LutTable) (env : String → Float)
    (b : TB) (v : T) (x : Float) : Prop :=
  ∀ (t : Tape Float) (vals : Array Float),
    evalTapeT tables env t = .ok vals → vals.size = t.size →
    ∃ (id : Nat) (t' : Tape Float) (vals' : Array Float),
      b.run t = .ok (id, t') ∧
      id < t'.size ∧
      t'.requireValue (s := S) id = .ok v ∧
      Extends t' t ∧
      evalTapeT tables env t' = .ok vals' ∧
      vals'.size = t'.size ∧
      vals'.getD id 0.0 = x ∧
      (∀ i, i < vals.size → vals'.getD i 0.0 = vals.getD i 0.0)

/-- A named input leaf: stored placeholder `v`, re-interpreted as `env nm`. -/
theorem FaithfulT_named_leaf (tables : String → Option LutTable) (env : String → Float)
    (nm : String) (v : T) :
    FaithfulT tables env (⟨TapeM.leaf v (name := some nm)⟩ : TB) v (env nm) := by
  intro t vals hev hsz
  refine ⟨t.size, (Tape.leaf (t := t) v (name := some nm)).1,
    vals.push (env nm), ?run, ?lt, ?store, ?ext, ?ev, ?sz, ?val, ?pre⟩
  case run => unfold TapeM.leaf Tape.leaf Tape.addNode; rfl
  case store => exact leaf_value t v (some nm) true
  case lt => exact requireValue_lt_of_ok _ t.size (leaf_value t v (some nm) true)
  case ext => exact extends_of_value (leaf_value t v (some nm) true) (frameOver_addNode t _)
  case ev => show evalTapeT tables env (t.addNode _).1 = _; rw [evalTapeT_addNode, hev]; rfl
  case sz => rw [Array.size_push, hsz]; simp [Tape.leaf, Tape.addNode, Tape.size]
  case val => rw [← hsz]; exact getD_push_size vals (env nm)
  case pre => intro i hi; exact getD_push_lt vals (env nm) i hi

/-- A constant scalar leaf: stored `fill x`, re-interpreted as `x`. -/
theorem FaithfulT_const (tables : String → Option LutTable) (env : String → Float) (x : Float) :
    FaithfulT tables env (TapeBuilder.const x : TB) (Tensor.full S x) x := by
  intro t vals hev hsz
  refine ⟨t.size, (Tape.leaf (t := t) (Tensor.full S x) (name := none)).1,
    vals.push x, ?run, ?lt, ?store, ?ext, ?ev, ?sz, ?val, ?pre⟩
  case run => unfold TapeBuilder.const TapeM.leaf Tape.leaf Tape.addNode; rfl
  case store => exact leaf_value t (Tensor.full S x) none true
  case lt => exact requireValue_lt_of_ok _ t.size (leaf_value t (Tensor.full S x) none true)
  case ext => exact extends_of_value (leaf_value t (Tensor.full S x) none true) (frameOver_addNode t _)
  case ev =>
    show evalTapeT tables env (t.addNode _).1 = _
    rw [evalTapeT_addNode, hev]
    simp [stepValT, nodeScalar, Tensor.full, TorchLean.Tensor.Internal.Rep.const,
      TorchLean.Tensor.Internal.Rep.ofFlatFn, TorchLean.Storage.toArray_ofFn]
    rfl
  case sz => rw [Array.size_push, hsz]; simp [Tape.leaf, Tape.addNode, Tape.size]
  case val => rw [← hsz]; exact getD_push_size vals x
  case pre => intro i hi; exact getD_push_lt vals x i hi

/-! ## Generic op-preservation, then the arithmetic instances -/

/-- **Generic binary-op faithfulness** — `Faithful_bin` lifted: the interpreter equation is now
against the extended alphabet `cOpT tables`. -/
theorem FaithfulT_bin (tables : String → Option LutTable) (env : String → Float)
    (top : Nat → Nat → TapeM Float Nat) (nm : String)
    (sop : T → T → T) (fop : Float → Float → Float)
    (hrun : ∀ (tt : Tape Float) (idA idB : Nat) {va vb : T},
       tt.requireValue (s := S) idA = .ok va → tt.requireValue (s := S) idB = .ok vb →
       ∃ nd : Node Float, (top idA idB).run tt = .ok (tt.size, (tt.addNode nd).1) ∧
         nd.name = some nm ∧ nd.parents = #[idA, idB] ∧
         nd.value = Spec.SomeTensor.ofTensor (sop va vb))
    (hcop : ∀ a b : Float, cOpT tables nm [a, b] = .ok (fop a b))
    {a b : TB} {va vb : T} {xa xb : Float}
    (ha : FaithfulT tables env a va xa) (hb : FaithfulT tables env b vb xb) :
    FaithfulT tables env (TapeBuilder.bin top a b) (sop va vb) (fop xa xb) := by
  intro t vals hev hsz
  obtain ⟨idA, tA, valsA, harun, haLt, haStore, haExt, haEv, haSz, haVal, haPre⟩ := ha t vals hev hsz
  obtain ⟨idB, tB, valsB, hbrun, hbLt, hbStore, hbExt, hbEv, hbSz, hbVal, hbPre⟩ :=
    hb tA valsA haEv haSz
  have haStoreB : tB.requireValue (s := S) idA = .ok va := (hbExt.2 idA haLt).trans haStore
  obtain ⟨nd, hndRun, hndName, hndPar, hndVal⟩ := hrun tB idA idB haStoreB hbStore
  have hidA_valsA : idA < valsA.size := by rw [haSz]; exact haLt
  have hxa : valsB.getD idA 0.0 = xa := (hbPre idA hidA_valsA).trans haVal
  have hstoreNew : (tB.addNode nd).1.requireValue (s := S) tB.size = .ok (sop va vb) :=
    requireValue_addNode_self tB nd hndVal
  have hle1 : vals.size ≤ valsA.size := by rw [hsz, haSz]; exact haExt.1
  have hle2 : valsA.size ≤ valsB.size := by rw [haSz, hbSz]; exact hbExt.1
  refine ⟨tB.size, (tB.addNode nd).1, valsB.push (fop xa xb),
    ?run, ?lt, ?store, ?ext, ?ev, ?sz, ?val, ?pre⟩
  case run => exact bin_run top a b t tA tB (tB.addNode nd).1 idA idB tB.size harun hbrun hndRun
  case store => exact hstoreNew
  case lt => exact requireValue_lt_of_ok _ tB.size hstoreNew
  case ext => exact (extends_of_value hstoreNew (frameOver_addNode tB nd)).trans (hbExt.trans haExt)
  case ev =>
    have hstep : stepValT tables env valsB nd = .ok (fop xa xb) := by
      unfold stepValT
      simp only [hndName, hndPar, List.isEmpty_toArray, List.isEmpty_cons, List.map_toArray, List.map_cons,
        List.map_nil,
        Bool.false_eq_true, ite_false]
      rw [hxa, hbVal]; exact hcop xa xb
    rw [evalTapeT_addNode, hbEv]
    show Except.map (fun v => valsB.push v) (stepValT tables env valsB nd)
      = Except.ok (valsB.push (fop xa xb))
    rw [hstep]; rfl
  case sz => rw [Array.size_push, hbSz, Tape.size_addNode]
  case val => rw [← hbSz]; exact getD_push_size valsB (fop xa xb)
  case pre =>
    intro i hi
    have hiA : i < valsA.size := Nat.lt_of_lt_of_le hi hle1
    have hiB : i < valsB.size := Nat.lt_of_lt_of_le hiA hle2
    rw [getD_push_lt valsB _ i hiB, hbPre i hiA, haPre i hi]

theorem FaithfulT_add (tables : String → Option LutTable) (env : String → Float)
    {a b : TB} {va vb : T} {xa xb : Float}
    (ha : FaithfulT tables env a va xa) (hb : FaithfulT tables env b vb xb) :
    FaithfulT tables env (a + b) (addSpec va vb) (xa + xb) := by
  show FaithfulT tables env (TapeBuilder.bin (TapeM.add (s := S)) a b) _ _
  refine FaithfulT_bin tables env (TapeM.add (s := S)) "add" addSpec (· + ·) ?hrun
    (fun a b => (cOpT_base tables rfl [a, b]).trans rfl) ha hb
  intro tt idA idB va vb hA hB
  obtain ⟨nd, heq, hn, hp, hv⟩ := tapeAdd_addNode tt idA idB hA hB
  exact ⟨nd, add_run_ok tt (tt.addNode nd).1 idA idB tt.size heq, hn, hp, hv⟩

theorem FaithfulT_sub (tables : String → Option LutTable) (env : String → Float)
    {a b : TB} {va vb : T} {xa xb : Float}
    (ha : FaithfulT tables env a va xa) (hb : FaithfulT tables env b vb xb) :
    FaithfulT tables env (a - b) (subSpec va vb) (xa - xb) := by
  show FaithfulT tables env (TapeBuilder.bin (TapeM.sub (s := S)) a b) _ _
  refine FaithfulT_bin tables env (TapeM.sub (s := S)) "sub" subSpec (· - ·) ?hrun
    (fun a b => (cOpT_base tables rfl [a, b]).trans rfl) ha hb
  intro tt idA idB va vb hA hB
  obtain ⟨nd, heq, hn, hp, hv⟩ := tapeSub_addNode tt idA idB hA hB
  exact ⟨nd, sub_run_ok tt (tt.addNode nd).1 idA idB tt.size heq, hn, hp, hv⟩

theorem FaithfulT_mul (tables : String → Option LutTable) (env : String → Float)
    {a b : TB} {va vb : T} {xa xb : Float}
    (ha : FaithfulT tables env a va xa) (hb : FaithfulT tables env b vb xb) :
    FaithfulT tables env (a * b) (mulSpec va vb) (xa * xb) := by
  show FaithfulT tables env (TapeBuilder.bin (TapeM.mul (s := S)) a b) _ _
  refine FaithfulT_bin tables env (TapeM.mul (s := S)) "mul" mulSpec (· * ·) ?hrun
    (fun a b => (cOpT_base tables rfl [a, b]).trans rfl) ha hb
  intro tt idA idB va vb hA hB
  obtain ⟨nd, heq, hn, hp, hv⟩ := tapeMul_addNode tt idA idB hA hB
  exact ⟨nd, mul_run_ok tt (tt.addNode nd).1 idA idB tt.size heq, hn, hp, hv⟩

/-! ## The genuinely new step: the fetch preserves the bridge -/

/-- The node `TapeBuilder.lutFetchM` appends, as a function of the operand ids and stored
tensors. -/
def lutNode (tbl : LutTable) (idA idB : Nat) (vl vu : T) : Node Float :=
  { name := some tbl.nodeName
  , value := Spec.SomeTensor.ofTensor (map2Spec (fun a b => tbl.refFetch a b) vl vu)
  , requiresGrad := false
  , parents := #[idA, idB]
  , backward := fun _ => .ok #[] }

/-- Run bridge for the recording action: given the operand sub-runs and their stored tensors on
the final operand tape, `lutFetchM`'s run appends exactly `lutNode` (the `requireValue` reads
inside the action succeed by hypothesis, so the `StateT`/`Except` threading closes). -/
theorem lutFetchM_run (tbl : LutTable) (l u : TB) (t tA tB : Tape Float)
    (idA idB : Nat) {vl vu : T}
    (hl : l.run t = .ok (idA, tA)) (hu : u.run tA = .ok (idB, tB))
    (hL : tB.requireValue (s := S) idA = .ok vl)
    (hU : tB.requireValue (s := S) idB = .ok vu) :
    (TapeBuilder.lutFetchM tbl l u).run t
      = .ok (tB.size, (tB.addNode (lutNode tbl idA idB vl vu)).1) := by
  unfold TapeBuilder.lutFetchM lutNode
  simp only [TapeM.run, StateT.run, StateT.bind, StateT.pure, StateT.lift, StateT.map,
    bind, Bind.bind, pure, Pure.pure, Functor.map, MonadState.get, MonadStateOf.get, getThe,
    StateT.get, MonadStateOf.set, StateT.set, monadLift, MonadLift.monadLift, liftM,
    Except.bind, Except.pure, Tape.addNode, Tape.size, hl, hu, hL, hU]

/-- **Fetch faithfulness.** The recording instance's fetch stores the elementwise `refFetch` of
its parents' stored tensors (recorder half) and re-interprets, under the extended alphabet, to
`refFetch` of the parents' re-interpreted floats (codegen half, `cOpT_lutfetch`) — for every
environment in which the node's table resolves. -/
theorem FaithfulT_lutfetch (tables : String → Option LutTable) (env : String → Float)
    (tbl : LutTable) {tn : String}
    (hn : lutNodeName? tbl.nodeName = some tn) (ht : tables tn = some tbl)
    {l u : TB} {vl vu : T} {xl xu : Float}
    (hl : FaithfulT tables env l vl xl) (hu : FaithfulT tables env u vu xu) :
    FaithfulT tables env (LutInterp.lutFetch tbl l u)
      (map2Spec (fun a b => tbl.refFetch a b) vl vu) (tbl.refFetch xl xu) := by
  intro t vals hev hsz
  obtain ⟨idA, tA, valsA, harun, haLt, haStore, haExt, haEv, haSz, haVal, haPre⟩ := hl t vals hev hsz
  obtain ⟨idB, tB, valsB, hbrun, hbLt, hbStore, hbExt, hbEv, hbSz, hbVal, hbPre⟩ :=
    hu tA valsA haEv haSz
  have haStoreB : tB.requireValue (s := S) idA = .ok vl := (hbExt.2 idA haLt).trans haStore
  have hrun := lutFetchM_run tbl l u t tA tB idA idB harun hbrun haStoreB hbStore
  have hidA_valsA : idA < valsA.size := by rw [haSz]; exact haLt
  have hxa : valsB.getD idA 0.0 = xl := (hbPre idA hidA_valsA).trans haVal
  have hstoreNew : (tB.addNode (lutNode tbl idA idB vl vu)).1.requireValue (s := S) tB.size
      = .ok (map2Spec (fun a b => tbl.refFetch a b) vl vu) :=
    requireValue_addNode_self tB _ rfl
  have hle1 : vals.size ≤ valsA.size := by rw [hsz, haSz]; exact haExt.1
  have hle2 : valsA.size ≤ valsB.size := by rw [haSz, hbSz]; exact hbExt.1
  refine ⟨tB.size, (tB.addNode (lutNode tbl idA idB vl vu)).1,
    valsB.push (tbl.refFetch xl xu), ?run, ?lt, ?store, ?ext, ?ev, ?sz, ?val, ?pre⟩
  case run => exact hrun
  case store => exact hstoreNew
  case lt => exact requireValue_lt_of_ok _ tB.size hstoreNew
  case ext =>
    exact (extends_of_value hstoreNew (frameOver_addNode tB _)).trans (hbExt.trans haExt)
  case ev =>
    have hstep : stepValT tables env valsB (lutNode tbl idA idB vl vu)
        = .ok (tbl.refFetch xl xu) := by
      unfold stepValT lutNode
      simp only [List.isEmpty_toArray, List.isEmpty_cons, List.map_toArray, List.map_cons,
        List.map_nil,
        Bool.false_eq_true, ite_false]
      rw [hxa, hbVal]
      exact cOpT_lutfetch hn tables tbl ht xl xu
    rw [evalTapeT_addNode, hbEv]
    show Except.map (fun v => valsB.push v)
        (stepValT tables env valsB (lutNode tbl idA idB vl vu))
      = Except.ok (valsB.push (tbl.refFetch xl xu))
    rw [hstep]; rfl
  case sz => rw [Array.size_push, hbSz, Tape.size_addNode]
  case val => rw [← hbSz]; exact getD_push_size valsB (tbl.refFetch xl xu)
  case pre =>
    intro i hi
    have hiA : i < valsA.size := Nat.lt_of_lt_of_le hi hle1
    have hiB : i < valsB.size := Nat.lt_of_lt_of_le hiA hle2
    rw [getD_push_lt valsB _ i hiB, hbPre i hiA, haPre i hi]

/-! ## The fixture kernel, faithful for all inputs -/

/-- The mixed arithmetic+fetch model preserves the bridge: fetch on the first two operands, plus
`bias²` through the unchanged base alphabet. -/
theorem lutModel_faithful (env : String → Float)
    {layer u bias : TB} {vlay vu vb : T} {xlay xu xb : Float}
    (hlay : FaithfulT demoTables env layer vlay xlay)
    (hu : FaithfulT demoTables env u vu xu)
    (hb : FaithfulT demoTables env bias vb xb) :
    FaithfulT demoTables env (lutModel layer u bias)
      (addSpec (map2Spec (fun a b => demoLut.refFetch a b) vlay vu) (mulSpec vb vb))
      (demoLut.refFetch xlay xu + xb * xb) := by
  unfold lutModel
  exact FaithfulT_add demoTables env
    (FaithfulT_lutfetch demoTables env demoLut (tn := "demolut")
      (by simp +decide [lutNodeName?, LutTable.nodeName, demoLut]) rfl hlay hu)
    (FaithfulT_mul demoTables env hb hb)

/-- **Capstone (over all inputs).** The exact tape `examples.tape_codegen_lut` records
(`lutRecord`'s program), re-interpreted by the table-extended `evalTapeT` at ANY environment,
computes the `[NumCarrier]+[LutInterp]` source model at that environment — the
`#guard lutEvalFaithful` single-pixel check, promoted to a theorem over all inputs. -/
theorem lut_kernel_faithful (env : String → Float) :
    ∃ (id : Nat) (t' : Tape Float) (vals : Array Float),
      (lutModel (α := TB) (inLeafV "layer" envLayer) (inLeafV "u" envU)
        (inLeafV "bias" envBias)).run Tape.empty = .ok (id, t') ∧
      evalTapeT demoTables env t' = .ok vals ∧
      vals.getD id 0.0 =
        lutModel (α := Float) (env "layer") (env "u") (env "bias") := by
  obtain ⟨id, t', vals, hrun, _, _, _, hev, _, hval, _⟩ :=
    lutModel_faithful env
      (FaithfulT_named_leaf demoTables env "layer" (Tensor.full S envLayer))
      (FaithfulT_named_leaf demoTables env "u" (Tensor.full S envU))
      (FaithfulT_named_leaf demoTables env "bias" (Tensor.full S envBias))
      Tape.empty #[] (evalTapeT_empty demoTables env) rfl
  exact ⟨id, t', vals, hrun, hev, hval⟩

/-! ## Axiom audit — these rest only on the standard axioms (no `sorryAx`). -/

/-- info: 'PropertyKindCalculus.Examples.TapeCodegenLutEndToEnd.FaithfulT_lutfetch' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms FaithfulT_lutfetch

/-- info: 'PropertyKindCalculus.Examples.TapeCodegenLutEndToEnd.lut_kernel_faithful' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms lut_kernel_faithful

end PropertyKindCalculus.Examples.TapeCodegenLutEndToEnd
