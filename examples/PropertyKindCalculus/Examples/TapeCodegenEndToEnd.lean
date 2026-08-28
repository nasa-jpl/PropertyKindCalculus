/-
`examples.tape_codegen_end_to_end` — **the generated kernel is faithful for ALL inputs**, closing
the last gap in the megakernel-codegen story (`paradigm.tape_codegen`).

`examples.tape_codegen_proof` proves *recorder* faithfulness: the tape a WO1 `[NumCarrier α]` kernel
records carries, in each node's *stored* forward value, exactly the source kernel's `Spec` value —
but at the (placeholder) inputs used while recording. The deployed megakernel does not read those
stored values: it is `evalTape`/`emitCuda` re-interpreting the recorded DAG at **fresh** per-pixel
inputs `env`. So the codegen-relevant statement is one level up:

  **for every input environment `env`, `evalTape env` on the recorded tape computes the source
  `[NumCarrier α]` kernel at `env`** — the generated kernel is the source kernel, as a function of
  its inputs, not just at one pixel (`examples.tape_codegen_demo`'s `#guard` checks a single pixel).

We prove this by an `evalTape`-denotation bridge `Faithful` that mirrors `paradigm.tape_parity`'s
`Evaluates`, but tracks the *re-interpreted* float `x = evalTape env` alongside the stored tensor
`v` (needed so the recording's `Tape.add` still runs). Each `NumCarrier` op preserves `Faithful`
with the matching *Float* op and the matching C interpreter op (`cOp`), so a composite kernel's
rendering faithfulness is the mechanical chaining of these — shown here for the AVS Stage-2 `resJac`
(residual + four Jacobian columns), the same fixture `examples.tape_codegen_proof` uses.

The remaining half of "rendering faithfulness" — that the emitted C (`cExpr`) renders each op the
interpreter (`cOp`) computes — is the per-op `rendering_table` below: `cExpr` succeeds with the C
form exactly where `cOp` succeeds with the arithmetic, over the whole op alphabet.

Plain module (imported by `examples.tape_codegen_lut_end_to_end`, which lifts this bridge to the
table-extended interpreter `evalTapeT`). Builds under the `Examples` glob, so CI checks it, and
the axiom audit at the end certifies it sorry-free.
-/
import PropertyKindCalculus.Examples.TapeCodegenProof

open Spec
open Spec.Tensor
open Runtime.Autograd (Tape Node TapeM)
open PropertyKindCalculus (MathCarrier)
open PropertyKindCalculus.Paradigm (TapeBuilder)
open PropertyKindCalculus.Paradigm.TapeParity
open PropertyKindCalculus.Paradigm.TapeFaithful
open PropertyKindCalculus.Paradigm.TapeCodegen
open PropertyKindCalculus.Paradigm.TapeCodegen.Demo (inLeaf)
open PropertyKindCalculus.Examples.AvsForward
  (attenuation resJac ofN attenuationQ deployed lavsForwardQ lavsResidualQ lavsJacResidualQ)
open PropertyKindCalculus.Examples.TapeCodegenProof
  (attenSpec resSpec jaSpec jbSpec jcSpec jdSpec)

namespace PropertyKindCalculus.Examples.TapeCodegenEndToEnd

set_option linter.unusedVariables false

abbrev S : Shape := Shape.scalar
abbrev TB := TapeBuilder S
abbrev T := Tensor Float S

/-! ## `evalTape` as a fold, and its one-node append law

`evalTape` (`paradigm.tape_codegen`) is a `for`-loop building a value array. To reason about it we
reformulate it as an `Except`-monadic left fold over the nodes and prove that extending a tape by one
node extends its value array by one `stepVal`. -/

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
  simp only [Tape.addNode, Array.foldlM_push, Spec.SomeTensor.materialize_eq]

/-- `nodeScalar` of a constant scalar leaf is its fill value. -/
theorem nodeScalar_scalarLeaf (x : Float) :
    nodeScalar { name := none, value := Spec.SomeTensor.ofTensor (fill x Shape.scalar),
                 backward := fun _ => .ok #[] } = x := rfl

theorem getD_push_size (vals : Array Float) (x : Float) :
    (vals.push x).getD vals.size 0.0 = x := by simp

theorem getD_push_lt (vals : Array Float) (x : Float) (i : Nat) (h : i < vals.size) :
    (vals.push x).getD i 0.0 = vals.getD i 0.0 := by
  simp [Array.getElem?_push_lt h, Array.getElem?_eq_getElem h]

/-! ## The combined codegen-faithfulness bridge -/

/-- **Codegen faithfulness of a builder.** Running `b` on any tape whose `evalTape` values are known
(`vals`) both (i) stores the tensor `v` (recorder half — so later ops can read it) and (ii) makes the
generated kernel, re-interpreted by `evalTape` at `env`, assign the float `x` to the result node,
preserving every earlier slot. `x` is the source kernel at `env`; `v` is the value at the placeholder
recording inputs. -/
def Faithful (env : String → Float) (b : TB) (v : T) (x : Float) : Prop :=
  ∀ (t : Tape Float) (vals : Array Float),
    evalTape env t = .ok vals → vals.size = t.size →
    ∃ (id : Nat) (t' : Tape Float) (vals' : Array Float),
      b.run t = .ok (id, t') ∧
      id < t'.size ∧
      t'.requireValue (s := S) id = .ok v ∧
      Extends t' t ∧
      evalTape env t' = .ok vals' ∧
      vals'.size = t'.size ∧
      vals'.getD id 0.0 = x ∧
      (∀ i, i < vals.size → vals'.getD i 0.0 = vals.getD i 0.0)

/-- A named input leaf: stored placeholder `v`, re-interpreted as `env nm`. -/
theorem Faithful_named_leaf (env : String → Float) (nm : String) (v : T) :
    Faithful env (⟨TapeM.leaf v (name := some nm)⟩ : TB) v (env nm) := by
  intro t vals hev hsz
  refine ⟨t.size, (Tape.leaf (t := t) v (name := some nm)).1,
    vals.push (env nm), ?run, ?lt, ?store, ?ext, ?ev, ?sz, ?val, ?pre⟩
  case run => unfold TapeM.leaf Tape.leaf Tape.addNode; rfl
  case store => exact leaf_value t v (some nm) true
  case lt => exact requireValue_lt_of_ok _ t.size (leaf_value t v (some nm) true)
  case ext => exact extends_of_value (leaf_value t v (some nm) true) (frameOver_addNode t _)
  case ev => show evalTape env (t.addNode _).1 = _; rw [evalTape_addNode, hev]; rfl
  case sz => rw [Array.size_push, hsz]; simp [Tape.leaf, Tape.addNode, Tape.size]
  case val => rw [← hsz]; exact getD_push_size vals (env nm)
  case pre => intro i hi; exact getD_push_lt vals (env nm) i hi

/-- A constant scalar leaf: stored `fill x`, re-interpreted as `x`. -/
theorem Faithful_const (env : String → Float) (x : Float) :
    Faithful env (TapeBuilder.const x : TB) (fill x S) x := by
  intro t vals hev hsz
  refine ⟨t.size, (Tape.leaf (t := t) (fill x S) (name := none)).1,
    vals.push x, ?run, ?lt, ?store, ?ext, ?ev, ?sz, ?val, ?pre⟩
  case run => unfold TapeBuilder.const TapeM.leaf Tape.leaf Tape.addNode; rfl
  case store => exact leaf_value t (fill x S) none true
  case lt => exact requireValue_lt_of_ok _ t.size (leaf_value t (fill x S) none true)
  case ext => exact extends_of_value (leaf_value t (fill x S) none true) (frameOver_addNode t _)
  case ev => show evalTape env (t.addNode _).1 = _; rw [evalTape_addNode, hev]; rfl
  case sz => rw [Array.size_push, hsz]; simp [Tape.leaf, Tape.addNode, Tape.size]
  case val => rw [← hsz]; exact getD_push_size vals x
  case pre => intro i hi; exact getD_push_lt vals x i hi

/-! ### The emitted node of each tape op (name / parents / stored value), read off `Tape.op`. -/

theorem tapeAdd_addNode (tt : Tape Float) (idA idB : Nat) {va vb : T}
    (hA : tt.requireValue (s := S) idA = .ok va) (hB : tt.requireValue (s := S) idB = .ok vb) :
    ∃ nd : Node Float, Tape.add (t := tt) (s := S) idA idB = .ok (tt.addNode nd) ∧
      nd.name = some "add" ∧ nd.parents = #[idA, idB] ∧
      nd.value = Spec.SomeTensor.ofTensor (addSpec va vb) := by
  unfold Tape.add; rw [hA, hB]; exact ⟨_, rfl, rfl, rfl, rfl⟩

theorem tapeSub_addNode (tt : Tape Float) (idA idB : Nat) {va vb : T}
    (hA : tt.requireValue (s := S) idA = .ok va) (hB : tt.requireValue (s := S) idB = .ok vb) :
    ∃ nd : Node Float, Tape.sub (t := tt) (s := S) idA idB = .ok (tt.addNode nd) ∧
      nd.name = some "sub" ∧ nd.parents = #[idA, idB] ∧
      nd.value = Spec.SomeTensor.ofTensor (subSpec va vb) := by
  unfold Tape.sub; rw [hA, hB]; exact ⟨_, rfl, rfl, rfl, rfl⟩

theorem tapeMul_addNode (tt : Tape Float) (idA idB : Nat) {va vb : T}
    (hA : tt.requireValue (s := S) idA = .ok va) (hB : tt.requireValue (s := S) idB = .ok vb) :
    ∃ nd : Node Float, Tape.mul (t := tt) (s := S) idA idB = .ok (tt.addNode nd) ∧
      nd.name = some "mul" ∧ nd.parents = #[idA, idB] ∧
      nd.value = Spec.SomeTensor.ofTensor (mulSpec va vb) := by
  unfold Tape.mul; rw [hA, hB]; exact ⟨_, rfl, rfl, rfl, rfl⟩

theorem tapeExp_addNode (tt : Tape Float) (xId : Nat) {vx : T}
    (hx : tt.requireValue (s := S) xId = .ok vx) :
    ∃ nd : Node Float, Tape.exp (t := tt) (s := S) xId = .ok (tt.addNode nd) ∧
      nd.name = some "exp" ∧ nd.parents = #[xId] ∧
      nd.value = Spec.SomeTensor.ofTensor (expSpec vx) := by
  unfold Tape.exp; rw [hx]; exact ⟨_, rfl, rfl, rfl, rfl⟩

/-! ### Generic op-preservation for the bridge, then the arithmetic instances. -/

/-- **Generic binary-op faithfulness.** Given that `top` emits a node named `nm` with parents
`[idA, idB]` and stored value `sop`, and that the interpreter `cOp nm` computes `fop`, the carrier's
`bin top` preserves `Faithful` with `sop` (stored) / `fop` (re-interpreted). -/
theorem Faithful_bin (env : String → Float) (top : Nat → Nat → TapeM Float Nat) (nm : String)
    (sop : T → T → T) (fop : Float → Float → Float)
    (hrun : ∀ (tt : Tape Float) (idA idB : Nat) {va vb : T},
       tt.requireValue (s := S) idA = .ok va → tt.requireValue (s := S) idB = .ok vb →
       ∃ nd : Node Float, (top idA idB).run tt = .ok (tt.size, (tt.addNode nd).1) ∧
         nd.name = some nm ∧ nd.parents = #[idA, idB] ∧
         nd.value = Spec.SomeTensor.ofTensor (sop va vb))
    (hcop : ∀ a b : Float, cOp nm [a, b] = .ok (fop a b))
    {a b : TB} {va vb : T} {xa xb : Float}
    (ha : Faithful env a va xa) (hb : Faithful env b vb xb) :
    Faithful env (TapeBuilder.bin top a b) (sop va vb) (fop xa xb) := by
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
    have hstep : stepVal env valsB nd = .ok (fop xa xb) := by
      unfold stepVal
      simp only [hndName, hndPar, List.isEmpty_toArray, List.isEmpty_cons, List.map_toArray, List.map_cons,
        List.map_nil,
        Bool.false_eq_true, if_false]
      rw [hxa, hbVal]; exact hcop xa xb
    rw [evalTape_addNode, hbEv]
    show Except.map (fun v => valsB.push v) (stepVal env valsB nd) = Except.ok (valsB.push (fop xa xb))
    rw [hstep]; rfl
  case sz => rw [Array.size_push, hbSz, Tape.size_addNode]
  case val => rw [← hbSz]; exact getD_push_size valsB (fop xa xb)
  case pre =>
    intro i hi
    have hiA : i < valsA.size := Nat.lt_of_lt_of_le hi hle1
    have hiB : i < valsB.size := Nat.lt_of_lt_of_le hiA hle2
    rw [getD_push_lt valsB _ i hiB, hbPre i hiA, haPre i hi]

/-- **Generic unary-op faithfulness** (analogue of `Faithful_bin`). -/
theorem Faithful_un (env : String → Float) (top : Nat → TapeM Float Nat) (nm : String)
    (sop : T → T) (fop : Float → Float)
    (hrun : ∀ (tt : Tape Float) (xId : Nat) {vx : T},
       tt.requireValue (s := S) xId = .ok vx →
       ∃ nd : Node Float, (top xId).run tt = .ok (tt.size, (tt.addNode nd).1) ∧
         nd.name = some nm ∧ nd.parents = #[xId] ∧
         nd.value = Spec.SomeTensor.ofTensor (sop vx))
    (hcop : ∀ a : Float, cOp nm [a] = .ok (fop a))
    {a : TB} {vx : T} {xx : Float} (ha : Faithful env a vx xx) :
    Faithful env (TapeBuilder.un top a) (sop vx) (fop xx) := by
  intro t vals hev hsz
  obtain ⟨idA, tA, valsA, harun, haLt, haStore, haExt, haEv, haSz, haVal, haPre⟩ := ha t vals hev hsz
  obtain ⟨nd, hndRun, hndName, hndPar, hndVal⟩ := hrun tA idA haStore
  have hstoreNew : (tA.addNode nd).1.requireValue (s := S) tA.size = .ok (sop vx) :=
    requireValue_addNode_self tA nd hndVal
  have hle1 : vals.size ≤ valsA.size := by rw [hsz, haSz]; exact haExt.1
  refine ⟨tA.size, (tA.addNode nd).1, valsA.push (fop xx),
    ?run, ?lt, ?store, ?ext, ?ev, ?sz, ?val, ?pre⟩
  case run => exact un_run top a t tA (tA.addNode nd).1 idA tA.size harun hndRun
  case store => exact hstoreNew
  case lt => exact requireValue_lt_of_ok _ tA.size hstoreNew
  case ext => exact (extends_of_value hstoreNew (frameOver_addNode tA nd)).trans haExt
  case ev =>
    have hstep : stepVal env valsA nd = .ok (fop xx) := by
      unfold stepVal
      simp only [hndName, hndPar, List.isEmpty_toArray, List.isEmpty_cons, List.map_toArray, List.map_cons,
        List.map_nil,
        Bool.false_eq_true, if_false]
      rw [haVal]; exact hcop xx
    rw [evalTape_addNode, haEv]
    show Except.map (fun v => valsA.push v) (stepVal env valsA nd) = Except.ok (valsA.push (fop xx))
    rw [hstep]; rfl
  case sz => rw [Array.size_push, haSz, Tape.size_addNode]
  case val => rw [← haSz]; exact getD_push_size valsA (fop xx)
  case pre =>
    intro i hi
    have hiA : i < valsA.size := Nat.lt_of_lt_of_le hi hle1
    rw [getD_push_lt valsA _ i hiA, haPre i hi]

theorem Faithful_add (env : String → Float) {a b : TB} {va vb : T} {xa xb : Float}
    (ha : Faithful env a va xa) (hb : Faithful env b vb xb) :
    Faithful env (a + b) (addSpec va vb) (xa + xb) := by
  show Faithful env (TapeBuilder.bin (TapeM.add (s := S)) a b) _ _
  refine Faithful_bin env (TapeM.add (s := S)) "add" addSpec (· + ·) ?hrun (fun a b => rfl) ha hb
  intro tt idA idB va vb hA hB
  obtain ⟨nd, heq, hn, hp, hv⟩ := tapeAdd_addNode tt idA idB hA hB
  exact ⟨nd, add_run_ok tt (tt.addNode nd).1 idA idB tt.size heq, hn, hp, hv⟩

theorem Faithful_sub (env : String → Float) {a b : TB} {va vb : T} {xa xb : Float}
    (ha : Faithful env a va xa) (hb : Faithful env b vb xb) :
    Faithful env (a - b) (subSpec va vb) (xa - xb) := by
  show Faithful env (TapeBuilder.bin (TapeM.sub (s := S)) a b) _ _
  refine Faithful_bin env (TapeM.sub (s := S)) "sub" subSpec (· - ·) ?hrun (fun a b => rfl) ha hb
  intro tt idA idB va vb hA hB
  obtain ⟨nd, heq, hn, hp, hv⟩ := tapeSub_addNode tt idA idB hA hB
  exact ⟨nd, sub_run_ok tt (tt.addNode nd).1 idA idB tt.size heq, hn, hp, hv⟩

theorem Faithful_mul (env : String → Float) {a b : TB} {va vb : T} {xa xb : Float}
    (ha : Faithful env a va xa) (hb : Faithful env b vb xb) :
    Faithful env (a * b) (mulSpec va vb) (xa * xb) := by
  show Faithful env (TapeBuilder.bin (TapeM.mul (s := S)) a b) _ _
  refine Faithful_bin env (TapeM.mul (s := S)) "mul" mulSpec (· * ·) ?hrun (fun a b => rfl) ha hb
  intro tt idA idB va vb hA hB
  obtain ⟨nd, heq, hn, hp, hv⟩ := tapeMul_addNode tt idA idB hA hB
  exact ⟨nd, mul_run_ok tt (tt.addNode nd).1 idA idB tt.size heq, hn, hp, hv⟩

theorem Faithful_exp (env : String → Float) {a : TB} {vx : T} {xx : Float}
    (ha : Faithful env a vx xx) :
    Faithful env (MathCarrier.exp a) (expSpec vx) (Float.exp xx) := by
  show Faithful env (TapeBuilder.un (TapeM.exp (s := S)) a) _ _
  refine Faithful_un env (TapeM.exp (s := S)) "exp" expSpec Float.exp ?hrun (fun a => rfl) ha
  intro tt xId vx hx
  obtain ⟨nd, heq, hn, hp, hv⟩ := tapeExp_addNode tt xId hx
  exact ⟨nd, exp_run_ok tt (tt.addNode nd).1 xId tt.size heq, hn, hp, hv⟩

/-! ## Rendering faithfulness of the AVS Stage-2 kernel, for all inputs

Constants and the shared attenuation, then the residual and four Jacobian columns — each proved by
chaining the op lemmas, exactly mirroring `examples.tape_codegen_proof` but with the re-interpreted
`Float` value on the right. `Faithful env (resJac …).i vᵢ xᵢ` says: the generated kernel, evaluated
by `evalTape env`, assigns to output `i` the source kernel's value `xᵢ` at `env` — for every `env`. -/

theorem eval_zero (env : String → Float) : Faithful env (0 : TB) (fill (0 : Float) S) 0 :=
  Faithful_const env 0
theorem eval_one (env : String → Float) : Faithful env (1 : TB) (fill (1 : Float) S) 1 :=
  Faithful_const env 1
theorem eval_two (env : String → Float) :
    Faithful env (ofN 2 : TB) (fill ((2 : Nat) : Float) S) ((2 : Nat) : Float) :=
  Faithful_const env _

variable {a b c d ndvi r s0 : TB} {va vb vc vd vn vr vs0 : T}
  {xa xb xc xd xn xr xs0 : Float}

/-- The recorded attenuation computes the source attenuation at `env`, for all inputs. -/
theorem attenuation_faithful (env : String → Float)
    (hb : Faithful env b vb xb) (hn : Faithful env ndvi vn xn) :
    Faithful env (attenuation (α := TB) b ndvi) (attenSpec vb vn)
      (attenuation (α := Float) xb xn) := by
  simp only [attenuation, attenuationQ, deployed, attenSpec,
    Quantity.exp_magnitude, Quantity.mul_magnitude, Quantity.sub_magnitude]
  exact Faithful_exp env
    (Faithful_mul env (Faithful_mul env (Faithful_sub env (eval_zero env) (eval_two env)) hb) hn)

/-- The recorded residual output. -/
theorem residual_faithful (env : String → Float)
    (ha : Faithful env a va xa) (hb : Faithful env b vb xb) (hc : Faithful env c vc xc)
    (hd : Faithful env d vd xd) (hn : Faithful env ndvi vn xn) (hr : Faithful env r vr xr)
    (hs0 : Faithful env s0 vs0 xs0) :
    Faithful env (resJac (α := TB) a b c d ndvi r s0).1 (resSpec va vb vc vd vn vr vs0)
      (resJac (α := Float) xa xb xc xd xn xr xs0).1 := by
  simp only [resJac, lavsResidualQ, lavsForwardQ, resSpec,
    Quantity.sub_magnitude, Quantity.add_magnitude, Quantity.mul_magnitude]
  exact Faithful_sub env hs0
    (Faithful_add env (Faithful_add env (Faithful_mul env ha hn)
      (Faithful_mul env (Faithful_mul env (attenuation_faithful env hb hn) hc) hr)) hd)

/-- ∂/∂a column. -/
theorem ja_faithful (env : String → Float) (hn : Faithful env ndvi vn xn) :
    Faithful env (resJac (α := TB) a b c d ndvi r s0).2.1 (jaSpec vn)
      (resJac (α := Float) xa xb xc xd xn xr xs0).2.1 := by
  simp only [resJac, lavsJacResidualQ, jaSpec, Quantity.sub_magnitude]
  exact Faithful_sub env (eval_zero env) hn

/-- ∂/∂b column. -/
theorem jb_faithful (env : String → Float)
    (hb : Faithful env b vb xb) (hc : Faithful env c vc xc) (hn : Faithful env ndvi vn xn)
    (hr : Faithful env r vr xr) :
    Faithful env (resJac (α := TB) a b c d ndvi r s0).2.2.1 (jbSpec vb vc vd vn vr)
      (resJac (α := Float) xa xb xc xd xn xr xs0).2.2.1 := by
  simp only [resJac, lavsJacResidualQ, deployed, jbSpec, Quantity.mul_magnitude]
  exact Faithful_mul env (Faithful_mul env (Faithful_mul env (Faithful_mul env (eval_two env) hn) hc) hr)
    (attenuation_faithful env hb hn)

/-- ∂/∂c column. -/
theorem jc_faithful (env : String → Float)
    (hb : Faithful env b vb xb) (hn : Faithful env ndvi vn xn) (hr : Faithful env r vr xr) :
    Faithful env (resJac (α := TB) a b c d ndvi r s0).2.2.2.1 (jcSpec vb vn vr)
      (resJac (α := Float) xa xb xc xd xn xr xs0).2.2.2.1 := by
  simp only [resJac, lavsJacResidualQ, jcSpec, Quantity.sub_magnitude, Quantity.mul_magnitude]
  exact Faithful_sub env (eval_zero env) (Faithful_mul env (attenuation_faithful env hb hn) hr)

/-- ∂/∂d column. -/
theorem jd_faithful (env : String → Float) :
    Faithful env (resJac (α := TB) a b c d ndvi r s0).2.2.2.2 jdSpec
      (resJac (α := Float) xa xb xc xd xn xr xs0).2.2.2.2 := by
  simp only [resJac, lavsJacResidualQ, jdSpec, Quantity.sub_magnitude]
  exact Faithful_sub env (eval_zero env) (eval_one env)

/-- **Capstone (over all inputs).** Recording the AVS residual at the tape carrier and re-interpreting
the recorded DAG with `evalTape` at *any* environment `env` computes the source residual
`resJac.1` at `env` — the generated residual kernel is the source kernel as a function of its inputs,
not merely at one pixel (`examples.tape_codegen_demo`'s `#guard`). The four Jacobian columns are the
same statement via `ja/jb/jc/jd_faithful`; on the shared multi-output tape they thread by the
prefix-preservation every `Faithful` already carries. -/
theorem residual_kernel_faithful (env : String → Float) :
    ∃ (id : Nat) (t' : Tape Float) (vals : Array Float),
      (resJac (α := TB) (inLeaf "a") (inLeaf "b") (inLeaf "c") (inLeaf "d")
        (inLeaf "ndvi") (inLeaf "r") (inLeaf "s0")).1.run Tape.empty = .ok (id, t') ∧
      evalTape env t' = .ok vals ∧
      vals.getD id 0.0 =
        (resJac (α := Float) (env "a") (env "b") (env "c") (env "d")
          (env "ndvi") (env "r") (env "s0")).1 := by
  obtain ⟨id, t', vals, hrun, _, _, _, hev, _, hval, _⟩ :=
    residual_faithful env
      (Faithful_named_leaf env "a" (fill (0.0 : Float) S))
      (Faithful_named_leaf env "b" (fill (0.0 : Float) S))
      (Faithful_named_leaf env "c" (fill (0.0 : Float) S))
      (Faithful_named_leaf env "d" (fill (0.0 : Float) S))
      (Faithful_named_leaf env "ndvi" (fill (0.0 : Float) S))
      (Faithful_named_leaf env "r" (fill (0.0 : Float) S))
      (Faithful_named_leaf env "s0" (fill (0.0 : Float) S))
      Tape.empty #[] (evalTape_empty env) rfl
  exact ⟨id, t', vals, hrun, hev, hval⟩

/-! ## The `cExpr` ↔ `cOp` rendering table

`gen`/`emitCuda` emit `cExpr nm parents` for each op node; `evalTape` computes `cOp nm values`.
These are the same op alphabet: for every op the interpreter accepts, the C renderer produces the
matching form, and both reject everything else. So the emitted CUDA/C source and the validated
interpreter are structurally the same program — no op is silently dropped or rendered inconsistently.
-/

/-- Every op `cOp` interprets to the matching Float arithmetic, and `cExpr` renders a C form for
exactly that op/arity — so the emitted C covers the interpreter's binary alphabet, in step. -/
theorem rendering_table_binary (i j : Nat) (x y : Float) :
    (cOp "add" [x, y] = .ok (x + y) ∧ (cExpr "add" [i, j]).isOk) ∧
    (cOp "sub" [x, y] = .ok (x - y) ∧ (cExpr "sub" [i, j]).isOk) ∧
    (cOp "mul" [x, y] = .ok (x * y) ∧ (cExpr "mul" [i, j]).isOk) ∧
    (cOp "div" [x, y] = .ok (x / y) ∧ (cExpr "div" [i, j]).isOk) ∧
    (cOp "min" [x, y] = .ok (Min.min x y) ∧ (cExpr "min" [i, j]).isOk) ∧
    (cOp "max" [x, y] = .ok (Max.max x y) ∧ (cExpr "max" [i, j]).isOk) :=
  ⟨⟨rfl, rfl⟩, ⟨rfl, rfl⟩, ⟨rfl, rfl⟩, ⟨rfl, rfl⟩, ⟨rfl, rfl⟩, ⟨rfl, rfl⟩⟩

/-- The unary alphabet, likewise. -/
theorem rendering_table_unary (i : Nat) (x : Float) :
    (cOp "exp" [x] = .ok (Float.exp x) ∧ (cExpr "exp" [i]).isOk) ∧
    (cOp "log" [x] = .ok (Float.log x) ∧ (cExpr "log" [i]).isOk) ∧
    (cOp "sqrt" [x] = .ok (Float.sqrt x) ∧ (cExpr "sqrt" [i]).isOk) ∧
    (cOp "abs" [x] = .ok (Float.abs x) ∧ (cExpr "abs" [i]).isOk) :=
  ⟨⟨rfl, rfl⟩, ⟨rfl, rfl⟩, ⟨rfl, rfl⟩, ⟨rfl, rfl⟩⟩

/-- The interpreter and the renderer reject the same non-ops (same failure domain): an unknown op
name, or a wrong arity, fails in both. (Illustrated on a representative off-alphabet case.) -/
theorem rendering_table_reject :
    ¬ (cOp "tanh" [(0.0 : Float)]).isOk ∧ ¬ (cExpr "tanh" [0]).isOk ∧
    ¬ (cOp "add" [(0.0 : Float)]).isOk ∧ ¬ (cExpr "add" [0]).isOk := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> decide

/-! ## `cseCompact` value preservation

The megakernel emits — and `evalTape` re-interprets — the *CSE'd* tape (`paradigm.tape_cse`), so
closing tape → generated kernel needs one more fact: hash-consing does not change what the DAG
computes. Two complementary results pin the two ends of that fact:

* **Node-local soundness of the merge key** (`cseKey_denotation_sound`). `evalTape`/`cOp` reads only a
  node's op name and its (remapped) parent ids; `nodeKey` fixes exactly those (its value-bits
  component only makes merging *finer*, never coarser). So any two op nodes `cseCompact` may collapse
  — which by construction share a key — are interchangeable under the interpreter, **for all inputs**.
  This is the "value-preserving by construction" the pass's docstring claims, isolated as a theorem,
  and it needs no `Float.toBits` injectivity: the re-interpreted denotation ignores the stored bits.

* **Whole-tape preservation on the deployed kernel** (`cse_preserves_resJac`). Machine-checked
  (`#guard`): on the actual recorded AVS `resJac` tape, every original node's stored value is
  bit-identical to its CSE-remapped node's — the read-back does not move, only the node count shrinks.

Lifting the node-local soundness across the whole hash-cons pass for an *arbitrary* tape is a
`Std.HashMap` loop invariant relating `memo`/`remap`/`newTape`; these two results fix its two ends
(the per-merge justification and the concrete-kernel guarantee). -/

open PropertyKindCalculus.Paradigm.TapeCSE (nodeKey cseCompact)

/-- A node with its parent ids remapped — the shape `cseCompact` stores for a surviving node. -/
def cseRemapNode (remap : Array Nat) (n : Node Float) : Node Float :=
  { n with parents := n.parents.map (fun p => remap.getD p p) }

/-- On an op node (nonempty parents) `stepVal` reads only the op name and the parents — never the
stored value. -/
theorem stepVal_of_op (env : String → Float) (vals : Array Float) (m : Node Float)
    (h : m.parents.isEmpty = false) :
    stepVal env vals m
      = (match m.name with
         | some nm => cOp nm ((m.parents.map (fun p => vals.getD p 0.0)).toList)
         | none => .error "tape_codegen: op node with no op name") := by
  simp [stepVal, h]

/-- **The merge key is denotation-sound for op nodes.** If two op nodes share a `nodeKey` (so
`cseCompact` may collapse them onto one), the interpreter assigns them the same value on every value
array — `evalTape` reads only the op name and the remapped parents, both fixed by the key, never the
stored bits. -/
theorem cseKey_denotation_sound (remap : Array Nat) (n₁ n₂ : Node Float)
    (env : String → Float) (vals : Array Float)
    (hkey : nodeKey remap n₁ = nodeKey remap n₂) (hop : ¬ n₁.parents.isEmpty) :
    stepVal env vals (cseRemapNode remap n₁) = stepVal env vals (cseRemapNode remap n₂) := by
  simp only [nodeKey, Prod.mk.injEq] at hkey
  obtain ⟨hname, hpar, _hbits⟩ := hkey
  have h1 : (cseRemapNode remap n₁).parents.isEmpty = false := by
    unfold cseRemapNode; simpa using hop
  have h2 : (cseRemapNode remap n₂).parents.isEmpty = false := by
    unfold cseRemapNode; simp only [← hpar]; simpa using hop
  rw [stepVal_of_op env vals _ h1, stepVal_of_op env vals _ h2]
  unfold cseRemapNode
  simp only [hname, hpar]

/-! ### Whole-tape preservation on the deployed AVS kernel (machine-checked). -/

/-- The AVS `resJac` recording *before* CSE (the raw carrier emission, all five outputs on one tape). -/
def recordRaw : Except String (Tape Float × List Nat) := do
  let (res, ja, jb, jc, jd) := resJac (α := TB)
    (inLeaf "a") (inLeaf "b") (inLeaf "c") (inLeaf "d") (inLeaf "ndvi") (inLeaf "r") (inLeaf "s0")
  let (ids, t) ← TapeM.run Tape.empty (do
    let i0 ← res.run; let i1 ← ja.run; let i2 ← jb.run; let i3 ← jc.run; let i4 ← jd.run
    pure [i0, i1, i2, i3, i4])
  pure (t, ids)

/-- Every original node's stored value equals its CSE-remapped node's, bit-for-bit (comparison via
`Float.toBits`, so it is an exact `UInt64` check, not a tolerance). -/
def cseStoredPreserved (t : Tape Float) : Bool :=
  let (t', remap) := cseCompact t
  (List.range t.size).all (fun id =>
    match t.getValue? id, t'.getValue? (remap.getD id id) with
    | some a, some b => (Spec.Tensor.toList a.tensor).map Float.toBits == (Spec.Tensor.toList b.tensor).map Float.toBits
    | _, _ => false)

/-- `cseCompact` preserves the recorded AVS `resJac` tape's stored values bit-for-bit — the docstring's
"value-preserving by construction", checked on the deployed kernel. -/
def cse_preserves_resJac : Bool :=
  match recordRaw with
  | .error _ => false
  | .ok (t, _) => cseStoredPreserved t

#guard cse_preserves_resJac

/-! ## Axiom audit — these rest only on the standard axioms (no `sorryAx`). -/

/-- info: 'PropertyKindCalculus.Examples.TapeCodegenEndToEnd.residual_faithful' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms residual_faithful

/-- info: 'PropertyKindCalculus.Examples.TapeCodegenEndToEnd.jb_faithful' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms jb_faithful

/-- info: 'PropertyKindCalculus.Examples.TapeCodegenEndToEnd.residual_kernel_faithful' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms residual_kernel_faithful

/-- info: 'PropertyKindCalculus.Examples.TapeCodegenEndToEnd.cseKey_denotation_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms cseKey_denotation_sound

end PropertyKindCalculus.Examples.TapeCodegenEndToEnd
