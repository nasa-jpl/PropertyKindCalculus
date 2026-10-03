/-
# Worked example — the `TapeM` bridge: `do`-block programs are eager-provenance-covered

`Runtime.Autograd.TapeM` (`StateT (Tape α) Result`) is the tape-builder monad TorchLean users
write eager programs in: each `TapeM.<op>` implicitly threads the tape around the pure
`Tape.<op>`. The eager-provenance closure (`Experiments/EagerProvenance.lean`) covers tapes
built by *explicit* `Tape.<op>` chains; this file closes the remaining gap to the monadic
style:

  * **The uniform reshuffle, reduced once — upstream.** Every `TapeM` op wrapper is
    `TapeM.Internal.record` at its pure op, and TorchLean's `Proofs.Autograd.Builder` reduces
    that threading once: `record_run_ok` / `record_run_inv` relate a pure op's success to the
    wrapped op's `run` success, the per-op family (`run_mul_ok`, `run_scale_ok`, …) is
    `record_run_ok` at each op, `run_leaf` computes the total leaf, and `run_bind_inv` inverts
    a successful `run` of `m >>= f` into its two successful stages, so a `do`-block's `run`
    hypothesis decomposes into per-op `.ok` facts. This file consumes that layer.
  * **The demo** — `progMulScale`, the user-style program
    `do let a ← leaf x₀; let b ← leaf x₁; let m ← mul a b; scale m c`: a successful `run`
    from the empty tape yields `EagerBuilds` for the 2-node P-graph `scale (mul x₀ x₁) c` by
    composing the constructors — so `direct_PR_soundness_eager` covers the tape the monadic
    program actually built, with no compilation and no hand-threading.

Axiom pins confirm the classical trio only.
-/

module

public import PropertyKindCalculus.UncertaintyExamples.AutogradDirectSim
meta import PropertyKindCalculus.UncertaintyExamples.AutogradDirectSim
public import NN.Runtime.Autograd.Engine.TapeM
meta import NN.Runtime.Autograd.Engine.TapeM
public import NN.Proofs.Autograd.Tape.Builder
meta import NN.Proofs.Autograd.Tape.Builder

@[expose] public section Blanket

namespace PropertyKindCalculus.UncertaintyExamples.TapeMBridge

open Spec TorchLean TorchLean.Tensor Proofs Proofs.Autograd
open PropertyKindCalculus.UncertaintyExamples.AutogradDirectSim
open Runtime.Autograd (Tape TapeM Result)
open Proofs.Autograd.Builder (record_run_inv run_bind_inv run_leaf)

noncomputable section

/-! ## The demo: a `do`-block program is eager-provenance-covered -/

/-- The fresh id a successful `Tape.mul` returns is the pre-append tape size (the
    `addNode` invariant, read back through the op's `do`-block). -/
theorem tape_mul_id {s : Shape} {t t' : Tape ℝ} {aId bId id : Nat}
    (h : Runtime.Autograd.Tape.mul (α := ℝ) (s := s) t aId bId = .ok (t', id)) :
    id = t.size := by
  cases hA : Runtime.Autograd.Tape.requireValue (α := ℝ) (t := t) (s := s) aId with
  | error e => simp [Runtime.Autograd.Tape.mul, Runtime.Autograd.Tape.binary, hA, bind, Except.bind] at h
  | ok aT =>
    cases hB : Runtime.Autograd.Tape.requireValue (α := ℝ) (t := t) (s := s) bId with
    | error e => simp [Runtime.Autograd.Tape.mul, Runtime.Autograd.Tape.binary, hA, hB, bind, Except.bind] at h
    | ok bT =>
      simp only [Runtime.Autograd.Tape.mul, Runtime.Autograd.Tape.binary, hA, hB, bind, Except.bind,
        pure, Except.pure, Except.ok.injEq] at h
      have h2 := congrArg Prod.snd h
      rw [Runtime.Autograd.Tape.addNode_id] at h2
      exact h2.symm

/-- User-style eager program: `(x₀ * x₁) * c`, written monadically. -/
def progMulScale (c : ℝ) (x0T x1T : Tensor ℝ Shape.scalar) : TapeM ℝ Nat := do
  let a ← TapeM.leaf x0T
  let b ← TapeM.leaf x1T
  let m ← TapeM.mul (α := ℝ) (s := Shape.scalar) a b
  TapeM.scale (α := ℝ) (s := Shape.scalar) m c

/-- Index of the `mul` output in the context extended by the first node. -/
def ixm : Idx (Γ2 ++ [Shape.scalar]) Shape.scalar := ⟨⟨2, by decide⟩, rfl⟩

/-- The 2-node P-graph the program realises: `scale (mul x₀ x₁) c`. -/
def mulScaleGraph (c : ℝ) : Graph Γ2 [Shape.scalar, Shape.scalar] :=
  .snoc (.snoc .nil (TapeNodes.mul ix0 ix1)) (TapeNodes.scale ixm c)

set_option maxHeartbeats 6400000 in
/-- The bridge demo: a successful monadic `run` of `progMulScale` from the empty tape is
    covered by `EagerBuilds` at `mulScaleGraph` — the closure reaches `do`-block programs.

    The proof is pure peeling: three `run_bind_inv` decompose the `do`-block,
    `run_leaf` computes the two leaf stages (ids `0`, `1`; tape = the `addLeaves` fold),
    `record_run_inv` turns the two monadic op stages back into pure `Tape.mul`/`Tape.scale`
    successes, and those are exactly the `hop` obligations of the `EagerBuilds.mul` and
    `EagerBuilds.scale` constructors. -/
theorem progMulScale_run_eagerBuilds (c : ℝ) (x0T x1T : Tensor ℝ Shape.scalar)
    {idF : Nat} {t' : PRSim.RTape}
    (h : (progMulScale c x0T x1T).run Runtime.Autograd.Tape.empty = .ok (idF, t')) :
    PRSim.EagerBuilds (mulScaleGraph c) (.cons x0T (.cons x1T .nil)) t' := by
  have hrun := h
  -- peel the four stages of the do-block
  obtain ⟨a, t1, hleaf0, hrest⟩ := run_bind_inv (m := TapeM.leaf x0T) hrun
  obtain ⟨b, t2, hleaf1, hrest2⟩ := run_bind_inv (m := TapeM.leaf x1T) hrest
  obtain ⟨m, t3, hmulM, hscaleM⟩ := run_bind_inv hrest2
  -- the two leaf stages are deterministic: extract ids and tapes
  rw [run_leaf] at hleaf0 hleaf1
  simp only [Except.ok.injEq, Prod.mk.injEq] at hleaf0 hleaf1
  obtain ⟨ha, ht1⟩ := hleaf0
  obtain ⟨hb, ht2⟩ := hleaf1
  subst ht1 ht2 ha hb
  -- the two op stages: back to pure `Tape` successes
  have hmul := record_run_inv (op := fun tt =>
    Runtime.Autograd.Tape.mul (α := ℝ) (t := tt) (s := Shape.scalar)
      (Runtime.Autograd.Tape.leaf (t := Runtime.Autograd.Tape.empty) x0T).2
      (Runtime.Autograd.Tape.leaf
        (t := (Runtime.Autograd.Tape.leaf (t := Runtime.Autograd.Tape.empty) x0T).1) x1T).2)
    hmulM
  have hscale := record_run_inv (op := fun tt =>
    Runtime.Autograd.Tape.scale (α := ℝ) (t := tt) (s := Shape.scalar) m c) hscaleM
  -- leaf ids are the pre-append sizes: 0 and 1
  have ha0 : (Runtime.Autograd.Tape.leaf (t := Runtime.Autograd.Tape.empty) x0T).2 = 0 := rfl
  have hb1 : (Runtime.Autograd.Tape.leaf
      (t := (Runtime.Autograd.Tape.leaf (t := Runtime.Autograd.Tape.empty) x0T).1) x1T).2
      = 1 := rfl
  rw [ha0, hb1] at hmul
  -- the two-leaf tape IS the `addLeaves` fold of the input list
  have htape :
      (Runtime.Autograd.Tape.leaf
        (t := (Runtime.Autograd.Tape.leaf (t := Runtime.Autograd.Tape.empty) x0T).1) x1T).1
      = Algebra.Graph.addLeaves (α := ℝ) (t := Runtime.Autograd.Tape.empty)
          (TensorPack.cons x0T (TensorPack.cons x1T TensorPack.nil)) := rfl
  rw [htape] at hmul
  -- the mul id is the pre-append size of the two-leaf tape: 2
  have hm2 : m = 2 := by rw [tape_mul_id hmul]; rfl
  subst hm2
  -- assemble the two constructors
  have hmulB := PRSim.EagerBuilds.mul (g := .nil) ix0 ix1
    (PRSim.EagerBuilds.nil (TensorPack.cons x0T (TensorPack.cons x1T TensorPack.nil))) hmul
  have hb := PRSim.EagerBuilds.scale ixm c hmulB hscale
  exact hb

/-- Differentiability witness for the chained graph, from the upstream per-node facts. -/
def mulScaleCorrect (c : ℝ) : GraphFDerivCorrect (mulScaleGraph c) :=
  ⟨⟨PUnit.unit, TapeNodes.mulFderiv ix0 ix1⟩, TapeNodes.scaleFderiv ixm c⟩

set_option maxHeartbeats 6400000 in
/-- **The endpoint reaches `do`-block programs**: composing the bridge demo with
    `direct_PR_soundness_eager`, the reverse pass on the tape a monadic program built realises
    the adjoint of the Fréchet derivative of the program's own forward evaluation. -/
example (c : ℝ) (x0T x1T : Tensor ℝ Shape.scalar) {idF : Nat} {t' : PRSim.RTape}
    (h : (progMulScale c x0T x1T).run Runtime.Autograd.Tape.empty = .ok (idF, t'))
    (seed : TorchLean.TensorPack ℝ (Γ2 ++ [Shape.scalar, Shape.scalar])) :
    ∃ out : Array PRSim.Any,
      Runtime.Autograd.Tape.backwardDenseFrom (t := t')
          (TorchLean.TensorPack.toShapeErasedArray (α := ℝ) seed) = .ok out ∧
      PRSim.ArrCorr
        ((fderiv ℝ ((mulScaleGraph c).evalVec)
            (flattenCtx (TensorPack.cons x0T (TensorPack.cons x1T TensorPack.nil)))).adjoint
          (flattenCtx seed))
        (out.extract 0 Γ2.length) :=
  PRSim.direct_PR_soundness_eager (mulScaleGraph c) (mulScaleCorrect c)
    (TensorPack.cons x0T (TensorPack.cons x1T TensorPack.nil))
    (progMulScale_run_eagerBuilds c x0T x1T h) seed

/--
info: 'PropertyKindCalculus.UncertaintyExamples.TapeMBridge.progMulScale_run_eagerBuilds' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in #print axioms progMulScale_run_eagerBuilds

end

end PropertyKindCalculus.UncertaintyExamples.TapeMBridge

end Blanket
