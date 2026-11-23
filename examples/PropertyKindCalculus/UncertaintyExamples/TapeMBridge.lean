/-
# A `do`-block recording program is covered by eager provenance

`EagerProvenance.lean` covers tapes recorded by explicit `CpuTape` steps. Programs are usually
written in the `TapeM` monad, which threads the tape through those steps. This example closes
that gap for one program:

  * `progMulExp` is `do let a ← leaf x₀; let b ← leaf x₁; let m ← mul a b; exp m`;
  * `progMulExp_run_eagerBuilds`: a successful run from the empty tape is an `EagerBuilds` of
    the two-node graph `exp (mul x₀ x₁)`;
  * the closing example applies `direct_PR_soundness_eager` to that tape.

The proof unfolds the four monadic stages into the two pure steps `CpuTape.mul` and
`CpuTape.exp`, and reads the id of the `mul` node from `TapeFaithful.mul_value`.
-/

module

public import PropertyKindCalculus.UncertaintyExamples.AutogradDirectSim
public import PropertyKindCalculus.Torch.Paradigm.TapeFaithful

@[expose] public noncomputable section Blanket

open TorchLean TorchLean.Tensor TorchLean.Tape PropertyKindCalculus.Paradigm
open PropertyKindCalculus.UncertaintyExamples.AutogradDirectSim

namespace PropertyKindCalculus.UncertaintyExamples.TapeMBridge

/-- The program `exp (x₀ * x₁)`, written in the recording monad. -/
def progMulExp (x0T x1T : Tensor ℝ Shape.scalar) : TapeM ℝ Nat := do
  let a ← TapeM.leaf x0T
  let b ← TapeM.leaf x1T
  let m ← TapeM.mul (s := Shape.scalar) a b
  TapeM.exp (s := Shape.scalar) m

/-- Index of the `mul` output in the context extended by the first node. -/
def ixm : Idx ((Γ2 ++ []) ++ [Shape.scalar]) Shape.scalar := ⟨⟨2, by decide⟩, rfl⟩

/-- The `exp` node reading the `mul` output. -/
def expMulNode : Tape.LawfulNode (α := ℝ) Unit ((Γ2 ++ []) ++ [Shape.scalar]) Shape.scalar :=
  Tape.LawfulNode.ofArm (Op.exp (s := Shape.scalar)) rfl (ixm, ())
    (Arm.adj_of_cert₁ fun xs δ => Op.exp_backward_eq_adjoint xs.1 δ)

/-- The two-node graph the program records: `exp (mul x₀ x₁)`. -/
def mulExpGraph : PRSim.PGraph Γ2 [Shape.scalar, Shape.scalar] :=
  .snoc prodGraph expMulNode

/-- A successful run of `progMulExp` from the empty tape is an eager build of `mulExpGraph`. -/
theorem progMulExp_run_eagerBuilds (x0T x1T : Tensor ℝ Shape.scalar)
    {idF : Nat} {t' : PRSim.RTape}
    (h : (progMulExp x0T x1T).run (Tape.empty : PRSim.RTape) = .ok (idF, t')) :
    PRSim.EagerBuilds mulExpGraph (.cons x0T (.cons x1T .nil)) t' := by
  have hnil := PRSim.EagerBuilds.nil (Γ := Γ2) (.cons x0T (.cons x1T .nil))
  -- The run is the two pure steps, on the tape of the two leaves.
  simp only [progMulExp, TapeM.run, StateT.run, bind, StateT.bind, TapeM.leaf, TapeM.mul,
    TapeM.exp, TapeM.record, pure, Except.pure, Except.bind] at h
  obtain ⟨t3, hmul', -, -⟩ := TapeFaithful.mul_value
    (Tape.addLeaves (t := (Tape.empty : PRSim.RTape)) (.cons x0T (.cons x1T .nil))) 0 1
    (hnil.inv.requireValue ix0) (hnil.inv.requireValue ix1)
  have hmul : CpuTape.mul (s := Shape.scalar)
      (Tape.addLeaves (t := (Tape.empty : PRSim.RTape)) (.cons x0T (.cons x1T .nil))) 0 1
        = .ok (t3, 2) := hmul'
  have hmul2 : CpuTape.mul (s := Shape.scalar)
      (CpuTape.leaf (CpuTape.leaf (Tape.empty : PRSim.RTape) x0T).1 x1T).1
      (CpuTape.leaf (Tape.empty : PRSim.RTape) x0T).2
      (CpuTape.leaf (CpuTape.leaf (Tape.empty : PRSim.RTape) x0T).1 x1T).2 = .ok (t3, 2) := hmul
  rw [hmul2] at h
  cases hexp : CpuTape.exp (s := Shape.scalar) t3 2 with
  | error e => simp [Except.map, hexp] at h
  | ok r =>
    obtain ⟨t4, id4⟩ := r
    simp only [Except.map, hexp, Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨-, rfl⟩ := h
    have hb := PRSim.EagerBuilds.unary (id := id4) (name := "exp")
      (op := Op.exp (s := Shape.scalar)) rfl ixm
      (Arm.adj_of_cert₁ fun xs δ => Op.exp_backward_eq_adjoint xs.1 δ)
      (eagerBuilds_prod _ t3 2 hmul) hexp
    exact hb (PRSim.aliasOf_eq_none rfl _) rfl

/-- Differentiability witness for the two-node graph. -/
def mulExpCorrect : RealGraph.FDerivCorrect (Γ := Γ2) mulExpGraph.toData () :=
  ⟨prodCorrect, Tape.RealNode.FDerivCorrect.ofArm₁
    (cert := fun x δ => Op.exp_backward_eq_adjoint x δ)⟩

/-- The fderiv endpoint holds on the tape the monadic program recorded. -/
example (x0T x1T : Tensor ℝ Shape.scalar) {idF : Nat} {t' : PRSim.RTape}
    (h : (progMulExp x0T x1T).run (Tape.empty : PRSim.RTape) = .ok (idF, t'))
    (seed : TensorPack ℝ (Γ2 ++ [Shape.scalar, Shape.scalar])) :
    ∃ out : Array PRSim.Any,
      Tape.backwardDenseFrom (t := t') (grads0 := TensorPack.erase seed) = .ok out ∧
      PRSim.ArrCorr
        ((fderiv ℝ (mulExpGraph.toData.evalVec ())
            (TensorPack.toVec (Γ := Γ2) (.cons x0T (.cons x1T .nil)))).adjoint
          (TensorPack.toVec seed))
        (out.extract 0 Γ2.length) :=
  PRSim.direct_PR_soundness_eager mulExpGraph mulExpCorrect _
    (progMulExp_run_eagerBuilds x0T x1T h) seed

/--
info: 'PropertyKindCalculus.UncertaintyExamples.TapeMBridge.progMulExp_run_eagerBuilds' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in #print axioms progMulExp_run_eagerBuilds

end PropertyKindCalculus.UncertaintyExamples.TapeMBridge
