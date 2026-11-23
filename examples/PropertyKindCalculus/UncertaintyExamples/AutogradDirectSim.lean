/-
# The direct P↔R simulation, exercised on concrete tapes

Examples for `Uncertainty/Experiments/PRSimulation.lean` and `EagerProvenance.lean`:

  * the lowered tape of a one-node graph forward-simulates it and meets the fderiv endpoint
    (`direct_PR_soundness_compiled`);
  * a tape of two leaves is `BackwardShapeWF`, so its dense reverse pass succeeds;
  * tapes recorded with `CpuTape.mul`, `CpuTape.sub` and `CpuTape.exp` are `EagerBuilds` of the
    matching `LawfulNode.ofArm` graphs, and meet the fderiv endpoint
    (`direct_PR_soundness_eager`).

None of these three operators has an alias rule, and their rules emit contributions in port
order; both facts are closed by `rfl`.
-/

module

public import PropertyKindCalculus.Uncertainty.Experiments.PRSimulation
public import PropertyKindCalculus.Uncertainty.Experiments.EagerProvenance
public import TorchLean.NN.Op.Pointwise

@[expose] public noncomputable section Blanket

open TorchLean TorchLean.Tensor TorchLean.Tape PropertyKindCalculus.Paradigm

namespace PropertyKindCalculus.UncertaintyExamples.AutogradDirectSim

/-- Two scalar inputs. -/
abbrev Γ2 : List Shape := [Shape.scalar, Shape.scalar]

/-- Index of the first input. -/
def ix0 : Idx (Γ2 ++ []) Shape.scalar := ⟨⟨0, by decide⟩, rfl⟩

/-- Index of the second input. -/
def ix1 : Idx (Γ2 ++ []) Shape.scalar := ⟨⟨1, by decide⟩, rfl⟩

/-! ## The product `x₀ * x₁` -/

/-- The product node, from the `mul` arm and its derivative certificate. -/
def prodNode : Tape.LawfulNode (α := ℝ) Unit Γ2 Shape.scalar :=
  Tape.LawfulNode.ofArm (Op.mul (s := Shape.scalar)) rfl (Γ := Γ2) (ix0, ix1, ())
    (Arm.adj_of_cert₂ fun xs δ => Op.mul_prod_backward_eq_adjoint xs.1 xs.2.1 δ)

/-- The one-node product graph. -/
def prodGraph : PRSim.PGraph Γ2 [Shape.scalar] := .snoc .nil prodNode

/-- Differentiability witness, from the same certificate. -/
def prodCorrect : RealGraph.FDerivCorrect (Γ := Γ2) prodGraph.toData () :=
  ⟨PUnit.unit, Tape.RealNode.FDerivCorrect.ofArm₂
    fun x y δ => Op.mul_prod_backward_eq_adjoint x y δ⟩

/-- The lowered product tape meets the fderiv endpoint. -/
example (x : TensorPack ℝ Γ2) (seed : TensorPack ℝ (Γ2 ++ [Shape.scalar])) :
    ∃ out : Array PRSim.Any,
      Tape.backwardDenseFrom (t := (GraphData.toTape prodGraph.toData x ()).1)
          (grads0 := TensorPack.erase seed) = .ok out ∧
      PRSim.ArrCorr ((fderiv ℝ (prodGraph.toData.evalVec ()) (TensorPack.toVec x)).adjoint
          (TensorPack.toVec seed))
        (out.extract 0 Γ2.length) :=
  PRSim.direct_PR_soundness_compiled prodGraph prodCorrect x seed

/-- The lowered product tape forward-simulates the graph. -/
example (x : TensorPack ℝ Γ2) :
    PRSim.ForwardSim prodGraph (TensorPack.toVec x) (GraphData.toTape prodGraph.toData x ()).1 :=
  PRSim.forwardSim_toTape prodGraph x

/-- A tape of two scalar leaves is shape-total, so its dense reverse pass cannot fail. -/
example (a b : Tensor ℝ Shape.scalar) :
    PRSim.BackwardShapeWF
      (CpuTape.leaf (CpuTape.leaf (Tape.empty : PRSim.RTape) a).1 b).1 :=
  PRSim.backwardShapeWF_leaf _ (PRSim.backwardShapeWF_leaf _ PRSim.backwardShapeWF_empty _ _ _) _ _ _

/-- A recorded `mul` of the two leaves is an eager build of the product graph. -/
theorem eagerBuilds_prod (x : TensorPack ℝ Γ2) (t' : PRSim.RTape) (id : Nat)
    (hop : CpuTape.mul (s := Shape.scalar)
      (Tape.addLeaves (t := (Tape.empty : PRSim.RTape)) x) 0 1 = .ok (t', id)) :
    PRSim.EagerBuilds prodGraph x t' := by
  have h := PRSim.EagerBuilds.binary (g := .nil) (id := id) (name := "mul")
    (op := Op.mul (s := Shape.scalar)) rfl ix0 ix1
    (Arm.adj_of_cert₂ fun xs δ => Op.mul_prod_backward_eq_adjoint xs.1 xs.2.1 δ)
    (PRSim.EagerBuilds.nil x) hop
  exact h (PRSim.aliasOf_eq_none rfl _) rfl

/-- The recorded product tape meets the fderiv endpoint. -/
example (x : TensorPack ℝ Γ2) (t' : PRSim.RTape) (id : Nat)
    (hop : CpuTape.mul (s := Shape.scalar)
      (Tape.addLeaves (t := (Tape.empty : PRSim.RTape)) x) 0 1 = .ok (t', id))
    (seed : TensorPack ℝ (Γ2 ++ [Shape.scalar])) :
    ∃ out : Array PRSim.Any,
      Tape.backwardDenseFrom (t := t') (grads0 := TensorPack.erase seed) = .ok out ∧
      PRSim.ArrCorr ((fderiv ℝ (prodGraph.toData.evalVec ()) (TensorPack.toVec x)).adjoint
          (TensorPack.toVec seed))
        (out.extract 0 Γ2.length) :=
  PRSim.direct_PR_soundness_eager prodGraph prodCorrect x (eagerBuilds_prod x t' id hop) seed

/-- The recorded product tape forward-simulates the graph. -/
example (x : TensorPack ℝ Γ2) (t' : PRSim.RTape) (id : Nat)
    (hop : CpuTape.mul (s := Shape.scalar)
      (Tape.addLeaves (t := (Tape.empty : PRSim.RTape)) x) 0 1 = .ok (t', id)) :
    PRSim.ForwardSim prodGraph (TensorPack.toVec x) t' :=
  PRSim.forwardSim_eager (eagerBuilds_prod x t' id hop)

/-! ## The difference `x₀ - x₁` -/

/-- The difference node. -/
def subNode : Tape.LawfulNode (α := ℝ) Unit Γ2 Shape.scalar :=
  Tape.LawfulNode.ofArm (Op.sub (s := Shape.scalar)) rfl (Γ := Γ2) (ix0, ix1, ())
    (Arm.adj_of_cert₂ fun xs δ => Op.sub_prod_backward_eq_adjoint xs.1 xs.2.1 δ)

/-- The one-node difference graph. -/
def subGraph : PRSim.PGraph Γ2 [Shape.scalar] := .snoc .nil subNode

/-- Differentiability witness. -/
def subCorrect : RealGraph.FDerivCorrect (Γ := Γ2) subGraph.toData () :=
  ⟨PUnit.unit, Tape.RealNode.FDerivCorrect.ofArm₂
    fun x y δ => Op.sub_prod_backward_eq_adjoint x y δ⟩

/-- A recorded `sub` of the two leaves is an eager build of the difference graph. -/
theorem eagerBuilds_sub (x : TensorPack ℝ Γ2) (t' : PRSim.RTape) (id : Nat)
    (hop : CpuTape.sub (s := Shape.scalar)
      (Tape.addLeaves (t := (Tape.empty : PRSim.RTape)) x) 0 1 = .ok (t', id)) :
    PRSim.EagerBuilds subGraph x t' := by
  have h := PRSim.EagerBuilds.binary (g := .nil) (id := id) (name := "sub")
    (op := Op.sub (s := Shape.scalar)) rfl ix0 ix1
    (Arm.adj_of_cert₂ fun xs δ => Op.sub_prod_backward_eq_adjoint xs.1 xs.2.1 δ)
    (PRSim.EagerBuilds.nil x) hop
  exact h (PRSim.aliasOf_eq_none rfl _) rfl

/-- The recorded difference tape meets the fderiv endpoint. -/
example (x : TensorPack ℝ Γ2) (t' : PRSim.RTape) (id : Nat)
    (hop : CpuTape.sub (s := Shape.scalar)
      (Tape.addLeaves (t := (Tape.empty : PRSim.RTape)) x) 0 1 = .ok (t', id))
    (seed : TensorPack ℝ (Γ2 ++ [Shape.scalar])) :
    ∃ out : Array PRSim.Any,
      Tape.backwardDenseFrom (t := t') (grads0 := TensorPack.erase seed) = .ok out ∧
      PRSim.ArrCorr ((fderiv ℝ (subGraph.toData.evalVec ()) (TensorPack.toVec x)).adjoint
          (TensorPack.toVec seed))
        (out.extract 0 Γ2.length) :=
  PRSim.direct_PR_soundness_eager subGraph subCorrect x (eagerBuilds_sub x t' id hop) seed

/-! ## The exponential `exp x₀` -/

/-- The exponential node. -/
def expNode : Tape.LawfulNode (α := ℝ) Unit Γ2 Shape.scalar :=
  Tape.LawfulNode.ofArm (Op.exp (s := Shape.scalar)) rfl (Γ := Γ2) (ix0, ())
    (Arm.adj_of_cert₁ fun xs δ => Op.exp_backward_eq_adjoint xs.1 δ)

/-- The one-node exponential graph. -/
def expGraph : PRSim.PGraph Γ2 [Shape.scalar] := .snoc .nil expNode

/-- Differentiability witness. -/
def expCorrect : RealGraph.FDerivCorrect (Γ := Γ2) expGraph.toData () :=
  ⟨PUnit.unit, Tape.RealNode.FDerivCorrect.ofArm₁
    (cert := fun x δ => Op.exp_backward_eq_adjoint x δ)⟩

/-- A recorded `exp` of the first leaf is an eager build of the exponential graph. -/
theorem eagerBuilds_exp (x : TensorPack ℝ Γ2) (t' : PRSim.RTape) (id : Nat)
    (hop : CpuTape.exp (s := Shape.scalar)
      (Tape.addLeaves (t := (Tape.empty : PRSim.RTape)) x) 0 = .ok (t', id)) :
    PRSim.EagerBuilds expGraph x t' := by
  have h := PRSim.EagerBuilds.unary (g := .nil) (id := id) (name := "exp")
    (op := Op.exp (s := Shape.scalar)) rfl ix0
    (Arm.adj_of_cert₁ fun xs δ => Op.exp_backward_eq_adjoint xs.1 δ)
    (PRSim.EagerBuilds.nil x) hop
  exact h (PRSim.aliasOf_eq_none rfl _) rfl

/-- The recorded exponential tape meets the fderiv endpoint. -/
example (x : TensorPack ℝ Γ2) (t' : PRSim.RTape) (id : Nat)
    (hop : CpuTape.exp (s := Shape.scalar)
      (Tape.addLeaves (t := (Tape.empty : PRSim.RTape)) x) 0 = .ok (t', id))
    (seed : TensorPack ℝ (Γ2 ++ [Shape.scalar])) :
    ∃ out : Array PRSim.Any,
      Tape.backwardDenseFrom (t := t') (grads0 := TensorPack.erase seed) = .ok out ∧
      PRSim.ArrCorr ((fderiv ℝ (expGraph.toData.evalVec ()) (TensorPack.toVec x)).adjoint
          (TensorPack.toVec seed))
        (out.extract 0 Γ2.length) :=
  PRSim.direct_PR_soundness_eager expGraph expCorrect x (eagerBuilds_exp x t' id hop) seed

/--
info: 'PropertyKindCalculus.UncertaintyExamples.AutogradDirectSim.eagerBuilds_prod' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in #print axioms eagerBuilds_prod

/--
info: 'PRSim.direct_PR_soundness_eager' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in #print axioms PRSim.direct_PR_soundness_eager

end PropertyKindCalculus.UncertaintyExamples.AutogradDirectSim
