/-
# Worked example — Stage 3.6: the direct P↔R simulation, closed

The `PRSim` spike's five obligations are now theorems (`Uncertainty/Experiments/PRSimulation.lean`);
this probe instantiates them on concrete artifacts so the module keeps building — and keeps
meaning what it says — under CI.

  * **Vectorization homomorphisms** — `mulSpec_ofVecT`/`addSpec_ofVecT` applied at a concrete
    vector shape (the R kernels are the Hadamard product / Euclidean `+` under vectorization).
  * **A concrete product graph** — `prodGraph = x₀ * x₁` over two scalar inputs, with its
    `GraphFDerivCorrect` witness assembled from the upstream per-node `mulFderiv`; the Stage-3.6
    endpoint `direct_PR_soundness_compiled` then says: the executable dense reverse pass on the
    compiled tape succeeds, and the input-prefix of its output realises `(fderiv ℝ eval x)† seed`.
  * **`ForwardSim` inhabited** — the compiled tape forward-simulates `prodGraph`
    (`forwardSim_compileAux`), so the spike's simulation relation is realised, not hypothetical.
  * **An eager well-formed tape** — two `Tape.leaf`s then `Tape.mul` on the *runtime* engine:
    the constructor lemmas discharge `BackwardShapeWF`, the closure hypothesis under which the
    total reverse pass provably returns `.ok` (`backwardDenseFrom_ok`).
  * **The eager-provenance closure** (`Experiments/EagerProvenance.lean`) — `EagerBuilds`
    witnesses the runtime-constructed tape for `prodGraph` (leaf fold + one eager `Tape.mul`),
    and `direct_PR_soundness_eager` gives the fderiv endpoint on *that* tape, no compilation
    involved: the reverse pass the eager construction pattern actually runs is theorem-covered.

These are `ℝ`-level proof terms (like `AdequacyDag`); the axiom prints confirm the classical
trio only — no `sorryAx`, which is the point: the spike is closed, not silently deferred.
-/
import PropertyKindCalculus.Uncertainty.Experiments.PRSimulation
import PropertyKindCalculus.Uncertainty.Experiments.EagerProvenance

namespace PropertyKindCalculus.UncertaintyExamples.AutogradDirectSim

open Spec Tensor Proofs.Autograd

noncomputable section

/-! ## The two vectorization homomorphisms, at a concrete shape -/

/-- `mulSpec` at a 3-vector shape is the Hadamard product under vectorization. -/
example (u v : Vec (Shape.dim 3 Shape.scalar).size) :
    mulSpec (ofVecT u) (ofVecT v) = ofVecT (PRSim.hadamardVec u v) :=
  PRSim.mulSpec_ofVecT u v

/-- `addSpec` at the same shape is Euclidean `+` under vectorization. -/
example (u v : Vec (Shape.dim 3 Shape.scalar).size) :
    addSpec (ofVecT u) (ofVecT v) = ofVecT (u + v) :=
  PRSim.addSpec_ofVecT u v

/-! ## A concrete P graph: the scalar product `x₀ * x₁` -/

/-- Two scalar inputs. -/
abbrev Γ2 : List Shape := [Shape.scalar, Shape.scalar]

/-- Index of the first input. -/
def ix0 : Idx Γ2 Shape.scalar := ⟨⟨0, by decide⟩, rfl⟩

/-- Index of the second input. -/
def ix1 : Idx Γ2 Shape.scalar := ⟨⟨1, by decide⟩, rfl⟩

/-- The one-node product graph `x₀ * x₁`. -/
def prodGraph : Graph Γ2 [Shape.scalar] := .snoc .nil (TapeNodes.mul ix0 ix1)

/-- Differentiability witness, assembled from the upstream per-node `mulFderiv`. -/
def prodCorrect : GraphFDerivCorrect prodGraph := ⟨PUnit.unit, TapeNodes.mulFderiv ix0 ix1⟩

/-- **The Stage-3.6 endpoint on the product graph**: the runtime dense reverse pass on the
    compiled tape succeeds, and the `Γ`-prefix of its output realises the adjoint of the Fréchet
    derivative of the graph's forward evaluation. -/
example (x : TList Γ2) (seed : TList (Γ2 ++ [Shape.scalar])) :
    ∃ out : Array PRSim.Any,
      Runtime.Autograd.Tape.backwardDenseFrom
          (t := (Algebra.Graph.compileAux (α := ℝ) (Δ := Unit) prodGraph.toAlgebra x ()).1)
          (grads0 := Algebra.TList.toAnyArray (α := ℝ) (ss := Γ2 ++ [Shape.scalar]) seed)
        = .ok out ∧
      PRSim.ArrCorr ((fderiv ℝ (prodGraph.evalVec) (flattenCtx x)).adjoint (flattenCtx seed))
        (out.extract 0 Γ2.length) :=
  PRSim.direct_PR_soundness_compiled prodGraph prodCorrect x seed

/-- The compiled tape forward-simulates the graph — the simulation relation is inhabited. -/
example (x : TList Γ2) :
    PRSim.ForwardSim prodGraph (flattenCtx x)
      (Algebra.Graph.compileAux (α := ℝ) (Δ := Unit) prodGraph.toAlgebra x ()).1 :=
  PRSim.forwardSim_compileAux prodGraph x

/-! ## An eager runtime tape with provably shape-total closures -/

/-- Leaf `x₀ = 2` on the empty runtime tape. -/
def t1 : PRSim.RTape :=
  (Runtime.Autograd.Tape.leaf (α := ℝ) Runtime.Autograd.Tape.empty
    (Tensor.scalar (2 : ℝ)) none true).1

/-- Leaf `x₁ = 3` on top. -/
def t2 : PRSim.RTape :=
  (Runtime.Autograd.Tape.leaf (α := ℝ) t1 (Tensor.scalar (3 : ℝ)) none true).1

/-- The two-leaf tape has shape-total closures (constructor by constructor). -/
theorem t2_wf : PRSim.BackwardShapeWF t2 :=
  PRSim.backwardShapeWF_leaf t1
    (PRSim.backwardShapeWF_leaf Runtime.Autograd.Tape.empty
      PRSim.backwardShapeWF_empty _ _ _) _ _ _

/-- Whatever tape the eager `mul 0 1` returns is again shape-total — the `BackwardShapeWF`
    hypothesis of `backwardDenseFrom_ok` is discharged on eagerly built tapes. -/
theorem eager_mul_wf (t' : PRSim.RTape) (id : Nat)
    (h : Runtime.Autograd.Tape.mul (α := ℝ) (s := Shape.scalar) t2 0 1 = .ok (t', id)) :
    PRSim.BackwardShapeWF t' :=
  PRSim.backwardShapeWF_mul t2 t2_wf 0 1 t' id h

/-! ## The eager-provenance closure: the endpoint on the runtime-built tape itself -/

set_option maxHeartbeats 1600000 in
/-- The runtime tape built for `prodGraph`'s inputs: the `Tape.leaf` fold (= `addLeaves`),
    then one eager `Tape.mul 0 1` — exactly what `TapeM` does. `EagerBuilds` witnesses it. -/
theorem eagerBuilds_prod (x : TList Γ2) (t' : PRSim.RTape) (id : Nat)
    (hop : Runtime.Autograd.Tape.mul (α := ℝ) (s := Shape.scalar)
      (Algebra.Graph.addLeaves (α := ℝ) (t := Runtime.Autograd.Tape.empty) x) 0 1
      = .ok (t', id)) :
    PRSim.EagerBuilds prodGraph x t' := by
  show PRSim.EagerBuilds (.snoc .nil (TapeNodes.mul ix0 ix1)) x t'
  exact PRSim.EagerBuilds.mul (g := .nil) ix0 ix1 (PRSim.EagerBuilds.nil x) hop

/-- **The endpoint on the eager tape**: the dense reverse pass on the runtime-constructed tape
    succeeds and its input-prefix realises `(fderiv ℝ eval x)† seed` — no compilation involved;
    this is the tape `Sensitivity.gradient`'s construction pattern produces. -/
example (x : TList Γ2) (t' : PRSim.RTape) (id : Nat)
    (hop : Runtime.Autograd.Tape.mul (α := ℝ) (s := Shape.scalar)
      (Algebra.Graph.addLeaves (α := ℝ) (t := Runtime.Autograd.Tape.empty) x) 0 1
      = .ok (t', id))
    (seed : TList (Γ2 ++ [Shape.scalar])) :
    ∃ out : Array PRSim.Any,
      Runtime.Autograd.Tape.backwardDenseFrom (t := t')
          (Algebra.TList.toAnyArray (α := ℝ) seed) = .ok out ∧
      PRSim.ArrCorr ((fderiv ℝ (prodGraph.evalVec) (flattenCtx x)).adjoint (flattenCtx seed))
        (out.extract 0 Γ2.length) :=
  PRSim.direct_PR_soundness_eager prodGraph prodCorrect x (eagerBuilds_prod x t' id hop) seed

/-- Eager tapes inhabit the forward simulation relation too. -/
example (x : TList Γ2) (t' : PRSim.RTape) (id : Nat)
    (hop : Runtime.Autograd.Tape.mul (α := ℝ) (s := Shape.scalar)
      (Algebra.Graph.addLeaves (α := ℝ) (t := Runtime.Autograd.Tape.empty) x) 0 1
      = .ok (t', id)) :
    PRSim.ForwardSim prodGraph (flattenCtx x) t' :=
  PRSim.forwardSim_eager (eagerBuilds_prod x t' id hop)

/-! ## Axiom profiles — closed means closed -/

/-- info: 'PRSim.mulSpec_ofVecT' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms PRSim.mulSpec_ofVecT

/-- info: 'PRSim.addSpec_ofVecT' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms PRSim.addSpec_ofVecT

/-- info: 'PRSim.backwardDenseFrom_ok' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms PRSim.backwardDenseFrom_ok

/-- info: 'PRSim.forwardSim_compileAux' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms PRSim.forwardSim_compileAux

/--
info: 'PRSim.direct_PR_soundness_compiled' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in #print axioms PRSim.direct_PR_soundness_compiled

/--
info: 'PRSim.direct_PR_soundness_compiled_at' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in #print axioms PRSim.direct_PR_soundness_compiled_at

/--
info: 'PRSim.backwardDenseFrom_eager_eq_compiled' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in #print axioms PRSim.backwardDenseFrom_eager_eq_compiled

/-- info: 'PRSim.direct_PR_soundness_eager' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms PRSim.direct_PR_soundness_eager

/-- info: 'PRSim.forwardSim_eager' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms PRSim.forwardSim_eager

end

end PropertyKindCalculus.UncertaintyExamples.AutogradDirectSim
