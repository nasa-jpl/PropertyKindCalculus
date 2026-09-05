/-
# Worked example — Stage 3.6: the direct P↔R simulation, closed

The `PRSim` spike's five obligations are now theorems (`Uncertainty/Experiments/PRSimulation.lean`);
this probe instantiates them on concrete artifacts so the module keeps building — and keeps
meaning what it says — under CI.

  * **Vectorization homomorphisms** — `mulSpec_vecToTensor`/`addSpec_vecToTensor` applied at a concrete
    vector shape (the R kernels are the Hadamard product / Euclidean `+` under vectorization).
  * **A concrete product graph** — `prodGraph = x₀ * x₁` over two scalar inputs, with its
    `GraphFDerivCorrect` witness assembled from the upstream per-node `mulFderiv`; the Stage-3.6
    endpoint `direct_PR_soundness_compiled` then says: the executable dense reverse pass on the
    compiled tape succeeds, and the input-prefix of its output realises `(fderiv ℝ eval x)† seed`.
  * **`ForwardSim` inhabited** — the compiled tape forward-simulates `prodGraph`
    (`forwardSim_lowerGraphToTape`), so the spike's simulation relation is realised, not hypothetical.
  * **An eager well-formed tape** — two `Tape.leaf`s then `Tape.mul` on the *runtime* engine:
    the constructor lemmas discharge `BackwardShapeWF`, the closure hypothesis under which the
    total reverse pass provably returns `.ok` (`backwardDenseFrom_ok`).
  * **The eager-provenance closure** (`Experiments/EagerProvenance.lean`) — `EagerBuilds`
    witnesses the runtime-constructed tape for `prodGraph` (leaf fold + one eager `Tape.mul`),
    and `direct_PR_soundness_eager` gives the fderiv endpoint on *that* tape, no compilation
    involved: the reverse pass the eager construction pattern actually runs is theorem-covered.
  * **A second binary op** — the same closure on `subGraph = x₀ - x₁` through the new `EagerBuilds.sub`
    constructor (runtime `Tape.sub`, whose right parent receives the negated cotangent), so "one
    crank beyond `add`/`mul`" is a checked instance, not a promise.
  * **A pointwise binary op** — the same closure on `divGraph = x₀ / x₁` through `EagerBuilds.div`
    (runtime `Tape.div`, quotient-rule cotangents). Differentiability holds only where the
    denominator is nonzero, so the witness is `GraphFDerivCorrectAt` (upstream `divFderivAt`) and
    the endpoint is the pointwise `direct_PR_soundness_eager_at`, the hypothesis threaded through
    the example binders.

These are `ℝ`-level proof terms (like `AdequacyDag`); the axiom prints confirm the classical
trio only — no `sorryAx`, which is the point: the spike is closed, not silently deferred.
-/
import PropertyKindCalculus.Uncertainty.Experiments.PRSimulation
import PropertyKindCalculus.Uncertainty.Experiments.EagerProvenance

namespace PropertyKindCalculus.UncertaintyExamples.AutogradDirectSim

open Spec Tensor Proofs.Autograd TorchLean

noncomputable section

/-! ## The two vectorization homomorphisms, at a concrete shape -/

/-- `mulSpec` at a 3-vector shape is the Hadamard product under vectorization. -/
example (u v : Vec (Shape.dim 3 Shape.scalar).size) :
    mulSpec (vecToTensor u) (vecToTensor v) = vecToTensor (PRSim.hadamardVec u v) :=
  PRSim.mulSpec_vecToTensor u v

/-- `addSpec` at the same shape is Euclidean `+` under vectorization. -/
example (u v : Vec (Shape.dim 3 Shape.scalar).size) :
    addSpec (vecToTensor u) (vecToTensor v) = vecToTensor (u + v) :=
  PRSim.addSpec_vecToTensor u v

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
example (x : TorchLean.TensorPack ℝ Γ2) (seed : TorchLean.TensorPack ℝ (Γ2 ++ [Shape.scalar])) :
    ∃ out : Array PRSim.Any,
      Runtime.Autograd.Tape.backwardDenseFrom
          (t := (Algebra.Graph.lowerGraphToTape (α := ℝ) (Δ := Unit) prodGraph.toAlgebra x ()).1)
          (grads0 := TorchLean.TensorPack.toShapeErasedArray (α := ℝ) (ss := Γ2 ++ [Shape.scalar]) seed)
        = .ok out ∧
      PRSim.ArrCorr ((fderiv ℝ (prodGraph.evalVec) (flattenCtx x)).adjoint (flattenCtx seed))
        (out.extract 0 Γ2.length) :=
  PRSim.direct_PR_soundness_compiled prodGraph prodCorrect x seed

/-- The compiled tape forward-simulates the graph — the simulation relation is inhabited. -/
example (x : TorchLean.TensorPack ℝ Γ2) :
    PRSim.ForwardSim prodGraph (flattenCtx x)
      (Algebra.Graph.lowerGraphToTape (α := ℝ) (Δ := Unit) prodGraph.toAlgebra x ()).1 :=
  PRSim.forwardSim_lowerGraphToTape prodGraph x

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
theorem eagerBuilds_prod (x : TorchLean.TensorPack ℝ Γ2) (t' : PRSim.RTape) (id : Nat)
    (hop : Runtime.Autograd.Tape.mul (α := ℝ) (s := Shape.scalar)
      (Algebra.Graph.addLeaves (α := ℝ) (t := Runtime.Autograd.Tape.empty) x) 0 1
      = .ok (t', id)) :
    PRSim.EagerBuilds prodGraph x t' := by
  show PRSim.EagerBuilds (.snoc .nil (TapeNodes.mul ix0 ix1)) x t'
  exact PRSim.EagerBuilds.mul (g := .nil) ix0 ix1 (PRSim.EagerBuilds.nil x) hop

/-- **The endpoint on the eager tape**: the dense reverse pass on the runtime-constructed tape
    succeeds and its input-prefix realises `(fderiv ℝ eval x)† seed` — no compilation involved;
    this is the tape `Sensitivity.gradient`'s construction pattern produces. -/
example (x : TorchLean.TensorPack ℝ Γ2) (t' : PRSim.RTape) (id : Nat)
    (hop : Runtime.Autograd.Tape.mul (α := ℝ) (s := Shape.scalar)
      (Algebra.Graph.addLeaves (α := ℝ) (t := Runtime.Autograd.Tape.empty) x) 0 1
      = .ok (t', id))
    (seed : TorchLean.TensorPack ℝ (Γ2 ++ [Shape.scalar])) :
    ∃ out : Array PRSim.Any,
      Runtime.Autograd.Tape.backwardDenseFrom (t := t')
          (TorchLean.TensorPack.toShapeErasedArray (α := ℝ) seed) = .ok out ∧
      PRSim.ArrCorr ((fderiv ℝ (prodGraph.evalVec) (flattenCtx x)).adjoint (flattenCtx seed))
        (out.extract 0 Γ2.length) :=
  PRSim.direct_PR_soundness_eager prodGraph prodCorrect x (eagerBuilds_prod x t' id hop) seed

/-- Eager tapes inhabit the forward simulation relation too. -/
example (x : TorchLean.TensorPack ℝ Γ2) (t' : PRSim.RTape) (id : Nat)
    (hop : Runtime.Autograd.Tape.mul (α := ℝ) (s := Shape.scalar)
      (Algebra.Graph.addLeaves (α := ℝ) (t := Runtime.Autograd.Tape.empty) x) 0 1
      = .ok (t', id)) :
    PRSim.ForwardSim prodGraph (flattenCtx x) t' :=
  PRSim.forwardSim_eager (eagerBuilds_prod x t' id hop)

/-! ## The `sub` crank: the same closure on `x₀ - x₁`, no add/mul reuse

The eager-provenance machine covers a second binary op with no change to its §C/§D/§F structure —
only the per-op §B accounting (`sub_vjp_add_eq`, whose right parent receives the *negated*
cotangent). The endpoint transfers verbatim: `EagerBuilds.sub` witnesses the runtime `Tape.sub`
tape, and `direct_PR_soundness_eager` gives the fderiv adjoint on it. -/

/-- The one-node difference graph `x₀ - x₁`. -/
def subGraph : Graph Γ2 [Shape.scalar] := .snoc .nil (TapeNodes.sub ix0 ix1)

/-- Differentiability witness, assembled from the upstream per-node `subFderiv`. -/
def subCorrect : GraphFDerivCorrect subGraph := ⟨PUnit.unit, TapeNodes.subFderiv ix0 ix1⟩

set_option maxHeartbeats 1600000 in
/-- The runtime tape built for `subGraph`'s inputs: the `Tape.leaf` fold (= `addLeaves`), then one
    eager `Tape.sub 0 1`. `EagerBuilds` witnesses it via the new `sub` constructor. -/
theorem eagerBuilds_sub (x : TorchLean.TensorPack ℝ Γ2) (t' : PRSim.RTape) (id : Nat)
    (hop : Runtime.Autograd.Tape.sub (α := ℝ) (s := Shape.scalar)
      (Algebra.Graph.addLeaves (α := ℝ) (t := Runtime.Autograd.Tape.empty) x) 0 1
      = .ok (t', id)) :
    PRSim.EagerBuilds subGraph x t' := by
  show PRSim.EagerBuilds (.snoc .nil (TapeNodes.sub ix0 ix1)) x t'
  exact PRSim.EagerBuilds.sub (g := .nil) ix0 ix1 (PRSim.EagerBuilds.nil x) hop

/-- **The endpoint on the eager `sub` tape**: the dense reverse pass on the runtime-constructed
    difference tape succeeds and its input-prefix realises `(fderiv ℝ eval x)† seed`. -/
example (x : TorchLean.TensorPack ℝ Γ2) (t' : PRSim.RTape) (id : Nat)
    (hop : Runtime.Autograd.Tape.sub (α := ℝ) (s := Shape.scalar)
      (Algebra.Graph.addLeaves (α := ℝ) (t := Runtime.Autograd.Tape.empty) x) 0 1
      = .ok (t', id))
    (seed : TorchLean.TensorPack ℝ (Γ2 ++ [Shape.scalar])) :
    ∃ out : Array PRSim.Any,
      Runtime.Autograd.Tape.backwardDenseFrom (t := t')
          (TorchLean.TensorPack.toShapeErasedArray (α := ℝ) seed) = .ok out ∧
      PRSim.ArrCorr ((fderiv ℝ (subGraph.evalVec) (flattenCtx x)).adjoint (flattenCtx seed))
        (out.extract 0 Γ2.length) :=
  PRSim.direct_PR_soundness_eager subGraph subCorrect x (eagerBuilds_sub x t' id hop) seed

/-- Eager `sub` tapes inhabit the forward simulation relation too. -/
example (x : TorchLean.TensorPack ℝ Γ2) (t' : PRSim.RTape) (id : Nat)
    (hop : Runtime.Autograd.Tape.sub (α := ℝ) (s := Shape.scalar)
      (Algebra.Graph.addLeaves (α := ℝ) (t := Runtime.Autograd.Tape.empty) x) 0 1
      = .ok (t', id)) :
    PRSim.ForwardSim subGraph (flattenCtx x) t' :=
  PRSim.forwardSim_eager (eagerBuilds_sub x t' id hop)

/-! ## The `scale` crank: the *unary* (one-parent) machine on `3 · x₀`

`scale` is the first one-parent op: a single contribution `scaleSpec δ c` at one parent, so it
exercises the reduced (one-`addGradAll`) variant of the machine — the shape every `Arithmetic`/
`Elementwise` unary (activations included) shares. Same endpoint transfer via the same generic
`direct_PR_soundness_eager`. -/

/-- The one-node scaling graph `3 · x₀`. -/
def scaleGraph : Graph Γ2 [Shape.scalar] := .snoc .nil (TapeNodes.scale ix0 3)

/-- Differentiability witness, assembled from the upstream per-node `scaleFderiv`. -/
def scaleCorrect : GraphFDerivCorrect scaleGraph := ⟨PUnit.unit, TapeNodes.scaleFderiv ix0 3⟩

set_option maxHeartbeats 1600000 in
/-- `EagerBuilds` witnesses the runtime `Tape.scale 0 3` tape via the new `scale` constructor. -/
theorem eagerBuilds_scale (x : TorchLean.TensorPack ℝ Γ2) (t' : PRSim.RTape) (id : Nat)
    (hop : Runtime.Autograd.Tape.scale (α := ℝ) (s := Shape.scalar)
      (Algebra.Graph.addLeaves (α := ℝ) (t := Runtime.Autograd.Tape.empty) x) 0 3
      = .ok (t', id)) :
    PRSim.EagerBuilds scaleGraph x t' := by
  show PRSim.EagerBuilds (.snoc .nil (TapeNodes.scale ix0 3)) x t'
  exact PRSim.EagerBuilds.scale (g := .nil) ix0 3 (PRSim.EagerBuilds.nil x) hop

/-- **The endpoint on the eager `scale` tape**: the dense reverse pass on the runtime-constructed
    one-parent tape succeeds and its input-prefix realises `(fderiv ℝ eval x)† seed`. -/
example (x : TorchLean.TensorPack ℝ Γ2) (t' : PRSim.RTape) (id : Nat)
    (hop : Runtime.Autograd.Tape.scale (α := ℝ) (s := Shape.scalar)
      (Algebra.Graph.addLeaves (α := ℝ) (t := Runtime.Autograd.Tape.empty) x) 0 3
      = .ok (t', id))
    (seed : TorchLean.TensorPack ℝ (Γ2 ++ [Shape.scalar])) :
    ∃ out : Array PRSim.Any,
      Runtime.Autograd.Tape.backwardDenseFrom (t := t')
          (TorchLean.TensorPack.toShapeErasedArray (α := ℝ) seed) = .ok out ∧
      PRSim.ArrCorr ((fderiv ℝ (scaleGraph.evalVec) (flattenCtx x)).adjoint (flattenCtx seed))
        (out.extract 0 Γ2.length) :=
  PRSim.direct_PR_soundness_eager scaleGraph scaleCorrect x (eagerBuilds_scale x t' id hop) seed

/-! ### The elementwise/activation family through the *generic* unary machine

`exp` is a genuine activation instance of the abstracted unary crank: the P-node is
`TapeNodes.elemwise Real.exp Real.exp`, the runtime is `Tape.exp` (defeq to the shared
`Tape.unary` shape with `fwdSpec = bwdSpec = expSpec = mapSpec Real.exp`), and the two per-op
bridges are the *single* pointwise fact `tensorToVec_mapSpec_apply`. No new §E/§F reasoning: the whole
`{exp, log, tanh, sigmoid, sinh, cosh, softplus, …}` family reuses `EagerBuilds.unary`. -/

/-- The one-node exponential graph `exp(x₀)`.  `TapeNodes.exp ix0` unfolds to exactly
    `TapeNodes.elemwise ix0 Real.exp Real.exp`; spelling the `elemwise` form here keeps the eager
    witness's `whnf` cheap (it is the constructor's own result head). -/
def expGraph : Graph Γ2 [Shape.scalar] := .snoc .nil (TapeNodes.elemwise ix0 Real.exp Real.exp)

/-- Differentiability witness from the upstream *global* `expFderiv`
    (`= elemwiseFderiv Real.exp Real.exp _`). -/
def expCorrect : GraphFDerivCorrect expGraph :=
  ⟨PUnit.unit, TapeNodes.elemwiseFderiv ix0 Real.exp Real.exp (fun z => Real.hasDerivAt_exp z)⟩

set_option maxHeartbeats 6400000 in
/-- `EagerBuilds` witnesses the runtime `exp` tape via the generic `unary` constructor —
    `exp = elemwise Real.exp Real.exp`, `fwdSpec = bwdSpec = expSpec`, both bridges from
    `tensorToVec_mapSpec_apply` (since `MathFunctions.exp = Real.exp` on `ℝ`).

    The runtime op is written here in the shared `Tape.unary "exp" … expSpec …` shape it reduces to;
    `Runtime.Autograd.Tape.exp t 0` is *definitionally* this call, so this is the genuine `exp`
    activation, presented in the form that makes the one-parent node shape manifest. -/
theorem eagerBuilds_exp (x : TorchLean.TensorPack ℝ Γ2) (t' : PRSim.RTape) (id : Nat)
    (hop : Runtime.Autograd.Tape.unary (α := ℝ) (σ := Shape.scalar) (τ := Shape.scalar)
      (Algebra.Graph.addLeaves (α := ℝ) (t := Runtime.Autograd.Tape.empty) x) "exp" 0
      expSpec (fun xv d => mulSpec (expSpec xv) d) = .ok (t', id)) :
    PRSim.EagerBuilds expGraph x t' := by
  show PRSim.EagerBuilds (.snoc .nil (TapeNodes.elemwise ix0 Real.exp Real.exp)) x t'
  exact PRSim.EagerBuilds.unary (g := .nil) ix0 "exp" Real.exp Real.exp expSpec expSpec
    (fun u i => PRSim.tensorToVec_mapSpec_apply u i) (fun u i => PRSim.tensorToVec_mapSpec_apply u i)
    (PRSim.EagerBuilds.nil x) hop

set_option maxHeartbeats 6400000 in
/-- **The endpoint on the eager `exp` tape** — the *same* generic `direct_PR_soundness_eager`
    transfers the fderiv-adjoint endpoint to this activation tape, no per-op change. -/
example (x : TorchLean.TensorPack ℝ Γ2) (t' : PRSim.RTape) (id : Nat)
    (hop : Runtime.Autograd.Tape.unary (α := ℝ) (σ := Shape.scalar) (τ := Shape.scalar)
      (Algebra.Graph.addLeaves (α := ℝ) (t := Runtime.Autograd.Tape.empty) x) "exp" 0
      expSpec (fun xv d => mulSpec (expSpec xv) d) = .ok (t', id))
    (seed : TorchLean.TensorPack ℝ (Γ2 ++ [Shape.scalar])) :
    ∃ out : Array PRSim.Any,
      Runtime.Autograd.Tape.backwardDenseFrom (t := t')
          (TorchLean.TensorPack.toShapeErasedArray (α := ℝ) seed) = .ok out ∧
      PRSim.ArrCorr ((fderiv ℝ (expGraph.evalVec) (flattenCtx x)).adjoint (flattenCtx seed))
        (out.extract 0 Γ2.length) :=
  PRSim.direct_PR_soundness_eager expGraph expCorrect x (eagerBuilds_exp x t' id hop) seed

/-! ## The `div` crank: the *pointwise* binary machine on `x₀ / x₁`

`div` is the third binary op through the same §C/§D/§F machine (`EagerBuilds.div` witnesses the
runtime `Tape.div` tape, whose backward feeds the quotient-rule cotangents — `divSpec δ b` to the
left parent, the negated `subSpec (fill 0) (mulSpec δ (divSpec a (mulSpec b b)))` to the right).
The provenance identification is unconditional, but the quotient rule is a genuine Fréchet
derivative only where the denominator is nonzero — so the correctness witness is the *pointwise*
`GraphFDerivCorrectAt` (upstream `TapeNodes.divFderivAt` under the nonzero hypothesis at the
concrete input) and the endpoint transfers through `direct_PR_soundness_eager_at`. -/

/-- The one-node quotient graph `x₀ / x₁`. -/
def divGraph : Graph Γ2 [Shape.scalar] := .snoc .nil (TapeNodes.div ix0 ix1)

/-- Pointwise differentiability witness at the input `x`, under the denominator-nonzero
    hypothesis (the standard mathematical domain of the quotient rule), assembled from the
    upstream per-node `divFderivAt`. -/
def divCorrectAt (x : TorchLean.TensorPack ℝ Γ2)
    (hb : ∀ i : Fin (Spec.Shape.size Shape.scalar),
      CtxVec.get (Γ := Γ2) (s := Shape.scalar) ix1
        (Graph.evalVec (Γ := Γ2) (ss := []) .nil (flattenCtx x)) i ≠ 0) :
    GraphFDerivCorrectAt divGraph (flattenCtx x) :=
  ⟨PUnit.unit, TapeNodes.divFderivAt ix0 ix1 _ hb⟩

set_option maxHeartbeats 6400000 in
/-- The runtime tape built for `divGraph`'s inputs: the `Tape.leaf` fold (= `addLeaves`), then one
    eager `Tape.div 0 1`. `EagerBuilds` witnesses it via the new `div` constructor. -/
theorem eagerBuilds_div (x : TorchLean.TensorPack ℝ Γ2) (t' : PRSim.RTape) (id : Nat)
    (hop : Runtime.Autograd.Tape.div (α := ℝ) (s := Shape.scalar)
      (Algebra.Graph.addLeaves (α := ℝ) (t := Runtime.Autograd.Tape.empty) x) 0 1
      = .ok (t', id)) :
    PRSim.EagerBuilds divGraph x t' := by
  show PRSim.EagerBuilds (.snoc .nil (TapeNodes.div ix0 ix1)) x t'
  exact PRSim.EagerBuilds.div (g := .nil) ix0 ix1 (PRSim.EagerBuilds.nil x) hop

set_option maxHeartbeats 6400000 in
/-- **The endpoint on the eager `div` tape**: under the denominator-nonzero hypothesis at the
    concrete input, the dense reverse pass on the runtime-constructed quotient tape succeeds and
    its input-prefix realises `(fderiv ℝ eval x)† seed` — via the *pointwise*
    `direct_PR_soundness_eager_at`. -/
example (x : TorchLean.TensorPack ℝ Γ2)
    (hb : ∀ i : Fin (Spec.Shape.size Shape.scalar),
      CtxVec.get (Γ := Γ2) (s := Shape.scalar) ix1
        (Graph.evalVec (Γ := Γ2) (ss := []) .nil (flattenCtx x)) i ≠ 0)
    (t' : PRSim.RTape) (id : Nat)
    (hop : Runtime.Autograd.Tape.div (α := ℝ) (s := Shape.scalar)
      (Algebra.Graph.addLeaves (α := ℝ) (t := Runtime.Autograd.Tape.empty) x) 0 1
      = .ok (t', id))
    (seed : TorchLean.TensorPack ℝ (Γ2 ++ [Shape.scalar])) :
    ∃ out : Array PRSim.Any,
      Runtime.Autograd.Tape.backwardDenseFrom (t := t')
          (TorchLean.TensorPack.toShapeErasedArray (α := ℝ) seed) = .ok out ∧
      PRSim.ArrCorr ((fderiv ℝ (divGraph.evalVec) (flattenCtx x)).adjoint (flattenCtx seed))
        (out.extract 0 Γ2.length) :=
  PRSim.direct_PR_soundness_eager_at divGraph x (divCorrectAt x hb)
    (eagerBuilds_div x t' id hop) seed

/-- Eager `div` tapes inhabit the forward simulation relation too (no differentiability, hence no
    nonzero hypothesis, is needed for the forward direction). -/
example (x : TorchLean.TensorPack ℝ Γ2) (t' : PRSim.RTape) (id : Nat)
    (hop : Runtime.Autograd.Tape.div (α := ℝ) (s := Shape.scalar)
      (Algebra.Graph.addLeaves (α := ℝ) (t := Runtime.Autograd.Tape.empty) x) 0 1
      = .ok (t', id)) :
    PRSim.ForwardSim divGraph (flattenCtx x) t' :=
  PRSim.forwardSim_eager (eagerBuilds_div x t' id hop)

/-! ## Axiom profiles — closed means closed -/

/-- info: 'PRSim.mulSpec_vecToTensor' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms PRSim.mulSpec_vecToTensor

/-- info: 'PRSim.addSpec_vecToTensor' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms PRSim.addSpec_vecToTensor

/-- info: 'PRSim.backwardDenseFrom_ok' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms PRSim.backwardDenseFrom_ok

/-- info: 'PRSim.forwardSim_lowerGraphToTape' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms PRSim.forwardSim_lowerGraphToTape

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

/--
info: 'PRSim.direct_PR_soundness_eager_at' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in #print axioms PRSim.direct_PR_soundness_eager_at

/-- info: 'PRSim.forwardSim_eager' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms PRSim.forwardSim_eager

/--
info: 'PropertyKindCalculus.UncertaintyExamples.AutogradDirectSim.eagerBuilds_exp' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in #print axioms eagerBuilds_exp

/--
info: 'PropertyKindCalculus.UncertaintyExamples.AutogradDirectSim.eagerBuilds_div' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in #print axioms eagerBuilds_div


section
-- The scalar sigmoid specs are irreducible for this block: the instance unification otherwise
-- substitutes their bodies through the elemwise node machinery and diverges (>25M heartbeats);
-- opaque constants keep it in the same budget as the `exp` instance. Assignment still works —
-- only unfolding-during-unification is blocked.
attribute [local irreducible] Activation.Math.sigmoidSpec Activation.Math.sigmoidDerivSpec

/-! ### `sigmoid` through the same generic unary machine

A second activation instance of the abstracted unary crank, with *nothing* new: the P-node is
`TapeNodes.elemwise Activation.Math.sigmoidSpec Activation.Math.sigmoidDerivSpec`, the runtime is
`Tape.sigmoid` (defeq to the shared `Tape.unary` shape with `fwdSpec = Activation.sigmoidSpec` and
`bwdSpec = Activation.sigmoidDerivSpec`, each `mapSpec` of the *same* scalar spec), and the two
per-op bridges are again the single pointwise fact `tensorToVec_mapSpec_apply`. No new §E/§F
reasoning: this is the promised `{exp, log, tanh, sigmoid, …}` reuse of `EagerBuilds.unary`,
cranked once more. -/

/-- The one-node logistic graph `sigmoid(x₀)`.  `TapeNodes.sigmoid ix0` unfolds to exactly
    `TapeNodes.elemwise ix0 Activation.Math.sigmoidSpec Activation.Math.sigmoidDerivSpec`;
    spelling the `elemwise` form here keeps the eager witness's `whnf` cheap (it is the
    constructor's own result head). -/
def sigmoidGraph : Graph Γ2 [Shape.scalar] :=
  .snoc .nil (TapeNodes.elemwise ix0 Activation.Math.sigmoidSpec Activation.Math.sigmoidDerivSpec)

/-- Differentiability witness from the upstream *global* scalar fact
    `Proofs.sigmoid_deriv_correct` — the same assembly as `TapeNodes.sigmoidFderiv`, spelled in
    the `elemwiseFderiv` form to match `sigmoidGraph`. -/
def sigmoidCorrect : GraphFDerivCorrect sigmoidGraph :=
  ⟨PUnit.unit, TapeNodes.elemwiseFderiv ix0
    Activation.Math.sigmoidSpec Activation.Math.sigmoidDerivSpec
    (fun z => Proofs.sigmoid_deriv_correct (x := z))⟩

set_option maxHeartbeats 6400000 in
/-- `EagerBuilds` witnesses the runtime `sigmoid` tape via the generic `unary` constructor —
    `sigmoid = elemwise Activation.Math.sigmoidSpec Activation.Math.sigmoidDerivSpec`,
    `fwdSpec = Activation.sigmoidSpec`, `bwdSpec = Activation.sigmoidDerivSpec` (each is
    `mapSpec` of the corresponding scalar spec), both bridges from `tensorToVec_mapSpec_apply`.

    The runtime op is written here in the shared `Tape.unary "sigmoid" … Activation.sigmoidSpec …`
    shape it reduces to; `Runtime.Autograd.Tape.sigmoid t 0` is *definitionally* this call (its
    `let dsig` ζ-reduces into the `mulSpec (bwdSpec x) dLdy` contribution), so this is the genuine
    `sigmoid` activation, presented in the form that makes the one-parent node shape manifest. -/
theorem eagerBuilds_sigmoid (x : TorchLean.TensorPack ℝ Γ2) (t' : PRSim.RTape) (id : Nat)
    (hop : Runtime.Autograd.Tape.unary (α := ℝ) (σ := Shape.scalar) (τ := Shape.scalar)
      (Algebra.Graph.addLeaves (α := ℝ) (t := Runtime.Autograd.Tape.empty) x) "sigmoid" 0
      Activation.sigmoidSpec
      (fun xv d => mulSpec (Activation.sigmoidDerivSpec xv) d) = .ok (t', id)) :
    PRSim.EagerBuilds sigmoidGraph x t' := by
  show PRSim.EagerBuilds
    (.snoc .nil
      (TapeNodes.elemwise ix0 Activation.Math.sigmoidSpec Activation.Math.sigmoidDerivSpec)) x t'
  exact PRSim.EagerBuilds.unary (g := .nil) ix0 "sigmoid"
    Activation.Math.sigmoidSpec Activation.Math.sigmoidDerivSpec
    Activation.sigmoidSpec Activation.sigmoidDerivSpec
    (fun u i => PRSim.tensorToVec_mapSpec_apply u i) (fun u i => PRSim.tensorToVec_mapSpec_apply u i)
    (PRSim.EagerBuilds.nil x) hop

set_option maxHeartbeats 6400000 in
/-- **The endpoint on the eager `sigmoid` tape** — the *same* generic `direct_PR_soundness_eager`
    transfers the fderiv-adjoint endpoint to this activation tape, no per-op change (the scalar
    derivative fact is global, so the universal endpoint applies — no `_at` threading needed). -/
example (x : TorchLean.TensorPack ℝ Γ2) (t' : PRSim.RTape) (id : Nat)
    (hop : Runtime.Autograd.Tape.unary (α := ℝ) (σ := Shape.scalar) (τ := Shape.scalar)
      (Algebra.Graph.addLeaves (α := ℝ) (t := Runtime.Autograd.Tape.empty) x) "sigmoid" 0
      Activation.sigmoidSpec
      (fun xv d => mulSpec (Activation.sigmoidDerivSpec xv) d) = .ok (t', id))
    (seed : TorchLean.TensorPack ℝ (Γ2 ++ [Shape.scalar])) :
    ∃ out : Array PRSim.Any,
      Runtime.Autograd.Tape.backwardDenseFrom (t := t')
          (TorchLean.TensorPack.toShapeErasedArray (α := ℝ) seed) = .ok out ∧
      PRSim.ArrCorr ((fderiv ℝ (sigmoidGraph.evalVec) (flattenCtx x)).adjoint (flattenCtx seed))
        (out.extract 0 Γ2.length) :=
  PRSim.direct_PR_soundness_eager sigmoidGraph sigmoidCorrect x
    (eagerBuilds_sigmoid x t' id hop) seed

/--
info: 'PropertyKindCalculus.UncertaintyExamples.AutogradDirectSim.eagerBuilds_sigmoid' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in #print axioms eagerBuilds_sigmoid

end

section
-- Same irreducibility shield as the sigmoid block (see comment there).
attribute [local irreducible] Activation.Math.tanhSpec Activation.Math.tanhDerivSpec

/-! ### `tanh` through the *same* generic unary machine — the family claim made good

`tanh` is the second activation instance of the abstracted unary crank, with zero new op
reasoning: the P-node is `TapeNodes.elemwise Activation.Math.tanhSpec Activation.Math.tanhDerivSpec`
(exactly what `TapeNodes.tanh` unfolds to), the runtime `Tape.tanh` is defeq to the shared
`Tape.unary "tanh" … Activation.tanhSpec …` shape (forward `tanhSpec = mapSpec Math.tanhSpec`,
backward `mulSpec (tanhDerivSpec x) dLdy` with `tanhDerivSpec = mapSpec Math.tanhDerivSpec`), and
both per-op bridges are again the *single* pointwise fact `tensorToVec_mapSpec_apply` — this time with
no instance unfolding at all, since the node's scalar functions *are* the `Math` specs. -/

/-- The one-node hyperbolic-tangent graph `tanh(x₀)`.  `TapeNodes.tanh ix0` unfolds to exactly
    `TapeNodes.elemwise ix0 Activation.Math.tanhSpec Activation.Math.tanhDerivSpec`; spelling the
    `elemwise` form here keeps the eager witness's `whnf` cheap (it is the constructor's own
    result head). -/
def tanhGraph : Graph Γ2 [Shape.scalar] :=
  .snoc .nil (TapeNodes.elemwise ix0 Activation.Math.tanhSpec Activation.Math.tanhDerivSpec)

/-- Differentiability witness from the upstream *global* scalar fact `Proofs.tanh_deriv_correct`
    (`tanh' = 1 - tanh²`, everywhere) — the same assembly as `TapeNodes.tanhFderiv`. -/
def tanhCorrect : GraphFDerivCorrect tanhGraph :=
  ⟨PUnit.unit, TapeNodes.elemwiseFderiv ix0 Activation.Math.tanhSpec Activation.Math.tanhDerivSpec
    (fun z => Proofs.tanh_deriv_correct (x := z))⟩

set_option maxHeartbeats 6400000 in
/-- `EagerBuilds` witnesses the runtime `tanh` tape via the generic `unary` constructor —
    `tanh = elemwise Math.tanhSpec Math.tanhDerivSpec`, `fwdSpec = Activation.tanhSpec =
    mapSpec Math.tanhSpec`, `bwdSpec = Activation.tanhDerivSpec = mapSpec Math.tanhDerivSpec`,
    both bridges from `tensorToVec_mapSpec_apply` (on `ℝ`, `MathFunctions.tanh = Real.tanh`).

    The runtime op is written here in the shared `Tape.unary "tanh" … Activation.tanhSpec …`
    shape it reduces to; `Runtime.Autograd.Tape.tanh t 0` is *definitionally* this call (the
    node-literal's `let dtanh := …` zeta-reduces to the generic backward), so this is the genuine
    `tanh` activation, presented in the form that makes the one-parent node shape manifest. -/
theorem eagerBuilds_tanh (x : TorchLean.TensorPack ℝ Γ2) (t' : PRSim.RTape) (id : Nat)
    (hop : Runtime.Autograd.Tape.unary (α := ℝ) (σ := Shape.scalar) (τ := Shape.scalar)
      (Algebra.Graph.addLeaves (α := ℝ) (t := Runtime.Autograd.Tape.empty) x) "tanh" 0
      Activation.tanhSpec (fun xv d => mulSpec (Activation.tanhDerivSpec xv) d) = .ok (t', id)) :
    PRSim.EagerBuilds tanhGraph x t' := by
  show PRSim.EagerBuilds
    (.snoc .nil (TapeNodes.elemwise ix0 Activation.Math.tanhSpec Activation.Math.tanhDerivSpec))
    x t'
  exact PRSim.EagerBuilds.unary (g := .nil) ix0 "tanh"
    Activation.Math.tanhSpec Activation.Math.tanhDerivSpec
    Activation.tanhSpec Activation.tanhDerivSpec
    (fun u i => PRSim.tensorToVec_mapSpec_apply u i) (fun u i => PRSim.tensorToVec_mapSpec_apply u i)
    (PRSim.EagerBuilds.nil x) hop

set_option maxHeartbeats 6400000 in
/-- **The endpoint on the eager `tanh` tape** — the *same* generic `direct_PR_soundness_eager`
    transfers the fderiv-adjoint endpoint to this activation tape, no per-op change (the upstream
    `tanh` derivative fact is global, so no pointwise `_at` threading is needed). -/
example (x : TorchLean.TensorPack ℝ Γ2) (t' : PRSim.RTape) (id : Nat)
    (hop : Runtime.Autograd.Tape.unary (α := ℝ) (σ := Shape.scalar) (τ := Shape.scalar)
      (Algebra.Graph.addLeaves (α := ℝ) (t := Runtime.Autograd.Tape.empty) x) "tanh" 0
      Activation.tanhSpec (fun xv d => mulSpec (Activation.tanhDerivSpec xv) d) = .ok (t', id))
    (seed : TorchLean.TensorPack ℝ (Γ2 ++ [Shape.scalar])) :
    ∃ out : Array PRSim.Any,
      Runtime.Autograd.Tape.backwardDenseFrom (t := t')
          (TorchLean.TensorPack.toShapeErasedArray (α := ℝ) seed) = .ok out ∧
      PRSim.ArrCorr ((fderiv ℝ (tanhGraph.evalVec) (flattenCtx x)).adjoint (flattenCtx seed))
        (out.extract 0 Γ2.length) :=
  PRSim.direct_PR_soundness_eager tanhGraph tanhCorrect x (eagerBuilds_tanh x t' id hop) seed

/--
info: 'PropertyKindCalculus.UncertaintyExamples.AutogradDirectSim.eagerBuilds_tanh' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in #print axioms eagerBuilds_tanh

end

section
-- Same irreducibility shield as the sigmoid block (see comment there).
attribute [local irreducible] Activation.Math.softplusSpec Activation.Math.softplusDerivSpec
/-! ### `softplus`: a second activation instance of the generic unary machine

The P-node is `TapeNodes.elemwise ix0 Activation.Math.softplusSpec
Activation.Math.softplusDerivSpec` (scalar softplus and its derivative, sigmoid); the runtime is
`Tape.softplus` — definitionally the shared `Tape.unary "softplus" …` shape with
`fwdSpec = Activation.softplusSpec` and backward contribution
`mulSpec (Activation.softplusDerivSpec x) dLdy`.  Both runtime specs are literally `mapSpec` of
the *same* scalar maps the P-node carries, so — with `exp` as the baseline — the two bridges need
no instance-rfl step at all: both are `tensorToVec_mapSpec_apply` verbatim.  The upstream derivative
witness `Proofs.softplus_deriv_correct` is *global* (`∀ x, HasDerivAt`), so the *universal*
endpoint `direct_PR_soundness_eager` applies, exactly as for `exp`. -/

/-- The one-node softplus graph `softplus(x₀)`.  `TapeNodes.softplus ix0` unfolds to exactly
    `TapeNodes.elemwise ix0 Activation.Math.softplusSpec Activation.Math.softplusDerivSpec`;
    spelling the `elemwise` form here keeps the eager witness's `whnf` cheap (it is the
    constructor's own result head). -/
def softplusGraph : Graph Γ2 [Shape.scalar] :=
  .snoc .nil
    (TapeNodes.elemwise ix0 Activation.Math.softplusSpec Activation.Math.softplusDerivSpec)

/-- Differentiability witness from the upstream *global* `Proofs.softplus_deriv_correct`
    (`softplus' = sigmoid`, everywhere — the same fact `TapeNodes.softplusFderiv` is built
    from). -/
def softplusCorrect : GraphFDerivCorrect softplusGraph :=
  ⟨PUnit.unit, TapeNodes.elemwiseFderiv ix0 Activation.Math.softplusSpec
    Activation.Math.softplusDerivSpec (fun z => Proofs.softplus_deriv_correct z)⟩

set_option maxHeartbeats 6400000 in
/-- `EagerBuilds` witnesses the runtime `softplus` tape via the generic `unary` constructor —
    `softplus = elemwise Activation.Math.softplusSpec Activation.Math.softplusDerivSpec`,
    `fwdSpec = Activation.softplusSpec`, `bwdSpec = Activation.softplusDerivSpec` (each `mapSpec`
    of the corresponding scalar map), both bridges from `tensorToVec_mapSpec_apply`.

    The runtime op is written here in the shared
    `Tape.unary "softplus" … Activation.softplusSpec …` shape it reduces to;
    `Runtime.Autograd.Tape.softplus t 0` is *definitionally* this call, so this is the genuine
    `softplus` activation, presented in the form that makes the one-parent node shape manifest. -/
theorem eagerBuilds_softplus (x : TorchLean.TensorPack ℝ Γ2) (t' : PRSim.RTape) (id : Nat)
    (hop : Runtime.Autograd.Tape.unary (α := ℝ) (σ := Shape.scalar) (τ := Shape.scalar)
      (Algebra.Graph.addLeaves (α := ℝ) (t := Runtime.Autograd.Tape.empty) x) "softplus" 0
      Activation.softplusSpec
      (fun xv d => mulSpec (Activation.softplusDerivSpec xv) d) = .ok (t', id)) :
    PRSim.EagerBuilds softplusGraph x t' := by
  show PRSim.EagerBuilds
    (.snoc .nil
      (TapeNodes.elemwise ix0 Activation.Math.softplusSpec Activation.Math.softplusDerivSpec))
    x t'
  exact PRSim.EagerBuilds.unary (g := .nil) ix0 "softplus"
    Activation.Math.softplusSpec Activation.Math.softplusDerivSpec
    Activation.softplusSpec Activation.softplusDerivSpec
    (fun u i => PRSim.tensorToVec_mapSpec_apply u i) (fun u i => PRSim.tensorToVec_mapSpec_apply u i)
    (PRSim.EagerBuilds.nil x) hop

set_option maxHeartbeats 6400000 in
/-- **The endpoint on the eager `softplus` tape** — the *same* generic
    `direct_PR_soundness_eager` transfers the fderiv-adjoint endpoint to this activation tape, no
    per-op change (the upstream derivative witness is global, so the universal endpoint applies
    rather than the pointwise `_at` variant). -/
example (x : TorchLean.TensorPack ℝ Γ2) (t' : PRSim.RTape) (id : Nat)
    (hop : Runtime.Autograd.Tape.unary (α := ℝ) (σ := Shape.scalar) (τ := Shape.scalar)
      (Algebra.Graph.addLeaves (α := ℝ) (t := Runtime.Autograd.Tape.empty) x) "softplus" 0
      Activation.softplusSpec
      (fun xv d => mulSpec (Activation.softplusDerivSpec xv) d) = .ok (t', id))
    (seed : TorchLean.TensorPack ℝ (Γ2 ++ [Shape.scalar])) :
    ∃ out : Array PRSim.Any,
      Runtime.Autograd.Tape.backwardDenseFrom (t := t')
          (TorchLean.TensorPack.toShapeErasedArray (α := ℝ) seed) = .ok out ∧
      PRSim.ArrCorr ((fderiv ℝ (softplusGraph.evalVec) (flattenCtx x)).adjoint (flattenCtx seed))
        (out.extract 0 Γ2.length) :=
  PRSim.direct_PR_soundness_eager softplusGraph softplusCorrect x
    (eagerBuilds_softplus x t' id hop) seed

/--
info: 'PropertyKindCalculus.UncertaintyExamples.AutogradDirectSim.softplusCorrect' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in #print axioms softplusCorrect

/--
info: 'PropertyKindCalculus.UncertaintyExamples.AutogradDirectSim.eagerBuilds_softplus' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in #print axioms eagerBuilds_softplus

end

section
-- Same irreducibility shield as the sigmoid block (see comment there).
attribute [local irreducible] Activation.Math.reluSpec Activation.Math.reluDerivSpec
/-! ### A pointwise activation through the generic unary machine: `relu`

Same `EagerBuilds.unary` crank as `exp`, but the scalar derivative only exists away from the kink:
the P-witness is the *pointwise* `TapeNodes.reluFderivAt` (inputs `≠ 0`), so the endpoint is the
pointwise `direct_PR_soundness_eager_at` (`GraphFDerivCorrectAt` at the actual input) with the
domain hypothesis threaded through the example binders. Both tensor specs are `mapSpec` of the
*same* scalar specs the P-node carries (`Activation.reluSpec = mapSpec Activation.Math.reluSpec`,
likewise the derivative), so both bridges are again `tensorToVec_mapSpec_apply` — no per-op scalar
bridging at all. -/

/-- The one-node rectifier graph `relu(x₀)`.  `TapeNodes.relu ix0` unfolds to exactly
    `TapeNodes.elemwise ix0 Activation.Math.reluSpec Activation.Math.reluDerivSpec`; spelling the
    `elemwise` form here keeps the eager witness's `whnf` cheap (it is the constructor's own
    result head). -/
def reluGraph : Graph Γ2 [Shape.scalar] :=
  .snoc .nil (TapeNodes.elemwise ix0 Activation.Math.reluSpec Activation.Math.reluDerivSpec)

/-- Pointwise differentiability witness from the upstream per-node `reluFderivAt`, under the
    domain hypothesis that the input coordinates avoid the kink at `0`.  The hypothesis is stated
    at `Graph.evalVec .nil (flattenCtx x)` — the exact basepoint `GraphFDerivCorrectAt` computes
    for the single node. -/
def reluCorrectAt (x : TorchLean.TensorPack ℝ Γ2)
    (hx : ∀ i : Fin (Spec.Shape.size Shape.scalar),
      CtxVec.get (Γ := Γ2) (s := Shape.scalar) ix0
        (Graph.evalVec (Γ := Γ2) .nil (flattenCtx x)) i ≠ 0) :
    GraphFDerivCorrectAt reluGraph (flattenCtx x) :=
  ⟨PUnit.unit, TapeNodes.reluFderivAt ix0 (Graph.evalVec (Γ := Γ2) .nil (flattenCtx x)) hx⟩

set_option maxHeartbeats 6400000 in
/-- `EagerBuilds` witnesses the runtime `relu` tape via the generic `unary` constructor —
    `relu = elemwise Activation.Math.reluSpec Activation.Math.reluDerivSpec`,
    `fwdSpec = Activation.reluSpec`, `bwdSpec = Activation.reluDerivSpec` (each the `mapSpec` of
    the matching scalar spec), both bridges from `tensorToVec_mapSpec_apply`.

    The runtime op is written here in the shared `Tape.unary "relu" … Activation.reluSpec …` shape
    it reduces to; `Runtime.Autograd.Tape.relu t 0` is *definitionally* this call, so this is the
    genuine `relu` activation, presented in the form that makes the one-parent node shape
    manifest. -/
theorem eagerBuilds_relu (x : TorchLean.TensorPack ℝ Γ2) (t' : PRSim.RTape) (id : Nat)
    (hop : Runtime.Autograd.Tape.unary (α := ℝ) (σ := Shape.scalar) (τ := Shape.scalar)
      (Algebra.Graph.addLeaves (α := ℝ) (t := Runtime.Autograd.Tape.empty) x) "relu" 0
      Activation.reluSpec (fun xv d => mulSpec (Activation.reluDerivSpec xv) d) = .ok (t', id)) :
    PRSim.EagerBuilds reluGraph x t' := by
  show PRSim.EagerBuilds
    (.snoc .nil (TapeNodes.elemwise ix0 Activation.Math.reluSpec Activation.Math.reluDerivSpec))
    x t'
  exact PRSim.EagerBuilds.unary (g := .nil) ix0 "relu" Activation.Math.reluSpec
    Activation.Math.reluDerivSpec Activation.reluSpec Activation.reluDerivSpec
    (fun u i => PRSim.tensorToVec_mapSpec_apply u i) (fun u i => PRSim.tensorToVec_mapSpec_apply u i)
    (PRSim.EagerBuilds.nil x) hop

set_option maxHeartbeats 6400000 in
/-- **The endpoint on the eager `relu` tape** — the *pointwise* `direct_PR_soundness_eager_at`
    transfers the fderiv-adjoint endpoint to this activation tape under the away-from-the-kink
    domain hypothesis; no per-op change beyond threading `hx`. -/
example (x : TorchLean.TensorPack ℝ Γ2) (t' : PRSim.RTape) (id : Nat)
    (hop : Runtime.Autograd.Tape.unary (α := ℝ) (σ := Shape.scalar) (τ := Shape.scalar)
      (Algebra.Graph.addLeaves (α := ℝ) (t := Runtime.Autograd.Tape.empty) x) "relu" 0
      Activation.reluSpec (fun xv d => mulSpec (Activation.reluDerivSpec xv) d) = .ok (t', id))
    (hx : ∀ i : Fin (Spec.Shape.size Shape.scalar),
      CtxVec.get (Γ := Γ2) (s := Shape.scalar) ix0
        (Graph.evalVec (Γ := Γ2) .nil (flattenCtx x)) i ≠ 0)
    (seed : TorchLean.TensorPack ℝ (Γ2 ++ [Shape.scalar])) :
    ∃ out : Array PRSim.Any,
      Runtime.Autograd.Tape.backwardDenseFrom (t := t')
          (TorchLean.TensorPack.toShapeErasedArray (α := ℝ) seed) = .ok out ∧
      PRSim.ArrCorr ((fderiv ℝ (reluGraph.evalVec) (flattenCtx x)).adjoint (flattenCtx seed))
        (out.extract 0 Γ2.length) :=
  PRSim.direct_PR_soundness_eager_at reluGraph x (reluCorrectAt x hx)
    (eagerBuilds_relu x t' id hop) seed

/--
info: 'PropertyKindCalculus.UncertaintyExamples.AutogradDirectSim.eagerBuilds_relu' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in #print axioms eagerBuilds_relu

end

/-- Pointwise: `invSpec` acts coordinatewise as `(·)⁻¹` under vectorization.  `invSpec` is
    `mapSpec (fun x => 1 / x)` (`Spec/Core/TensorOps.lean:216`), *not* literally `mapSpec (·⁻¹)`,
    so the `log` backward bridge is `tensorToVec_mapSpec_apply` composed with `one_div`. -/
theorem tensorToVec_invSpec_apply {s : Shape} (u : Tensor ℝ s) (i : Fin (Spec.Shape.size s)) :
    tensorToVec (t := invSpec u) i = (tensorToVec (t := u) i)⁻¹ :=
  (PRSim.tensorToVec_mapSpec_apply u i).trans (one_div _)

/-! ### The pointwise (`At`) crank of the generic unary machine: `log`, differentiable off zero

`log` is the first *domain-restricted* member of the elementwise family: the P-node is
`TapeNodes.elemwise Real.log (fun z => z⁻¹)` (= `TapeNodes.log`), differentiable only at nonzero
inputs, so the witness is `GraphFDerivCorrectAt` (assembled from `elemwiseFderivAt` +
`Real.hasDerivAt_log`, exactly the assembly inside `TapeNodes.logFderivAt`) and the endpoint is
the pointwise `direct_PR_soundness_eager_at`, with the nonzero-input hypothesis threaded through
the binders.  Bridges: `logSpec = mapSpec MathFunctions.log` with `MathFunctions.log = Real.log`
on `ℝ` (instance-`rfl`, like `exp`), while `invSpec = mapSpec (1 / ·)`, so its bridge is
`tensorToVec_invSpec_apply` (= `tensorToVec_mapSpec_apply` composed with `one_div`). -/

/-- The one-node logarithm graph `log(x₀)`.  `TapeNodes.log ix0` unfolds to exactly
    `TapeNodes.elemwise ix0 Real.log (fun z => z⁻¹)`; spelling the `elemwise` form here keeps the
    eager witness's `whnf` cheap (it is the constructor's own result head), exactly as `expGraph`
    does. -/
def logGraph : Graph Γ2 [Shape.scalar] :=
  .snoc .nil (TapeNodes.elemwise ix0 Real.log (fun z => z⁻¹))

/-- Pointwise differentiability witness at nonzero inputs — the `At` analog of `expCorrect`,
    assembled from the upstream per-node `elemwiseFderivAt` + `Real.hasDerivAt_log` exactly as
    `TapeNodes.logFderivAt` does, spelled at the `elemwise` form and at basepoint `flattenCtx x`
    (`Graph.evalVec .nil` is the identity cast on the literal `Γ2`). -/
def logCorrectAt (x : TorchLean.TensorPack ℝ Γ2)
    (hx : ∀ i : Fin (Spec.Shape.size Shape.scalar),
      CtxVec.get (Γ := Γ2) (s := Shape.scalar) ix0 (flattenCtx x) i ≠ 0) :
    GraphFDerivCorrectAt logGraph (flattenCtx x) :=
  ⟨PUnit.unit, TapeNodes.elemwiseFderivAt ix0 Real.log (fun z => z⁻¹) (flattenCtx x)
    (fun i => Real.hasDerivAt_log (hx i))⟩

set_option maxHeartbeats 6400000 in
/-- `EagerBuilds` witnesses the runtime `log` tape via the generic `unary` constructor —
    `log = elemwise Real.log (fun z => z⁻¹)`, `fwdSpec = logSpec`, `bwdSpec = invSpec`, forward
    bridge from `tensorToVec_mapSpec_apply` (since `MathFunctions.log = Real.log` on `ℝ`), backward
    bridge from `tensorToVec_invSpec_apply` (`invSpec = mapSpec (1 / ·)` and `1 / z = z⁻¹`).

    Unlike `exp` (where `Tape.exp t 0` is *definitionally* the `Tape.unary` call), the runtime
    `Runtime.Autograd.Tape.log` first guards: it throws unless every input is `> 0`
    (`Engine/Core/ActivationsLoss.lean:187`), so `Tape.log t 0` is **not** defeq to this
    `Tape.unary "log"` call.  The guard only gates *success*, not the node content — on the `.ok`
    path `Tape.log` pushes exactly this node (name `"log"`, forward `logSpec`, backward
    `fun xv d => mulSpec (invSpec xv) d`), so the shared `Tape.unary` form below is the honest
    hypothesis for the probe. -/
theorem eagerBuilds_log (x : TorchLean.TensorPack ℝ Γ2) (t' : PRSim.RTape) (id : Nat)
    (hop : Runtime.Autograd.Tape.unary (α := ℝ) (σ := Shape.scalar) (τ := Shape.scalar)
      (Algebra.Graph.addLeaves (α := ℝ) (t := Runtime.Autograd.Tape.empty) x) "log" 0
      logSpec (fun xv d => mulSpec (invSpec xv) d) = .ok (t', id)) :
    PRSim.EagerBuilds logGraph x t' := by
  show PRSim.EagerBuilds (.snoc .nil (TapeNodes.elemwise ix0 Real.log (fun z => z⁻¹))) x t'
  exact PRSim.EagerBuilds.unary (g := .nil) ix0 "log" Real.log (fun z => z⁻¹) logSpec invSpec
    (fun u i => PRSim.tensorToVec_mapSpec_apply u i) (fun u i => tensorToVec_invSpec_apply u i)
    (PRSim.EagerBuilds.nil x) hop

set_option maxHeartbeats 6400000 in
/-- **The pointwise endpoint on the eager `log` tape** — the generic
    `direct_PR_soundness_eager_at` transfers the fderiv-adjoint endpoint to this domain-restricted
    activation tape, with the nonzero-input hypothesis threaded through the binders; no per-op
    §E/§F reasoning. -/
example (x : TorchLean.TensorPack ℝ Γ2)
    (hx : ∀ i : Fin (Spec.Shape.size Shape.scalar),
      CtxVec.get (Γ := Γ2) (s := Shape.scalar) ix0 (flattenCtx x) i ≠ 0)
    (t' : PRSim.RTape) (id : Nat)
    (hop : Runtime.Autograd.Tape.unary (α := ℝ) (σ := Shape.scalar) (τ := Shape.scalar)
      (Algebra.Graph.addLeaves (α := ℝ) (t := Runtime.Autograd.Tape.empty) x) "log" 0
      logSpec (fun xv d => mulSpec (invSpec xv) d) = .ok (t', id))
    (seed : TorchLean.TensorPack ℝ (Γ2 ++ [Shape.scalar])) :
    ∃ out : Array PRSim.Any,
      Runtime.Autograd.Tape.backwardDenseFrom (t := t')
          (TorchLean.TensorPack.toShapeErasedArray (α := ℝ) seed) = .ok out ∧
      PRSim.ArrCorr ((fderiv ℝ (logGraph.evalVec) (flattenCtx x)).adjoint (flattenCtx seed))
        (out.extract 0 Γ2.length) :=
  PRSim.direct_PR_soundness_eager_at logGraph x (logCorrectAt x hx)
    (eagerBuilds_log x t' id hop) seed

/--
info: 'PropertyKindCalculus.UncertaintyExamples.AutogradDirectSim.eagerBuilds_log' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in #print axioms eagerBuilds_log

/-- The runtime `signSpec` scalar — a `>`/`<` `ite`, stated over *arbitrary* `Decidable`
    instances so it composes definitionally with whatever instances `signSpec`'s elaboration
    picked — agrees with the `SignType.sign` coercion in `TapeNodes.abs`'s derivative slot:
    trichotomy at `0`. -/
theorem sign_ite_eq (v : ℝ) {d1 : Decidable (v > 0)} {d2 : Decidable (v < 0)} :
    (@ite ℝ (v > 0) d1 (1 : ℝ) (@ite ℝ (v < 0) d2 (-1) 0)) = (SignType.sign v : ℝ) := by
  split_ifs with h1 h2
  · simp [sign_pos h1]
  · simp [sign_neg h2]
  · have h0 : v = 0 := le_antisymm (not_lt.mp h1) (not_lt.mp h2)
    simp [h0]

/-- Pointwise bridge for the `abs` backward: vectorizing the runtime `signSpec` applies the
    `SignType.sign` coercion coordinatewise — `tensorToVec_mapSpec_apply` composed with the scalar
    trichotomy fact (the per-op analog of the instance-`rfl` step `exp` gets for free). -/
theorem tensorToVec_signSpec_apply {s : Shape} (u : Tensor ℝ s) (i : Fin (Spec.Shape.size s)) :
    tensorToVec (t := signSpec u) i = (SignType.sign (tensorToVec (t := u) i) : ℝ) :=
  (PRSim.tensorToVec_mapSpec_apply u i).trans (sign_ite_eq (tensorToVec (t := u) i))

/-! ### The pointwise (`At`) unary crank: `abs` through the same generic machine

`abs` joins the elementwise family through the *same* `EagerBuilds.unary` constructor, but on the
`div` route: the provenance identification is unconditional, while `|·|` is a genuine Fréchet
derivative only away from `0` — so the correctness witness is the *pointwise*
`GraphFDerivCorrectAt` (upstream `TapeNodes.absFderivAt` under the input-nonzero hypothesis at
the concrete input) and the endpoint transfers through `direct_PR_soundness_eager_at`. The
forward bridge is the same `tensorToVec_mapSpec_apply` (`absSpec = mapSpec MathFunctions.abs` and
`MathFunctions.abs = |·|` on `ℝ`); the backward bridge is the one genuine per-op fact
`tensorToVec_signSpec_apply`, because the runtime `signSpec` (a `>`/`<` `ite`) and the P-side
`SignType.sign` coercion differ syntactically — they agree by trichotomy at `0`. -/

/-- The one-node absolute-value graph `|x₀|`.  `TapeNodes.abs ix0` unfolds to exactly
    `TapeNodes.elemwise ix0 (fun v => |v|) (fun v => (SignType.sign v : ℝ))`; spelling the
    `elemwise` form here keeps the eager witness's `whnf` cheap (it is the constructor's own
    result head). -/
def absGraph : Graph Γ2 [Shape.scalar] :=
  .snoc .nil (TapeNodes.elemwise ix0 (fun v : ℝ => |v|) (fun v => (SignType.sign v : ℝ)))

/-- Pointwise differentiability witness at the input `x`, under the input-nonzero hypothesis
    (the standard mathematical domain of `d|v| = sign v`), assembled from the upstream per-node
    `absFderivAt`. -/
def absCorrectAt (x : TorchLean.TensorPack ℝ Γ2)
    (hx : ∀ i : Fin (Spec.Shape.size Shape.scalar),
      CtxVec.get (Γ := Γ2) (s := Shape.scalar) ix0
        (Graph.evalVec (Γ := Γ2) (ss := []) .nil (flattenCtx x)) i ≠ 0) :
    GraphFDerivCorrectAt absGraph (flattenCtx x) :=
  ⟨PUnit.unit, TapeNodes.absFderivAt ix0 _ hx⟩

set_option maxHeartbeats 6400000 in
/-- `EagerBuilds` witnesses the runtime `abs` tape via the same generic `unary` constructor —
    `abs = elemwise (fun v => |v|) (fun v => (SignType.sign v : ℝ))`, `fwdSpec = absSpec`
    (bridged by `tensorToVec_mapSpec_apply`, since `MathFunctions.abs = |·|` on `ℝ`),
    `bwdSpec = signSpec` (bridged by the trichotomy fact `tensorToVec_signSpec_apply`).

    The runtime op is written here in the shared `Tape.unary "abs" … absSpec …` shape it reduces
    to; `Runtime.Autograd.Tape.abs t 0` is *definitionally* this call (its `let`-bound backward
    zeta-reduces to `fun xv d => mulSpec (signSpec xv) d`), so this is the genuine `abs` op,
    presented in the form that makes the one-parent node shape manifest. -/
theorem eagerBuilds_abs (x : TorchLean.TensorPack ℝ Γ2) (t' : PRSim.RTape) (id : Nat)
    (hop : Runtime.Autograd.Tape.unary (α := ℝ) (σ := Shape.scalar) (τ := Shape.scalar)
      (Algebra.Graph.addLeaves (α := ℝ) (t := Runtime.Autograd.Tape.empty) x) "abs" 0
      absSpec (fun xv d => mulSpec (signSpec xv) d) = .ok (t', id)) :
    PRSim.EagerBuilds absGraph x t' := by
  show PRSim.EagerBuilds
    (.snoc .nil (TapeNodes.elemwise ix0 (fun v : ℝ => |v|) (fun v => (SignType.sign v : ℝ))))
    x t'
  exact PRSim.EagerBuilds.unary (g := .nil) ix0 "abs" (fun v : ℝ => |v|)
    (fun v => (SignType.sign v : ℝ)) absSpec signSpec
    (fun u i => PRSim.tensorToVec_mapSpec_apply u i) (fun u i => tensorToVec_signSpec_apply u i)
    (PRSim.EagerBuilds.nil x) hop

set_option maxHeartbeats 6400000 in
/-- **The endpoint on the eager `abs` tape**: under the input-nonzero hypothesis at the concrete
    input, the dense reverse pass on the runtime-constructed tape succeeds and its input-prefix
    realises `(fderiv ℝ eval x)† seed` — via the *pointwise* `direct_PR_soundness_eager_at`. -/
example (x : TorchLean.TensorPack ℝ Γ2)
    (hx : ∀ i : Fin (Spec.Shape.size Shape.scalar),
      CtxVec.get (Γ := Γ2) (s := Shape.scalar) ix0
        (Graph.evalVec (Γ := Γ2) (ss := []) .nil (flattenCtx x)) i ≠ 0)
    (t' : PRSim.RTape) (id : Nat)
    (hop : Runtime.Autograd.Tape.unary (α := ℝ) (σ := Shape.scalar) (τ := Shape.scalar)
      (Algebra.Graph.addLeaves (α := ℝ) (t := Runtime.Autograd.Tape.empty) x) "abs" 0
      absSpec (fun xv d => mulSpec (signSpec xv) d) = .ok (t', id))
    (seed : TorchLean.TensorPack ℝ (Γ2 ++ [Shape.scalar])) :
    ∃ out : Array PRSim.Any,
      Runtime.Autograd.Tape.backwardDenseFrom (t := t')
          (TorchLean.TensorPack.toShapeErasedArray (α := ℝ) seed) = .ok out ∧
      PRSim.ArrCorr ((fderiv ℝ (absGraph.evalVec) (flattenCtx x)).adjoint (flattenCtx seed))
        (out.extract 0 Γ2.length) :=
  PRSim.direct_PR_soundness_eager_at absGraph x (absCorrectAt x hx)
    (eagerBuilds_abs x t' id hop) seed

/--
info: 'PropertyKindCalculus.UncertaintyExamples.AutogradDirectSim.eagerBuilds_abs' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in #print axioms eagerBuilds_abs

/-! ### Scalar facts for the `sqrt` bridges (root-level; only Mathlib + `MathFunctions` needed)

Two pointwise facts close the gap between the runtime `sqrt` tensor kernels and the P-side
scalar pair `(Real.sqrt, fun v => 1 / (2 * Real.sqrt v))`:

* the runtime *forward* `sqrtSpec` is the **clamped** `MathFunctions.sqrt (max v 0)`
  (`NN/Spec/Core/TensorOps.lean`) — invisible over `ℝ`, where `Real.sqrt` already totalizes
  negatives to `0`, so `√(max v 0) = √v` at every real;
* the runtime *backward* is the `mapSpec`-with-`if` lambda of `Tape.sqrt`
  (`NN/Runtime/Autograd/Engine/Core/Elementwise.lean`), which agrees with the totalized
  `1 / (2 * Real.sqrt v)` at *every* real: on `v > 0` directly (`((2 : Nat) : ℝ) = 2`), and on
  `v ≤ 0` both sides are `0` (`√v = 0` there, and `1 / 0 = 0` in `ℝ`). -/

/-- Clamp collapse over `ℝ`: `MathFunctions.sqrt (max v 0) = Real.sqrt v` — `Real.sqrt`
    totalizes negatives to `0`, so the spec kernel's clamp is invisible. -/
theorem sqrt_clamp_scalar_eq (v : ℝ) :
    MathFunctions.sqrt (Max.max v (0 : ℝ)) = Real.sqrt v := by
  show Real.sqrt (max v 0) = Real.sqrt v
  rcases le_total 0 v with hv | hv
  · rw [max_eq_left hv]
  · rw [max_eq_right hv, Real.sqrt_zero, Real.sqrt_eq_zero'.mpr hv]

/-- The runtime `sqrt` backward's totalized scalar (the `if v > 0` branch of `Tape.sqrt`'s
    `mapSpec`) is the totalized `1 / (2 * Real.sqrt v)` at *every* real: `v > 0` directly, and
    `v ≤ 0` gives `Real.sqrt v = 0`, so `1 / (2 * 0) = 1 / 0 = 0` matches the else-branch. -/
theorem sqrt_bwd_scalar_eq (v : ℝ) :
    (if v > 0 then (1 : ℝ) / (((2 : Nat) : ℝ) * MathFunctions.sqrt v) else (0 : ℝ))
      = 1 / (2 * Real.sqrt v) := by
  by_cases hv : v > 0
  · rw [if_pos hv]
    show (1 : ℝ) / (((2 : Nat) : ℝ) * Real.sqrt v) = 1 / (2 * Real.sqrt v)
    norm_num
  · rw [if_neg hv, Real.sqrt_eq_zero'.mpr (not_lt.mp hv)]
    norm_num


open Spec Tensor Proofs.Autograd


/-! ## The pointwise unary crank: `sqrt` through the *generic* `EagerBuilds.unary` machine

`sqrt` combines the two frontiers already opened separately: like `exp` it is an
`Elementwise` activation covered by the generic `unary` constructor (no new §E/§F reasoning),
and like `div` it is only *pointwise* differentiable — `Real.sqrt` has no derivative at `0` —
so the graph witness is `GraphFDerivCorrectAt` (upstream per-node `sqrtFderivAt` under a
strict-positivity hypothesis on the node's inputs, weakened to the `≠ 0` the witness wants)
and the endpoint transfers through `direct_PR_soundness_eager_at`.  The eager witness itself
needs no differentiability: `EagerBuilds.unary` covers the runtime op with forward `sqrtSpec`
(the *clamped* `√(max v 0)`, invisible over `ℝ`) and backward the literal `mapSpec`-with-`if`
lambda (the totalized `1 / (2·√v)`), both bridged pointwise by `tensorToVec_mapSpec_apply`
composed with the scalar facts `sqrt_clamp_scalar_eq` / `sqrt_bwd_scalar_eq`. -/

/-- The runtime `sqrt` backward tensor spec — the literal `mapSpec`-with-`if` lambda that
    `Runtime.Autograd.Tape.sqrt` pushes (`Engine/Core/Elementwise.lean`): `1 / (2·√v)` on
    `v > 0`, totalized to `0` elsewhere. -/
def sqrtBwdSpec {s : Shape} : Tensor ℝ s → Tensor ℝ s :=
  mapSpec (fun v =>
    if v > 0 then (1 : ℝ) / (((2 : Nat) : ℝ) * MathFunctions.sqrt v) else (0 : ℝ))

/-- The one-node square-root graph `√x₀`.  `TapeNodes.sqrt ix0` unfolds to exactly
    `TapeNodes.elemwise ix0 Real.sqrt (fun v => 1 / (2 * Real.sqrt v))`; spelling the `elemwise`
    form here keeps the eager witness's `whnf` cheap (it is the constructor's own result head). -/
def sqrtGraph : Graph Γ2 [Shape.scalar] :=
  .snoc .nil (TapeNodes.elemwise ix0 Real.sqrt (fun v => 1 / (2 * Real.sqrt v)))

/-- Pointwise differentiability witness at the input `x`, under strict positivity of the node's
    input coordinates (the natural `sqrt` domain, weakened to the `≠ 0` the upstream per-node
    `sqrtFderivAt` wants). -/
def sqrtCorrectAt (x : TorchLean.TensorPack ℝ Γ2)
    (hx : ∀ i : Fin (Spec.Shape.size Shape.scalar),
      0 < CtxVec.get (Γ := Γ2) (s := Shape.scalar) ix0
        (Graph.evalVec (Γ := Γ2) (ss := []) .nil (flattenCtx x)) i) :
    GraphFDerivCorrectAt sqrtGraph (flattenCtx x) :=
  ⟨PUnit.unit, TapeNodes.sqrtFderivAt ix0 _ (fun i => (hx i).ne')⟩

set_option maxHeartbeats 6400000 in
/-- `EagerBuilds` witnesses the runtime `sqrt` tape via the generic `unary` constructor —
    `sqrt = elemwise Real.sqrt (fun v => 1 / (2 * Real.sqrt v))`, `fwdSpec = sqrtSpec`,
    `bwdSpec = sqrtBwdSpec` (the literal `mapSpec`-with-`if` backward of `Tape.sqrt`), both
    bridges from `tensorToVec_mapSpec_apply` composed with the scalar facts above.

    The runtime op is written here in the shared `Tape.unary "sqrt" … sqrtSpec …` shape it
    reduces to; `Runtime.Autograd.Tape.sqrt t 0` reduces *definitionally* to this call (its
    `let`-bound backward zeta-reduces to the `mulSpec`-composed form), so this is the genuine
    `sqrt` node, presented in the form that makes the one-parent node shape manifest. -/
theorem eagerBuilds_sqrt (x : TorchLean.TensorPack ℝ Γ2) (t' : PRSim.RTape) (id : Nat)
    (hop : Runtime.Autograd.Tape.unary (α := ℝ) (σ := Shape.scalar) (τ := Shape.scalar)
      (Algebra.Graph.addLeaves (α := ℝ) (t := Runtime.Autograd.Tape.empty) x) "sqrt" 0
      sqrtSpec (fun xv d => mulSpec (sqrtBwdSpec xv) d) = .ok (t', id)) :
    PRSim.EagerBuilds sqrtGraph x t' := by
  show PRSim.EagerBuilds
    (.snoc .nil (TapeNodes.elemwise ix0 Real.sqrt (fun v => 1 / (2 * Real.sqrt v)))) x t'
  exact PRSim.EagerBuilds.unary (g := .nil) ix0 "sqrt" Real.sqrt
    (fun v => 1 / (2 * Real.sqrt v)) sqrtSpec sqrtBwdSpec
    (fun u i => (PRSim.tensorToVec_mapSpec_apply u i).trans (sqrt_clamp_scalar_eq (tensorToVec (t := u) i)))
    (fun u i => (PRSim.tensorToVec_mapSpec_apply u i).trans (sqrt_bwd_scalar_eq (tensorToVec (t := u) i)))
    (PRSim.EagerBuilds.nil x) hop

set_option maxHeartbeats 6400000 in
/-- **The endpoint on the eager `sqrt` tape** — under strict positivity of the node's inputs at
    the concrete `x`, the *pointwise* generic `direct_PR_soundness_eager_at` transfers the
    fderiv-adjoint endpoint to this activation tape; the domain hypothesis `hx` is threaded
    through the pointwise witness `sqrtCorrectAt`. -/
example (x : TorchLean.TensorPack ℝ Γ2)
    (hx : ∀ i : Fin (Spec.Shape.size Shape.scalar),
      0 < CtxVec.get (Γ := Γ2) (s := Shape.scalar) ix0
        (Graph.evalVec (Γ := Γ2) (ss := []) .nil (flattenCtx x)) i)
    (t' : PRSim.RTape) (id : Nat)
    (hop : Runtime.Autograd.Tape.unary (α := ℝ) (σ := Shape.scalar) (τ := Shape.scalar)
      (Algebra.Graph.addLeaves (α := ℝ) (t := Runtime.Autograd.Tape.empty) x) "sqrt" 0
      sqrtSpec (fun xv d => mulSpec (sqrtBwdSpec xv) d) = .ok (t', id))
    (seed : TorchLean.TensorPack ℝ (Γ2 ++ [Shape.scalar])) :
    ∃ out : Array PRSim.Any,
      Runtime.Autograd.Tape.backwardDenseFrom (t := t')
          (TorchLean.TensorPack.toShapeErasedArray (α := ℝ) seed) = .ok out ∧
      PRSim.ArrCorr ((fderiv ℝ (sqrtGraph.evalVec) (flattenCtx x)).adjoint (flattenCtx seed))
        (out.extract 0 Γ2.length) :=
  PRSim.direct_PR_soundness_eager_at sqrtGraph x (sqrtCorrectAt x hx)
    (eagerBuilds_sqrt x t' id hop) seed

/--
info: 'PropertyKindCalculus.UncertaintyExamples.AutogradDirectSim.eagerBuilds_sqrt' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in #print axioms eagerBuilds_sqrt

end

end PropertyKindCalculus.UncertaintyExamples.AutogradDirectSim
