/-
# The observable — the operator realization of a measurand

`Measurand` (the Mathlib-free core) says what a measurand *is*: estimate at its kind,
variance at the squared kind through a carried edge, an indication predicate. This
module supplies the canonical *operator* realization, on an inner-product state space:
a measurand whose model is a **self-adjoint operator quantity**.

The shape is not quantum-mechanical — it is spectral theory's, and quantum observables
are one instance of it. Over `ℝ` the same structure carries a covariance operator, or a
random variable read as a multiplication operator on an `L²` space; in every case
self-adjointness is what makes the operator *observable* — real expectations, a real
spectrum to serve as the indication set — so it is a field, and the identification with
a measurand below cannot be applied to a non-observable by accident.

`Observable.toMeasurand` is the identification, as a construction:

  * the **states** are the operator's domain — the honest state space of an unbounded
    operator (`Mathlib`'s `LinearPMap`);
  * the **estimate** in a state ψ is `re ⟪ψ, Âψ⟫` — for a *unit* ψ this is the
    expectation (the Rayleigh quotient's numerator); the real part is exact, not a
    projection, because the operator is self-adjoint;
  * the **variance** is the second moment about it, `‖Âψ‖² − (re ⟪ψ, Âψ⟫)²`, landing
    at the squared kind through the authored edge the measurand carries;
  * the **indications** are the model's to name — for an operator, its spectrum; the
    predicate is an argument because Mathlib does not yet provide a spectrum for
    `LinearPMap`, and a model usually knows its indication set more concretely (an
    eigenvalue family) than the abstract spectrum names it.

σ, and the `estimate ± σ` bounds, are *inherited* from `Measurand` — nothing here
restates them.
-/

module

public import PropertyKindCalculus.Measurand
public import Mathlib.Analysis.InnerProductSpace.LinearPMap

@[expose] public section Blanket

namespace PropertyKindCalculus

/-- **An observable, typed**: a self-adjoint operator quantity on an inner-product
state space over `𝕜` (`ℝ` or `ℂ`). The kind index `k` is what the operator form has
nowhere to carry — *which* kind-of-property the observable observes. -/
structure Observable (𝕜 : Type) [RCLike 𝕜] (k : KindOfProperty) (H : Type)
    [NormedAddCommGroup H] [InnerProductSpace 𝕜 H] [CompleteSpace H] where
  /-- The operator, at its kind. -/
  op : Quantity k (H →ₗ.[𝕜] H)
  /-- The observable's defining property. -/
  selfAdjoint : IsSelfAdjoint op.magnitude

namespace Observable

variable {𝕜 : Type} [RCLike 𝕜] {k k₂ : KindOfProperty} {H : Type}
  [NormedAddCommGroup H] [InnerProductSpace 𝕜 H] [CompleteSpace H]

/-- **Observable = measurand** — the identification, as a construction: states the
operator's domain, estimate `re ⟪ψ, Âψ⟫`, variance the second moment about it at the
squared kind, indications the model's (`ind` — for an operator, its spectrum). -/
def toMeasurand (A : Observable 𝕜 k H) (hkk : ProductKind k k k₂)
    (ind : Quantity k ℝ → Prop) : Measurand k k₂ A.op.magnitude.domain ℝ where
  square := hkk
  estimate ψ :=
    .attest "re ⟪ψ, Âψ⟫ — exact for a self-adjoint operator; the best estimate"
      (RCLike.re (inner 𝕜 (ψ : H) (A.op.magnitude ψ)))
  variance ψ :=
    .attest "‖Âψ‖² − (re ⟪ψ, Âψ⟫)² — the second moment about the best estimate"
      (‖A.op.magnitude ψ‖ ^ 2 - (RCLike.re (inner 𝕜 (ψ : H) (A.op.magnitude ψ))) ^ 2)
  IsIndication := ind

@[simp] theorem toMeasurand_estimate (A : Observable 𝕜 k H) (hkk : ProductKind k k k₂)
    (ind : Quantity k ℝ → Prop) (ψ : A.op.magnitude.domain) :
    ((A.toMeasurand hkk ind).estimate ψ).magnitude
      = RCLike.re (inner 𝕜 (ψ : H) (A.op.magnitude ψ)) := rfl

@[simp] theorem toMeasurand_variance (A : Observable 𝕜 k H) (hkk : ProductKind k k k₂)
    (ind : Quantity k ℝ → Prop) (ψ : A.op.magnitude.domain) :
    ((A.toMeasurand hkk ind).variance ψ).magnitude
      = ‖A.op.magnitude ψ‖ ^ 2
          - (RCLike.re (inner 𝕜 (ψ : H) (A.op.magnitude ψ))) ^ 2 := rfl

@[simp] theorem toMeasurand_isIndication (A : Observable 𝕜 k H)
    (hkk : ProductKind k k k₂) (ind : Quantity k ℝ → Prop) (E : Quantity k ℝ) :
    (A.toMeasurand hkk ind).IsIndication E = ind E := rfl

end Observable

end PropertyKindCalculus

end Blanket
