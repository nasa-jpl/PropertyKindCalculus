/-
# M-T4 — the measurand vocabulary, realized for the oscillator

The fourth item of the pilot's
[Stage-2 metrological TODO slate](../../PLAN.md#the-pilot-quantummechanicsharmonicoscillator).
The vocabulary itself is **PKC's**, not this file's: `PropertyKindCalculus.Measurand`
is the VIM measurand in the Mathlib-free core — estimate at kind `k`, variance at the
squared kind through the authored `ProductKind k k k₂` edge, the indication predicate,
and σ/`upper`/`lower` derived once for every model. What this file supplies is the
*quantum realization*:

* An `Observable k H` is a self-adjoint operator quantity — self-adjointness is the
  mathematical form of "observable", and the identification observable = measurand is
  `Observable.toMeasurand`: expectation `⟪ψ, Âψ⟫` as the estimate, the second moment
  about it as the variance, the states the domain of the (unbounded) operator. (For the
  oscillator's Hamiltonian, self-adjointness is upstream's own open `informal_lemma`,
  so `hamiltonianObservable` takes it as a hypothesis — the vocabulary is ready before
  the analysis is.)
* The **indications** of the Hamiltonian measurand are the eigenvalue set, carrying the
  energy kind: upstream's spectrum TODO ("the (point) spectrum … is
  `Set.range Q.eigenEnergy`") is the analysis statement that this predicate *is* the
  spectrum, and the licensed-fold eigenvalue already satisfies it.
* Under the kinded TISE the estimate lands exactly on the eigenvalue
  (`expectation_eigenstate`, conditional on the two open upstream TODOs it names), with
  the norm supplied by the *discharged* orthonormality.
* The variance rides the Stage-1 `energy · energy → energySquared` edge, and σ is PKC's
  generic attested root — the R14 attachment point, inherited rather than restated.
-/

import ForPhysLib.QuantumMechanics.HarmonicOscillator.Kinded
import PropertyKindCalculus.Measurand
import PropertyKindCalculus.Function
import Mathlib.Analysis.InnerProductSpace.LinearPMap

open PropertyKindCalculus MeasureTheory Complex Real
open QuantumMechanics HarmonicOscillator SpaceDHilbertSpace SchwartzSubmodule
open InnerProductSpace
open ForPhysLib.QuantumMechanics.HarmonicOscillator
open ForPhysLib.QuantumMechanics.HarmonicOscillator.Kinds
open ForPhysLib.QuantumMechanics.HarmonicOscillator.Orthonormality

namespace ForPhysLib.QuantumMechanics.HarmonicOscillator

local notation "PhysHO" => _root_.QuantumMechanics.HarmonicOscillator

variable {d : ℕ}

noncomputable section

/-! ## The quantum realization of the measurand -/

/-- **An observable, typed**: a self-adjoint operator quantity. The kind index `k` is
what the analysis form has nowhere to carry — *which* kind-of-property the observable
observes; self-adjointness is a field, so the identification with a measurand below
cannot be applied to a non-observable by accident. -/
structure Observable (k : KindOfProperty) (H : Type)
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] where
  /-- The operator, at its kind. -/
  op : Quantity k (H →ₗ.[ℂ] H)
  /-- The observable's defining property. -/
  selfAdjoint : IsSelfAdjoint op.magnitude

namespace Observable

variable {k k₂ : KindOfProperty} {H : Type}
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- **Observable = measurand** — the identification, as a construction. The states are
the operator's domain (the honest state space of an unbounded operator); the estimate
is GUM's best estimate `⟪ψ, Âψ⟫` (real part — for a self-adjoint operator the
imaginary part vanishes, and `ℝ` is what a `Quantity k ℝ` a report can carry needs);
the variance is the second moment about it, landing through the authored square edge;
the indications are the model's to name (for an operator, its spectrum). -/
def toMeasurand (A : Observable k H) (hkk : ProductKind k k k₂)
    (ind : Quantity k ℝ → Prop) : Measurand k k₂ A.op.magnitude.domain ℝ where
  square := hkk
  estimate ψ :=
    .attest "⟪ψ, Âψ⟫ — real for a self-adjoint operator; GUM's best estimate"
      (⟪(ψ : H), A.op.magnitude ψ⟫_ℂ).re
  variance ψ :=
    .attest "⟪Âψ, Âψ⟫ − ⟪ψ, Âψ⟫² — the second moment about the best estimate"
      (‖A.op.magnitude ψ‖ ^ 2 - ((⟪(ψ : H), A.op.magnitude ψ⟫_ℂ).re) ^ 2)
  IsIndication := ind

end Observable

/-- The best estimate and its σ are the *same kind* — `E ± σ` is a same-kind sum
(PKC's `Measurand.upper`/`lower` are built from exactly this), which is why σ must
cross back down from the variance's kind. -/
example (E σE : Quantity energyK ℝ) : Quantity energyK ℝ := E + σE

-- Refused: an energy plus an energy-variance — the kinds the root exists to separate.
#check_failure fun (E : Quantity energyK ℝ) (V : Quantity energySquared ℝ) => E + V

/-! ## The Hamiltonian as a measurand -/

/-- The oscillator's Hamiltonian as an observable. Self-adjointness is upstream's own
open `informal_lemma` (`hamiltonian_essentially_self_adjoint`), so it enters as a
hypothesis: the vocabulary is ready before the analysis discharges it. -/
def hamiltonianObservable (Q : PhysHO d) (hsa : IsSelfAdjoint Q.hamiltonian) :
    Observable energyK Q.HS :=
  { op := hamiltonianOpQ Q, selfAdjoint := hsa }

/-- **The Hamiltonian measurand**: the observable identified as a measurand, with the
variance on the Stage-1 `energy · energy` edge and the eigenvalue set as the
indications — the kinded set upstream's spectrum TODO ("the (point) spectrum of the
self-adjoint Hamiltonian is `Set.range Q.eigenEnergy`") will identify with the actual
spectrum. -/
def hamiltonianMeasurand (Q : PhysHO d) (hsa : IsSelfAdjoint Q.hamiltonian) :
    Measurand energyK energySquared (hamiltonianOpQ Q).magnitude.domain ℝ :=
  (hamiltonianObservable Q hsa).toMeasurand Metrology.mechanicalEnergy_mul_self
    (fun E => ∃ n : Fin d → ℕ, E.magnitude = Q.eigenEnergy n)

/-- The licensed-fold eigenvalue is an indication. -/
theorem eigenEnergyQ_isIndication (Q : PhysHO d) (n : Fin d → ℕ)
    (hsa : IsSelfAdjoint Q.hamiltonian) :
    (hamiltonianMeasurand Q hsa).IsIndication (Kinded.eigenEnergyQ Q n) :=
  ⟨n, Kinded.eigenEnergyQ_magnitude Q n⟩

/-- **The vocabulary composes**: under the kinded TISE (M-T3) and self-adjointness —
the two named open upstream TODOs — the measurand's best estimate in an eigenstate is
exactly its eigenvalue, with the norm supplied by the *discharged* orthonormality.
Every kinded object in the statement has already been authored: the measurand (PKC's,
realized at F1's operator), the eigenvalue (the licensed fold), the crossing
(`energySMul`), the norm (`Orthonormality`). -/
theorem expectation_eigenstate (Q : PhysHO d) (n : Fin d → ℕ)
    (hsa : IsSelfAdjoint Q.hamiltonian) (ht : Kinded.SatisfiesTISE Q n) :
    ∃ hmem : (Q.eigenstate n : Q.HS) ∈ (hamiltonianOpQ Q).magnitude.domain,
      (hamiltonianMeasurand Q hsa).estimate ⟨_, hmem⟩ = Kinded.eigenEnergyQ Q n := by
  obtain ⟨hmem, heq⟩ := ht
  refine ⟨hmem, ?_⟩
  apply Quantity.ext
  show (⟪(Q.eigenstate n : Q.HS), (hamiltonianOpQ Q).magnitude ⟨_, hmem⟩⟫_ℂ).re
      = (Kinded.eigenEnergyQ Q n).magnitude
  rw [heq]
  show (⟪(Q.eigenstate n : Q.HS),
      ((Kinded.eigenEnergyQ Q n).magnitude : ℂ) • (Q.eigenstate n : Q.HS)⟫_ℂ).re = _
  rw [inner_smul_right]
  have hnorm : ⟪(Q.eigenstate n : Q.HS), (Q.eigenstate n : Q.HS)⟫_ℂ = 1 := by
    have h1 := eigenstates_orthonormal' Q n n
    simpa [KroneckerDelta.eq_one_of_same n] using h1
  rw [hnorm, mul_one, Complex.ofReal_re]

/-- **σ is inherited, not restated**: the standard uncertainty of the Hamiltonian
measurand is PKC's generic attested root, landing back at the energy kind — at the `ℝ`
carrier, `MathCarrier.sqrt` *is* `Real.sqrt`, definitionally. -/
theorem sigma_hamiltonian (Q : PhysHO d) (hsa : IsSelfAdjoint Q.hamiltonian)
    (ψ : (hamiltonianOpQ Q).magnitude.domain) :
    ((hamiltonianMeasurand Q hsa).sigma ψ).magnitude
      = √(((hamiltonianMeasurand Q hsa).variance ψ).magnitude) := rfl

end

end ForPhysLib.QuantumMechanics.HarmonicOscillator
