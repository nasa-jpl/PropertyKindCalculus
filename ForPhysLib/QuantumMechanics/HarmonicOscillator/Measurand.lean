/-
# M-T4 — the measurand vocabulary, realized for the oscillator

The fourth item of the pilot's
[Stage-2 metrological TODO slate](../../PLAN.md#the-pilot-quantummechanicsharmonicoscillator).
The vocabulary is **PKC's**, at both levels, and this file only instantiates it:
`PropertyKindCalculus.Measurand` (Mathlib-free core) is the VIM measurand — estimate at
kind `k`, variance at the squared kind through the authored `ProductKind k k k₂` edge,
the indication predicate, σ/`upper`/`lower` derived once for every model — and
`PropertyKindCalculus.Observable` (the Mathlib-facing layer) is its operator
realization: a self-adjoint operator quantity over any `RCLike` scalar field, with
`Observable.toMeasurand` the observable = measurand identification. Nothing
quantum-specific remains in either; what this file supplies is the oscillator:

* `hamiltonianObservable` — the Hamiltonian at `𝕜 = ℂ` on `Q.HS`, at the energy kind.
  Self-adjointness is upstream's own open `informal_lemma`
  (`hamiltonian_essentially_self_adjoint`), so it enters as a hypothesis — the
  vocabulary is ready before the analysis is.
* `hamiltonianMeasurand` — the identification, with the variance on the Stage-1
  `energy · energy → energySquared` edge and the eigenvalue set as the **indications**:
  upstream's spectrum TODO ("the (point) spectrum … is `Set.range Q.eigenEnergy`") is
  the analysis statement that this predicate *is* the spectrum, and the licensed-fold
  eigenvalue already satisfies it.
* Under the kinded TISE the estimate lands exactly on the eigenvalue
  (`expectation_eigenstate`, conditional on the two open upstream TODOs it names), with
  the norm supplied by the *discharged* orthonormality.
* σ is the core's attested root — the R14 attachment point — inherited, not restated:
  at the `ℝ` carrier `MathCarrier.sqrt` *is* `Real.sqrt`, definitionally
  (`sigma_hamiltonian`).
-/

import ForPhysLib.QuantumMechanics.HarmonicOscillator.Kinded
import PropertyKindCalculus.Observable
import PropertyKindCalculus.Function

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

/-- The best estimate and its σ are the *same kind* — `E ± σ` is a same-kind sum
(PKC's `Measurand.upper`/`lower` are built from exactly this), which is why σ must
cross back down from the variance's kind. -/
example (E σE : Quantity energyK ℝ) : Quantity energyK ℝ := E + σE

-- Refused: an energy plus an energy-variance — the kinds the root exists to separate.
#check_failure fun (E : Quantity energyK ℝ) (V : Quantity energySquared ℝ) => E + V

/-! ## The Hamiltonian as an observable, and as a measurand -/

/-- The oscillator's Hamiltonian as an observable (PKC's operator realization, at
`𝕜 = ℂ`). Self-adjointness is upstream's own open `informal_lemma`
(`hamiltonian_essentially_self_adjoint`), so it enters as a hypothesis: the vocabulary
is ready before the analysis discharges it. -/
def hamiltonianObservable (Q : PhysHO d) (hsa : IsSelfAdjoint Q.hamiltonian) :
    Observable ℂ energyK Q.HS :=
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
Every kinded object in the statement has already been authored: the measurand and its
operator realization (PKC's, at F1's operator), the eigenvalue (the licensed fold),
the crossing (`energySMul`), the norm (`Orthonormality`). -/
theorem expectation_eigenstate (Q : PhysHO d) (n : Fin d → ℕ)
    (hsa : IsSelfAdjoint Q.hamiltonian) (ht : Kinded.SatisfiesTISE Q n) :
    ∃ hmem : (Q.eigenstate n : Q.HS) ∈ (hamiltonianOpQ Q).magnitude.domain,
      (hamiltonianMeasurand Q hsa).estimate ⟨_, hmem⟩ = Kinded.eigenEnergyQ Q n := by
  obtain ⟨hmem, heq⟩ := ht
  refine ⟨hmem, ?_⟩
  apply Quantity.ext
  show RCLike.re
      (inner ℂ ((Q.eigenstate n : Q.HS)) ((hamiltonianOpQ Q).magnitude ⟨_, hmem⟩))
      = (Kinded.eigenEnergyQ Q n).magnitude
  rw [heq]
  show RCLike.re (inner ℂ ((Q.eigenstate n : Q.HS))
      (((Kinded.eigenEnergyQ Q n).magnitude : ℂ) • (Q.eigenstate n : Q.HS))) = _
  rw [inner_smul_right]
  have hnorm : ⟪(Q.eigenstate n : Q.HS), (Q.eigenstate n : Q.HS)⟫_ℂ = 1 := by
    have h1 := eigenstates_orthonormal' Q n n
    simpa [KroneckerDelta.eq_one_of_same n] using h1
  rw [hnorm, mul_one]
  simp

/-- **σ is inherited, not restated**: the standard uncertainty of the Hamiltonian
measurand is the core's generic attested root, landing back at the energy kind — at
the `ℝ` carrier, `MathCarrier.sqrt` *is* `Real.sqrt`, definitionally. -/
theorem sigma_hamiltonian (Q : PhysHO d) (hsa : IsSelfAdjoint Q.hamiltonian)
    (ψ : (hamiltonianOpQ Q).magnitude.domain) :
    ((hamiltonianMeasurand Q hsa).sigma ψ).magnitude
      = √(((hamiltonianMeasurand Q hsa).variance ψ).magnitude) := rfl

end

end ForPhysLib.QuantumMechanics.HarmonicOscillator
