/-
# M-T4 — the measurand vocabulary

The fourth item of the pilot's
[Stage-2 metrological TODO slate](../../PLAN.md#the-pilot-quantummechanicsharmonicoscillator),
in its own file because it is new *vocabulary*, not re-authoring: what the analysis
tradition calls an observable — a self-adjoint operator — is what VIM calls a
**measurand**, and the kind layer is where that identification becomes typed.

* A `Measurand k H` is a self-adjoint operator quantity at kind `k`: self-adjointness
  is the mathematical form of "observable", carried as a field so nothing below applies
  to a non-observable operator by accident. (For the oscillator's Hamiltonian,
  self-adjointness is upstream's own open `informal_lemma`, so `hamiltonianMeasurand`
  takes it as a hypothesis — the vocabulary is ready before the analysis is.)
* The **indications** are the values a measurement can return — the spectrum — carrying
  the operator's kind: `hamiltonianIndications` is the kinded set upstream's spectrum
  TODO ("the (point) spectrum … is `Set.range Q.eigenEnergy`") will identify with the
  actual spectrum, and the licensed-fold eigenvalue is already a member.
* The **expectation** `⟪ψ, Âψ⟫` is GUM's best estimate — an energy, for the
  Hamiltonian; under the kinded TISE it lands exactly on the eigenvalue
  (`expectation_eigenstate`, conditional on the two open upstream TODOs it names).
* The **variance** is kind-squared — the quantity lands through the authored
  `energy · energy` edge — and the standard uncertainty σ is one attested root back
  (radicand-first, again). σ is where PKC's R14 uncertainty ladder attaches:
  REQUIREMENTS.md records R14 as *not validated* by the survey because no surveyed
  quantity carries a measured uncertainty — a measurand's σ is the first one that
  could.
-/

import ForPhysLib.QuantumMechanics.HarmonicOscillator.Kinded
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

/-! ## The vocabulary -/

/-- **A measurand (VIM 2.3), typed**: a self-adjoint operator quantity. The kind index
`k` is what the analysis form has nowhere to carry: *which* kind-of-property the
observable observes. Self-adjointness — the mathematical form of "observable" — is a
field, so the vocabulary below cannot be applied to a non-observable by accident. -/
structure Measurand (k : KindOfProperty) (H : Type)
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] where
  /-- The operator, at its kind. -/
  op : Quantity k (H →ₗ.[ℂ] H)
  /-- The observable's defining property. -/
  selfAdjoint : IsSelfAdjoint op.magnitude

namespace Measurand

variable {k k₂ : KindOfProperty} {H : Type}
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- **The expectation `⟪ψ, Âψ⟫` — GUM's best estimate**, at the measurand's kind. The
real part is the honest executable form: for a self-adjoint operator the imaginary
part vanishes, and stating the value in `ℝ` is what lets it be a `Quantity k ℝ` a
report can carry. -/
def expectationQ (M : Measurand k H) (ψ : H) (h : ψ ∈ M.op.magnitude.domain) :
    Quantity k ℝ :=
  .attest "⟪ψ, Âψ⟫ — real for a self-adjoint operator; GUM's best estimate"
    (⟪ψ, M.op.magnitude ⟨ψ, h⟩⟫_ℂ).re

/-- **The variance `⟪Âψ, Âψ⟫ − ⟪ψ, Âψ⟫²` lands at kind squared** — the gate is the
authored `ProductKind k k k₂` edge, so a variance exists only where the directory has
sanctioned the square (for energy: the Stage-1 `energy · energy → energySquared`
edge). -/
def varianceQ (M : Measurand k H) (_hkk : ProductKind k k k₂)
    (ψ : H) (h : ψ ∈ M.op.magnitude.domain) : Quantity k₂ ℝ :=
  .attest "⟪Âψ, Âψ⟫ − ⟪ψ, Âψ⟫² — the second moment about the best estimate"
    (‖M.op.magnitude ⟨ψ, h⟩‖ ^ 2 - ((⟪ψ, M.op.magnitude ⟨ψ, h⟩⟫_ℂ).re) ^ 2)

/-- **The standard uncertainty σ — one attested root back to the measurand's kind**
(radicand-first: the variance is the registered object, the root is the crossing).
This is where PKC's R14 uncertainty ladder attaches to the survey: σ is the first
quantity in the two mechanics directories that *could* carry a measured uncertainty. -/
def sigmaQ (M : Measurand k H) (hkk : ProductKind k k k₂)
    (ψ : H) (h : ψ ∈ M.op.magnitude.domain) : Quantity k ℝ :=
  .attest "the root of the variance — roots are not a kind operation"
    (√(varianceQ M hkk ψ h).magnitude)

/-- The best estimate and its σ are the *same kind* — `E ± σ` is a same-kind sum,
which is exactly why σ must cross back down from the variance's kind. -/
example (E σE : Quantity energyK ℝ) : Quantity energyK ℝ := E + σE

-- Refused: an energy plus an energy-variance — the kinds the root exists to separate.
#check_failure fun (E : Quantity energyK ℝ) (V : Quantity energySquared ℝ) => E + V

/-! ## The Hamiltonian as a measurand -/

/-- The oscillator's Hamiltonian as a measurand. Self-adjointness is upstream's own
open `informal_lemma` (`hamiltonian_essentially_self_adjoint`), so it enters as a
hypothesis: the vocabulary is ready before the analysis discharges it. -/
def hamiltonianMeasurand (Q : PhysHO d) (hsa : IsSelfAdjoint Q.hamiltonian) :
    Measurand energyK Q.HS :=
  { op := hamiltonianOpQ Q, selfAdjoint := hsa }

/-- **The indications, carrying the operator's kind**: the values an energy
measurement on the oscillator can return. Upstream's spectrum TODO ("the (point)
spectrum of the self-adjoint Hamiltonian is `Set.range Q.eigenEnergy`") is the
analysis statement that this set *is* the spectrum; the kinded set is statable now. -/
def hamiltonianIndications (Q : PhysHO d) : Set (Quantity energyK ℝ) :=
  { E | ∃ n : Fin d → ℕ, E.magnitude = Q.eigenEnergy n }

/-- The licensed-fold eigenvalue is an indication. -/
theorem eigenEnergyQ_mem_indications (Q : PhysHO d) (n : Fin d → ℕ) :
    Kinded.eigenEnergyQ Q n ∈ hamiltonianIndications Q :=
  ⟨n, Kinded.eigenEnergyQ_magnitude Q n⟩

/-- **The vocabulary composes**: under the kinded TISE (M-T3) and self-adjointness —
the two named open upstream TODOs — the best estimate in an eigenstate is exactly its
eigenvalue, with the norm supplied by the *discharged* orthonormality. Every kinded
object in the statement has already been authored: the measurand (F1), the eigenvalue
(the licensed fold), the crossing (`energySMul`), the norm (`Orthonormality`). -/
theorem expectation_eigenstate (Q : PhysHO d) (n : Fin d → ℕ)
    (hsa : IsSelfAdjoint Q.hamiltonian) (ht : Kinded.SatisfiesTISE Q n) :
    ∃ h : (Q.eigenstate n : Q.HS) ∈ (hamiltonianMeasurand Q hsa).op.magnitude.domain,
      expectationQ (hamiltonianMeasurand Q hsa) (Q.eigenstate n : Q.HS) h
        = Kinded.eigenEnergyQ Q n := by
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

end Measurand

end

end ForPhysLib.QuantumMechanics.HarmonicOscillator
