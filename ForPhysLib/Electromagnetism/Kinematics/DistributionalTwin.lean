/-
# The Distributional twin — one physics, two carriers, one vocabulary

Upstream maintains the potential → fields chain twice. `Kinematics/` spells it over the
smooth `ElectromagneticPotential`; `Distributional/` re-spells it over
`SpaceTime d →d[ℝ] Lorentz.Vector d` — and the defining equations are the *same
sentences*: the twin's `electricField` is `-distSpaceGrad (φ) - distTimeDeriv (𝐀)`,
the chain's is `-∇φ - ∂ₜ𝐀` (`electricField_eq`); both carry the `/c` convention in the
same slot; both derive `F` from `∂A`. This file pins the duplication finding:

* **The kind cost of the twin is zero.** Every reading below lands at a kind the
  chain's Stage 0/1 already registered — the potential at 6-32, the electric field at
  6-10, the tensor at the chain's one `fieldStrength` mint. No new kind, no new
  pairing, no new edge; the directory's mint ratchet enforces that this file *cannot*
  quietly add vocabulary. The duplication is carrier-level only.

* **The twin restates the chain's law, verbatim** — `distElectricField_eq` below pins
  the twin's defining equation by `rfl` in the same shape as the chain's
  `electricField_eq`. Two authored spellings of one sentence is the finding.

* **The deduplication theorem is not yet statable.** There is no smooth →
  distributional embedding for `A^μ` (`Space.distOfFunction` covers `Space d`, not
  `SpaceTime d`; `Distributional/Basic.lean`'s own TODO asks even for the E/B
  constructors), so "the twin agrees with the chain along the embedding" cannot be
  written today — the `#check_failure` below is that absence as a build artifact. The
  constructor is the missing piece; once it exists, the agreement theorems are the
  natural deduplication contract.
-/

module

public import ForPhysLib.Electromagnetism.Kinematics.Kinded
meta import ForPhysLib.Electromagnetism.Kinematics.Kinded
public import Physlib.Electromagnetism.Distributional.ElectricField
meta import Physlib.Electromagnetism.Distributional.ElectricField
public import Physlib.Electromagnetism.Distributional.FieldStrength
meta import Physlib.Electromagnetism.Distributional.FieldStrength

@[expose] public section

open PropertyKindCalculus
open Electromagnetism
open ForPhysLib.Electromagnetism.Kinematics
open ForPhysLib.Electromagnetism.Kinematics.Kinds

namespace ForPhysLib.Electromagnetism.Kinematics.DistributionalTwin

variable {d : ℕ}

noncomputable section

/-! ## The twin's readings, at the chain's kinds -/

/-- The distributional potential, read at the chain's 6-32 — the *same* kind the
smooth `A^μ` carries; only the carrier differs. -/
@[kindIngest]
def distPotentialQ (A : DistElectromagneticPotential d) :
    Quantity vectorPotentialK (DistElectromagneticPotential d) :=
  .attest "the distributional A^μ — the twin carrier at the chain's kind" A

/-- The twin's electric field at the chain's 6-10: the same `-∇φ - ∂ₜ𝐀`, with the
distributional `∇`/`∂ₜ` unseen by any table — one attested crossing, exactly as the
chain's. -/
@[kindCrossing]
def distElectricFieldQ (cq : Quantity speedOfLightK SpeedOfLight)
    (Aq : Quantity vectorPotentialK (DistElectromagneticPotential d)) :
    Quantity electricFieldK ((Time × Space d) →d[ℝ] EuclideanSpace ℝ (Fin d)) :=
  .attest "the twin's -∇φ - ∂ₜ𝐀 — distributional derivatives ride the same crossing"
    (DistElectromagneticPotential.electricField cq.magnitude Aq.magnitude)

/-- The twin's field-strength tensor at the chain's one mint — the frame-covariant
extent kind, carrier-generic as minted. -/
@[kindCrossing]
def distFieldStrengthQ (Aq : Quantity vectorPotentialK (DistElectromagneticPotential d)) :
    Quantity Kinds.fieldStrength
      ((SpaceTime d) →d[ℝ] TensorProduct ℝ (Lorentz.Vector d) (Lorentz.Vector d)) :=
  .attest "the twin's F = dA — the antisymmetrized distributional derivative"
    (DistElectromagneticPotential.fieldStrength Aq.magnitude)

/-! ## The restated law, pinned -/

/-- **The twin's defining equation is the chain's, re-authored**: the distributional
`E` is definitionally `-distSpaceGrad φ - distTimeDeriv 𝐀` — the same sentence
`electricField_eq` proves for the smooth chain. One law, two spellings: the
duplication finding as an `rfl`. -/
theorem distElectricField_eq (c : SpeedOfLight) (A : DistElectromagneticPotential d) :
    DistElectromagneticPotential.electricField c A
      = - Space.distSpaceGrad (A.scalarPotential c)
        - Space.distTimeDeriv (A.vectorPotential c) := rfl

/-- The kinded twin erases to upstream's own reading — the Stage-2 invariant holds
for the twin at zero extra cost. -/
theorem distElectricFieldQ_magnitude (cS : SpeedOfLight)
    (A : DistElectromagneticPotential d) :
    (distElectricFieldQ (speedQ cS) (distPotentialQ A)).magnitude
      = DistElectromagneticPotential.electricField cS A := rfl

/-! ## The missing bridge, as a build artifact -/

-- There is no smooth → distributional embedding for the potential: the deduplication
-- theorem ("the twin agrees with the chain along the embedding") has no statement to
-- be given yet. When upstream adds the constructor, this refusal becomes the contract.
#check_failure fun (A : ElectromagneticPotential 3) => (A : DistElectromagneticPotential 3)

end

end ForPhysLib.Electromagnetism.Kinematics.DistributionalTwin

