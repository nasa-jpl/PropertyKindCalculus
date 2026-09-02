/-
# Stage 3 — the operator table of `Physlib/ClassicalMechanics` (two subtrees)

The fourth rung of [the adoption ladder](../PLAN.md#stage-3-the-operator-table) for
the campaign's third directory: the kind algebra registered once as
`KindMul`/`KindDiv` instances, so that with `open scoped
PropertyKindCalculus.OperatorTable` the ordinary `*` and `/` elaborate through the
table — and an unregistered pair **fails to elaborate**.

**Six entries predate this file** — Feasibility registered the edges its probes rode
(`k/m → ω²`, `m·v → p`, `m·a → F`, `ω·t → phase`, `v/ω → displacement`,
`I·ω → L`). This file registers the seven remaining edges with scalar call sites,
each demonstrated at a source equation; exactly **one** of Stage 1's fourteen laws
stays law-only — conservation's `∂ₜE`, whose division rides `fderiv` where no table
sees it (directory 2's majority case, here the exception: classical point mechanics
is scalar-multiplicative almost everywhere).

**No interval scale anywhere** — unlike directory 2, every kind here is ratio-scale,
so nothing in this directory is adjudicated by scale: the whole discrimination burden
falls on kind identity, which is exactly the six-joules/two-ω's finding.

**The refusals are discrimination and subtree boundaries**: the *oscillator's* `ω`
times an angular momentum is refused (only the rigid body's 3-12 contracts with `L` —
the shared letter, discriminated at the table); `E·t` is refused (the action is the
pilot's kind, not this directory's); `F·v` is refused (power delivery is upstream's
`informal_lemma`, not formalized surface — the table refuses what the directory does
not own).
-/

import ForPhysLib.ClassicalMechanics.Kinded.HarmonicOscillator
import ForPhysLib.ClassicalMechanics.Kinded.RigidBody
import PropertyKindCalculus.DimensionalCoverage

namespace ForPhysLib.ClassicalMechanics.Operators

open PropertyKindCalculus
open ForPhysLib.ClassicalMechanics
open ForPhysLib.ClassicalMechanics.Kinded
open Time ContDiff InnerProductSpace
open scoped PropertyKindCalculus.OperatorTable

local notation "HO" => _root_.ClassicalMechanics.HarmonicOscillator
local notation "E1" => EuclideanSpace ℝ (Fin 1)

noncomputable section

/-! ## The registrations — seven edges, each on its Stage-1 law -/

/-- `⟪p, v⟫ → 2T` — the Legendre pairing, at the kinds the pointwise readings
carry. -/
instance : KindMul momentumK velocityK kineticEnergyK :=
  ⟨Metrology.momentum_mul_velocity⟩

/-- `p / m → v` — the inverse canonical momentum (`toCanonicalMomentum.symm`). -/
instance : KindDiv momentumK massK velocityK :=
  ⟨Metrology.momentum_div_mass⟩

/-- `k · x → F` — Hooke's law. -/
instance : KindMul springConstantK displacementK forceK :=
  ⟨Metrology.springConstant_mul_displacement⟩

/-- `ω · A → v` — the amplitude–phase velocity (`v₀ = A ω sin φ`). -/
instance : KindMul angularFrequencyK displacementK velocityK :=
  ⟨Metrology.angularFrequency_mul_displacement⟩

/-- `phase / ω → T` — the period (`2π/ω`, the numerator one full turn). -/
instance : KindDiv phaseAngleK angularFrequencyK periodDurationK :=
  ⟨Metrology.phaseAngle_div_angularFrequency⟩

/-- `ω × r`'s component products — the rigid body's velocity decomposition. -/
instance : KindMul angularVelocityK displacementK velocityK :=
  ⟨Metrology.angularVelocity_mul_displacement⟩

/-- `ω · L → 2T_rot` — the rotational contraction. -/
instance : KindMul angularVelocityK angularMomentumK rotationalKineticEnergyK :=
  ⟨Metrology.angularVelocity_mul_angularMomentum⟩

/-! ## The operator idiom — `*` and `/` through the table (MR28) -/

/-- A pointwise displacement reading along a trajectory. -/
@[kindIngest]
def displacementAtQ (xₜ : Time → E1) (t : Time) : Quantity displacementK ℝ :=
  .attest "the trajectory's displacement, component 0" (xₜ t 0)

/-- Hooke's force, now one `*`: `−(k·x)` — the result kind computed by the table. -/
def hookeForceQ (S : HO) (xq : Quantity displacementK ℝ) : Quantity forceK ℝ :=
  (-1 : ℝ) • (springQ S * xq)

/-- **Upstream's `force_eq_linear` closes the table product**: the one-`*` Hooke
reading is the chain's `force`, componentwise. -/
theorem hookeForceQ_erases (S : HO) (xₜ : Time → E1) (t : Time) :
    (hookeForceQ S (displacementAtQ xₜ t)).magnitude = (forceAtQ S xₜ t).magnitude := by
  show (-1 : ℝ) * (S.k * xₜ t 0) = S.force (xₜ t) 0
  rw [S.force_eq_linear]
  simp

/-- One full turn of phase — the `2π` of the period, as a declared constant at 3-7
rather than a dimensionless numeral. -/
@[kindConst]
def fullTurnQ : Quantity phaseAngleK ℝ :=
  .attest "2π — one full turn of phase" (2 * Real.pi)

/-- The period, now one `/`: a full turn per angular frequency — and definitionally
upstream's `period`. -/
theorem period_from_the_table (S : HO) :
    ((fullTurnQ / omegaQ (omegaSqQ S) : Quantity periodDurationK ℝ)).magnitude =
      S.period := rfl

/-- The amplitude–phase velocity, now one `*`: `v₀ = sin φ · (ω·A)` — the numeral
`sin φ` on the numeral action, the product through the table. -/
theorem amplitudePhase_velocity_from_the_table (S : HO)
    (IC : _root_.ClassicalMechanics.HarmonicOscillator.AmplitudePhase) :
    (Real.sin IC.φ •
        (omegaQ (omegaSqQ S) *
          (.attest "the amplitude" IC.A : Quantity displacementK ℝ)) :
      Quantity velocityK ℝ).magnitude =
      (IC.toInitialConditions S).v₀ 0 := by
  show Real.sin IC.φ * (S.ω * IC.A) = (IC.toInitialConditions S).v₀ 0
  show Real.sin IC.φ * (S.ω * IC.A) = EuclideanSpace.single 0 (IC.A * S.ω * Real.sin IC.φ) 0
  simp
  ring

/-- The kinetic energy, now table-spelled end to end — and definitionally Stage 2's
witness. -/
theorem kineticEnergy_from_the_table (S : HO) (xₜ : Time → E1) (t : Time) :
    ((1 / 2 : ℝ) •
        ((massQ S * velocityAtQ xₜ t : Quantity momentumK ℝ) * velocityAtQ xₜ t :
          Quantity kineticEnergyK ℝ)).magnitude =
      (kineticFromTableQ (massQ S) (velocityAtQ xₜ t)).magnitude := rfl

/-- The rotational contraction, now one `*` per term: `ω i · L i` lands at the
rotational species. -/
example (M : RigidBodyMotion 3) (t : Time) (R : RigidBody 3) (i : Fin 3) :
    Quantity rotationalKineticEnergyK ℝ :=
  omegaVecAtQ M t i * angularMomentumFromTableQ R (M.angularVelocity t) i

/-- The inverse canonical momentum, one `/`: a momentum over the mass is a
velocity. -/
example (S : HO) (pq : Quantity momentumK ℝ) : Quantity velocityK ℝ :=
  pq / massQ S

/-! ## What the table refuses -/

-- Refused: the *oscillator's* `ω` times an angular momentum. Only the rigid body's
-- angular velocity (3-12) contracts with `L`; the angular frequency (3-18) — same
-- dimension, same letter — is no entry: the shared-letter discrimination, at the
-- table.
#check_failure fun (ωq : Quantity angularFrequencyK ℝ)
  (L : Quantity angularMomentumK ℝ) => ωq * L

-- Refused: `E·t`. Dimensionally the action — the pilot's kind, minted for the
-- quantum oscillator; this directory's surface never forms it.
#check_failure fun (E : Quantity mechanicalEnergyK ℝ) (t : Quantity durationK ℝ) =>
  E * t

-- Refused: `F·v`. The delivered power `P = F·V + M·ω` is upstream's
-- `informal_lemma` (`rigid_body_work_and_power`), not formalized surface — the
-- table refuses what the directory does not own.
#check_failure fun (F : Quantity forceK ℝ) (v : Quantity velocityK ℝ) => F * v

/-! ## The dimensional audit, re-pinned over the operator registrations -/

/--
info: dimensional coverage:
[coherent] [table] angularFrequencyK · displacementK → velocityK
[coherent] [table] angularVelocityK · angularMomentumK → rotationalKineticEnergyK
[coherent] [table] angularVelocityK · displacementK → velocityK
[coherent] [table] momentumK / massK → velocityK
[coherent] [table] momentumK · velocityK → kineticEnergyK
[coherent] [table] phaseAngleK / angularFrequencyK → periodDurationK
[coherent] [table] springConstantK · displacementK → forceK
7 kind edge(s), all dimensionally coherent — clean
-/
#guard_msgs (whitespace := lax) in
#kind_dimensional_coverage ForPhysLib.ClassicalMechanics.Operators

end

end ForPhysLib.ClassicalMechanics.Operators
