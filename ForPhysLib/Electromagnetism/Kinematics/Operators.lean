/-
# Stage 3 — the operator table of `Physlib/Electromagnetism/Kinematics`

The fourth rung of [the adoption ladder](../../PLAN.md#stage-3-the-operator-table) for
the campaign's second directory: the kind algebra registered once as
`KindMul`/`KindDiv` instances, so that with `open scoped
PropertyKindCalculus.OperatorTable` the ordinary `*` and `/` elaborate through the
table — and an unregistered pair **fails to elaborate**.

**Two entries predate this file** — Feasibility registered the upward velocity edge
twice (`c·A → potential difference`, `c·B → E`), which is why `boostedEQ` already
elaborates through `*`. This file registers the three remaining edges that have
scalar call sites; the seven law-only edges of Stage 1 (the derivative edges, the
gauge edge, the line integrals) stay laws, because their divisions live inside
Mathlib's `fderiv` and `∫` where no table ever sees them — the pilot's `p̂²/m`
precedent, now the *majority* case: in a field theory most of the kind algebra rides
the analysis operators, and the audit stage measures exactly that.

**Instance heads are spelled at the kinds the quantities carry** (the pilot's finding
8, already re-confirmed by Stage 2's one ascription): the pointwise readings carry
Feasibility's catalogue-lookup spellings, `fieldStrengthAtQ` carries Stage 0's
`fieldStrength` literal, and each head below matches its consumers.

**The table is curated per kind, not per dimension** — and this directory's refusals
are *subtree boundaries*: `E · B` is the Poynting route, which needs `μ₀`
(`Vacuum/Constant.lean` — not this chain); `F · F` is the Lagrangian density
(`Dynamics/` — not this chain). The kinematics table refuses what the kinematics
directory does not own.
-/

module

public import ForPhysLib.Electromagnetism.Kinematics.Kinded
meta import ForPhysLib.Electromagnetism.Kinematics.Kinded
public import PropertyKindCalculus.DimensionalCoverage
meta import PropertyKindCalculus.DimensionalCoverage

@[expose] public section

namespace ForPhysLib.Electromagnetism.Kinematics.Operators

open PropertyKindCalculus
open ForPhysLib.Electromagnetism.Kinematics
open ForPhysLib.Electromagnetism.Kinematics.Kinds
open ForPhysLib.Electromagnetism.Kinematics.Kinded
open scoped PropertyKindCalculus.OperatorTable

local notation "EMPot " d:max => _root_.Electromagnetism.ElectromagneticPotential d

variable {d : ℕ}

/-! ## The registrations — three edges, each on its Stage-1 law -/

/-- `φ-difference / c → vector potential` — `ofPotentials`' time slot, at the kinds
the torsor extent and the declared speed carry. -/
instance : KindDiv potentialDifferenceK speedOfLightK vectorPotentialK :=
  ⟨Metrology.electricPotentialDifference_div_speedOfLight⟩

/-- `c · F⁰ⁱ → E` — the tensor's electric reading, at the kinds `speedRQ` and
`fieldStrengthAtQ` carry. -/
instance : KindMul speedOfLightK fieldStrength electricFieldK :=
  ⟨Metrology.speedOfLight_mul_fieldStrength⟩

/-- `E / c → B` — the boost's downward mixing, and the tensor's own storage of the
electric block. -/
instance : KindDiv electricFieldK speedOfLightK magneticFluxDensityK :=
  ⟨Metrology.electricFieldStrength_div_speedOfLight⟩

/-! ## The interval potential and the torsor — the division only the extent may take -/

/-- A pointwise reading of the scalar potential, at the **interval-scale** 6-11.1. -/
@[kindIngest]
noncomputable def scalarPotentialAtQ (cS : SpeedOfLight) (A : EMPot d)
    (t : Time) (x : Space d) : Quantity electricPotentialK ℝ :=
  .attest "pointwise reading of the chain's scalarPotential — gauge-fixed, interval"
    (A.scalarPotential cS t x)

/-- The torsor's `−ᵥ`: two positions on the potential axis determine an extent — the
interval kind's *only* outbound arithmetic, landing at the ratio-scale 6-11.2. -/
@[kindCrossing]
def potentialSubQ (x y : Quantity electricPotentialK ℝ) :
    Quantity potentialDifferenceK ℝ :=
  .attest "the torsor −ᵥ: interval positions determine a ratio-scale extent"
    (x.magnitude - y.magnitude)

/-- **The `φ/c` entry, consumed**: a potential *difference* per speed is a
vector-potential value — the time slot of `ofPotentials`, reachable only through the
torsor. -/
noncomputable example (cS : SpeedOfLight) (A : EMPot d) (t : Time) (x y : Space d) :
    Quantity vectorPotentialK ℝ :=
  potentialSubQ (scalarPotentialAtQ cS A t x) (scalarPotentialAtQ cS A t y) / speedRQ cS

/- Refused: the interval potential itself over a speed. `(electric potential, speed of
light)` is no entry — and none is registrable: `ofRatio` is unprovable at 6-11.1's
scale (Feasibility's pinned refusal). Only the extent divides. -/
#check_failure fun (cS : SpeedOfLight) (φ : Quantity electricPotentialK ℝ) =>
  φ / speedRQ cS

/-! ## The operator idiom — `*` and `/` through the table (MR28) -/

/-- The tensor's electric reading, now one `*`: the result kind is *computed* by the
table (an `outParam`), not annotated — and this is definitionally Stage 2's
call-site-witness spelling (`electricReadingQ`). -/
noncomputable def electricReadingFromTable (cS : SpeedOfLight) (A : EMPot d)
    (x : SpaceTime d) (i : Fin d) : Quantity electricFieldK ℝ :=
  (-1 : ℝ) • (speedRQ cS * fieldStrengthAtQ A x (Sum.inl 0, Sum.inr i))

/-- The table spelling *is* the Stage-2 spelling — definitionally. -/
theorem electricReadingFromTable_eq (cS : SpeedOfLight) (A : EMPot d)
    (x : SpaceTime d) (i : Fin d) :
    electricReadingFromTable cS A x i = electricReadingQ cS A x i := rfl

/-- **Upstream's tensor-to-field lemma closes the table product**: at the sliced
point, the one-`*` reading is the chain's `electricField` (through Stage 2's
erasure). -/
theorem electricReadingFromTable_erases (cS : SpeedOfLight) (A : EMPot d)
    (hA : Differentiable ℝ A) (t : Time) (x : Space d) (i : Fin d) :
    (electricReadingFromTable cS A ((SpaceTime.toTimeAndSpace cS).symm (t, x)) i).magnitude =
      A.electricField cS t x i := by
  rw [electricReadingFromTable_eq]
  exact electricReadingQ_erases cS A hA t x i

/-- The boost's downward mixing, now one `/`: `γ·(B + (β·E)/c)` fully through the
table (the upward mixing has been one `*` since Feasibility's `boostedEQ`). -/
noncomputable example (γv β : ℝ) (cq : Quantity speedOfLightK ℝ)
    (B : Quantity magneticFluxDensityK ℝ) (E : Quantity electricFieldK ℝ) :
    Quantity magneticFluxDensityK ℝ :=
  γv • (B + (β • E) / cq)

/-! ## What the table refuses — the subtree boundaries -/

-- Refused: `E · B`. Dimensionally the Poynting route — but `S = (E × B)/μ₀` needs the
-- vacuum permeability, which lives in `Vacuum/Constant.lean`, not this chain. The
-- kinematics table refuses what the kinematics directory does not own.
#check_failure fun (E : Quantity electricFieldK ℝ) (B : Quantity magneticFluxDensityK ℝ) =>
  E * B

-- Refused: `F · F`. The Lagrangian density `F_{μν}F^{μν}` is `Dynamics/`' object; the
-- kinematics chain never squares its tensor.
#check_failure fun (F₁ F₂ : Quantity fieldStrength ℝ) => F₁ * F₂

-- Refused: a chart entry plus an extent entry — same tesla, no join: the
-- antisymmetrization between `∂A` and `F` is a *crossing*, never an addition.
#check_failure fun (dA : Quantity potentialGradient ℝ) (F : Quantity fieldStrength ℝ) =>
  dA + F

/-! ## The dimensional audit, re-pinned over the operator registrations -/

/--
info: dimensional coverage:
[coherent] [table] electricFieldK / speedOfLightK → magneticFluxDensityK
[coherent] [table] potentialDifferenceK / speedOfLightK → vectorPotentialK
[coherent] [table] speedOfLightK · fieldStrength → electricFieldK
3 kind edge(s), all dimensionally coherent — clean
-/
#guard_msgs (whitespace := lax) in
#kind_dimensional_coverage ForPhysLib.Electromagnetism.Kinematics.Operators

end ForPhysLib.Electromagnetism.Kinematics.Operators

