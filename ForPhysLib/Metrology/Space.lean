/-
# Stage 1 — the metrology annex of `Physlib/SpaceAndTime/Space`

The second rung of [the adoption ladder](../PLAN.md#stage-1-the-metrology-annex), for the
same first directory as Stage 0: each Stage-0 kind paired with its PhysLib `Dimension` as
a `DimensionedKind`, the directory's small kind algebra authored, and
`#kind_dimensional_coverage` pinned over it with `#guard_msgs` — the stage that converts
prose dimension claims into statements a build can fail on, at **zero cost to existing
code**: nothing in PhysLib changes, or even imports this.

**And the lookup is now a theorem.** Stage 0 copied its ids, scales and examination
principles from PKC's ISO 80000-3 catalogue; this module imports that catalogue and proves
the agreement by `decide` — kind by kind, and dimension by dimension. A Stage-0 edit that
drifts from the standard stops compiling here. -/

import ForPhysLib.Kinds.Space
import ForPhysLib.Examination.Space
import PropertyKindCalculus.Dimension
import PropertyKindCalculus.DimensionalCoverage
import PropertyKindCalculus.Iso80000.Part3

namespace ForPhysLib.Metrology.Space

open PropertyKindCalculus ForPhysLib.Kinds.Space

/-! ## The pairings -/

/-- Length is `L`. -/
def lengthDK : DimensionedKind := { kind := length, dim := Dim.length }
/-- Distance is `L` — the metric's values, in the directory's own `LengthUnit`. -/
def distanceDK : DimensionedKind := { kind := distance, dim := Dim.length }
/-- A position vector is `L` (from the origin). -/
def positionVectorDK : DimensionedKind := { kind := positionVector, dim := Dim.length }
/-- A displacement is `L` (between points). -/
def displacementDK : DimensionedKind := { kind := displacement, dim := Dim.length }
/-- Plane angle is dimension one — the `T⁻¹`-free member of the rotation API. -/
def planeAngleDK : DimensionedKind := { kind := planeAngle, dim := 1 }
/-- Area is `L²` — where the cross product and the slice product structure land. -/
def areaDK : DimensionedKind := { kind := area, dim := Dim.area }

/-! ## The lookup, proved

Stage 0's vocabulary agrees with `Iso80000.Part3` — same kinds (ids, scales, examination
principles) and same dimensions. Decided, so drift is a build failure. -/

example : length         = Iso80000.Part3.length.kind         := by decide
example : distance       = Iso80000.Part3.distance.kind       := by decide
example : positionVector = Iso80000.Part3.positionVector.kind := by decide
example : displacement   = Iso80000.Part3.displacement.kind   := by decide
example : planeAngle     = Iso80000.Part3.planeAngle.kind     := by decide
example : area           = Iso80000.Part3.area.kind           := by decide

example : lengthDK.dim         = Iso80000.Part3.length.dim         := rfl
example : distanceDK.dim       = Iso80000.Part3.distance.dim       := rfl
example : positionVectorDK.dim = Iso80000.Part3.positionVector.dim := rfl
example : displacementDK.dim   = Iso80000.Part3.displacement.dim   := rfl
example : planeAngleDK.dim     = Iso80000.Part3.planeAngle.dim     := rfl
example : areaDK.dim           = Iso80000.Part3.area.dim           := rfl

/-! ## The directory's kind algebra, and its dimensional audit

Two authored edges — the ones the directory's API actually exercises: the slice
equivalence `Space (d+1) ≃L ℝ × Space d` and the cross product `⨯ₑ₃` give lengths their
product structure landing in area, and a rotation's angle is arc per radius, dimension
one. `#kind_dimensional_coverage` then walks every authored edge and checks it in
PhysLib's dimension group. -/

/-- Lengths multiply to an area — the slice/cross-product structure, as a kind law. -/
theorem length_mul_length : ProductKind length length area := ProductKind.ofRatio _ _ _

/-- A plane angle is a ratio of lengths (arc per radius) — dimension one, as the
quotient law says. -/
theorem angle_is_length_ratio : QuotientKind length length planeAngle :=
  QuotientKind.ofRatio _ _ _

/--
info: dimensional coverage:
[coherent] length / length → planeAngle
[coherent] length · length → area
2 kind edge(s), all dimensionally coherent — clean
-/
#guard_msgs (whitespace := lax) in
#kind_dimensional_coverage ForPhysLib.Metrology.Space

end ForPhysLib.Metrology.Space
