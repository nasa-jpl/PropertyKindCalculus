/-
# Stage 1 — the metrology annex of `Physlib/SpaceAndTime/Space`

The second rung of [the adoption ladder](../PLAN.md#stage-1-the-metrology-annex), for the
same first directory as Stage 0: each Stage-0 kind paired with its PhysLib `Dimension` as
a `DimensionedKind` — the lookups by *referencing the catalogue's own entries* — the
directory's small kind algebra authored, and
`#kind_dimensional_coverage` pinned over it with `#guard_msgs` — the stage that converts
prose dimension claims into statements a build can fail on, at **zero cost to existing
code**: nothing in PhysLib changes, or even imports this.

**And the lookup is definitional.** Stage 0's kinds *are* the catalogue entries'
own projections; this module records the identification kind by kind (`rfl` — there
is no second spelling to drift) and checks each pairing's dimension against the
catalogue's. -/

import ForPhysLib.Kinds.Space
import ForPhysLib.Examination.Space
import PropertyKindCalculus.Dimension
import PropertyKindCalculus.DimensionalCoverage
import PropertyKindCalculus.Iso80000.Part3

namespace ForPhysLib.Metrology.Space

open PropertyKindCalculus ForPhysLib.Kinds.Space

/-! ## The pairings -/

/-- Length is `L`. -/
def lengthDK : DimensionedKind := Iso80000.Part3.length
/-- Distance is `L` — the metric's values, in the directory's own `LengthUnit`. -/
def distanceDK : DimensionedKind := Iso80000.Part3.distance
/-- A position vector is `L` (from the origin). -/
def positionVectorDK : DimensionedKind := Iso80000.Part3.positionVector
/-- A displacement is `L` (between points). -/
def displacementDK : DimensionedKind := Iso80000.Part3.displacement
/-- Plane angle is dimension one — the `T⁻¹`-free member of the rotation API. -/
def planeAngleDK : DimensionedKind := Iso80000.Part3.planeAngle
/-- Area is `L²` — where the cross product and the slice product structure land. -/
def areaDK : DimensionedKind := Iso80000.Part3.area

/-! ## The lookup, definitional

Stage 0's vocabulary *is* `Iso80000.Part3`'s — each kind is the catalogue entry's own
projection, so the identification is `rfl` and drift is impossible by construction. -/

example : length         = Iso80000.Part3.length.kind         := rfl
example : distance       = Iso80000.Part3.distance.kind       := rfl
example : positionVector = Iso80000.Part3.positionVector.kind := rfl
example : displacement   = Iso80000.Part3.displacement.kind   := rfl
example : planeAngle     = Iso80000.Part3.planeAngle.kind     := rfl
example : area           = Iso80000.Part3.area.kind           := rfl

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
