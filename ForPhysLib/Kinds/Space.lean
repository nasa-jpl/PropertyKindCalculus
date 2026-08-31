/-
# Stage 0 — the kind vocabulary of `Physlib/SpaceAndTime/Space`

The first rung of [the adoption ladder](../PLAN.md#stage-0-the-kind-vocabulary), built for
the directory the plan names first: *"small, foundational, and its API map already contains
the `LengthUnit` requirement."* One file, bare `KindOfProperty` declarations, Mathlib-free
— importable by anything, costing nothing until something imports it.

**This is a lookup, not a design.** Every kind below is an ISO 80000-3 item, already
catalogued with its examination principle in PKC's `Iso80000.Part3`; ids, scales and
principle strings are copied *verbatim* from that catalogue, and Stage 1
(`ForPhysLib.Metrology.Space`) proves the agreement by `decide` — so this file cannot
silently drift from the standard it looks up. That is the asymmetry
[MR11](../REQUIREMENTS.md#mr11-authoring-ergonomics) priced: PhysLib's kinds exist already;
Stage 0 writes them down.

**The vocabulary is what the directory's own API speaks.** From `Space/API-map.yaml`:
`Space d` is flat Euclidean space *"with an arbitrary but fixed choice of length unit and
origin"*; the API carries a metric (`Dist`), a norm, a `LengthUnit`, and — decisively — an
`AddTorsor (EuclideanSpace ℝ (Fin d)) (Space d)`: PhysLib itself keeps *points* and
*translations* as different types. The kind layer names the two length-readings that
distinction carries: a **position vector** (item 3-1.10, examined *from the chosen
origin*) and a **displacement** (item 3-1.11, examined *between two points*). They are
distinct kinds — proved below from their examination principles — yet mutually comparable
as lengths, which is exactly the torsor the code already has, said at the kind level.
-/

import PropertyKindCalculus

namespace ForPhysLib.Kinds.Space

open PropertyKindCalculus

/-- Length — ISO 80000-3 item 3-1.1, the genus of the family. Ratio-scale, no
distinguishing examination principle. What the directory's norm and `LengthUnit` measure. -/
def length : KindOfProperty := { id := "length", scale := .ratio }

/-- Distance — item 3-1.8, the shortest path length between two points: the directory's
`Dist`/metric structure. -/
def distance : KindOfProperty :=
  { id := "distance", scale := .ratio, examPrinciple := some "shortest-path" }

/-- Position vector — item 3-1.10, examined *from the chosen origin*: what a point of
`Space d` reports once `Origin.lean`'s conventional zero is fixed. The origin-dependence
the API map states in prose ("arbitrary but fixed choice of … origin") is carried here as
the examination principle. -/
def positionVector : KindOfProperty :=
  { id := "position vector", scale := .ratio, examPrinciple := some "from-origin" }

/-- Displacement — item 3-1.11, examined *between two points*: what the torsor's
`EuclideanSpace` vectors are, origin-free. -/
def displacement : KindOfProperty :=
  { id := "displacement", scale := .ratio, examPrinciple := some "between-points" }

/-- Plane angle — item 3-5, dimension one: what `EuclideanGroup`'s rotations turn by. -/
def planeAngle : KindOfProperty := { id := "plane angle", scale := .ratio }

/-- Area — item 3-3: where the directory's cross product (`⨯ₑ₃`) and the slice product
structure `Space (d+1) ≃ ℝ × Space d` land dimensionally. -/
def area : KindOfProperty := { id := "area", scale := .ratio }

/-! ## Distinctness — the collisions the vocabulary exists to prevent

All of these share the dimension `L` (or `1`); nothing dimensional separates them. The
kind layer does, decidably. -/

/-- **A position is not a displacement** — the kind-level statement of the API's own
`Space d` vs `EuclideanSpace` distinction, individuated by examination principle. -/
theorem positionVector_ne_displacement : positionVector ≠ displacement := by decide

/-- A distance is not a bare length (it is examined between two points, shortest-path). -/
theorem distance_ne_length : distance ≠ length := by decide

/-- A distance is not a displacement — scalar of the metric vs vector of the torsor. -/
theorem distance_ne_displacement : distance ≠ displacement := by decide

/-! ## The directory's specialization lattice

The direct-parent edges among the directory's own kinds — a coarsening of the full
ISO 80000-3 lattice in `Iso80000.Part3` (there, distance runs through path length; this
directory never speaks of path length, and specialization is transitive, so the direct
edge is sound). -/

/-- The direct-parent edges of the `Space` directory's length family. -/
inductive Edge : KindOfProperty → KindOfProperty → Prop
  /-- A distance is a kind of length. -/
  | distance_length : Edge distance length
  /-- A position vector is a length quantity from the origin. -/
  | positionVector_length : Edge positionVector length
  /-- A displacement is a length quantity between points. -/
  | displacement_length : Edge displacement length

/-- Distance specializes length. -/
theorem distance_specializes_length : Specializes Edge distance length :=
  .of_edge .distance_length

/-- **Position and displacement are mutually comparable as lengths** while staying
distinct kinds — comparability without identity (R2), on exactly the pair the torsor
relates. -/
theorem positionVector_comparable_displacement :
    MutuallyComparable Edge positionVector displacement :=
  ⟨length, .of_edge .positionVector_length, .of_edge .displacement_length⟩

end ForPhysLib.Kinds.Space
