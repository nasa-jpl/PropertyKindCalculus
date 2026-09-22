/-
# Stage 3 — the operator table of `Physlib/SpaceAndTime/Space`

The fourth rung of [the adoption ladder](../PLAN.md#stage-3-the-operator-table): the
directory's kind algebra registered once as `KindMul`/`KindDiv` instances, so that with
`open scoped PropertyKindCalculus.OperatorTable` the ordinary `*` and `/` elaborate
through the table — and an unregistered pair **fails to elaborate**. This is the stage
where [MR11](../REQUIREMENTS.md#mr11-authoring-ergonomics) is paid down: the demos below
use the operator idiom, never the longhand witness form
([MR28](../REQUIREMENTS.md#mr28-kind-generic)).

**The table is curated per kind, not per dimension.** `length · length → area` is
registered; `distance · distance` is not — same dimension `L`, no sanctioned product —
and the probe shows it refused. That asymmetry is the whole point of a curated table:
dimensional admissibility is necessary, the registration is the design decision.

The same two edges Stage 1 authored as laws back the instances, so the Stage-1
`#kind_dimensional_coverage` discipline re-pins here over the *operator* registrations:
the table cannot drift from the dimensional audit.
-/

module

public import ForPhysLib.Metrology.Space
public import ForPhysLib.Kinded.Space
public import PropertyKindCalculus.DimensionalCoverage

public section -- pkc-blanket
@[expose] section -- pkc-blanket-expose

namespace ForPhysLib.Operators.Space

open PropertyKindCalculus ForPhysLib.Kinds.Space
open scoped PropertyKindCalculus.OperatorTable

/-- `length · length → area`, registered once for the directory — the slice/cross-product
structure, entering the table on Stage 1's authored law. -/
instance : KindMul length length area := ⟨Metrology.Space.length_mul_length⟩

/-- `length / length → plane angle`, registered once — arc per radius, dimension one. -/
instance : KindDiv length length planeAngle := ⟨Metrology.Space.angle_is_length_ratio⟩

/-! ## The operator idiom — `*` and `/` through the table (MR28) -/

/-- Two lengths multiply straight to an area; the result kind is *computed* by the table
(`area` is an `outParam`), not annotated. -/
noncomputable example (a b : Quantity length ℝ) : Quantity area ℝ := a * b

/-- Arc per radius is a plane angle, through the table's quotient entry. -/
noncomputable example (arc radius : Quantity length ℝ) : Quantity planeAngle ℝ := arc / radius

/-- The Stage-2 author-forms compose through the table: the area spanned by two
displacements' extents, in the directory's own length unit. -/
noncomputable def spanArea {d : ℕ}
    (v w : Quantity displacement (EuclideanSpace ℝ (Fin d))) : Quantity area ℝ :=
  Kinded.Space.lengthOf v * Kinded.Space.lengthOf w

/-- Erasure survives the table: the operator-built area's magnitude is the product of the
norms, by `rfl` — the table operator *is* the named verified constructor. -/
theorem spanArea_magnitude {d : ℕ}
    (v w : Quantity displacement (EuclideanSpace ℝ (Fin d))) :
    (spanArea v w).magnitude = ‖v.magnitude‖ * ‖w.magnitude‖ := rfl

/-! ## What the table refuses -/

-- Refused: `area · area` is registered nowhere, so the product does not elaborate.
#check_failure fun (a b : Quantity area ℝ) => a * b

-- Refused: `distance · distance` — dimensionally a length squared, but the table is
-- curated per kind and no product of distances was sanctioned. Necessity vs design.
#check_failure fun (p q : _root_.Space 3) =>
  Kinded.Space.distanceQ p q * Kinded.Space.distanceQ p q

/-! ## The dimensional audit, re-pinned over the operator registrations -/

/--
info: dimensional coverage:
[coherent] [table] length / length → planeAngle
[coherent] [table] length · length → area
2 kind edge(s), all dimensionally coherent — clean
-/
#guard_msgs (whitespace := lax) in
#kind_dimensional_coverage ForPhysLib.Operators.Space

end ForPhysLib.Operators.Space

end -- pkc-blanket-expose
end -- pkc-blanket
