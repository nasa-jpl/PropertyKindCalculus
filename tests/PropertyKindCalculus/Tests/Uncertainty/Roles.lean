/-
# Validation probes — an estimate is not its dispersion

Probes for `PropertyKindCalculus.Uncertainty.Roles`. Two things are being checked, and the
second is the one that matters.

  * That the arithmetic is right: quadrature is not addition, an expansion is a construction at
    the measurand's kind, a factor is refused rather than divided by zero.
  * That the arithmetic a role forbids **does not compile**. Those are `#check_failure`s, and
    they are the whole content of the module — a wrapper that only renamed things would pass
    every numeric probe here and prevent nothing.
-/

import PropertyKindCalculus
import PropertyKindCalculus.Uncertainty.Roles
import PropertyKindCalculus.Uncertainty.Conformity

namespace PropertyKindCalculus.Tests.Roles

open PropertyKindCalculus
open PropertyKindCalculus.Uncertainty

/-- A ratio kind, so uncertainties of it are licensed. -/
def K : KindOfProperty := { id := "storage per pixel", scale := .ratio }

def y : Estimate K Float := ⟨⟨524.5⟩⟩
def u : Dispersion K Float := ⟨⟨2.727⟩⟩

/-! ## The operations a role forbids

An `Estimate` and a `Dispersion` are the same kind and the same carrier. Nothing but these
refusals stops one being handed to the other's slot — which is exactly the transposition that
turns a band reading of `42 u` into `1/42`. -/

-- A dispersion is not an estimate and cannot be centred on.
#check_failure (y.minus y : LowerBound K Float)
-- An estimate is not a dispersion and cannot be combined in quadrature.
#check_failure Dispersion.combine [y]
-- Neither is a bare quantity: the wrapper is not a coercion.
#check_failure (⟨2.727⟩ : Quantity K Float).magnitude + (u : Quantity K Float).magnitude
-- And dispersions do not add. There is no `Add (Dispersion K Float)` and none is coming; this
-- is the single most important line in the file.
#check_failure u + u

/-! ## Quadrature is not addition

Two equal contributors give `√2 u`, not `2 u` — a fold written as a sum over-states by 41 % at
two terms. The probe is the disagreement itself, because that is what a reader has to believe. -/

#guard (Dispersion.combine [u, u]).magnitude < 2.0 * u.magnitude
#guard ((Dispersion.combine [u, u]).magnitude - Float.sqrt 2.0 * u.magnitude).abs < 1e-12
-- Combining is dominating: the result is at least as large as any one contributor, which is
-- what makes a budget a budget.
#guard (Dispersion.combine [u, ⟨⟨1.0⟩⟩]).magnitude ≥ u.magnitude
-- The empty model has no combined uncertainty, and that is zero rather than undefined.
#guard (Dispersion.combine (k := K) (R := Float) []).magnitude == 0.0

/-! ## Expansion, and the endpoints it produces

`U = k·u` is still a dispersion — a width, not a location — and the interval it bounds comes
back at the endpoint ROLES, so `Decimal`'s role-directed rounding applies to it unchanged. -/

def k2 : Quantity coverageFactor Float := ⟨2.0⟩

#guard ((u.expanded k2).magnitude - 5.454).abs < 1e-12
#guard ((y.minus (u.expanded k2)).q.magnitude - 519.046).abs < 1e-12
#guard ((y.plus (u.expanded k2)).q.magnitude - 529.954).abs < 1e-12
-- The endpoints arrive as bounds, so the shortening that is safe for each is already decided.
#guard ((y.minus (u.expanded k2)).roundedDown 2).q.magnitude ≤ (y.minus (u.expanded k2)).q.magnitude
#guard ((y.plus (u.expanded k2)).roundedUp 2).q.magnitude ≥ (y.plus (u.expanded k2)).q.magnitude
-- A lower endpoint may not be rounded the way an upper one is — the pairing is in the types.
#check_failure (y.minus (u.expanded k2)).roundedUp 2

/-! ## A factor is read, never assumed

`g/u` at a dispersion of zero is refused. A margin measured against no dispersion is not a large
coverage factor; it is a factor with no meaning, and the two must not answer alike. -/

#guard (u.factorOf ⟨11.972⟩).isSome
#guard (((u.factorOf ⟨11.972⟩).map (·.magnitude)).getD 0.0 - 4.39017234).abs < 1e-6
#guard (Dispersion.factorOf (⟨⟨0.0⟩⟩ : Dispersion K Float) ⟨11.972⟩).isNone

-- The numerator is a plain quantity, because what gets divided is a margin — a displacement.
-- Handing it an estimate is the transposition this module exists to stop.
#check_failure u.factorOf y

/-! ## What an estimate admits

A correction moves it and it stays an estimate; a comparison with another estimate does not
produce an estimate, because a difference of two estimates is a displacement. -/

#guard ((y.corrected ⟨1.5⟩).magnitude - 526.0).abs < 1e-12
#guard ((y.deviation ⟨⟨512.528⟩⟩).magnitude - 11.972).abs < 1e-12
-- The deviation is exactly what `factorOf` wants, and it type-checks there precisely because it
-- came back as a value rather than as an estimate. This pair is the module working.
#guard (u.factorOf (y.deviation ⟨⟨512.528⟩⟩)).isSome
-- Whereas a correction is not a second estimate to be subtracted.
#check_failure y.corrected y

/-! ## The band reading's label

The classification without its evidence — the three-valued answer a record states and a report
prints, kept in this library so a consumer cannot invent a fourth. -/

#guard (Conformity.BandReading.systematic ⟨42.0⟩).label == .systematic
#guard (Conformity.BandReading.coverage ⟨2.0⟩ ⟨0.01⟩).label == .coverage
#guard Conformity.BandReading.unstated.label == .unstated

/-! ## Axiom profiles -/

/-- info: 'PropertyKindCalculus.Uncertainty.Estimate.minus_magnitude' does not depend on any axioms -/
#guard_msgs in #print axioms Estimate.minus_magnitude

/-- info: 'PropertyKindCalculus.Uncertainty.Dispersion.combine_singleton' does not depend on any axioms -/
#guard_msgs in #print axioms Dispersion.combine_singleton

end PropertyKindCalculus.Tests.Roles
