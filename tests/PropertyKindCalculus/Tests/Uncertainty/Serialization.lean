/-
# Validation probes — the rounding at the edge of an evaluation

Probes for `PropertyKindCalculus.Uncertainty.Adequacy.Serialization`, the fifth adequacy
sub-property. What they check is the split that makes it a sub-property rather than a lint:
the same text, against the same magnitude, is **adequate or not depending on the role the
magnitude plays** — so a verdict cannot be reduced to an inequality on the displacement.

  * a crossing that reads back is `.exact`, and adequate for anything;
  * a crossing that does not read back is adequate for a *bound* iff it moved the way the role
    allows, and adequate for a *value* never;
  * a magnitude the carrier cannot render is refused, not approximated.
-/

module

public import PropertyKindCalculus
meta import PropertyKindCalculus
public import PropertyKindCalculus.Uncertainty.Adequacy.Serialization
meta import PropertyKindCalculus.Uncertainty.Adequacy.Serialization

public section -- pkc-blanket
@[expose] section -- pkc-blanket-expose

namespace PropertyKindCalculus.Tests.Serialization

open PropertyKindCalculus
open PropertyKindCalculus.Uncertainty.Adequacy

/-- A ratio kind, so bounds of it may be formed. -/
def rateK : KindOfProperty := { id := "rate", scale := .ratio }

/-! ## Exactness costs nothing and is always the adequate outcome -/

#guard verdictOfValue (4.262e-05 : Float) "0.00004262" == .exact
#guard (verdictOfValue (4.262e-05 : Float) "0.00004262").adequateAsValue
#guard (verdictOfValue (4.262e-05 : Float) "0.00004262").adequateAsBound

-- The text a six-place printer would have produced for the same magnitude.
#guard verdictOfValue (4.262e-05 : Float) "0.000043" == .shortenedUnsafely
#guard !(verdictOfValue (4.262e-05 : Float) "0.000043").adequateAsValue

/-! ## The same text, two roles, two verdicts

This is the pair the module exists for. `0.00004262` sits *below* `4.26266e-05`: as a floor it
gives slack away and still holds, as a ceiling it has stopped covering, and as a value it is
simply a different number. No inequality on the displacement distinguishes these three — the
displacement is the same in all three. -/

def floorB : LowerBound rateK Float := ⟨⟨4.26266e-05⟩⟩
def ceilB : UpperBound rateK Float := ⟨⟨4.26266e-05⟩⟩

#guard verdictAtLower floorB "0.00004262" == .shortenedSafely
#guard verdictAtUpper ceilB "0.00004262" == .shortenedUnsafely
#guard verdictOfValue (4.26266e-05 : Float) "0.00004262" == .shortenedUnsafely

#guard (verdictAtLower floorB "0.00004262").adequateAsBound
#guard !(verdictAtUpper ceilB "0.00004262").adequateAsBound
-- And a safe shortening is still not a value: what it claims is weaker, not the same.
#guard !(verdictAtLower floorB "0.00004262").adequateAsValue

-- The dual text moves the other way and swaps which role survives.
#guard verdictAtLower floorB "0.00004263" == .shortenedUnsafely
#guard verdictAtUpper ceilB "0.00004263" == .shortenedSafely

/-! ## The role-directed operations produce crossings their own role accepts

`Decimal`'s `roundedDown`/`roundedUp` are the constructive half of this property: what they
emit is never `.shortenedUnsafely` for the role that emitted it. -/

#guard (verdictAtLower floorB
  ((DecimalCarrier.toFixed? floorB.q.magnitude 8 .down).getD "")).adequateAsBound
#guard (verdictAtUpper ceilB
  ((DecimalCarrier.toFixed? ceilB.q.magnitude 8 .up).getD "")).adequateAsBound

-- Whereas rendering either one to-nearest is adequate for at most one of them, and which one
-- is not knowable from the direction — it depends on where the discarded digits fell.
#guard (verdictAtUpper ceilB
  ((DecimalCarrier.toFixed? ceilB.q.magnitude 8 .nearest).getD "")).adequateAsBound
#guard !(verdictAtLower floorB
  ((DecimalCarrier.toFixed? floorB.q.magnitude 8 .nearest).getD "")).adequateAsBound

/-! ## Refusals -/

-- Text that is not a decimal at all reads back as nothing, and the crossing is refused rather
-- than scored.
#guard verdictOfValue (1.0 : Float) "not a number" == .unrepresentable
#guard !(verdictOfValue (1.0 : Float) "not a number").adequateAsBound

-- A value not equal to itself cannot be recovered by any text.
#guard (DecimalCarrier.showExact? (0.0 / 0.0 : Float)).isNone

/-! ## Displacement is evidence, not a criterion

It is `none` exactly when the text does not read back at all, and zero exactly when the
crossing was exact — which is the whole of "an exact crossing leaves the budget alone". -/

#guard (displacement (⟨4.262e-05⟩ : Quantity rateK Float) "0.00004262").map (·.magnitude)
  == some 0.0
#guard (displacement (⟨1.0⟩ : Quantity rateK Float) "not a number").isNone
-- Nonzero, signed, and reported at the quantity's own kind rather than as a naked float. The
-- sign is the direction the crossing moved, which is what a role has an opinion about.
#guard (displacement (⟨4.26266e-05⟩ : Quantity rateK Float) "0.00004262").map (·.magnitude)
  == some (4.262e-05 - 4.26266e-05)

/-! ## Axiom profile -/

/-- info: 'PropertyKindCalculus.Uncertainty.Adequacy.displacement_eq_zero_of_exact' does not depend on any axioms -/
#guard_msgs in #print axioms displacement_eq_zero_of_exact

end PropertyKindCalculus.Tests.Serialization

end -- pkc-blanket-expose
end -- pkc-blanket
