/-
# Validation probes — writing a magnitude down, and the direction a role rounds in

Inhabitation, boundary, and axiom-profile probes for `PropertyKindCalculus.Decimal`. The
probes check the three properties the module exists for:

  * **exactness is found rather than assumed** — `showExact?` recovers each value at whatever
    precision that value needs, across scales where a fixed-place printer has plenty of
    significant digits, exactly none, and one too few;
  * **the digit budget belongs to the carrier** — seventeen significant digits are needed to
    separate `0.1 + 0.2` from `0.3`, and the binary64 instance has seventeen;
  * **rounding direction is the role's** — a lower endpoint cannot be shortened upward and an
    upper endpoint cannot be shortened downward, whatever the nearer neighbour is, and the
    operation falls back to the unshortened endpoint rather than crossing.

The rounding probes are stated at the three ways this goes wrong in practice: a floor, a
margin, and a value (which has no direction, only exactness).
-/

module

public import PropertyKindCalculus
meta import PropertyKindCalculus

public section -- pkc-blanket
@[expose] section -- pkc-blanket-expose

namespace PropertyKindCalculus.Tests.Decimal

open PropertyKindCalculus

/-- A ratio kind, so bounds of it may be formed. -/
def rateK : KindOfProperty := { id := "rate", scale := .ratio }

/-! ## Exactness is found, not assumed

Three scales of the same kind. A printer fixed at six decimal places has four significant
digits to spare on the first, exactly none on the second, and — the case that makes "just use
more places" no answer — one too few on the third. -/

#guard DecimalCarrier.showExact? (78519000.0 : Float) == some "78519000"
#guard DecimalCarrier.showExact? (4.262e-05 : Float) == some "0.00004262"
#guard DecimalCarrier.showExact? (5.12881e-05 : Float) == some "0.0000512881"

-- What the fixed-place printer would have written instead, at each: a different number every
-- time, and one that still parses, still type-checks, and still looks reviewed.
#guard DecimalCarrier.roundTo? (4.262e-05 : Float) 6 .nearest == some 4.3e-05
#guard DecimalCarrier.roundTo? (5.12881e-05 : Float) 6 .nearest == some 5.1e-05
#guard !DecimalCarrier.readsBack "0.000043" (4.262e-05 : Float)

-- The text is checked against the reader the *consumer* uses. These literals are elaborated by
-- the compiler, not by this module, so they are the independent half of the claim.
#guard (0.00004262 : Float) == 4.262e-05
#guard (0.0000512881 : Float) == 5.12881e-05

/-! ## The digit budget is the carrier's

Seventeen significant digits separate any two binary64 values, and fewer than seventeen do not
separate these two. A carrier of a different width wants a different budget and gets it from
its own instance, which is why the budget is a class field and not a constant in the printer. -/

#guard DecimalCarrier.readsBack "0.30000000000000004" (0.1 + 0.2 : Float)
#guard !DecimalCarrier.readsBack "0.3" (0.1 + 0.2 : Float)
#guard DecimalCarrier.sigDigits (R := Float) == 17

-- Refusals are answers. A value not equal to itself is recovered by no text at all, and is
-- refused rather than approximated to one that parses.
#guard (DecimalCarrier.showExact? (0.0 / 0.0 : Float)).isNone

/-! ## Direction is the role's

A floor. Shortened to four decimals it may only move down; the nearer neighbour is up, and the
role wins. -/

def floorB : LowerBound rateK Float := ⟨⟨4.26266e-05⟩⟩

-- To-nearest at 8 decimals gives `0.00004263`, which is *above* the floor and therefore no
-- longer a floor. The role supplies the direction, and the shortened floor is still a floor.
#guard DecimalCarrier.roundTo? (4.26266e-05 : Float) 8 .nearest == some 4.263e-05
#guard (floorB.roundedDown 8).q.magnitude == 4.262e-05
#guard (floorB.roundedDown 8).q.magnitude ≤ floorB.q.magnitude

/-- A margin, held as the upper role: what it must never do is shrink toward the limit it
protects. -/
def bandB : UpperBound rateK Float := ⟨⟨1754.0339⟩⟩

-- To-nearest at two decimals gives `1754.03`, four thousandths *below* the stated margin —
-- inconsequential in size and wrong in kind, since a margin's whole job is to be on one side.
#guard DecimalCarrier.roundTo? (1754.0339 : Float) 2 .nearest == some 1754.03
#guard (bandB.roundedUp 2).q.magnitude == 1754.04
#guard bandB.q.magnitude ≤ (bandB.roundedUp 2).q.magnitude

-- The direction is the number line's, so a floor below zero shortens away from zero while a
-- margin below zero shortens toward it. Getting this from `|x|` alone is the sign slip the
-- carrier's renderer exists to absorb.
#guard ((⟨⟨-1754.0339⟩⟩ : LowerBound rateK Float).roundedDown 2).q.magnitude == -1754.04
#guard ((⟨⟨-1754.0339⟩⟩ : UpperBound rateK Float).roundedUp 2).q.magnitude == -1754.03

-- Boundary: when the carrier cannot render at that precision, the answer is the original
-- endpoint and not a shortened one. The unsafe direction is unreachable, not merely unlikely.
#guard (floorB.roundedDown 400).q.magnitude == floorB.q.magnitude
#guard (bandB.roundedUp 400).q.magnitude == bandB.q.magnitude

-- Boundary: the direction is never selectable by direction. There is no `roundedUp` on a lower
-- endpoint and no `roundedDown` on an upper one, so a caller cannot ask for the other way by
-- naming it — the only way to move an endpoint the other way is to say which READING makes that
-- safe, which is what the two operations below are called after.
#check_failure floorB.roundedUp 8
#check_failure bandB.roundedDown 2

/-! ## The same side, the opposite safe direction

The geometric role — which side — does not fix the rounding. What fixes it is whether the
endpoint is **asserted** about a quantity or **imposed** upon one, which `Bounds` does not
record and cannot: it is a fact about why the bound exists.

`bandB` above is asserted ("the margin is at least this wide"), so shortening it upward keeps
it true. The same magnitude read as a *limit* ("the job may use at most 1754.0339") wants the
opposite move, because raising a limit admits values that should have failed. Both are
`UpperBound rateK Float`; nothing but the operation's name distinguishes them. -/

def budget : UpperBound rateK Float := ⟨⟨1754.0339⟩⟩
def minSpec : LowerBound rateK Float := ⟨⟨4.26266e-05⟩⟩

-- The requirement reading moves the other way, at the same side, from the same number.
#guard (budget.roundedDownAsRequirement 2).q.magnitude == 1754.03
#guard (bandB.roundedUp 2).q.magnitude == 1754.04
-- Which is the whole point: one number, one geometric side, two answers two decimals apart, and
-- the one that is correct is decided by something no rule in this file can see.
#guard (budget.roundedDownAsRequirement 2).q.magnitude != (bandB.roundedUp 2).q.magnitude

#guard (budget.roundedDownAsRequirement 2).q.magnitude ≤ budget.q.magnitude
#guard minSpec.q.magnitude ≤ (minSpec.roundedUpAsRequirement 8).q.magnitude
-- Eight places, rounded up: 0.0000426266 → 0.00004263. The asserted reading of the same
-- endpoint (`floorB.roundedDown 8`) gives 0.00004262 — adjacent representable decimals, and
-- only one of them holds for a given reading.
#guard (minSpec.roundedUpAsRequirement 8).q.magnitude == 4.263e-05
#guard (floorB.roundedDown 8).q.magnitude == 4.262e-05

-- A requirement that cannot be rendered at that precision keeps its original value, on the same
-- fallback rule the asserted pair uses: refusing to shorten is always admissible.
#guard (budget.roundedDownAsRequirement 400).q.magnitude == budget.q.magnitude
#guard (minSpec.roundedUpAsRequirement 400).q.magnitude == minSpec.q.magnitude

-- And the requirement operations are still side-locked: there is no way to spell "loosen this
-- requirement", because that is the move nothing here should make easy.
#check_failure budget.roundedUpAsRequirement 2
#check_failure minSpec.roundedDownAsRequirement 8

-- And no role offers a to-nearest. `RoundingDirection.nearest` exists — `showExact?` renders
-- with it — but no operation on a bound accepts a direction, so it cannot be selected at a
-- call site where the role has already decided.
#check_failure floorB.roundedTo 8 RoundingDirection.nearest

/-! ## Axiom profile

Both safety theorems are proved by cases over the carrier's decidable order, so neither reaches
for choice or for the order axioms a host float carrier could not supply. -/

/-- info: 'PropertyKindCalculus.LowerBound.roundedDown_safe' depends on axioms: [propext] -/
#guard_msgs in #print axioms LowerBound.roundedDown_safe

/-- info: 'PropertyKindCalculus.UpperBound.roundedUp_safe' depends on axioms: [propext] -/
#guard_msgs in #print axioms UpperBound.roundedUp_safe

end PropertyKindCalculus.Tests.Decimal

end -- pkc-blanket-expose
end -- pkc-blanket
