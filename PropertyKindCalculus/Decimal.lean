/-
# Decimal — writing a magnitude down, and reading back the same magnitude

A magnitude that leaves a computation as decimal text and comes back is passing through a
**rounding operation**. It is easy not to see it as one, because it has no arithmetic in it and
no operator symbol; but `read ∘ write` maps a carrier value to a carrier value, and unless the
text carries enough digits it is not the identity. Every other rounding in a measurement chain
is accounted for — `Uncertainty.Adequacy` exists to find the ones that hide inside `+` and `−`
— and this one has generally been accounted for nowhere, because the language's default
printer looks like a display concern.

**It is the one rounding that can be made exactly free, which is why nothing else is
acceptable.** An arithmetic rounding is forced: the carrier has the width it has, and half a
ulp is the price of the operation. The digits of a decimal are *chosen*. Taking an error there
spends part of the budget on nothing, and the error it spends is the worst kind — it is
**systematic**, identical on every read of that value forever, so it does not combine in
quadrature with anything and no amount of repetition averages it away.

## What goes wrong, and why "small enough" is not the test

The tempting criterion is the one that governs arithmetic: an error below the scale of `u` is
invisible, so six digits ought to be plenty. That criterion is wrong here for three separate
reasons, and the third is decisive.

1. It compares an *avoidable* error against a budget sized for *unavoidable* ones.
2. A fixed number of decimal **places** is not a number of significant **digits**. Six places is
   generous for a magnitude in the millions and has no significant digits at all below `10⁻⁶`,
   so the same printer is lavish and useless in one program, depending only on the scale the
   kind happens to be expressed at. This is how the failure survives review: it is invisible
   until a quantity arrives whose unit puts it near the printer's floor.
3. **A bound rounded the wrong way stops being a bound**, by any margin however small. A floor
   raised by one part in a million is no longer under the readings it was constructed to sit
   under; a guard band rounded toward the limit it protects buys a *smaller* consumer's risk
   than the one it states. Magnitude is not what is at stake — direction is, and to-nearest has
   no notion of direction.

Point 3 is why this module imports `Bounds`: the direction a magnitude must be rounded in is
determined by the **role** it plays, and `LowerBound`/`UpperBound` are exactly where that role
is recorded. The representation comes first here, the role-directed operations after it. The
dependency runs this way and not the other so that the many consumers of a bound do not acquire
a dependency on decimal text to get one.

## The carrier decides how many digits are enough

How many significant digits recover a value is a property of the **carrier**, not of the
number and not of the printer: 17 for an IEEE binary64, 9 for a binary32. So the budget belongs
in a class alongside the carrier's reader, and `showExact?` searches within it rather than
committing to a precision that would be wrong for some other carrier. Nothing here has to be
re-decided per kind or per magnitude.

**The reader is the specification.** `DecimalCarrier.ofDecimal?` must be the function the
*consumer* of the text uses — the elaborator that will read the emitted literal, the parser
that will read the record — and not a second decimal reader written for the occasion. Checking
a printer against a reader nobody will use answers a question nobody asked.

**Exactness is by construction, not by proof.** `showExact?` returns text only after reading
it back and finding the same value, so a `some` result carries its guarantee in the way it was
obtained. It is not a theorem: on a host carrier the reader and the printer are opaque foreign
functions (`UNCERTAINTY.md` §4.6 F says the same of the adequacy carrier's `Float`), so this is
a *checked* property of each value rather than a proved property of the pair. The distinction
is worth keeping in view — what is being relied on is that the check ran, which is why the API
offers no way to obtain the text without it.
-/

module

public import PropertyKindCalculus.Bounds
meta import PropertyKindCalculus.Bounds

public section -- pkc-blanket

namespace PropertyKindCalculus

/-- **Which way a magnitude is allowed to move when digits are dropped.**

Not a formatting preference — part of what the shortened number claims. `nearest` is the only
one that answers "which is closer", and it is the only one that cannot be used on a bound.
Directions are about the number line, so on a negative magnitude `down` still means *smaller*;
the carrier's renderer is responsible for that, not the caller. -/
inductive RoundingDirection where
  /-- Toward the nearer neighbour. Correct for a value, where the claim is a location. -/
  | nearest
  /-- Toward `-∞`. What a floor, a lower envelope, or any "at least this much" needs. -/
  | down
  /-- Toward `+∞`. What a ceiling, an upper envelope, or a margin that must not shrink needs. -/
  | up
deriving DecidableEq, Repr, Inhabited

/-- Reflecting a direction through zero, so a renderer working on `|x|` can restore the caller's
meaning for a negative magnitude. -/
def RoundingDirection.flip : RoundingDirection → RoundingDirection
  | .nearest => .nearest
  | .down => .up
  | .up => .down

/-- **What a carrier must supply to be written down and read back.**

Four things, of which only the first is about the carrier's *width* and the rest are about the
text: how many significant decimal digits distinguish any two of its values, where a value's
leading digit falls, how to render it at a chosen number of decimal places and in a chosen
direction, and — the one that must not be improvised — how the text will be read by whoever
receives it.

`toFixed?` may answer `none` for a `places` the carrier cannot scale to without losing the
integer it is building; that is a refusal, and it propagates to a refusal to write the value at
all rather than to a shortened form. -/
class DecimalCarrier (R : Type) where
  /-- Significant decimal digits sufficient to recover any value of `R`: 17 for an IEEE
  binary64, 9 for a binary32. The carrier's width, expressed in the alphabet the text uses. -/
  sigDigits : Nat
  /-- `⌊log₁₀ |x|⌋` — which decimal place the leading significant digit falls in, so a search
  need not start at zero for a small magnitude nor run past the end for a large one. Zero for a
  zero magnitude. Need only be right to within a place; the search absorbs the rest. -/
  decExponent : R → Int
  /-- `x` as decimal text with exactly `places` digits after the point, moved in the given
  direction, or `none` if this carrier cannot render it there. -/
  toFixed? : R → Nat → RoundingDirection → Option String
  /-- **The reader the text will actually meet.** Not a decimal parser written for this
  module: the elaborator that will read the emitted literal, or the parser that will read the
  file. A printer checked against the wrong reader is unchecked. -/
  ofDecimal? : String → Option R

namespace DecimalCarrier

variable {R : Type} [DecimalCarrier R] [BEq R]

/-- The decimal places worth trying for `x`: from the one that first reaches its leading
significant digit, through enough beyond it to spend the carrier's whole digit budget. The two
extra absorb a `decExponent` that landed a place out. -/
def placesToTry (x : R) : Nat × Nat :=
  let first := (-(decExponent x)).toNat
  (first, first + sigDigits (R := R) + 2)

/-- **`x` as the shortest decimal text that reads back as `x` itself**, or `none` if this
carrier can produce no such text.

The check is the specification: each candidate is read back through `ofDecimal?` and kept only
if it recovers the value. Shortest, because the search runs from the fewest places upward and
stops at the first that survives — a longer text says no more and is harder to read in a diff.

`none` is a real answer and must not be worked around by shortening. It means this value cannot
be written down at all in this carrier's fixed-point range — a magnitude so small that reaching
its digits would overflow the scaling, or one (a NaN) that is not equal to itself and so cannot
be recovered by any text. Both are refusals, and a value that cannot be written is a value that
must not be silently written differently. -/
def showExact? (x : R) : Option String :=
  let (lo, hi) := placesToTry x
  (List.range (hi + 1 - lo)).findSome? fun i =>
    (toFixed? x (lo + i) .nearest).bind fun s =>
      if ofDecimal? s == some x then some s else none

/-- Does `text` read back as `x`? The predicate `showExact?` establishes, asked separately so
that finished text can be audited by whoever did not print it — a printer that certifies its
own output is not a check, and the two are different programs in practice. -/
def readsBack (text : String) (x : R) : Bool := ofDecimal? text == some x

/-- **Rounding, as the round trip performed deliberately at reduced precision.** `none` if the
carrier cannot render or cannot re-read at that precision.

The direction is an explicit argument with no default, which is the point: at every call site
someone has to have decided what the shortened number is allowed to claim. The role-directed
operations below supply it from the role instead of leaving it to the caller. -/
def roundTo? (x : R) (places : Nat) (dir : RoundingDirection) : Option R :=
  (toFixed? x places dir).bind ofDecimal?

end DecimalCarrier

/-! ## The `Float` instance

The host carrier. Its reader is `ofDecimalLit?`, which is deliberately built from
`Float.ofScientific` — the function a Lean decimal literal elaborates to — so that a `Float`
certified here is one the *compiler* will read back from generated source. A reader assembled
from some other decimal parser would agree almost always, and the almost is the whole point. -/

namespace Float

/-- `10 ^ n` as a `Float`, by repeated multiplication: exact through `10 ^ 22`, the last power
of ten a binary64 holds exactly, and `+∞` far above the range any digit budget reaches. -/
def pow10 : Nat → Float
  | 0 => 1.0
  | n + 1 => 10.0 * pow10 n

/-- **The `Float` a Lean decimal literal denotes**, or `none` if the text is not a plain
decimal. Lean elaborates `0.00004262` as `OfScientific.ofScientific 4262 true 8`, so this is
that very function rather than a second decimal reader with its own rounding, and the answer is
therefore about the compiler that will read the text. -/
def ofDecimalLit? (s : String) : Option Float :=
  let (neg, body) := match s.toList with
    | '-' :: rest => (true, String.ofList rest)
    | _ => (false, s)
  let signed (v : Float) : Float := if neg then -v else v
  match body.splitOn "." with
  | [whole] => whole.toNat?.map fun m => signed (Float.ofScientific m true 0)
  | [whole, frac] =>
    if frac.isEmpty then none
    else (whole ++ frac).toNat?.map fun m => signed (Float.ofScientific m true frac.length)
  | _ => none

/-- `x` with exactly `places` digits after the point, moved in the given direction, or `none`
where scaling would leave the range in which the digits can be recovered as an integer.

The scaling is done on `|x|`, so the caller's direction is reflected for a negative magnitude:
`down` means toward `-∞` on the number line, which is *away* from zero on the magnitude. -/
def toFixedDecimal? (x : Float) (places : Nat) (dir : RoundingDirection) : Option String :=
  let scaled := x.abs * pow10 places
  if !scaled.isFinite || scaled ≥ 9.0e18 then none else
  let effective := if x < 0.0 then dir.flip else dir
  let rounded := match effective with
    | .nearest => scaled.round
    | .down => scaled.floor
    | .up => scaled.ceil
  let digits := toString rounded.toUInt64.toNat
  let padded := if digits.length ≤ places then
      String.ofList (List.replicate (places + 1 - digits.length) '0') ++ digits
    else digits
  let cs := padded.toList
  let body := if places == 0 then padded
    else String.ofList (cs.take (cs.length - places)) ++ "."
         ++ String.ofList (cs.drop (cs.length - places))
  some (if x < 0.0 then "-" ++ body else body)

end Float

/-- The host carrier's decimal representation. 17 significant digits recover any binary64.

**Fixed point, not scientific**, because the text's first consumer is generated source and a
diff a person reads. The cost is stated rather than hidden: a magnitude below about `10⁻²⁹⁰`
cannot be reached by scaling and `showExact?` refuses it. A carrier needing that range wants a
second instance whose `toFixed?` emits an exponent, and the reader to match. -/
instance : DecimalCarrier Float where
  sigDigits := 17
  decExponent x :=
    if x == 0.0 || !x.isFinite then 0
    else (Float.log10 x.abs).floor.toInt64.toInt
  toFixed? := Float.toFixedDecimal?
  ofDecimal? := Float.ofDecimalLit?

-- A whole number keeps no fraction, and the six trailing zeros a fixed-place printer would add
-- are not information.
#guard DecimalCarrier.showExact? (184.0 : Float) == some "184"
#guard DecimalCarrier.showExact? (78519000.0 : Float) == some "78519000"
#guard DecimalCarrier.showExact? (0.0 : Float) == some "0"
#guard DecimalCarrier.showExact? (0.0071 : Float) == some "0.0071"
#guard DecimalCarrier.showExact? (-0.5 : Float) == some "-0.5"
-- Magnitudes below a six-place printer's floor, where it has no significant digits left and
-- would answer `0.000043`, `0.000002` and `0.000051` — three different numbers.
#guard DecimalCarrier.showExact? (4.262e-05 : Float) == some "0.00004262"
#guard DecimalCarrier.showExact? (2.0212e-06 : Float) == some "0.0000020212"
#guard DecimalCarrier.showExact? (5.12881e-05 : Float) == some "0.0000512881"
-- The other half of the claim, which the search cannot make about itself: that the compiler
-- reads those texts back as those values. Fixed literals, elaborated by the same parser that
-- will elaborate any source this text is emitted into.
#guard (0.00004262 : Float) == 4.262e-05
#guard (0.0000020212 : Float) == 2.0212e-06
#guard (0.0000512881 : Float) == 5.12881e-05
-- Seventeen digits are needed and seventeen are available.
#guard (DecimalCarrier.showExact? (0.1 + 0.2 : Float)).isSome
#guard DecimalCarrier.readsBack "0.30000000000000004" (0.1 + 0.2 : Float)
#guard !DecimalCarrier.readsBack "0.3" (0.1 + 0.2 : Float)
-- A value not equal to itself is recoverable by no text, and is refused rather than approximated.
#guard (DecimalCarrier.showExact? (0.0 / 0.0 : Float)).isNone
-- Rounding is the round trip taken deliberately short, and the direction is the argument.
#guard DecimalCarrier.roundTo? (4.262e-05 : Float) 6 .nearest == some 4.3e-05
#guard DecimalCarrier.roundTo? (1754.0339 : Float) 2 .nearest == some 1754.03
#guard DecimalCarrier.roundTo? (1754.0339 : Float) 2 .down == some 1754.03
#guard DecimalCarrier.roundTo? (1754.0339 : Float) 2 .up == some 1754.04
-- On a negative magnitude the direction is the number line's, not the digits'.
#guard DecimalCarrier.roundTo? (-1754.0339 : Float) 2 .down == some (-1754.04)
#guard DecimalCarrier.roundTo? (-1754.0339 : Float) 2 .up == some (-1754.03)

/-! ## Rounding an endpoint — the direction is the role's, not the arithmetic's

**The operations are total and cannot break their own bound.** Each computes the shortened
magnitude and keeps it only if it moved the admissible way; otherwise it answers the original.
The fallback for "this carrier cannot render that precision" and for "the shortening went the
wrong way" is therefore the same one, and it is the safe one.

There is no `roundToNearest`, here or in `Bounds`, and none is coming. To-nearest is the
default everywhere else and it is right for a **value** — where the requirement is not a
direction at all but exactness, which is `showExact?` — while for the roles below it is wrong
half the time and silently. A rounding mode is not a formatting preference; it is part of what
the number claims.

### Which way is safe depends on something `Bounds` does not record

`LowerBound`/`UpperBound` carry a **geometric** role — which side of the number the endpoint is
on — and that is exactly what they were built for: it makes a comparison written backwards
unstateable. It is *not* enough to fix a rounding direction, and the gap is worth being precise
about, because the two readings look identical in the type and want opposite answers.

An endpoint is either **asserted** about a quantity or **imposed** upon one.

  * *Asserted*: "this process holds at most `X`" — the claim is `actual ≤ X`. Raising `X` keeps
    the claim true and gives slack away. **Safe direction: away from the quantity.**
  * *Imposed*: "`y` must be at most `L`" — the requirement is `y ≤ L`. Raising `L` admits values
    that should have failed. **Safe direction: toward the constrained region.**

So for the same geometric side the safe rounding is *inverted* between the two readings, and
all four combinations occur in this library. A residency ceiling and a coverage interval's upper
endpoint are asserted, and want `roundedUp`. A tolerance limit and the guarded acceptance limit
derived from it (`Uncertainty.Conformity.Tolerance`) are imposed, and want
`roundedDownAsRequirement` — rounding one *up* buys a larger consumer's risk than the record
stating it says it buys, which is the very failure the guard band exists to price.

Both pairs are provided and neither is the default, because no rule here can tell them apart:
the reading is a fact about why the bound exists, it lives in the caller, and a library that
guessed would be wrong silently in half the cases. The `AsRequirement` names are deliberately
the longer ones — not because that reading is rarer, but because it is the one where a reader
who is skimming would otherwise assume the wrong thing. -/

variable {k : KindOfProperty} {R : Type} [DecimalCarrier R]
  [LE R] [∀ x y : R, Decidable (x ≤ y)]

/-- **Shorten a lower endpoint to `places` decimals without letting it rise.** The shortened
magnitude if it sits at or below the original, the original otherwise — so a floor stays under
what it was built to sit under, whatever the carrier does with the digits. -/
def LowerBound.roundedDown (b : LowerBound k R) (places : Nat) : LowerBound k R :=
  match DecimalCarrier.roundTo? b.q.magnitude places .down with
  | some y => if y ≤ b.q.magnitude then ⟨⟨y⟩⟩ else b
  | none => b

/-- **Shorten an upper endpoint to `places` decimals without letting it fall** — the dual, and
the one a margin wants. A guard band shortened toward the limit it protects would buy a
*smaller* consumer's risk than the record stating it says it buys: inconsequential in size and
wrong in kind, since the number's whole job is to be on one particular side. -/
def UpperBound.roundedUp (b : UpperBound k R) (places : Nat) : UpperBound k R :=
  match DecimalCarrier.roundTo? b.q.magnitude places .up with
  | some y => if b.q.magnitude ≤ y then ⟨⟨y⟩⟩ else b
  | none => b

/-- **A shortened lower endpoint never rises**: it is either the original or one at or below
it. The disjunction is the honest form — "never rises" on its own would need reflexivity of
`≤`, which a host float carrier does not have, its NaN not being `≤` itself. Proved by cases
for that reason, and so the statement holds at every carrier rather than at ordered ones. -/
theorem LowerBound.roundedDown_safe (b : LowerBound k R) (places : Nat) :
    b.roundedDown places = b ∨ (b.roundedDown places).q.magnitude ≤ b.q.magnitude := by
  unfold LowerBound.roundedDown
  split
  · rename_i y _
    by_cases h : y ≤ b.q.magnitude
    · exact Or.inr (by simp [h])
    · exact Or.inl (by simp [h])
  · exact Or.inl rfl

/-- **A shortened upper endpoint never falls** — the dual of `LowerBound.roundedDown_safe`. -/
theorem UpperBound.roundedUp_safe (b : UpperBound k R) (places : Nat) :
    b.roundedUp places = b ∨ b.q.magnitude ≤ (b.roundedUp places).q.magnitude := by
  unfold UpperBound.roundedUp
  split
  · rename_i y _
    by_cases h : b.q.magnitude ≤ y
    · exact Or.inr (by simp [h])
    · exact Or.inl (by simp [h])
  · exact Or.inl rfl

/-- **Shorten an upper endpoint that is a REQUIREMENT, without letting it rise.**

The mirror of `roundedUp`, for the reading in which the endpoint is a limit something must not
exceed rather than a claim about what something holds. A tolerance limit, a budget a job is
allowed, a guarded acceptance limit: shortening one *upward* would admit values that should
have failed, and the size of the move is irrelevant — what broke is that the constraint is now
weaker than the one that was specified and priced.

Not a synonym for `LowerBound.roundedDown` despite moving the same way. This is an *upper*
endpoint, so every comparison against it still reads from above; only the admissible rounding
direction is shared, and conflating the two would put the comparison back the wrong way round —
which is what `Bounds` exists to prevent. -/
def UpperBound.roundedDownAsRequirement (b : UpperBound k R) (places : Nat) : UpperBound k R :=
  match DecimalCarrier.roundTo? b.q.magnitude places .down with
  | some y => if y ≤ b.q.magnitude then ⟨⟨y⟩⟩ else b
  | none => b

/-- **Shorten a lower endpoint that is a REQUIREMENT, without letting it fall** — the dual of
`UpperBound.roundedDownAsRequirement`, for a minimum something must meet rather than a floor
something is claimed to sit above. -/
def LowerBound.roundedUpAsRequirement (b : LowerBound k R) (places : Nat) : LowerBound k R :=
  match DecimalCarrier.roundTo? b.q.magnitude places .up with
  | some y => if b.q.magnitude ≤ y then ⟨⟨y⟩⟩ else b
  | none => b

/-- **A shortened upper requirement never rises**, so what it admits is never more than what
the specified limit admitted. -/
theorem UpperBound.roundedDownAsRequirement_safe (b : UpperBound k R) (places : Nat) :
    b.roundedDownAsRequirement places = b ∨
      (b.roundedDownAsRequirement places).q.magnitude ≤ b.q.magnitude := by
  unfold UpperBound.roundedDownAsRequirement
  split
  · rename_i y _
    by_cases h : y ≤ b.q.magnitude
    · exact Or.inr (by simp [h])
    · exact Or.inl (by simp [h])
  · exact Or.inl rfl

/-- **A shortened lower requirement never falls** — the dual of
`UpperBound.roundedDownAsRequirement_safe`. -/
theorem LowerBound.roundedUpAsRequirement_safe (b : LowerBound k R) (places : Nat) :
    b.roundedUpAsRequirement places = b ∨
      b.q.magnitude ≤ (b.roundedUpAsRequirement places).q.magnitude := by
  unfold LowerBound.roundedUpAsRequirement
  split
  · rename_i y _
    by_cases h : b.q.magnitude ≤ y
    · exact Or.inr (by simp [h])
    · exact Or.inl (by simp [h])
  · exact Or.inl rfl

end PropertyKindCalculus

end -- pkc-blanket
