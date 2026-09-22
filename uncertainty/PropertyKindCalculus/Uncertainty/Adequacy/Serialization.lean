/-
`PropertyKindCalculus.Uncertainty.Adequacy.Serialization` — **the fifth adequacy sub-property**
(`UNCERTAINTY.md` §4.2): the rounding that happens when a quantity is written down.

The four sub-properties in §4.2's table are all about roundings *inside* an evaluation —
absorption at an addition, cancellation at a subtraction, accumulated `(1+δ)` noise over the
DAG, and the dynamic range the whole box needs. Each is a rounding the carrier forces on you.
This module is about the one at the **edge**: a magnitude leaves as decimal text and comes back,
and `read ∘ write` is a map from carrier values to carrier values which is the identity only if
the text carried enough digits.

It is easy not to see this as a rounding. It has no operator symbol, it happens in a printer,
and the printer looks like a display concern. But a constant compiled from a record, a value
parsed from a file, a number handed between two programs — each is an evaluation whose first
step is a rounding nobody put in the budget.

## Why the criterion here is exactness, and not "small compared with `u`"

Every other sub-property is graded against the uncertainty scale: an error below half a ulp of
the accumulator is *invisible*, and that is the right test because the error is **forced**. The
same test applied here gives the wrong answer, for three reasons that stack.

1. **The error is avoidable.** The digits of a decimal are chosen, not imposed by a carrier
   width. Spending budget on an error you could have declined to take is not a trade-off; the
   budget exists for the roundings arithmetic cannot avoid.
2. **The error is systematic, not dispersive.** A value written short is written short every
   time it is read, identically. It does not combine in quadrature with anything, no repetition
   averages it out, and `u_c² = Σ cᵢ²u(xᵢ)²` is the wrong machine for it. A budget that
   absorbed it would be reporting a bias as a dispersion — the same error `Conformity` exists
   to keep out of a guard band.
3. **For a bound it is not a magnitude question at all.** A floor written up by one part in a
   million is no longer under what it was constructed to sit under, and no tolerance reaches
   that, because what broke is the *direction*. This is why `Decimal`'s role-directed
   operations exist, and why a serialization verdict has to know which role it is looking at.

Reason 3 is the decisive one, and it is what makes this a sub-property rather than a lint: the
other four can be discharged by an inequality on magnitudes, and this one cannot.

## Why this is not a counter in `AdequacyReport`

`AdequacyReport` accumulates sites found *while a model runs* at the `Adequacy` carrier, and
that carrier never serializes — the boundary is crossed before it is seeded and after it has
finished. Adding a third counter there would put an edge fact inside an interior report, so an
evaluation that is adequate throughout could be reported inadequate because of something that
happened before it started, and a `merge` of two operands' reports would combine boundary
crossings that never composed. The verdict here is therefore its own type, produced once per
crossing, and a caller that wants both states both.

Mathlib- and TorchLean-free: the whole content is `Decimal`'s reader against the value, which
is decidable at any host carrier. What it cannot do is *prove* the crossing exact — the reader
and the printer are opaque at a host carrier (`UNCERTAINTY.md` §4.6 F, which says the same of
the `Adequacy` carrier's `Float`) — so this is a checked property of each crossing, and the
API offers no way to obtain a verdict without running the check.
-/

module

public import PropertyKindCalculus.Decimal
public import PropertyKindCalculus.Uncertainty.Carriers

public section -- pkc-blanket
@[expose] section -- pkc-blanket-expose

namespace PropertyKindCalculus.Uncertainty.Adequacy

open PropertyKindCalculus

/-- **What became of a magnitude on its way through text.**

Four outcomes, not two, because "did not survive exactly" splits on whether a *role* was
respected — and that split is the whole reason the property is not an inequality. -/
inductive SerializationVerdict where
  /-- The text reads back as the value. Nothing entered the budget; this is the only outcome
  that is unconditionally adequate, and it is always available to a value the carrier can
  render at all. -/
  | exact
  /-- The text does not read back, but moved the way this magnitude's role permits — a floor
  written lower, a ceiling or a margin written higher. Adequate *as a bound*: what it claims is
  still true, and weaker. It is not adequate as a **value**, and a record stating it as an
  estimate is stating a number nobody measured. -/
  | shortenedSafely
  /-- The text does not read back and moved the way the role forbids. Never adequate, at any
  magnitude: a floor that rose is not a floor, a margin that shrank buys a smaller consumer's
  risk than it states. Size is not a defence. -/
  | shortenedUnsafely
  /-- No text this carrier can render reads back as this value — a magnitude outside the
  renderer's reach, or one not equal to itself. A refusal, and not a licence to write something
  nearby: a value that cannot be written down must not be silently written differently. -/
  | unrepresentable
deriving DecidableEq, Repr, Inhabited

/-- Is this crossing adequate for a magnitude carrying **no** role — an estimate, a coefficient,
a reading? Only exactness will do: a value's claim is its location, and a shortened location is
a different claim. -/
def SerializationVerdict.adequateAsValue : SerializationVerdict → Bool
  | .exact => true
  | _ => false

/-- Is this crossing adequate for a magnitude whose job is to bound? Exactness, or a shortening
that went the way the role allows — the bound still holds, with a little slack given away. -/
def SerializationVerdict.adequateAsBound : SerializationVerdict → Bool
  | .exact => true
  | .shortenedSafely => true
  | _ => false

variable {k : KindOfProperty} {R : Type} [DecimalCarrier R] [BEq R] [LE R]
  [∀ x y : R, Decidable (x ≤ y)]

/-- **The verdict for a magnitude with no role**: it survived or it did not. A caller holding a
role should use `verdictAtLower`/`verdictAtUpper`, which can tell a safe shortening from a
fatal one; here there is no role, so any shortening is fatal and the two failing outcomes
collapse. -/
def verdictOfValue (x : R) (text : String) : SerializationVerdict :=
  if DecimalCarrier.readsBack text x then .exact
  else match (DecimalCarrier.ofDecimal? text : Option R) with
    | some _ => .shortenedUnsafely
    | none => .unrepresentable

/-- **The verdict for a lower endpoint**: a shortening that moved down is safe, one that moved
up is not, and the direction is read off the text rather than assumed from how it was produced
— which is the point of checking finished text at all. -/
def verdictAtLower (b : LowerBound k R) (text : String) : SerializationVerdict :=
  if DecimalCarrier.readsBack text b.q.magnitude then .exact
  else match DecimalCarrier.ofDecimal? text with
    | some y => if y ≤ b.q.magnitude then .shortenedSafely else .shortenedUnsafely
    | none => .unrepresentable

/-- **The verdict for an upper endpoint** — the dual of `verdictAtLower`. -/
def verdictAtUpper (b : UpperBound k R) (text : String) : SerializationVerdict :=
  if DecimalCarrier.readsBack text b.q.magnitude then .exact
  else match DecimalCarrier.ofDecimal? text with
    | some y => if b.q.magnitude ≤ y then .shortenedSafely else .shortenedUnsafely
    | none => .unrepresentable

/-- **The displacement this crossing introduced**, at the magnitude's own kind, or `none` if
the text does not read back at all.

Provided as *evidence*, not as a criterion. It is what a reader asks for when triaging a
crossing that already failed — how far did it move, against what the value is known to — and
it is exactly what must not be turned into a tolerance, for the three reasons the module
header gives. A displacement of zero is the same statement as `.exact`. -/
def displacement {k' : KindOfProperty} {R' : Type} [DecimalCarrier R'] [Sub R']
    (x : Quantity k' R') (text : String) : Option (Quantity k' R') :=
  (DecimalCarrier.ofDecimal? text).map fun y => ⟨y - x.magnitude⟩

/-- **A crossing that is exact leaves the budget alone.** The displacement of an `.exact`
crossing is zero — stated as the definitional fact it is, so that the claim "serialization
contributes nothing when it round-trips" is a theorem in the layer that would otherwise have
to assert it in prose. -/
theorem displacement_eq_zero_of_exact {k' : KindOfProperty} {R' : Type} [DecimalCarrier R']
    [Sub R'] (x : Quantity k' R') (text : String)
    (h : DecimalCarrier.ofDecimal? text = some x.magnitude) :
    displacement x text = some ⟨x.magnitude - x.magnitude⟩ := by
  unfold displacement
  rw [h]
  rfl

end PropertyKindCalculus.Uncertainty.Adequacy

end -- pkc-blanket-expose
end -- pkc-blanket
