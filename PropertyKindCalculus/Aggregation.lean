/-
# Aggregation — the weighted mean, carried at whatever numbers the task uses

`PropertyKindCalculus.Extensivity` states the aggregation modes over the *numeral* of a
property value: a sum (§13.5.1), a shared constant (§13.5.4), and a value the parts do not
determine. The centre-of-mass mode is neither, and it is the one that needs a *denominator* —
so it needs a carrier with a `/`, and it needs the denominator to be nonzero.

This module carries that mode at an arbitrary `Carrier`, for the same reason `Quantity k R` is
carried at an arbitrary carrier: the mean a proof reasons about and the mean a program runs are
the same definition read at two different numbers. `WeightedCarving R P` is the carving together
with its weights and the license the division needs; `mean` is the ratio of the two folds; `mk?`
is the license established at run time rather than assumed.

## What the license is worth is a property of the carrier, not of this structure

The field `total_ne_zero` is a *necessary* condition everywhere and a *sufficient* one only where
the carrier's arithmetic obeys the field laws. The three carriers this library ships make the
point in three different ways:

  * over `ℝ` (or any lawful carrier with a field's cancellation) the field is exactly what the
    mean law needs, and `WeightedCarving.mean_const` — the law that separates this mode from a
    sum and from a shared constant — is proved from it and from nothing else;
  * over TorchLean's `FP32` the field is still necessary, and no longer sufficient: the mean is
    computed on a rounded grid, so the law holds only up to an accumulated rounding budget, and
    the *specification's* denominator has a license of its own that this one does not imply
    (a total weight that is nonzero on the grid may be zero exactly, and conversely);
  * over `Float` the field is satisfied by `NaN`, which is not zero and is not a weight either.
    A carving whose every weight is `NaN` is a term of this type and its mean of a constant is
    `NaN`. Nothing is wrong with the field; what is absent is any carrier law to spend it on.

So this structure is not a claim that a mean is safe. It is the place a mean's one side condition
is written down, so that each rung can say what it is worth there and the executable rungs can be
made to state their own, stronger gate rather than inherit a license that does not travel.

## Two ways to make the license travel, and one that does not

The general fact is that `total_ne_zero` mentions the *carrier's* arithmetic, so it is a different
statement at every carrier and the statements are logically independent. A `WeightedCarving FP32`
knows its **rounded** total is nonzero; a law about the mean it approximates needs the **exact**
total to be nonzero; neither implies the other. Two remedies, in order of strength:

  * **Do not round the denominator.** `totalWeight_toSpec_of_exact` below: where the refinement's
    rounding is the identity — a count folded in `Nat`, an exact integer weight — forgetting the
    total *is* the total of the forgotten weights, so there is one license rather than two and
    `licenses_agree_of_exact` says so. This is the strongest fix and it is available whenever the
    weights are counts or indicators, which is the common case: a validity mask, a sample count,
    a pixel tally. It costs nothing and it removes the question instead of answering it.
  * **Keep the weights nonnegative.** Where the denominator genuinely is a floating-point fold of
    real-valued weights — masses, areas, durations — nonnegativity restores the equivalence, since
    the failures in both directions need cancellation. That is a fact about a specific carrier's
    rounding, so it is proved at that carrier
    (`Uncertainty.Adequacy.licenses_agree_of_nonneg`) rather than here.

What does **not** work is testing the computed total against zero and concluding the mean exists.
That is a guard on the denominator the machine formed, not on the quantity being defined, and it
fails in both directions.

`mean_const` lives in the `Dimension` library, over `ℝ`, beside the parallel-axis theorem — the
two aggregation laws whose arithmetic the Mathlib-free core cannot do.
-/

module

public import PropertyKindCalculus.Extensivity
-- Private scope only: the proofs below reduce through bodies sealed in
-- `PropertyKindCalculus.Extensivity`; `import all` gives this module the reduction without
-- exposing them to every consumer.
import all PropertyKindCalculus.Extensivity
public import PropertyKindCalculus.QuantityRefinement

public section -- pkc-blanket

namespace PropertyKindCalculus

universe u

/-! ## The two folds a mean is built from -/

/-- **The total weight of a carving** — the fold of the weights under the carrier's addition.
This is the mean's denominator, and the reason a mean needs a side condition at all. -/
@[expose] def totalWeight {R : Type} {P : Type u} [Carrier R] (w : P → R) (d : Decomposition P) : R :=
  d.fold w Carrier.add

/-- **The weighted sum of a per-part value** — the mean's numerator. Needs the carrier's `*`
beside its `+`, which is why it is not among the modes `Extensivity` can state. -/
@[expose] def weightedSum {R : Type} {P : Type u} [Carrier R] [Mul R]
    (w v : P → R) (d : Decomposition P) : R :=
  d.fold (fun p => w p * v p) Carrier.add

/-! ## The carving, its license, and the mean -/

/-- A **weighted carving** at carrier `R`: parts, a weight for each, and the license the mean
needs. The third field is the whole point — a mean is not a function of the parts alone, and the
denominator is where that shows. A carving with no weight is not a term of this type: where a
formula defined without the hypothesis silently returns the origin for a massless body, there is
here nothing to return it from.

What the license *licenses* depends on the carrier; the module docstring says how far each of
this library's three carriers takes it. -/
structure WeightedCarving (R : Type) (P : Type u) [Carrier R] where
  /-- How the whole is carved. -/
  parts : Decomposition P
  /-- The weight of each part — mass, for a centre of mass. -/
  weight : P → R
  /-- **The license**: the total weight is not the carrier's zero. -/
  total_ne_zero : totalWeight weight parts ≠ Carrier.zero

/-- The carving's total weight — the mean's denominator, named. -/
def WeightedCarving.total {R : Type} {P : Type u} [Carrier R] (c : WeightedCarving R P) : R :=
  totalWeight c.weight c.parts

/-- **The license travels with the carving.** Every weighted carving has nonzero total weight by
construction, so the massless case is not a term to be handled — it is unreachable. -/
theorem WeightedCarving.total_ne_zero' {R : Type} {P : Type u} [Carrier R]
    (c : WeightedCarving R P) : c.total ≠ Carrier.zero := c.total_ne_zero

/-- **The weighted mean** of a per-part value over a carving — the centre-of-mass mode of
aggregation, with the denominator's license already discharged by the carving. Asks the carrier
for `*` and `/` beside the `+` every mode needs; a carrier that has only `+` carries the
extensive mode and not this one. -/
@[expose] def WeightedCarving.mean {R : Type} {P : Type u} [Carrier R] [Mul R] [Div R]
    (c : WeightedCarving R P) (v : P → R) : R :=
  weightedSum c.weight v c.parts / totalWeight c.weight c.parts

/-! ## Establishing the license at run time -/

/-- **The license, decided rather than assumed.** A program does not have a proof that its
weights sum to something nonzero; it has the weights. `mk?` runs the carrier's own equality test
on the total and either produces the carving — license included — or refuses. The refusal is the
value that a formula without the hypothesis would have had to invent.

The test is the carrier's `DecidableEq`, so what `mk?` rejects is exactly what the carrier calls
zero. At `Float` that is a narrower set than the weights a mean should refuse (`NaN` passes),
which is not a defect of this constructor but the reason an executable rung states its own gate:
TorchLean's own `NF.checkedDiv` guards the same division on `b.val = 0`, and a soil or radiance
kernel guards it on a valid-sample *count* long before either. -/
def WeightedCarving.mk? {R : Type} {P : Type u} [Carrier R] [DecidableEq R]
    (parts : Decomposition P) (weight : P → R) : Option (WeightedCarving R P) :=
  if h : totalWeight weight parts = Carrier.zero then none else some ⟨parts, weight, h⟩

/-- **`mk?` refuses exactly the unlicensed carvings.** -/
theorem WeightedCarving.mk?_eq_none_iff {R : Type} {P : Type u} [Carrier R] [DecidableEq R]
    (parts : Decomposition P) (weight : P → R) :
    WeightedCarving.mk? parts weight = none ↔ totalWeight weight parts = Carrier.zero := by
  unfold WeightedCarving.mk?
  by_cases h : totalWeight weight parts = Carrier.zero <;> simp [h]

/-- **And accepts exactly the licensed ones**, returning the carving it was asked for. -/
theorem WeightedCarving.mk?_eq_some {R : Type} {P : Type u} [Carrier R] [DecidableEq R]
    {parts : Decomposition P} {weight : P → R}
    (h : totalWeight weight parts ≠ Carrier.zero) :
    WeightedCarving.mk? parts weight = some ⟨parts, weight, h⟩ :=
  dite_eq_right h

/-- **Nothing is lost by going through `mk?`**: an accepted carving is the one whose parts and
weights were offered, so a mean computed after the check is the mean of the data. -/
theorem WeightedCarving.mk?_isSome_iff {R : Type} {P : Type u} [Carrier R] [DecidableEq R]
    (parts : Decomposition P) (weight : P → R) :
    (WeightedCarving.mk? parts weight).isSome = true
      ↔ totalWeight weight parts ≠ Carrier.zero := by
  unfold WeightedCarving.mk?
  by_cases h : totalWeight weight parts = Carrier.zero <;> simp [h]

/-! ## The license under a refinement: when there is one, and when there are two -/

/-- **A refinement that does not round carries a carving's total exactly.** Where the spec-side
`round` is the identity, `toSpec` is an additive homomorphism, so forgetting the executable total
gives the total of the forgotten weights — the fold and the forgetting commute.

The hypothesis is the whole content. A refinement whose rounding is *not* the identity relates the
two totals only through the accumulated rounding of every join, and then they are two different
numbers about which two different things must be known. -/
theorem totalWeight_toSpec_of_exact {E S : Type} {P : Type u} [Carrier E] [Carrier S]
    [CarrierRefinement E S] (hround : ∀ s : S, CarrierRefinement.round (E := E) s = s)
    (w : P → E) : ∀ d : Decomposition P,
      CarrierRefinement.toSpec (S := S) (totalWeight w d)
        = totalWeight (fun p => CarrierRefinement.toSpec (S := S) (w p)) d
  | .atom _ => rfl
  | .union a b => by
      show CarrierRefinement.toSpec (S := S) (Carrier.add (totalWeight w a) (totalWeight w b))
        = Carrier.add _ _
      rw [CarrierRefinement.toSpec_add, hround,
        totalWeight_toSpec_of_exact hround w a, totalWeight_toSpec_of_exact hround w b]
      rfl

/-- **So a non-rounding carrier has one license, not two.** The executable carving's own field and
the specification's precondition are then the same statement read through `toSpec`, and a run-time
test of the computed total *is* a test of the quantity being defined. This is why a mean whose
denominator is a count should fold that count in an exact carrier and convert once, rather than
accumulate it in the same floating-point type as the numerator.

The second hypothesis is that `toSpec` reflects zero — it sends only the exec zero to the spec
zero. Every refinement in this library has it; it is stated rather than assumed because a lossy
`toSpec` that collapsed a subnormal to zero would not. -/
theorem licenses_agree_of_exact {E S : Type} {P : Type u} [Carrier E] [Carrier S]
    [CarrierRefinement E S] (hround : ∀ s : S, CarrierRefinement.round (E := E) s = s)
    (hzero : ∀ x : E, CarrierRefinement.toSpec (S := S) x = Carrier.zero → x = Carrier.zero)
    (w : P → E) (d : Decomposition P) :
    totalWeight w d ≠ Carrier.zero
      ↔ totalWeight (fun p => CarrierRefinement.toSpec (S := S) (w p)) d ≠ Carrier.zero := by
  rw [← totalWeight_toSpec_of_exact hround w d]
  constructor
  · exact fun hE hS => hE (hzero _ hS)
  · intro hS hE
    exact hS (by rw [hE]; exact CarrierRefinement.toSpec_zero)

/-! ## The mode at the kind layer

Everything above ranges over a bare carrier `R`. That is the right level for the numerical
statements — the binary32 bound in `Uncertainty.Adequacy.MeanBound` is about magnitudes and nothing
else — but it is not the level a user writes a model at, and it leaves the kind calculus with
nothing to say about a mean. Three things are missing at the carrier layer and appear here.

* **The weight kind has to be additive.** `totalWeight` folds with `Carrier.add`, which is available
  for every carrier and asks no permission. Folding *quantities* goes through `Quantity.add`, which
  demands a `DifferenceKind` — so `WeightedCarvingQ` carries that proof as a field, and a carving of
  a kind that does not sum cannot be built at all.
* **The three kinds are related, not independent.** A weight of kind `kw` times a value of kind `kv`
  is a quantity of some third kind, and dividing that by `kw` has to land back on `kv`. Those are
  exactly a `ProductKind` and a `QuotientKind` license, and `mean` asks for both.
* **The mean's own division is an R10 site.** `Quantity.div_refines` says what an executable
  quotient becomes in the spec carrier; `meanQ_refines` is that law at the mean's `div` node, which
  is the first place in the library where a model-level construct rides the quotient bridge.

The kinded layer computes nothing new: `totalWeightQ_magnitude` and `weightedSumQ_magnitude` say the
folds erase to the carrier ones, so every numerical theorem proved down there applies up here
unchanged. What the kind index buys is the three obligations above, discharged once at construction
instead of trusted at each use. -/

/-- The kinded weight fold. Same shape as `totalWeight`, but each join is a `Quantity.add` and so
needs the weight kind to admit differences. -/
def totalWeightQ {P : Type u} {R : Type} [Carrier R] {kw : KindOfProperty}
    (hd : DifferenceKind kw) (w : P → Quantity kw R) : Decomposition P → Quantity kw R
  | .atom p => w p
  | .union a b => Quantity.add hd (totalWeightQ hd w a) (totalWeightQ hd w b)

/-- The kinded weighted sum `Σ wᵢ·vᵢ`. Each leaf is a licensed product at `kwv`; each join is an
addition at `kwv`, which therefore has to admit differences too. -/
def weightedSumQ {P : Type u} {R : Type} [Carrier R] [Mul R] [ScalarCarrier R]
    {kw kv kwv : KindOfProperty} (hp : ProductKind kw kv kwv) (hd : DifferenceKind kwv)
    (w : P → Quantity kw R) (v : P → Quantity kv R) : Decomposition P → Quantity kwv R
  | .atom p => Quantity.mul hp (w p) (v p)
  | .union a b => Quantity.add hd (weightedSumQ hp hd w v a) (weightedSumQ hp hd w v b)

/-- **The kinded weight fold erases to the carrier one.** The kind index is a tag: it gates which
folds may be written, and contributes nothing to the value. -/
theorem totalWeightQ_magnitude {P : Type u} {R : Type} [Carrier R] {kw : KindOfProperty}
    (hd : DifferenceKind kw) (w : P → Quantity kw R) :
    ∀ d : Decomposition P,
      (totalWeightQ hd w d).magnitude = totalWeight (fun p => (w p).magnitude) d
  | .atom _ => rfl
  | .union a b => by
      show Carrier.add (totalWeightQ hd w a).magnitude (totalWeightQ hd w b).magnitude
        = Carrier.add _ _
      rw [totalWeightQ_magnitude hd w a, totalWeightQ_magnitude hd w b]
      rfl

/-- **And so does the weighted sum.** -/
theorem weightedSumQ_magnitude {P : Type u} {R : Type} [Carrier R] [Mul R] [ScalarCarrier R]
    {kw kv kwv : KindOfProperty} (hp : ProductKind kw kv kwv) (hd : DifferenceKind kwv)
    (w : P → Quantity kw R) (v : P → Quantity kv R) :
    ∀ d : Decomposition P,
      (weightedSumQ hp hd w v d).magnitude
        = weightedSum (fun p => (w p).magnitude) (fun p => (v p).magnitude) d
  | .atom _ => rfl
  | .union a b => by
      show Carrier.add (weightedSumQ hp hd w v a).magnitude (weightedSumQ hp hd w v b).magnitude
        = Carrier.add _ _
      rw [weightedSumQ_magnitude hp hd w v a, weightedSumQ_magnitude hp hd w v b]
      rfl

/-- **A carving whose weights are quantities of a summable kind, with a nonzero total.** The
`differenceKind` field is the permission to fold at all; `total_ne_zero` is the license to divide,
stated on the magnitude because that is where division can fail. -/
structure WeightedCarvingQ (R : Type) [Carrier R] (kw : KindOfProperty) (P : Type u) where
  /-- The carving of the whole into parts. -/
  parts : Decomposition P
  /-- The weight borne by each part. -/
  weight : P → Quantity kw R
  /-- The weight kind admits differences, so the weights may be summed. -/
  differenceKind : DifferenceKind kw
  /-- The total weight is nonzero — the mean's denominator is licensed. -/
  total_ne_zero : (totalWeightQ differenceKind weight parts).magnitude ≠ Carrier.zero

/-- The carving's total weight, at the weight kind. -/
def WeightedCarvingQ.total {R : Type} {P : Type u} [Carrier R] {kw : KindOfProperty}
    (c : WeightedCarvingQ R kw P) : Quantity kw R :=
  totalWeightQ c.differenceKind c.weight c.parts

/-- **The kinded weighted mean.** `Σ wᵢ·vᵢ` at the product kind, divided by `Σ wᵢ` at the weight
kind, landing back at the value kind — which is what the `QuotientKind` license asserts and what
makes the result a mean *of the values* rather than of something else. -/
def WeightedCarvingQ.mean {R : Type} {P : Type u} [Carrier R] [Mul R] [Div R] [ScalarCarrier R]
    {kw kv kwv : KindOfProperty} (c : WeightedCarvingQ R kw P)
    (hp : ProductKind kw kv kwv) (hq : QuotientKind kwv kw kv) (hd : DifferenceKind kwv)
    (v : P → Quantity kv R) : Quantity kv R :=
  Quantity.div hq (weightedSumQ hp hd c.weight v c.parts) c.total

/-- Forget the kinds: the carrier-level carving the kinded one denotes. Its license is the kinded
one's, transported along `totalWeightQ_magnitude`. -/
def WeightedCarvingQ.toCarving {R : Type} {P : Type u} [Carrier R] {kw : KindOfProperty}
    (c : WeightedCarvingQ R kw P) : WeightedCarving R P :=
  ⟨c.parts, fun p => (c.weight p).magnitude,
    by rw [← totalWeightQ_magnitude c.differenceKind c.weight c.parts]; exact c.total_ne_zero⟩

/-- **The kinded mean erases to the carrier mean.** This is the bridge that lets the binary32 bound
of `Uncertainty.Adequacy.MeanBound`, which is stated about magnitudes, apply to a mean a user wrote
with kinds on. -/
theorem WeightedCarvingQ.mean_magnitude {R : Type} {P : Type u}
    [Carrier R] [Mul R] [Div R] [ScalarCarrier R] {kw kv kwv : KindOfProperty}
    (c : WeightedCarvingQ R kw P) (hp : ProductKind kw kv kwv) (hq : QuotientKind kwv kw kv)
    (hd : DifferenceKind kwv) (v : P → Quantity kv R) :
    (c.mean hp hq hd v).magnitude = c.toCarving.mean (fun p => (v p).magnitude) := by
  show (weightedSumQ hp hd c.weight v c.parts).magnitude / (totalWeightQ _ c.weight c.parts).magnitude
    = _
  rw [weightedSumQ_magnitude, totalWeightQ_magnitude]
  rfl

/-- Build a kinded carving when the total is decidably nonzero, or report that it is not. -/
def WeightedCarvingQ.mk? {R : Type} {P : Type u} [Carrier R] [DecidableEq R] {kw : KindOfProperty}
    (hd : DifferenceKind kw) (parts : Decomposition P) (weight : P → Quantity kw R) :
    Option (WeightedCarvingQ R kw P) :=
  if h : (totalWeightQ hd weight parts).magnitude = Carrier.zero then none
  else some ⟨parts, weight, hd, h⟩

/-- `mk?` refuses exactly when the total weight vanishes. -/
theorem WeightedCarvingQ.mk?_eq_none_iff {R : Type} {P : Type u} [Carrier R] [DecidableEq R]
    {kw : KindOfProperty} (hd : DifferenceKind kw) (parts : Decomposition P)
    (weight : P → Quantity kw R) :
    WeightedCarvingQ.mk? hd parts weight = none
      ↔ (totalWeightQ hd weight parts).magnitude = Carrier.zero := by
  unfold WeightedCarvingQ.mk?
  by_cases h : (totalWeightQ hd weight parts).magnitude = Carrier.zero <;> simp [h]

/-! ### The mean's division as an R10 site

`Quantity.div_refines` is the exec/spec bridge across a kind quotient. Until now nothing in the
library divided at the kind layer, so the law had no consumer that was not a test. The kinded mean
is one: its single `div` node is exactly a `QuotientKind kwv kw kv` site, and the theorem below is
`div_refines` read there.

What it does *not* say is that the whole mean commutes with `toSpec` — the folds above it round at
every join, and `licenses_agree_of_exact`'s hypothesis is precisely what would be needed to push
`toSpec` through them. The division is one step of that argument, stated where it is true
unconditionally. -/

/-- **The mean's quotient refines (R10).** Forgetting the executable mean to the spec carrier is the
rounding of the spec quotient of the forgotten numerator and denominator — `Quantity.div_refines` at
the mean's own division node. -/
theorem WeightedCarvingQ.mean_div_refines {E S : Type} {P : Type u}
    [Carrier E] [Carrier S] [Mul E] [Mul S] [Div E] [Div S] [ScalarCarrier E] [ScalarCarrier S]
    [CarrierRefinement E S] [DivRefinement E S] {kw kv kwv : KindOfProperty}
    (c : WeightedCarvingQ E kw P) (hp : ProductKind kw kv kwv) (hq : QuotientKind kwv kw kv)
    (hd : DifferenceKind kwv) (v : P → Quantity kv E) :
    (Quantity.toSpec (c.mean hp hq hd v) : Quantity kv S)
      = Quantity.roundBy (CarrierRefinement.round (E := E))
          (Quantity.div hq
            (Quantity.toSpec (weightedSumQ hp hd c.weight v c.parts))
            (Quantity.toSpec c.total)) :=
  Quantity.div_refines hq _ _

end PropertyKindCalculus

end -- pkc-blanket
