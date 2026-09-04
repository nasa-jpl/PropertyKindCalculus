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

`mean_const` therefore lives in the `Dimension` library, over `ℝ`, beside the parallel-axis
theorem — the two aggregation laws whose arithmetic the Mathlib-free core cannot do.
-/

import PropertyKindCalculus.Extensivity
import PropertyKindCalculus.Quantity

namespace PropertyKindCalculus

universe u

/-! ## The two folds a mean is built from -/

/-- **The total weight of a carving** — the fold of the weights under the carrier's addition.
This is the mean's denominator, and the reason a mean needs a side condition at all. -/
def totalWeight {R : Type} {P : Type u} [Carrier R] (w : P → R) (d : Decomposition P) : R :=
  d.fold w Carrier.add

/-- **The weighted sum of a per-part value** — the mean's numerator. Needs the carrier's `*`
beside its `+`, which is why it is not among the modes `Extensivity` can state. -/
def weightedSum {R : Type} {P : Type u} [Carrier R] [Mul R]
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
def WeightedCarving.mean {R : Type} {P : Type u} [Carrier R] [Mul R] [Div R]
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
  dif_neg h

/-- **Nothing is lost by going through `mk?`**: an accepted carving is the one whose parts and
weights were offered, so a mean computed after the check is the mean of the data. -/
theorem WeightedCarving.mk?_isSome_iff {R : Type} {P : Type u} [Carrier R] [DecidableEq R]
    (parts : Decomposition P) (weight : P → R) :
    (WeightedCarving.mk? parts weight).isSome = true
      ↔ totalWeight weight parts ≠ Carrier.zero := by
  unfold WeightedCarving.mk?
  by_cases h : totalWeight weight parts = Carrier.zero <;> simp [h]

end PropertyKindCalculus
