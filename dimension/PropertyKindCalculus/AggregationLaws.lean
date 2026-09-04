/-
# The two aggregation laws whose arithmetic the core cannot do

`PropertyKindCalculus.Extensivity` states the aggregation modes over the numeral of a property
value, in the Mathlib-free core: a sum (§13.5.1), a shared constant (§13.5.4), and a value the
parts do not determine at all. Two further laws belong beside them and cannot be stated there,
each for a specific arithmetic reason.

  * **The weighted mean** — the centre-of-mass mode, neither a sum nor a constant. Its law is
    that the mean of a constant is that constant, which needs *division*, and its side
    condition is that the total weight is nonzero. `WeightedCarving` carries that condition as
    a field, so a whole with no weight is not a term of the type: where a formula defined
    without the hypothesis silently returns the origin for a massless body, there is here
    nothing to return it from.
  * **The parallel-axis theorem** — the general `Transports` law for `inertiaAbout`. A moment
    of inertia is extensive about each axis separately (`inertiaMeasurement_extensiveAbout`,
    proved in core by `rfl`); what the core exhibits but cannot prove is the correction that
    relates two axes, because normalizing `w·(x−a)² − w·(x−b)²` is ring arithmetic over `Int`.
    The correction is built from two summaries of the very same carving — its total mass and
    its first moment — and both are folds the core already has, which is the reason this is a
    *metrological* statement and not just an algebraic identity: transporting an aggregate
    costs only quantities the parts already carry.

Lives in the `Dimension` library because both need Mathlib — `ℝ` for the first, `ring` for the
second — the one dependency kept out of the core spine.
-/

import PropertyKindCalculus.Extensivity
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Ring

namespace PropertyKindCalculus

universe u

/-! ## The weighted mean, with its license attached -/

/-- A **weighted carving**: parts, a weight for each, and the license the mean needs. The
third field is the whole point — a mean is not a function of the parts alone, and the
denominator is where that shows. -/
structure WeightedCarving (P : Type u) where
  /-- How the whole is carved. -/
  parts : Decomposition P
  /-- The weight of each part — mass, for a centre of mass. -/
  weight : P → ℝ
  /-- **The license**: the total weight is not zero. -/
  total_ne_zero : parts.fold weight (· + ·) ≠ 0

/-- The weighted mean of a per-part value over a carving — the centre-of-mass mode of
aggregation, with the denominator's license already discharged by the carving. -/
noncomputable def WeightedCarving.mean {P : Type u} (c : WeightedCarving P) (v : P → ℝ) : ℝ :=
  c.parts.fold (fun p => c.weight p * v p) (· + ·) / c.parts.fold c.weight (· + ·)

/-- A constant factors out of the fold — the one arithmetic fact the mean law needs. -/
theorem fold_mul_const {P : Type u} (w : P → ℝ) (v : ℝ) : ∀ d : Decomposition P,
    d.fold (fun p => w p * v) (· + ·) = d.fold w (· + ·) * v
  | .atom _ => rfl
  | .union a b => by
      simp only [Decomposition.fold, fold_mul_const w v a, fold_mul_const w v b, add_mul]

/-- **The mean of a constant is that constant.** The law that distinguishes this mode from a
sum and from a shared constant at once: put every part at the same place and the whole is at
that place, whatever the weights. The proof uses the license, which is why it is a field. -/
theorem WeightedCarving.mean_const {P : Type u} (c : WeightedCarving P) (v : ℝ) :
    c.mean (fun _ => v) = v := by
  rw [WeightedCarving.mean, fold_mul_const]
  exact mul_div_cancel_left₀ v c.total_ne_zero

/-- **The license travels with the carving.** Every weighted carving has nonzero total weight
by construction, so the massless case is not a term to be handled — it is unreachable. -/
theorem WeightedCarving.total_ne_zero' {P : Type u} (c : WeightedCarving P) :
    c.parts.fold c.weight (· + ·) ≠ 0 := c.total_ne_zero

/-! ## The parallel-axis theorem as a transport law -/

/-- **The parallel-axis theorem, over any carving of any part type.** The moment of inertia
about `a` is the moment about `b` plus a correction built from the carving's *first moment*
and its *total mass* — two extensive summaries of the same parts. Taking `b` at the centre of
mass makes the first moment vanish and leaves the textbook `M d²`.

Proved by induction on the carving: at a leaf it is `ring` on
`w·(x−a)² = w·(x−b)² + 2(b−a)·w·x + (a²−b²)·w`, and at a join the three folds distribute. -/
theorem parallelAxis {O : Type u} (w x : O → Int) (a b : Int) : ∀ d : Decomposition O,
    inertiaAbout w x a d
      = inertiaAbout w x b d
        + (2 * (b - a) * firstMoment w x d + (a * a - b * b) * partTotal w d)
  | .atom p => by
      show w p * ((x p - a) * (x p - a))
        = w p * ((x p - b) * (x p - b)) + (2 * (b - a) * (w p * x p) + (a * a - b * b) * w p)
      ring
  | .union d₁ d₂ => by
      show inertiaAbout w x a d₁ + inertiaAbout w x a d₂
        = (inertiaAbout w x b d₁ + inertiaAbout w x b d₂)
          + (2 * (b - a) * (firstMoment w x d₁ + firstMoment w x d₂)
             + (a * a - b * b) * (partTotal w d₁ + partTotal w d₂))
      rw [parallelAxis w x a b d₁, parallelAxis w x a b d₂]
      ring

/-- **So a moment of inertia transports**, and `extensiveAbout_mixed` applies to it: parts read
about their own axes aggregate to the whole once each is corrected. -/
theorem inertiaMeasurement_transports {O : Type u} (w x : O → Int) :
    Transports (inertiaMeasurement w x)
      (fun a b d => 2 * (b - a) * firstMoment w x d + (a * a - b * b) * partTotal w d) :=
  ⟨fun a b d => parallelAxis w x a b d⟩

/-- The parallel-axis correction at the rod's own mass and position. -/
abbrev rodCorr : Int → Int → Decomposition PointMass → Int := fun a b d =>
  2 * (b - a) * firstMoment PointMass.mass PointMass.position d
    + (a * a - b * b) * partTotal PointMass.mass d

/-- **The rod's mixed-axis sum, repaired.** Core exhibits the failure — each mass read about
an axis through itself contributes nothing, where the rod about its centre reads 2. Here is
the number that closes the gap, from the general law rather than from arithmetic on this
example. -/
theorem rod_mixed_axes_corrected :
    (rodInertia 0 rod).numeral
      = ((rodInertia (-1) rodLeft).numeral + rodCorr 0 (-1) rodLeft)
        + ((rodInertia 1 rodRight).numeral + rodCorr 0 1 rodRight) :=
  extensiveAbout_mixed (inertiaMeasurement_extensiveAbout _ _)
    (inertiaMeasurement_transports _ _) 0 (-1) 1 rodLeft rodRight

/-- Each correction is 1 — a unit mass moved a unit distance — and they sum to the 2 the naive
sum was missing. -/
theorem rod_corrections : rodCorr 0 (-1) rodLeft = 1 ∧ rodCorr 0 1 rodRight = 1 := by decide

end PropertyKindCalculus
