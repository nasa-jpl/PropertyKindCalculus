/-
# The aggregation laws whose arithmetic the core cannot do

`PropertyKindCalculus.Extensivity` states the aggregation modes over the numeral of a property
value, in the Mathlib-free core: a sum (§13.5.1), a shared constant (§13.5.4), and a value the
parts do not determine at all. Further laws belong beside them and cannot be stated there,
each for a specific arithmetic reason.

  * **The weighted mean** — the centre-of-mass mode, neither a sum nor a constant. The mode
    itself is carrier-parametric and lives in the core (`PropertyKindCalculus.Aggregation`):
    `WeightedCarving R P`, its nonzero-total license, `mean`, and the `mk?` that establishes
    the license at run time. What cannot live there is its *law* — that the mean of a constant
    is that constant — because the proof cancels the denominator against the numerator, and
    cancellation is a field law. So the structure travels down to every carrier and the law
    stops at the lawful ones; `mean_const` is stated here, over `ℝ`, and is the only thing the
    license is spent on.
  * **The parallel-axis theorem** — the general `Transports` law for `inertiaAbout`. A moment
    of inertia is extensive about each axis separately (`inertiaMeasurement_extensiveAbout`,
    proved in core by `rfl`); what the core exhibits but cannot prove is the correction that
    relates two axes, because normalizing `w·(x−a)² − w·(x−b)²` is ring arithmetic over `Int`.
    The correction is built from two summaries of the very same carving — its total mass and
    its first moment — and both are folds the core already has, which is the reason this is a
    *metrological* statement and not just an algebraic identity: transporting an aggregate
    costs only quantities the parts already carry.
  * **The rest of the transport tower** — the Galilean boost for a momentum (`momentumBoost`,
    priced in the carving's mass) and the change of reference point for an angular momentum
    (`angularMomentumTransport`, priced in the carving's momentum). With the parallel-axis
    theorem these share one shape: each correction is computable from summaries that are
    themselves extensive one rung down, and the tower grounds out in the one unconditional
    §13.5.1 kind — which is what makes mixed-parameter aggregation checkable all the way
    down rather than conditionally correct at every rung.

Lives in the `Dimension` library because these need Mathlib — `ℝ` for the mean, `ring` for
the transports — the one dependency kept out of the core spine.
-/

import PropertyKindCalculus.Aggregation
import PropertyKindCalculus.QuantityReal
import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.Ring

namespace PropertyKindCalculus

universe u

/-! ## The law of the weighted mean, at the carrier that can prove it -/

/-- A constant factors out of the weighted fold — the one arithmetic fact the mean law needs.
Stated over `ℝ`'s own `+` and `*`, which is what `weightedSum` and `totalWeight` unfold to at
the real carrier. -/
theorem fold_mul_const {P : Type u} (w : P → ℝ) (v : ℝ) : ∀ d : Decomposition P,
    weightedSum w (fun _ => v) d = totalWeight w d * v
  | .atom _ => rfl
  | .union a b => by
      show weightedSum w (fun _ => v) a + weightedSum w (fun _ => v) b
        = (totalWeight w a + totalWeight w b) * v
      rw [fold_mul_const w v a, fold_mul_const w v b, add_mul]

/-- **The mean of a constant is that constant.** The law that distinguishes this mode from a
sum and from a shared constant at once: put every part at the same place and the whole is at
that place, whatever the weights. The proof uses the license, which is why it is a field — and
it uses cancellation, which is why the law is here and the structure is in the core. -/
theorem WeightedCarving.mean_const {P : Type u} (c : WeightedCarving ℝ P) (v : ℝ) :
    c.mean (fun _ => v) = v := by
  rw [WeightedCarving.mean, fold_mul_const]
  exact mul_div_cancel_left₀ v c.total_ne_zero

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

/-! ## The rest of the transport tower — each correction priced one rung down -/

/-- **The Galilean boost, as a transport law**: the momentum read in the frame at `u₁` is the
momentum read at `u₂` plus the carving's mass times the frame difference — the correction is
the one unconditionally extensive summary there is, which is the tower's ground floor. -/
theorem momentumBoost {O : Type u} (w v : O → Int) (u₁ u₂ : Int) :
    ∀ d : Decomposition O,
      momentumIn w v u₁ d = momentumIn w v u₂ d + partTotal w d * (u₂ - u₁)
  | .atom p => by
      show w p * (v p - u₁) = w p * (v p - u₂) + w p * (u₂ - u₁)
      ring
  | .union a b => by
      show momentumIn w v u₁ a + momentumIn w v u₁ b
        = (momentumIn w v u₂ a + momentumIn w v u₂ b)
          + (partTotal w a + partTotal w b) * (u₂ - u₁)
      rw [momentumBoost w v u₁ u₂ a, momentumBoost w v u₁ u₂ b]
      ring

/-- So a momentum transports, and `extensiveAbout_mixed` applies to it. -/
theorem momentumMeasurement_transports {O : Type u} (w v : O → Int) :
    Transports (momentumMeasurement w v) (fun u₁ u₂ d => partTotal w d * (u₂ - u₁)) :=
  ⟨fun u₁ u₂ d => momentumBoost w v u₁ u₂ d⟩

/-- The boost correction at the drifting pair's own masses. -/
abbrev driftCorr : Int → Int → Decomposition MovingPointMass → Int := fun u₁ u₂ d =>
  partTotal MovingPointMass.mass d * (u₂ - u₁)

/-- **The rest-frame sum, repaired.** Core exhibits each mass reading zero in its own rest
frame where the laboratory reads the pair at 3; the two boost corrections close the gap, from
the general law rather than from arithmetic on this pair. -/
theorem drift_rest_frames_corrected :
    (driftMomentum 0 driftPair).numeral
      = ((driftMomentum 1 driftA).numeral + driftCorr 0 1 driftA)
        + ((driftMomentum 2 driftB).numeral + driftCorr 0 2 driftB) :=
  extensiveAbout_mixed (momentumMeasurement_extensiveAbout _ _)
    (momentumMeasurement_transports _ _) 0 1 2 driftA driftB

/-- Each correction is the part's own laboratory momentum — 1 and 2 — and they sum to the 3
the rest-frame sum was missing. -/
theorem drift_corrections : driftCorr 0 1 driftA = 1 ∧ driftCorr 0 2 driftB = 2 := by decide

/-- **An angular momentum transports between reference points, priced in momentum**:
`L_a = L_b + (b − a) × p`, componentwise over any carving, with the momentum components as
the first moments of the velocities. Taking `b` at a part's own mass centre and `a` at the
system's shows the split of an angular momentum into spin and orbital terms is this law and
not a new principle — and a part whose momentum vanishes reads the same about every point,
which is why a parked flywheel's spin may be summed untransported and a translating one's
may not. -/
theorem angularMomentumTransport {O : Type u} (w x y vx vy : O → Int) (a b : Int × Int) :
    ∀ d : Decomposition O,
      angularMomentumAbout w x y vx vy a d
        = angularMomentumAbout w x y vx vy b d
          + ((b.1 - a.1) * firstMoment w vy d - (b.2 - a.2) * firstMoment w vx d)
  | .atom p => by
      show w p * ((x p - a.1) * vy p - (y p - a.2) * vx p)
        = w p * ((x p - b.1) * vy p - (y p - b.2) * vx p)
          + ((b.1 - a.1) * (w p * vy p) - (b.2 - a.2) * (w p * vx p))
      ring
  | .union d₁ d₂ => by
      show angularMomentumAbout w x y vx vy a d₁ + angularMomentumAbout w x y vx vy a d₂
        = (angularMomentumAbout w x y vx vy b d₁ + angularMomentumAbout w x y vx vy b d₂)
          + ((b.1 - a.1) * (firstMoment w vy d₁ + firstMoment w vy d₂)
             - (b.2 - a.2) * (firstMoment w vx d₁ + firstMoment w vx d₂))
      rw [angularMomentumTransport w x y vx vy a b d₁,
        angularMomentumTransport w x y vx vy a b d₂]
      ring

/-- So an angular momentum transports, with the momentum components as the price. -/
theorem angularMomentumMeasurement_transports {O : Type u} (w x y vx vy : O → Int) :
    Transports (angularMomentumMeasurement w x y vx vy)
      (fun a b d =>
        (b.1 - a.1) * firstMoment w vy d - (b.2 - a.2) * firstMoment w vx d) :=
  ⟨fun a b d => angularMomentumTransport w x y vx vy a b d⟩

end PropertyKindCalculus
