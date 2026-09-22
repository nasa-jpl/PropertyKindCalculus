/-
# Validation probes — the weighted mean and the parallel-axis law (R9)

The two aggregation laws that need Mathlib, each with the danger its own shape brings.

A *mean of a constant is that constant* law is satisfied by anything that ignores its weights,
so the probe first builds a carving whose weights are genuinely unequal and checks that the
mean is **not** the unweighted average — `3/2`, where averaging the same two values gives `2`.
Only then is `mean_const` applied to it.

A *transport* law is empty if the correction is zero, so the probe drives `parallelAxis` at the
textbook instance: a rod of total mass 2 whose first moment about its centre vanishes, moved to
an axis one unit away. The correction is `M d² = 2`, and both moments are computed — 2 about
the centre, 4 about the end — so the law relates two numbers the file itself produces.
-/

module

public import PropertyKindCalculus.AggregationLaws
meta import PropertyKindCalculus.AggregationLaws

public section -- pkc-blanket
@[expose] section -- pkc-blanket-expose

namespace PropertyKindCalculus.Tests.AggregationLaws

open PropertyKindCalculus

/-! ## The weighted mean (R9) -/

/-- A carving of two parts with genuinely unequal weights: 1 and 3, so the total is 4 and the
license is discharged by arithmetic rather than by assumption. -/
noncomputable def unevenPair : WeightedCarving ℝ Bool where
  parts := .union (.atom true) (.atom false)
  weight := fun b => if b then 1 else 3
  total_ne_zero := by norm_num [totalWeight, Decomposition.fold, Carrier.add, Carrier.zero]

/-- The values carried by the two parts: 3 on the heavy-weighted part, 1 on the other. -/
noncomputable def unevenValue : Bool → ℝ := fun b => if b then 3 else 1

-- Boundary — the weights are load-bearing: the weighted mean is `6/4`, where the unweighted
-- average of the same two values is `2`. A `mean` that ignored its weights would fail here.
theorem r9_weighted_mean_ne_average : unevenPair.mean unevenValue = 3 / 2 := by
  norm_num [WeightedCarving.mean, weightedSum, totalWeight, unevenPair, unevenValue,
    Decomposition.fold, Carrier.add]

-- Inhabitation: the constant law, applied to that same carving — a mean that is neither a sum
-- nor a shared reading still sends a constant family to the constant.
theorem r9_weighted_mean_const (v : ℝ) : unevenPair.mean (fun _ => v) = v :=
  unevenPair.mean_const v

/-! ## The parallel-axis transport law (R9) -/

-- Inhabitation: the general law at the textbook instance — the rod, from its centre to an axis
-- through its left mass.
theorem r9_parallel_axis :
    inertiaAbout PointMass.mass PointMass.position (-1) rod
      = inertiaAbout PointMass.mass PointMass.position 0 rod
        + (2 * (0 - (-1)) * firstMoment PointMass.mass PointMass.position rod
           + ((-1) * (-1) - 0 * 0) * partTotal PointMass.mass rod) :=
  parallelAxis PointMass.mass PointMass.position (-1) 0 rod

-- … and the three numbers it relates. The first moment about the centre vanishes, which is why
-- the correction reduces to the textbook `M d²` with `M = 2`, `d = 1`.
#guard inertiaAbout PointMass.mass PointMass.position 0 rod == 2
#guard inertiaAbout PointMass.mass PointMass.position (-1) rod == 4
#guard firstMoment PointMass.mass PointMass.position rod == 0
#guard partTotal PointMass.mass rod == 2

-- Inhabitation: the transport law repairs the mixed-axis sum core exhibits as wrong.
theorem r9_rod_corrected :
    (rodInertia 0 rod).numeral
      = ((rodInertia (-1) rodLeft).numeral + rodCorr 0 (-1) rodLeft)
        + ((rodInertia 1 rodRight).numeral + rodCorr 0 1 rodRight) :=
  rod_mixed_axes_corrected

/-- info: 'PropertyKindCalculus.WeightedCarving.mean_const' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms WeightedCarving.mean_const

/-- info: 'PropertyKindCalculus.fold_mul_const' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms fold_mul_const

/-- info: 'PropertyKindCalculus.parallelAxis' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms parallelAxis

/-- info: 'PropertyKindCalculus.inertiaMeasurement_transports' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms inertiaMeasurement_transports

/-- info: 'PropertyKindCalculus.rod_mixed_axes_corrected' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms rod_mixed_axes_corrected

end PropertyKindCalculus.Tests.AggregationLaws

end -- pkc-blanket-expose
end -- pkc-blanket
