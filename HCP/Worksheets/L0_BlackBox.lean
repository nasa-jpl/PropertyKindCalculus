/-
# L0 — The black box

Six build-checked probes for the one-body spring–mass oscillator.

Edit this worksheet in place, build with `lake build HCP.Worksheets.L0_BlackBox`,
and compare with the solution at `HCP/L0_BlackBox.lean`.
-/

module

public import Physlib.ClassicalMechanics.HarmonicOscillator.Basic
public import Physlib.ClassicalMechanics.HarmonicOscillator.WithDim
public import Physlib.Optics.Frequency
public import ForPhysLib.ClassicalMechanics.Kinds
public import ForPhysLib.ClassicalMechanics.Metrology
public import ForPhysLib.ClassicalMechanics.Operators

@[expose] public section

open Dimension PropertyKindCalculus
open scoped NNReal PropertyKindCalculus.OperatorTable

noncomputable section

namespace HCP.Worksheets.L0_BlackBox

-- EXERCISE: bare_reals
-- TODO: explain what is physically wrong here and why this still type-checks.
-- Bare reals: √(S.m / S.k) is accepted as a real although oscillator frequency uses √(S.k / S.m); the bare values cannot catch this reciprocal-radicand mistake.
example (S : ClassicalMechanics.HarmonicOscillator) : ℝ :=
  √(S.m / S.k)
-- EXERCISE_END: bare_reals

-- EXERCISE: potential_energy_dimension
-- TODO: construct the potential-energy result with the matching dimension.
-- Dimensions: `S.potentialEnergy x` is a `WithDim` value of dimension M·L²·T⁻²; it carries dimension, not an energy kind or oscillator bearer.
example (S : ClassicalMechanics.HarmonicOscillatorWithDim)
    (x : WithDim L𝓭 (EuclideanSpace ℝ (Fin 1))) :
    WithDim (M𝓭 * L𝓭 * L𝓭 * T𝓭⁻¹ * T𝓭⁻¹) ℝ := by
  sorry
-- EXERCISE_END: potential_energy_dimension

-- EXERCISE: quotient_dimensions
-- TODO: build both quotient dimensions, then uncomment the rejected expression.
-- Dimensions: The dimension-only, bearer-free `WithDim` quotient m/k has dimension T², reciprocal to the T⁻² angular-frequency-squared dimension.
example (m : WithDim M𝓭 ℝ)
    (k : WithDim (M𝓭 * T𝓭⁻¹ * T𝓭⁻¹) ℝ) :
    WithDim (M𝓭 * (M𝓭 * T𝓭⁻¹ * T𝓭⁻¹)⁻¹) ℝ := by
  sorry

-- Dimensions: The dimension-only, bearer-free `WithDim` quotient k/m has dimension T⁻², matching angular frequency squared but carrying no kind.
example (m : WithDim M𝓭 ℝ)
    (k : WithDim (M𝓭 * T𝓭⁻¹ * T𝓭⁻¹) ℝ) :
    WithDim ((M𝓭 * T𝓭⁻¹ * T𝓭⁻¹) * M𝓭⁻¹) ℝ := by
  sorry

-- TODO: uncomment, read the error, and write one sentence on what PKC refused and why.
-- Dimensions: Refused: type mismatch between m/k's T² dimension and the required k/m dimension T⁻²; this prevents the reciprocal radicand for angular frequency.
-- example (m : WithDim M𝓭 ℝ)
--     (k : WithDim (M𝓭 * T𝓭⁻¹ * T𝓭⁻¹) ℝ) :
--     WithDim ((M𝓭 * T𝓭⁻¹ * T𝓭⁻¹) * M𝓭⁻¹) ℝ := m / k
-- EXERCISE_END: quotient_dimensions

-- EXERCISE: frequency_alias
-- TODO: explain why the dimension-only value can be used as a frequency.
-- Kind vs dimension: A WithDim T⁻¹ value is accepted as Frequency; equal dimensions erase the distinction between cyclic and angular frequency.
example (ω : WithDim T𝓭⁻¹ ℝ≥0) : Frequency :=
  (fun f : Frequency => f) ω
-- EXERCISE_END: frequency_alias

-- EXERCISE: distinct_kinds_same_dimension
-- TODO: prove the kinds differ while their dimensions agree.
-- Kind vs dimension: Proves that angular-frequency and frequency are distinct kinds even though both have dimension T⁻¹.
example :
    ForPhysLib.ClassicalMechanics.Kinds.angularFrequency ≠
      PropertyKindCalculus.Iso80000.Part3.frequency.kind := by
  sorry

-- Kind vs dimension: Proves that angular frequency and frequency have equal dimension; equal dimension does not identify their kinds.
example :
    ForPhysLib.ClassicalMechanics.Metrology.angularFrequencyDK.dim =
      PropertyKindCalculus.Iso80000.Part3.frequency.dim := by
  sorry
-- EXERCISE_END: distinct_kinds_same_dimension

-- EXERCISE: refused_kind_addition
-- TODO: uncomment, read the error, and write one sentence on what PKC refused and why.
-- Kind vs dimension: Refused: no HAdd instance combines angular-frequency and frequency quantities, preventing their unlicensed sum despite matching dimension T⁻¹.
-- example := fun (ω : Quantity ForPhysLib.ClassicalMechanics.Kinds.angularFrequency ℝ)
--     (f : Quantity PropertyKindCalculus.Iso80000.Part3.frequency.kind ℝ) => ω + f
-- EXERCISE_END: refused_kind_addition

-- EXERCISE: refused_reciprocal_radicand
-- TODO: uncomment, read the error, and write one sentence on what PKC refused and why.
-- Kind vs dimension: Refused: no HDiv instance licenses mass divided by spring-constant quantities, so the kinded reciprocal m/k quotient cannot be formed.
-- example := fun (S : ClassicalMechanics.HarmonicOscillator) =>
--   √((ForPhysLib.ClassicalMechanics.massQ S /
--     ForPhysLib.ClassicalMechanics.springQ S).magnitude)
-- EXERCISE_END: refused_reciprocal_radicand

end HCP.Worksheets.L0_BlackBox

end
