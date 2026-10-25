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
example (S : ClassicalMechanics.HarmonicOscillator) : ℝ :=
  √(S.m / S.k)
-- EXERCISE_END: bare_reals

-- EXERCISE: potential_energy_dimension
-- TODO: construct the potential-energy result with the matching dimension.
example (S : ClassicalMechanics.HarmonicOscillatorWithDim)
    (x : WithDim L𝓭 (EuclideanSpace ℝ (Fin 1))) :
    WithDim (M𝓭 * L𝓭 * L𝓭 * T𝓭⁻¹ * T𝓭⁻¹) ℝ := by
  sorry
-- EXERCISE_END: potential_energy_dimension

-- EXERCISE: quotient_dimensions
-- TODO: build both quotient dimensions, then uncomment the rejected expression.
example (m : WithDim M𝓭 ℝ)
    (k : WithDim (M𝓭 * T𝓭⁻¹ * T𝓭⁻¹) ℝ) :
    WithDim (M𝓭 * (M𝓭 * T𝓭⁻¹ * T𝓭⁻¹)⁻¹) ℝ := by
  sorry

example (m : WithDim M𝓭 ℝ)
    (k : WithDim (M𝓭 * T𝓭⁻¹ * T𝓭⁻¹) ℝ) :
    WithDim ((M𝓭 * T𝓭⁻¹ * T𝓭⁻¹) * M𝓭⁻¹) ℝ := by
  sorry

-- TODO: uncomment, read the error, and write one sentence on what PKC refused and why.
-- example (m : WithDim M𝓭 ℝ)
--     (k : WithDim (M𝓭 * T𝓭⁻¹ * T𝓭⁻¹) ℝ) :
--     WithDim ((M𝓭 * T𝓭⁻¹ * T𝓭⁻¹) * M𝓭⁻¹) ℝ := m / k
-- EXERCISE_END: quotient_dimensions

-- EXERCISE: frequency_alias
-- TODO: explain why the dimension-only value can be used as a frequency.
example (ω : WithDim T𝓭⁻¹ ℝ≥0) : Frequency :=
  (fun f : Frequency => f) ω
-- EXERCISE_END: frequency_alias

-- EXERCISE: distinct_kinds_same_dimension
-- TODO: prove the kinds differ while their dimensions agree.
example :
    ForPhysLib.ClassicalMechanics.Kinds.angularFrequency ≠
      PropertyKindCalculus.Iso80000.Part3.frequency.kind := by
  sorry

example :
    ForPhysLib.ClassicalMechanics.Metrology.angularFrequencyDK.dim =
      PropertyKindCalculus.Iso80000.Part3.frequency.dim := by
  sorry
-- EXERCISE_END: distinct_kinds_same_dimension

-- EXERCISE: refused_kind_addition
-- TODO: uncomment, read the error, and write one sentence on what PKC refused and why.
-- example := fun (ω : Quantity ForPhysLib.ClassicalMechanics.Kinds.angularFrequency ℝ)
--     (f : Quantity PropertyKindCalculus.Iso80000.Part3.frequency.kind ℝ) => ω + f
-- EXERCISE_END: refused_kind_addition

-- EXERCISE: refused_reciprocal_radicand
-- TODO: uncomment, read the error, and write one sentence on what PKC refused and why.
-- example := fun (S : ClassicalMechanics.HarmonicOscillator) =>
--   √((ForPhysLib.ClassicalMechanics.massQ S /
--     ForPhysLib.ClassicalMechanics.springQ S).magnitude)
-- EXERCISE_END: refused_reciprocal_radicand

end HCP.Worksheets.L0_BlackBox

end
