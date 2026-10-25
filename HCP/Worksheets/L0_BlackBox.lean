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
-- Lean type-checks the bare-real radicand for S, so the oscillator identity is not tracked.
example (S : ClassicalMechanics.HarmonicOscillator) : ℝ :=
  √(S.m / S.k)
-- EXERCISE_END: bare_reals

-- EXERCISE: potential_energy_dimension
-- TODO: construct the potential-energy result with the matching dimension.
-- Lean type-checks S's potential energy at x with the mass·length²/time² dimension.
example (S : ClassicalMechanics.HarmonicOscillatorWithDim)
    (x : WithDim L𝓭 (EuclideanSpace ℝ (Fin 1))) :
    WithDim (M𝓭 * L𝓭 * L𝓭 * T𝓭⁻¹ * T𝓭⁻¹) ℝ := by
  sorry
-- EXERCISE_END: potential_energy_dimension

-- EXERCISE: quotient_dimensions
-- TODO: build both quotient dimensions, then uncomment the rejected expression.
-- Lean type-checks m / k with mass divided by stiffness as its inferred dimension.
example (m : WithDim M𝓭 ℝ)
    (k : WithDim (M𝓭 * T𝓭⁻¹ * T𝓭⁻¹) ℝ) :
    WithDim (M𝓭 * (M𝓭 * T𝓭⁻¹ * T𝓭⁻¹)⁻¹) ℝ := by
  sorry

-- Lean type-checks k / m with stiffness divided by mass as its inferred dimension.
example (m : WithDim M𝓭 ℝ)
    (k : WithDim (M𝓭 * T𝓭⁻¹ * T𝓭⁻¹) ℝ) :
    WithDim ((M𝓭 * T𝓭⁻¹ * T𝓭⁻¹) * M𝓭⁻¹) ℝ := by
  sorry

-- TODO: uncomment, read the error, and write one sentence on what PKC refused and why.
-- Refused: Lean reports a type mismatch between the mass/stiffness and stiffness/mass dimensions for m / k.
-- example (m : WithDim M𝓭 ℝ)
--     (k : WithDim (M𝓭 * T𝓭⁻¹ * T𝓭⁻¹) ℝ) :
--     WithDim ((M𝓭 * T𝓭⁻¹ * T𝓭⁻¹) * M𝓭⁻¹) ℝ := m / k
-- EXERCISE_END: quotient_dimensions

-- EXERCISE: frequency_alias
-- TODO: explain why the dimension-only value can be used as a frequency.
-- Lean type-checks the time-inverse value as Frequency; dimensions alone do not distinguish the two frequency kinds.
example (ω : WithDim T𝓭⁻¹ ℝ≥0) : Frequency :=
  (fun f : Frequency => f) ω
-- EXERCISE_END: frequency_alias

-- EXERCISE: distinct_kinds_same_dimension
-- TODO: prove the kinds differ while their dimensions agree.
-- Lean proves angularFrequency and frequency.kind are distinct kinds despite their equal dimensions.
example :
    ForPhysLib.ClassicalMechanics.Kinds.angularFrequency ≠
      PropertyKindCalculus.Iso80000.Part3.frequency.kind := by
  sorry

-- Lean proves angularFrequencyDK and frequency have equal dimensions; this does not make their kinds equal.
example :
    ForPhysLib.ClassicalMechanics.Metrology.angularFrequencyDK.dim =
      PropertyKindCalculus.Iso80000.Part3.frequency.dim := by
  sorry
-- EXERCISE_END: distinct_kinds_same_dimension

-- EXERCISE: refused_kind_addition
-- TODO: uncomment, read the error, and write one sentence on what PKC refused and why.
-- Refused: Lean fails to type-check the angular-frequency/frequency sum because no HAdd instance exists for those quantity kinds.
-- example := fun (ω : Quantity ForPhysLib.ClassicalMechanics.Kinds.angularFrequency ℝ)
--     (f : Quantity PropertyKindCalculus.Iso80000.Part3.frequency.kind ℝ) => ω + f
-- EXERCISE_END: refused_kind_addition

-- EXERCISE: refused_reciprocal_radicand
-- TODO: uncomment, read the error, and write one sentence on what PKC refused and why.
-- Refused: Lean fails to type-check massQ / springQ because no HDiv instance exists for those quantity kinds.
-- example := fun (S : ClassicalMechanics.HarmonicOscillator) =>
--   √((ForPhysLib.ClassicalMechanics.massQ S /
--     ForPhysLib.ClassicalMechanics.springQ S).magnitude)
-- EXERCISE_END: refused_reciprocal_radicand

end HCP.Worksheets.L0_BlackBox

end
