/-
# L0 — The black box

Solution for the worksheet HCP/Worksheets/L0_BlackBox.lean.

Six build-checked probes for the one-body spring–mass oscillator.
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

-- ANCHOR: bare_reals
-- Lean type-checks the bare-real radicand for S, so the oscillator identity is not tracked.
example (S : ClassicalMechanics.HarmonicOscillator) : ℝ :=
  √(S.m / S.k)
-- ANCHOR_END: bare_reals

-- ANCHOR: potential_energy_dimension
-- Lean type-checks S's potential energy at x with the mass·length²/time² dimension.
example (S : ClassicalMechanics.HarmonicOscillatorWithDim)
    (x : WithDim L𝓭 (EuclideanSpace ℝ (Fin 1))) :
    WithDim (M𝓭 * L𝓭 * L𝓭 * T𝓭⁻¹ * T𝓭⁻¹) ℝ :=
  S.potentialEnergy x
-- ANCHOR_END: potential_energy_dimension

-- ANCHOR: quotient_dimensions
-- Lean type-checks m / k with mass divided by stiffness as its inferred dimension.
example (m : WithDim M𝓭 ℝ)
    (k : WithDim (M𝓭 * T𝓭⁻¹ * T𝓭⁻¹) ℝ) :
    WithDim (M𝓭 * (M𝓭 * T𝓭⁻¹ * T𝓭⁻¹)⁻¹) ℝ := m / k

-- Lean type-checks k / m with stiffness divided by mass as its inferred dimension.
example (m : WithDim M𝓭 ℝ)
    (k : WithDim (M𝓭 * T𝓭⁻¹ * T𝓭⁻¹) ℝ) :
    WithDim ((M𝓭 * T𝓭⁻¹ * T𝓭⁻¹) * M𝓭⁻¹) ℝ := k / m

-- Refused: Lean reports a type mismatch between the mass/stiffness and stiffness/mass dimensions for m / k.
/--
error: Type mismatch
  m / k
has type
  WithDim (M𝓭 * (M𝓭 * T𝓭⁻¹ * T𝓭⁻¹)⁻¹) ℝ
but is expected to have type
  WithDim (M𝓭 * T𝓭⁻¹ * T𝓭⁻¹ * M𝓭⁻¹) ℝ
-/
#guard_msgs (whitespace := lax) in
example (m : WithDim M𝓭 ℝ)
    (k : WithDim (M𝓭 * T𝓭⁻¹ * T𝓭⁻¹) ℝ) :
    WithDim ((M𝓭 * T𝓭⁻¹ * T𝓭⁻¹) * M𝓭⁻¹) ℝ := m / k
-- ANCHOR_END: quotient_dimensions

-- ANCHOR: frequency_alias
-- Lean type-checks the time-inverse value as Frequency; dimensions alone do not distinguish the two frequency kinds.
example (ω : WithDim T𝓭⁻¹ ℝ≥0) : Frequency :=
  (fun f : Frequency => f) ω
-- ANCHOR_END: frequency_alias

-- ANCHOR: distinct_kinds_same_dimension
-- Lean proves angularFrequency and frequency.kind are distinct kinds despite their equal dimensions.
example :
    ForPhysLib.ClassicalMechanics.Kinds.angularFrequency ≠
      PropertyKindCalculus.Iso80000.Part3.frequency.kind := by decide

-- Lean proves angularFrequencyDK and frequency have equal dimensions; this does not make their kinds equal.
example :
    ForPhysLib.ClassicalMechanics.Metrology.angularFrequencyDK.dim =
      PropertyKindCalculus.Iso80000.Part3.frequency.dim := rfl
-- ANCHOR_END: distinct_kinds_same_dimension

-- ANCHOR: refused_kind_addition
-- Refused: Lean fails to type-check the angular-frequency/frequency sum because no HAdd instance exists for those quantity kinds.
/--
error: failed to synthesize instance of type class
  HAdd (Quantity ForPhysLib.ClassicalMechanics.Kinds.angularFrequency ℝ)
    (Quantity (Iso80000.Part3.frequency.kind LTMCTDimensionBase) ℝ) ?m.6

Hint: Type class instance resolution failures can be inspected with the `set_option trace.Meta.synthInstance true` command.
-/
#guard_msgs (whitespace := lax) in
example := fun (ω : Quantity ForPhysLib.ClassicalMechanics.Kinds.angularFrequency ℝ)
    (f : Quantity PropertyKindCalculus.Iso80000.Part3.frequency.kind ℝ) => ω + f
-- ANCHOR_END: refused_kind_addition

-- ANCHOR: refused_reciprocal_radicand
-- Refused: Lean fails to type-check massQ / springQ because no HDiv instance exists for those quantity kinds.
/--
error: failed to synthesize instance of type class
  HDiv (Quantity ForPhysLib.ClassicalMechanics.massK ℝ) (Quantity ForPhysLib.ClassicalMechanics.springConstantK ℝ) ?m.6

Hint: Type class instance resolution failures can be inspected with the `set_option trace.Meta.synthInstance true` command.
-/
#guard_msgs (whitespace := lax) in
example := fun (S : ClassicalMechanics.HarmonicOscillator) =>
  √((ForPhysLib.ClassicalMechanics.massQ S /
    ForPhysLib.ClassicalMechanics.springQ S).magnitude)
-- ANCHOR_END: refused_reciprocal_radicand

end
