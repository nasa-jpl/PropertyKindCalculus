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
-- Bare reals: √(S.m / S.k) is accepted as a real although oscillator frequency uses √(S.k / S.m); the bare values cannot catch this reciprocal-radicand mistake.
example (S : ClassicalMechanics.HarmonicOscillator) : ℝ :=
  √(S.m / S.k)
-- ANCHOR_END: bare_reals

-- ANCHOR: potential_energy_dimension
-- Dimensions: `S.potentialEnergy x` is a `WithDim` value of dimension M·L²·T⁻²; it carries dimension, not an energy kind or oscillator bearer.
example (S : ClassicalMechanics.HarmonicOscillatorWithDim)
    (x : WithDim L𝓭 (EuclideanSpace ℝ (Fin 1))) :
    WithDim (M𝓭 * L𝓭 * L𝓭 * T𝓭⁻¹ * T𝓭⁻¹) ℝ :=
  S.potentialEnergy x
-- ANCHOR_END: potential_energy_dimension

-- ANCHOR: quotient_dimensions
-- Dimensions: The dimension-only, bearer-free `WithDim` quotient m/k has dimension T², reciprocal to the T⁻² angular-frequency-squared dimension.
example (m : WithDim M𝓭 ℝ)
    (k : WithDim (M𝓭 * T𝓭⁻¹ * T𝓭⁻¹) ℝ) :
    WithDim (M𝓭 * (M𝓭 * T𝓭⁻¹ * T𝓭⁻¹)⁻¹) ℝ := m / k

-- Dimensions: The dimension-only, bearer-free `WithDim` quotient k/m has dimension T⁻², matching angular frequency squared but carrying no kind.
example (m : WithDim M𝓭 ℝ)
    (k : WithDim (M𝓭 * T𝓭⁻¹ * T𝓭⁻¹) ℝ) :
    WithDim ((M𝓭 * T𝓭⁻¹ * T𝓭⁻¹) * M𝓭⁻¹) ℝ := k / m

-- Dimensions: Refused: type mismatch between m/k's T² dimension and the required k/m dimension T⁻²; this prevents the reciprocal radicand for angular frequency.
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
-- Kind vs dimension: A WithDim T⁻¹ value is accepted as Frequency; equal dimensions erase the distinction between cyclic and angular frequency.
example (ω : WithDim T𝓭⁻¹ ℝ≥0) : Frequency :=
  (fun f : Frequency => f) ω
-- ANCHOR_END: frequency_alias

-- ANCHOR: distinct_kinds_same_dimension
-- Kind vs dimension: Proves that angular-frequency and frequency are distinct kinds even though both have dimension T⁻¹.
example :
    ForPhysLib.ClassicalMechanics.Kinds.angularFrequency ≠
      PropertyKindCalculus.Iso80000.Part3.frequency.kind := by decide

-- Kind vs dimension: Proves that angular frequency and frequency have equal dimension; equal dimension does not identify their kinds.
example :
    ForPhysLib.ClassicalMechanics.Metrology.angularFrequencyDK.dim =
      PropertyKindCalculus.Iso80000.Part3.frequency.dim := rfl
-- ANCHOR_END: distinct_kinds_same_dimension

-- ANCHOR: refused_kind_addition
-- Kind vs dimension: Refused: no HAdd instance combines angular-frequency and frequency quantities, preventing their unlicensed sum despite matching dimension T⁻¹.
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
-- Kind vs dimension: Refused: no HDiv instance licenses mass divided by spring-constant quantities, so the kinded reciprocal m/k quotient cannot be formed.
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
