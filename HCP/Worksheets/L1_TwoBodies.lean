/-
# L1 — Two bodies

Seven build-checked probes of oscillator identity, designation, and per-oscillator quantities.

Edit this worksheet in place, build with `lake build HCP.Worksheets.L1_TwoBodies`,
and compare with the solution at `HCP/L1_TwoBodies.lean`.
-/

module

public import Physlib.ClassicalMechanics.HarmonicOscillator.Basic
public import ForPhysLib.ClassicalMechanics.Kinds
public import ForPhysLib.ClassicalMechanics.Metrology
public import ForPhysLib.ClassicalMechanics.Operators
public import PropertyKindCalculus

@[expose] public section

open PropertyKindCalculus
open scoped PropertyKindCalculus.OperatorTable

noncomputable section

namespace HCP.Worksheets.L1_TwoBodies

-- EXERCISE: bare_real_cross_oscillators
-- TODO: explain what the cross-oscillator expression hides and why it type-checks.
example (S₁ S₂ : ClassicalMechanics.HarmonicOscillator) : ℝ :=
  √(S₁.k / S₂.m)
-- EXERCISE_END: bare_real_cross_oscillators

-- EXERCISE: kinded_bearer_free_cross_oscillators
-- TODO: explain why matching kinds alone allow this cross-oscillator quotient.
example (S₁ S₂ : ClassicalMechanics.HarmonicOscillator) :
    Quantity ForPhysLib.ClassicalMechanics.omegaSquaredK ℝ :=
  ForPhysLib.ClassicalMechanics.springQ S₁ /
    ForPhysLib.ClassicalMechanics.massQ S₂
-- EXERCISE_END: kinded_bearer_free_cross_oscillators

-- EXERCISE: oscillator_context_and_sort
-- GIVEN:
inductive Oscillator | A | B
deriving DecidableEq, Repr

def oscillatorS : SortOfSystem := ⟨"harmonic oscillator"⟩

instance : Sorted Oscillator := ⟨fun _ => oscillatorS⟩

-- TODO: show both particulars have the declared sort.
example : Sorted.sortOf Oscillator.A = Sorted.sortOf Oscillator.B := by
  sorry
-- EXERCISE_END: oscillator_context_and_sort

-- EXERCISE: designation
-- TODO: give A and B distinct names and prove designation is injective.
instance : Designated Oscillator where
  designation
    | .A => by sorry
    | .B => by sorry
  designation_inj := by
    sorry

theorem constant_designation_not_injective :
    ¬ Function.Injective (fun _ : Oscillator => (⟨"oscillator"⟩ : Object)) := by
  sorry
-- EXERCISE_END: designation

-- EXERCISE: oscillator_indexed_quantities
-- GIVEN:
inductive Rig | R₁ | R₂
deriving DecidableEq, Repr

structure TwoOscillators (r : Rig) where
  osc : Oscillator → ClassicalMechanics.HarmonicOscillator

structure OscillatorOf (r : Rig) where
  osc : Oscillator

-- TODO: index each quantity by its oscillator and construct the k/m quotient.
def massOf {r : Rig} (sys : TwoOscillators r) (o : OscillatorOf r) :
    IndividualQuantity o ForPhysLib.ClassicalMechanics.massK ℝ := by
  sorry

def stiffnessOf {r : Rig} (sys : TwoOscillators r) (o : OscillatorOf r) :
    IndividualQuantity o ForPhysLib.ClassicalMechanics.springConstantK ℝ := by
  sorry

def omegaSqOf {r : Rig} (sys : TwoOscillators r) (o : OscillatorOf r) :
    IndividualQuantity o ForPhysLib.ClassicalMechanics.omegaSquaredK ℝ := by
  sorry

theorem omegaSqOf_magnitude {r : Rig} (sys : TwoOscillators r) (o : OscillatorOf r) :
    (omegaSqOf sys o).magnitude = (sys.osc o.osc).k / (sys.osc o.osc).m := by
  sorry

-- GIVEN:
def whole : Component := ⟨"whole"⟩

-- TODO: show the dedicated mass kind is shared by both oscillator particulars.
theorem mass_kind_shared_by_oscillators :
    ForPhysLib.ClassicalMechanics.massK.dedicatedFor Oscillator.A whole =
      ForPhysLib.ClassicalMechanics.massK.dedicatedFor Oscillator.B whole := by
  sorry
-- EXERCISE_END: oscillator_indexed_quantities

-- EXERCISE: refused_cross_oscillator
-- TODO: uncomment each expression, read the errors, and write one sentence on what PKC refused and why.
-- example {r : Rig} (sys : TwoOscillators r) :
--     IndividualQuantity (⟨.A⟩ : OscillatorOf r) ForPhysLib.ClassicalMechanics.massK ℝ :=
--   massOf sys ⟨.B⟩
-- example {r : Rig} (sys : TwoOscillators r) :=
--   IndividualQuantity.add DifferenceKind.ofScale (massOf sys ⟨.A⟩) (massOf sys ⟨.B⟩)
-- example {r : Rig} (sys : TwoOscillators r) :=
--   IndividualQuantity.div (by sorry) (stiffnessOf sys ⟨.A⟩) (massOf sys ⟨.B⟩)
-- example (o : Oscillator → ClassicalMechanics.HarmonicOscillator) :=
--   IndividualQuantity.add DifferenceKind.ofScale
--     (massOf (⟨o⟩ : TwoOscillators .R₁) ⟨.A⟩)
--     (massOf (⟨o⟩ : TwoOscillators .R₂) ⟨.A⟩)
-- EXERCISE_END: refused_cross_oscillator

-- EXERCISE: same_rig_estimate_difference
-- TODO: subtract two mass estimates on the same rig and prove the magnitude equation.
def oscillatorAMassDifference (earlier later : TwoOscillators .R₁) :
    IndividualQuantity (⟨.A⟩ : OscillatorOf .R₁)
      ForPhysLib.ClassicalMechanics.massK ℝ := by
  sorry

example (earlier later : TwoOscillators .R₁) :
    IndividualQuantity (⟨.A⟩ : OscillatorOf .R₁)
      ForPhysLib.ClassicalMechanics.massK ℝ := by
  sorry

theorem oscillatorAMassDifference_magnitude (earlier later : TwoOscillators .R₁) :
    (oscillatorAMassDifference earlier later).magnitude =
      (later.osc .A).m - (earlier.osc .A).m := by
  sorry
-- EXERCISE_END: same_rig_estimate_difference

-- EXERCISE: refused_unsorted_object
-- TODO: uncomment, read the error, and write one sentence on why this object has no usable sort.
-- example :=
--   ForPhysLib.ClassicalMechanics.massK.dedicatedFor
--     (⟨"oscillator A"⟩ : Object) whole
-- EXERCISE_END: refused_unsorted_object

end HCP.Worksheets.L1_TwoBodies

end
