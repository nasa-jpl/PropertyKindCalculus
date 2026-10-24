/-
# L1 — Two bodies

Seven build-checked probes of oscillator identity, designation, and per-oscillator quantities.
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

-- ANCHOR: bare_real_cross_oscillators
example (S₁ S₂ : ClassicalMechanics.HarmonicOscillator) : ℝ :=
  √(S₁.k / S₂.m)
-- ANCHOR_END: bare_real_cross_oscillators

-- ANCHOR: kinded_bearer_free_cross_oscillators
example (S₁ S₂ : ClassicalMechanics.HarmonicOscillator) :
    Quantity ForPhysLib.ClassicalMechanics.omegaSquaredK ℝ :=
  ForPhysLib.ClassicalMechanics.springQ S₁ /
    ForPhysLib.ClassicalMechanics.massQ S₂
-- ANCHOR_END: kinded_bearer_free_cross_oscillators

-- ANCHOR: oscillator_context_and_sort
inductive Oscillator | A | B
deriving DecidableEq, Repr

def oscillatorS : SortOfSystem := ⟨"harmonic oscillator"⟩

instance : Sorted Oscillator := ⟨fun _ => oscillatorS⟩

example : Sorted.sortOf Oscillator.A = Sorted.sortOf Oscillator.B := rfl
-- ANCHOR_END: oscillator_context_and_sort

-- ANCHOR: designation
instance : Designated Oscillator where
  designation
    | .A => ⟨"oscillator A"⟩
    | .B => ⟨"oscillator B"⟩
  designation_inj {x y} h := by
    cases x <;> cases y <;> first | rfl | exact absurd (System.mk.inj h) (by decide)

theorem constant_designation_not_injective :
    ¬ Function.Injective (fun _ : Oscillator => (⟨"oscillator"⟩ : Object)) := by
  intro h
  have hAB : Oscillator.A = Oscillator.B := h rfl
  cases hAB
-- ANCHOR_END: designation

-- ANCHOR: oscillator_indexed_quantities
/--
One rig name is one system; its records are states, configurations, or rival estimates to
compare. Different names denote distinct systems.
-/
inductive Rig | R₁ | R₂
deriving DecidableEq, Repr

structure TwoOscillators (r : Rig) where
  osc : Oscillator → ClassicalMechanics.HarmonicOscillator

structure OscillatorOf (r : Rig) where
  osc : Oscillator

def massOf {r : Rig} (sys : TwoOscillators r) (o : OscillatorOf r) :
    IndividualQuantity o ForPhysLib.ClassicalMechanics.massK ℝ :=
  ⟨(sys.osc o.osc).m⟩

def stiffnessOf {r : Rig} (sys : TwoOscillators r) (o : OscillatorOf r) :
    IndividualQuantity o ForPhysLib.ClassicalMechanics.springConstantK ℝ :=
  ⟨(sys.osc o.osc).k⟩

def omegaSqOf {r : Rig} (sys : TwoOscillators r) (o : OscillatorOf r) :
    IndividualQuantity o ForPhysLib.ClassicalMechanics.omegaSquaredK ℝ :=
  IndividualQuantity.div
    (KindDiv.law
      (k₁ := ForPhysLib.ClassicalMechanics.springConstantK)
      (k₂ := ForPhysLib.ClassicalMechanics.massK)
      (k := ForPhysLib.ClassicalMechanics.omegaSquaredK))
    (stiffnessOf sys o)
    (massOf sys o)

theorem omegaSqOf_magnitude {r : Rig} (sys : TwoOscillators r) (o : OscillatorOf r) :
    (omegaSqOf sys o).magnitude = (sys.osc o.osc).k / (sys.osc o.osc).m := by
  rw [omegaSqOf, IndividualQuantity.div_magnitude, stiffnessOf, massOf]

def whole : Component := ⟨"whole"⟩

theorem mass_kind_shared_by_oscillators :
    ForPhysLib.ClassicalMechanics.massK.dedicatedFor Oscillator.A whole =
      ForPhysLib.ClassicalMechanics.massK.dedicatedFor Oscillator.B whole :=
  KindOfProperty.dedicatedFor_congr rfl whole
-- ANCHOR_END: oscillator_indexed_quantities

-- ANCHOR: refused_cross_oscillator
/--
error: Type mismatch
  massOf sys { osc := Oscillator.B }
has type
  IndividualQuantity { osc := Oscillator.B } ForPhysLib.ClassicalMechanics.massK ℝ
but is expected to have type
  IndividualQuantity { osc := Oscillator.A } ForPhysLib.ClassicalMechanics.massK ℝ
-/
#guard_msgs in
example {r : Rig} (sys : TwoOscillators r) :
    IndividualQuantity (⟨.A⟩ : OscillatorOf r)
      ForPhysLib.ClassicalMechanics.massK ℝ :=
  massOf sys ⟨.B⟩

/--
error: Application type mismatch: The argument
  massOf sys { osc := Oscillator.B }
has type
  IndividualQuantity { osc := Oscillator.B } ForPhysLib.ClassicalMechanics.massK ℝ
but is expected to have type
  IndividualQuantity { osc := Oscillator.A } ForPhysLib.ClassicalMechanics.massK ℝ
in the application
  IndividualQuantity.add ⋯ (massOf sys { osc := Oscillator.A }) (massOf sys { osc := Oscillator.B })
-/
#guard_msgs in
example {r : Rig} (sys : TwoOscillators r) :=
  IndividualQuantity.add DifferenceKind.ofScale
    (massOf sys ⟨.A⟩) (massOf sys ⟨.B⟩)

/--
error: Application type mismatch: The argument
  massOf sys { osc := Oscillator.B }
has type
  IndividualQuantity { osc := Oscillator.B } ForPhysLib.ClassicalMechanics.massK ℝ
but is expected to have type
  IndividualQuantity { osc := Oscillator.A } ForPhysLib.ClassicalMechanics.massK ℝ
in the application
  IndividualQuantity.div h (stiffnessOf sys { osc := Oscillator.A }) (massOf sys { osc := Oscillator.B })
-/
#guard_msgs in
example {r : Rig} (sys : TwoOscillators r) :=
  let h :=
    KindDiv.law
      (k₁ := ForPhysLib.ClassicalMechanics.springConstantK)
      (k₂ := ForPhysLib.ClassicalMechanics.massK)
      (k := ForPhysLib.ClassicalMechanics.omegaSquaredK)
  IndividualQuantity.div h (stiffnessOf sys ⟨.A⟩) (massOf sys ⟨.B⟩)

/--
error: Application type mismatch: The argument
  massOf { osc := o } { osc := Oscillator.A }
has type
  IndividualQuantity (@OscillatorOf.mk Rig.R₂ Oscillator.A) ForPhysLib.ClassicalMechanics.massK ℝ
but is expected to have type
  IndividualQuantity (@OscillatorOf.mk Rig.R₁ Oscillator.A) ForPhysLib.ClassicalMechanics.massK ℝ
in the application
  IndividualQuantity.add ⋯ (massOf { osc := o } { osc := Oscillator.A }) (massOf { osc := o } { osc := Oscillator.A })
-/
#guard_msgs in
example (o : Oscillator → ClassicalMechanics.HarmonicOscillator) :=
  IndividualQuantity.add DifferenceKind.ofScale
    (massOf (⟨o⟩ : TwoOscillators .R₁) ⟨.A⟩)
    (massOf (⟨o⟩ : TwoOscillators .R₂) ⟨.A⟩)
-- ANCHOR_END: refused_cross_oscillator

-- ANCHOR: same_rig_estimate_difference
def oscillatorAMassDifference (earlier later : TwoOscillators .R₁) :
    IndividualQuantity (⟨.A⟩ : OscillatorOf .R₁)
      ForPhysLib.ClassicalMechanics.massK ℝ :=
  IndividualQuantity.add DifferenceKind.ofScale
    (massOf later ⟨.A⟩)
    (-(massOf earlier ⟨.A⟩))

#guard_msgs in
example (earlier later : TwoOscillators .R₁) :
    IndividualQuantity (⟨.A⟩ : OscillatorOf .R₁)
      ForPhysLib.ClassicalMechanics.massK ℝ :=
  oscillatorAMassDifference earlier later

theorem oscillatorAMassDifference_magnitude (earlier later : TwoOscillators .R₁) :
    (oscillatorAMassDifference earlier later).magnitude =
      (later.osc .A).m - (earlier.osc .A).m := by
  simp [oscillatorAMassDifference, IndividualQuantity.add_magnitude,
    IndividualQuantity.neg_magnitude, massOf]
  change (later.osc .A).m + (-(earlier.osc .A).m) =
    (later.osc .A).m - (earlier.osc .A).m
  ring
-- ANCHOR_END: same_rig_estimate_difference

-- ANCHOR: refused_unsorted_object
/--
error: failed to synthesize instance of type class
  Sorted System

Hint: Type class instance resolution failures can be inspected with the `set_option trace.Meta.synthInstance true` command.
-/
#guard_msgs in
example :=
  ForPhysLib.ClassicalMechanics.massK.dedicatedFor
    (⟨"oscillator A"⟩ : Object) whole
-- ANCHOR_END: refused_unsorted_object

end
