/-
# L1 — Two bodies

Seven build-checked probes of object identity, designation, and per-body quantities.
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

-- ANCHOR: bare_real_cross_body
example (S₁ S₂ : ClassicalMechanics.HarmonicOscillator) : ℝ :=
  √(S₁.k / S₂.m)
-- ANCHOR_END: bare_real_cross_body

-- ANCHOR: kinded_bearer_free_cross_body
example (S₁ S₂ : ClassicalMechanics.HarmonicOscillator) :
    Quantity ForPhysLib.ClassicalMechanics.omegaSquaredK ℝ :=
  ForPhysLib.ClassicalMechanics.springQ S₁ /
    ForPhysLib.ClassicalMechanics.massQ S₂
-- ANCHOR_END: kinded_bearer_free_cross_body

-- ANCHOR: context_and_sort
inductive Body | A | B
deriving DecidableEq, Repr

inductive Spring | kA | kB
deriving DecidableEq, Repr

def bodyS : SortOfSystem := ⟨"point mass"⟩
def springS : SortOfSystem := ⟨"linear spring"⟩

instance : Sorted Body := ⟨fun _ => bodyS⟩
instance : Sorted Spring := ⟨fun _ => springS⟩

example : Sorted.sortOf Body.A = Sorted.sortOf Body.B := rfl
-- ANCHOR_END: context_and_sort

-- ANCHOR: designation
instance : Designated Body where
  designation
    | .A => ⟨"body A"⟩
    | .B => ⟨"body B"⟩
  designation_inj {x y} h := by
    cases x <;> cases y <;> first | rfl | exact absurd (System.mk.inj h) (by decide)

theorem constant_designation_not_injective :
    ¬ Function.Injective (fun _ : Body => (⟨"body"⟩ : Object)) := by
  intro h
  have hAB : Body.A = Body.B := h rfl
  cases hAB
-- ANCHOR_END: designation

-- ANCHOR: bearer_indexed_quantities
structure TwoOscillators where
  osc : Body → ClassicalMechanics.HarmonicOscillator

def massOf (sys : TwoOscillators) (b : Body) :
    IndividualQuantity b ForPhysLib.ClassicalMechanics.massK ℝ :=
  ⟨(sys.osc b).m⟩

def wallSpring : Body → Spring
  | .A => .kA
  | .B => .kB

def bodyOfWallSpring : Spring → Body
  | .kA => .A
  | .kB => .B

theorem bodyOfWallSpring_wallSpring (b : Body) :
    bodyOfWallSpring (wallSpring b) = b := by
  cases b <;> rfl

def stiffnessOf (sys : TwoOscillators) (s : Spring) :
    IndividualQuantity s ForPhysLib.ClassicalMechanics.springConstantK ℝ :=
  ⟨(sys.osc (bodyOfWallSpring s)).k⟩

def whole : Component := ⟨"whole"⟩

theorem mass_kind_shared_by_bodies :
    ForPhysLib.ClassicalMechanics.massK.dedicatedFor Body.A whole =
      ForPhysLib.ClassicalMechanics.massK.dedicatedFor Body.B whole :=
  KindOfProperty.dedicatedFor_congr rfl whole
-- ANCHOR_END: bearer_indexed_quantities

-- ANCHOR: refused_cross_body_mass
/--
error: Type mismatch
  massOf sys Body.B
has type
  IndividualQuantity Body.B ForPhysLib.ClassicalMechanics.massK ℝ
but is expected to have type
  IndividualQuantity Body.A ForPhysLib.ClassicalMechanics.massK ℝ
-/
#guard_msgs in
example (sys : TwoOscillators) :
    IndividualQuantity Body.A ForPhysLib.ClassicalMechanics.massK ℝ :=
  massOf sys Body.B

/--
error: Application type mismatch: The argument
  massOf sys Body.B
has type
  IndividualQuantity Body.B ForPhysLib.ClassicalMechanics.massK ℝ
but is expected to have type
  IndividualQuantity Body.A ForPhysLib.ClassicalMechanics.massK ℝ
in the application
  IndividualQuantity.add ⋯ (massOf sys Body.A) (massOf sys Body.B)
-/
#guard_msgs in
example (sys : TwoOscillators) :=
  IndividualQuantity.add DifferenceKind.ofScale
    (massOf sys Body.A) (massOf sys Body.B)
-- ANCHOR_END: refused_cross_body_mass

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
