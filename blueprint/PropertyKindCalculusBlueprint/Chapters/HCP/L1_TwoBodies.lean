import Verso
import VersoManual
import VersoBlueprint
import PropertyKindCalculusBlueprint.References

open Verso.Genre
open Verso.Genre.Manual
open Informal
open Verso.Code.External

set_option verso.exampleProject ".."
set_option verso.exampleModule "HCP.L1_TwoBodies"

#doc (Manual) "L1 — Two bodies" =>
%%%
tag := "hcp-l1"
%%%

Two bodies are now in view, one inside each black-box oscillator: whose mass is this? Bare
reals and bearer-free kinded values let one oscillator's mass enter another's formula.
L1 indexes mass and stiffness by the oscillator, so its own `k/m` is accepted and a
cross-oscillator quotient is refused. Each oscillator is the whole characterized by
`ω₀`; this is why `k` and `m` share its index. L2 opens each box into body and spring(s),
revisits which component bears mass and stiffness, and considers the pair as a whole.

_1. Bare reals._ Put oscillator B's mass in oscillator A's frequency radicand. The
upstream oscillator accepts the cross-oscillator expression as a real:

```anchor bare_real_cross_oscillators
example (S₁ S₂ : ClassicalMechanics.HarmonicOscillator) : ℝ :=
  √(S₁.k / S₂.m)
```

_2. Kinded, but bearer-free._ The spring-constant/mass quotient also accepts values from
different oscillators. It is still a `Quantity`, with no oscillator index:

```anchor kinded_bearer_free_cross_oscillators
example (S₁ S₂ : ClassicalMechanics.HarmonicOscillator) :
    Quantity ForPhysLib.ClassicalMechanics.omegaSquaredK ℝ :=
  ForPhysLib.ClassicalMechanics.springQ S₁ /
    ForPhysLib.ClassicalMechanics.massQ S₂
```

_3. Declare the context._ Oscillators A and B are distinct particulars of one sort.
Each contains one body and one wall spring; neither component is separately indexed yet:

```anchor oscillator_context_and_sort
inductive Oscillator | A | B
deriving DecidableEq, Repr

def oscillatorS : SortOfSystem := ⟨"harmonic oscillator"⟩

instance : Sorted Oscillator := ⟨fun _ => oscillatorS⟩

example : Sorted.sortOf Oscillator.A = Sorted.sortOf Oscillator.B := rfl
```

_4. Designate without collapsing._ `Designated` requires an injective designation. A
constant name would report two oscillators as one, the R5 false-identity risk:

```anchor designation
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
```

_5. Carry the bearer._ The oscillator is the whole characterized by `ω₀`; mass and
stiffness therefore share its index. Under L0's massless-spring, fixed-wall assumptions,
these magnitudes read the body's mass and spring's stiffness. The existing kind table
supplies the quotient law; the magnitude theorem reads the real fields. The catalogue
entry is shared because both oscillators have the same sort:

```anchor oscillator_indexed_quantities
structure TwoOscillators where
  osc : Oscillator → ClassicalMechanics.HarmonicOscillator

def massOf (sys : TwoOscillators) (o : Oscillator) :
    IndividualQuantity o ForPhysLib.ClassicalMechanics.massK ℝ :=
  ⟨(sys.osc o).m⟩

def stiffnessOf (sys : TwoOscillators) (o : Oscillator) :
    IndividualQuantity o ForPhysLib.ClassicalMechanics.springConstantK ℝ :=
  ⟨(sys.osc o).k⟩

def omegaSqOf (sys : TwoOscillators) (o : Oscillator) :
    IndividualQuantity o ForPhysLib.ClassicalMechanics.omegaSquaredK ℝ :=
  IndividualQuantity.div
    (KindDiv.law
      (k₁ := ForPhysLib.ClassicalMechanics.springConstantK)
      (k₂ := ForPhysLib.ClassicalMechanics.massK)
      (k := ForPhysLib.ClassicalMechanics.omegaSquaredK))
    (stiffnessOf sys o)
    (massOf sys o)

theorem omegaSqOf_magnitude (sys : TwoOscillators) (o : Oscillator) :
    (omegaSqOf sys o).magnitude = (sys.osc o).k / (sys.osc o).m := by
  rw [omegaSqOf, IndividualQuantity.div_magnitude, stiffnessOf, massOf]

def whole : Component := ⟨"whole"⟩

theorem mass_kind_shared_by_oscillators :
    ForPhysLib.ClassicalMechanics.massK.dedicatedFor Oscillator.A whole =
      ForPhysLib.ClassicalMechanics.massK.dedicatedFor Oscillator.B whole :=
  KindOfProperty.dedicatedFor_congr rfl whole
```

_6. Refuse cross-oscillator substitution._ B's mass cannot fill A's slot, A's stiffness
cannot be divided by B's mass, and the two individual quantities cannot be added at this
layer. Total mass is physically meaningful, but whose total requires a whole; that is
L2's question:

```anchor refused_cross_oscillator
/--
error: Type mismatch
  massOf sys Oscillator.B
has type
  IndividualQuantity Oscillator.B ForPhysLib.ClassicalMechanics.massK ℝ
but is expected to have type
  IndividualQuantity Oscillator.A ForPhysLib.ClassicalMechanics.massK ℝ
-/
#guard_msgs in
example (sys : TwoOscillators) :
    IndividualQuantity Oscillator.A ForPhysLib.ClassicalMechanics.massK ℝ :=
  massOf sys Oscillator.B

/--
error: Application type mismatch: The argument
  massOf sys Oscillator.B
has type
  IndividualQuantity Oscillator.B ForPhysLib.ClassicalMechanics.massK ℝ
but is expected to have type
  IndividualQuantity Oscillator.A ForPhysLib.ClassicalMechanics.massK ℝ
in the application
  IndividualQuantity.add ⋯ (massOf sys Oscillator.A) (massOf sys Oscillator.B)
-/
#guard_msgs in
example (sys : TwoOscillators) :=
  IndividualQuantity.add DifferenceKind.ofScale
    (massOf sys Oscillator.A) (massOf sys Oscillator.B)

/--
error: Application type mismatch: The argument
  massOf sys Oscillator.B
has type
  IndividualQuantity Oscillator.B ForPhysLib.ClassicalMechanics.massK ℝ
but is expected to have type
  IndividualQuantity Oscillator.A ForPhysLib.ClassicalMechanics.massK ℝ
in the application
  IndividualQuantity.div h (stiffnessOf sys Oscillator.A) (massOf sys Oscillator.B)
-/
#guard_msgs in
example (sys : TwoOscillators) :=
  let h :=
    KindDiv.law
      (k₁ := ForPhysLib.ClassicalMechanics.springConstantK)
      (k₂ := ForPhysLib.ClassicalMechanics.massK)
      (k := ForPhysLib.ClassicalMechanics.omegaSquaredK)
  IndividualQuantity.div h (stiffnessOf sys .A) (massOf sys .B)
```

_7. A name is not a sort._ A nominal `Object` does not supply `Sorted System`, so the
catalogue cannot be dedicated through that name:

```anchor refused_unsorted_object
/--
error: failed to synthesize instance of type class
  Sorted System

Hint: Type class instance resolution failures can be inspected with the `set_option trace.Meta.synthInstance true` command.
-/
#guard_msgs in
example :=
  ForPhysLib.ClassicalMechanics.massK.dedicatedFor
    (⟨"oscillator A"⟩ : Object) whole
```
