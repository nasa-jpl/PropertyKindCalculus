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

The question is not whether both bodies have a mass, but whose mass appears in a formula.
Two point masses share one sort and have one wall spring each. They do not interact here:
the coupling spring and the pair as a system belong to L2.

_1. Bare reals._ Put S₂'s mass in S₁'s frequency radicand. The upstream oscillator
accepts the cross-body expression as a real:

```anchor bare_real_cross_body
example (S₁ S₂ : ClassicalMechanics.HarmonicOscillator) : ℝ :=
  √(S₁.k / S₂.m)
```

_2. Kinded, but bearer-free._ The spring-constant/mass quotient also accepts values from
different oscillators. It is still a `Quantity`, with no body index:

```anchor kinded_bearer_free_cross_body
example (S₁ S₂ : ClassicalMechanics.HarmonicOscillator) :
    Quantity ForPhysLib.ClassicalMechanics.omegaSquaredK ℝ :=
  ForPhysLib.ClassicalMechanics.springQ S₁ /
    ForPhysLib.ClassicalMechanics.massQ S₂
```

_3. Declare the context._ A and B are distinct particulars of one sort. The two springs
are wall springs only; there is no coupling spring in this lesson:

```anchor context_and_sort
inductive Body | A | B
deriving DecidableEq, Repr

inductive Spring | kA | kB
deriving DecidableEq, Repr

def bodyS : SortOfSystem := ⟨"point mass"⟩
def springS : SortOfSystem := ⟨"linear spring"⟩

instance : Sorted Body := ⟨fun _ => bodyS⟩
instance : Sorted Spring := ⟨fun _ => springS⟩

example : Sorted.sortOf Body.A = Sorted.sortOf Body.B := rfl
```

_4. Designate without collapsing._ `Designated` requires an injective designation. A
constant name would report two bodies as one, the R5 false-identity risk:

```anchor designation
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
```

_5. Carry the bearer._ Mass is indexed by the body; stiffness is indexed by that body's
wall spring. The inverse lookup records the one-to-one `wallSpring` association. The
catalogue entry, by contrast, is shared because both bodies have the same sort:

```anchor bearer_indexed_quantities
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
```

_6. Refuse cross-body substitution._ B's mass cannot fill A's slot, and the two individual
quantities cannot be added at this layer. Total mass is physically meaningful, but whose
total requires a whole; that is L2's question:

```anchor refused_cross_body_mass
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
