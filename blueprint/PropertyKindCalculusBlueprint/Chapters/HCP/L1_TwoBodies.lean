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

# Synopsis

## Purpose

Introduce the bearer: every quantity is about some particular system. With two black-box oscillators A and B, a quantity indexed by its oscillator lets A's own `k/m` through and refuses B's mass in A's formula; a nominal designation keeps A and B distinct systems even when their parameters match.

## PKC vocabulary in scope

New at this step:
- `SortOfSystem` — the universal category of a system, here "harmonic oscillator".
- `Sorted` (`sortOf`) — an object type whose objects know their sort.
- `Designated` (`designation`, `designation_inj`) — an object type whose objects have distinct nominal names.
- `IndividualQuantity` — a magnitude of kind `k` about one object `o`.
- `IndividualQuantity.add`, `IndividualQuantity.div` — same-object, kind-licensed arithmetic.
- `DifferenceKind.ofScale` — the difference law that licenses comparing two records of one quantity.
- `massK`, `springConstantK`, `omegaSquaredK` — the oscillator's kinds; k/m lands at `omegaSquaredK`.

Carried from earlier steps: `Quantity`, `massQ`, `springQ`.

## Verifiable properties

- Oscillators A and B have one sort (theorem) `HCP.L1_TwoBodies#oscillator_context_and_sort`.
- A and B have distinct designations, and a constant designation cannot be injective (theorem) `HCP.L1_TwoBodies#designation`.
- Oscillator A's own `k/m` type-checks at `omegaSquaredK` about A (type-checked) `HCP.L1_TwoBodies#oscillator_indexed_quantities`.
- Using B's mass where A's is expected is refused (refused) `HCP.L1_TwoBodies#refused_cross_oscillator`.
- Two records of oscillator A on rig R₁ give a typed change in A's mass (type-checked) `HCP.L1_TwoBodies#same_rig_estimate_difference`.
- An object type with no sort cannot bear a sorted quantity (refused) `HCP.L1_TwoBodies#refused_unsorted_object`.

## Errors prevented

- Cross-system contamination: oscillator B's mass entering oscillator A's frequency; bare reals and bearer-free kinds accept it, bearer-indexed quantities refuse it (`HCP.L1_TwoBodies#refused_cross_oscillator`).
- False identity: one name for both oscillators, so two systems are reported as one (`HCP.L1_TwoBodies#designation`).
- Unsorted bearer: a quantity about something that has no stated sort (`HCP.L1_TwoBodies#refused_unsorted_object`).


Two bodies are now in view, one inside each black-box oscillator: whose mass is this? Bare
reals and bearer-free kinded values let one oscillator's mass enter another's formula.
L1 indexes mass and stiffness by a rig-scoped oscillator, so its own `k/m` is accepted and
cross-oscillator operations are refused. One name is one system: records under that name
are its states at different times, its configurations, or rival estimates of it; comparing
them is the point. Different names are distinct systems, so R₁ and R₂ remain distinct even
when their parameter values match. Each oscillator is the whole characterized by `ω₀`;
this is why `k` and `m` share its index. L2 opens each box into body and spring(s), revisits
which component bears mass and stiffness, and considers the pair as a whole.

# Risks at this step

- *Cross-system contamination.* Oscillators A and B have the same kinds, so B's mass can enter A's frequency if the bearer is omitted; the cross-oscillator refusal is pinned at `HCP.L1_TwoBodies#refused_cross_oscillator`.
- *False identity.* Giving A and B one name makes two oscillators look like one system; the injective designation and its constant-name counterexample are pinned at `HCP.L1_TwoBodies#designation`.

*Further reading*
- `Exhibits/TwoRovers` (rovers A and B).
- `Exhibits/PointParticle`, finding 2.

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
constant name would report two oscillators as one, the false-identity risk:

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
stiffness therefore share its index. One `Rig` name is one system: two `TwoOscillators r`
records are its states at different times, configurations, or rival estimates, and
comparing their quantities is the point. `OscillatorOf r` keeps those records' oscillator
bearers shared; different rig names are distinct systems regardless of matching parameters.
Under L0's
massless-spring, fixed-wall assumptions, these magnitudes read the body's mass and
spring's stiffness. The existing kind table supplies the quotient law; the magnitude
theorem reads the real fields. The catalogue entry remains shared because both oscillators
have the same sort:

```anchor oscillator_indexed_quantities
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
```

The sort-level catalogue comparison uses `Sorted Oscillator`; the rig-scoped wrapper
needs no additional `Sorted` or `Designated` instance.

_6. Compare states; refuse cross-system substitution._ Two weighings of oscillator A at
different times on rig R₁ have a typed mass difference whose magnitude reads the later
and earlier real fields. B's mass cannot fill A's slot, A's stiffness cannot be divided by
B's mass, and the two different oscillators' quantities cannot be added at this layer. Nor
can same-named oscillator A masses be added across R₁ and R₂: those names identify
distinct systems. Total mass is physically meaningful, but whose total requires a whole;
that is L2's question:

```anchor refused_cross_oscillator
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
```

```anchor same_rig_estimate_difference
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
