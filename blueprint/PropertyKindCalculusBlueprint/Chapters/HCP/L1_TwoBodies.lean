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

/-
---
hcp: 2
id: hcp-l1
persona: 'PhysLib contributor'
layer: PKC
pull: 'Two bodies are now in view, one inside each oscillator: whose mass is this?'
improvement: 'Use nominal rig names: one name is one system, and its states, configurations, or estimates can be compared.'
concepts:
  - informal: 'two black-box harmonic oscillators, each with one body and wall spring'
    formal: 'Oscillator.A and Oscillator.B share oscillatorS'
    where: 'System-context card; HCP.L1_TwoBodies#oscillator_context_and_sort'
  - informal: 'the same kinded values without a bearer'
    formal: 'Quantity springConstantK ℝ / Quantity massK ℝ'
    where: 'HCP.L1_TwoBodies#kinded_bearer_free_cross_oscillators'
  - informal: 'a quantity about one particular oscillator'
    formal: 'IndividualQuantity o massK ℝ and IndividualQuantity o springConstantK ℝ share a rig-indexed OscillatorOf r bearer'
    where: 'HCP.L1_TwoBodies#oscillator_indexed_quantities'
  - informal: 'a catalogue entry shared by a sort'
    formal: 'dedicatedFor uses Sorted.sortOf rather than the object index'
    where: 'HCP.L1_TwoBodies#oscillator_indexed_quantities'
artifacts: ['Lean lesson HCP.L1_TwoBodies', 'Blueprint chapter L1 — Two bodies']
tools: ['lake build HCP', 'python3 HCP/check-hcp.py']
exercises: 7
disclosure: ['cross-oscillator bare-real substitution', 'bearer-free kinded quotient', 'oscillator sort and designation', 'same-oscillator k/m quotient', 'shared dedicated kind', 'cross-system refusals and same-rig time-state mass difference', 'nominal object has no sort']
owner: 'PKC methodology lead'
state:
  completed: []
---
-/

#doc (Manual) "L1 — Two bodies" =>
%%%
tag := "hcp-l1"
%%%

# Synopsis

## Purpose

Introduce the bearer: the particular system a quantity is about. The context has two black-box oscillators, A and B, each a body on a wall spring. An `IndividualQuantity o k ℝ` is a real magnitude of kind k about the object o, so the oscillator a quantity is about is part of its type. Dividing oscillator A's spring constant by oscillator A's mass type-checks and gives an `IndividualQuantity` of kind `omegaSquaredK` about A. Supplying oscillator B's mass where a mass about A is expected fails to type-check with a type mismatch. A `Designated` instance gives A and B distinct nominal names, so they remain two systems even when their parameter values are equal.

## PKC vocabulary in scope

New at this step:
- `SortOfSystem` — the universal category of a system, here "harmonic oscillator".
- `Sorted` (`sortOf`) — an object type whose objects know their sort.
- `Designated` (`designation`, `designation_inj`) — an object type whose objects have distinct nominal names.
- `IndividualQuantity` — a magnitude of kind `k` about one object `o`.
- `IndividualQuantity.add`, `IndividualQuantity.div` — same-object, kind-licensed arithmetic.
- `DifferenceKind.ofScale` — the difference law that licenses comparing two records of one quantity.
- `massK`, `springConstantK`, `omegaSquaredK` — the oscillator's kinds; k/m has kind `omegaSquaredK`.

Carried from earlier steps: `Quantity`, `massQ`, `springQ`.

## Verifiable properties

- Oscillators A and B have the same sort, harmonic oscillator (theorem) `HCP.L1_TwoBodies#oscillator_context_and_sort`.
- The designations of A and B are different, and a designation that gives every oscillator the same name is not injective, so it cannot be a `Designated` instance (theorem) `HCP.L1_TwoBodies#designation`.
- For each oscillator o, `omegaSqOf` divides o's spring constant by o's mass with `IndividualQuantity.div` and type-checks as an `IndividualQuantity` of kind `omegaSquaredK` about o, whose magnitude is o's k/m (type-checked) `HCP.L1_TwoBodies#oscillator_indexed_quantities`.
- Oscillator B's mass, supplied where a mass about A is expected, fails with a type mismatch: as a value, as an argument of `IndividualQuantity.add` or `IndividualQuantity.div`, and when oscillator A of rig R₁ is mixed with oscillator A of rig R₂ (refused) `HCP.L1_TwoBodies#refused_cross_oscillator`.
- Subtracting an earlier record of A's mass from a later one, both on rig R₁, type-checks as an `IndividualQuantity` of kind `massK` about A, using `DifferenceKind.ofScale`; its magnitude is the later mass minus the earlier mass (type-checked) `HCP.L1_TwoBodies#same_rig_estimate_difference`.
- Dedicating a kind to an object whose type has no `Sorted` instance fails to type-check (refused) `HCP.L1_TwoBodies#refused_unsorted_object`.

## Errors prevented

- Cross-system contamination: oscillator B's mass used in oscillator A's k/m. Bare reals and `Quantity` values without a bearer accept it; `IndividualQuantity` rejects it with a type mismatch (`HCP.L1_TwoBodies#bare_real_cross_oscillators`, `HCP.L1_TwoBodies#kinded_bearer_free_cross_oscillators`, `HCP.L1_TwoBodies#refused_cross_oscillator`).
- False identity: one name used for both oscillators, so A and B are reported as one system. The `designation_inj` proof that every `Designated` instance needs rules this out (`HCP.L1_TwoBodies#designation`).
- Unsorted bearer: a quantity about an object of no stated sort. It fails to type-check because no `Sorted` instance exists for the object's type (`HCP.L1_TwoBodies#refused_unsorted_object`).

# Persona

You are a PhysLib contributor: a physicist who writes Lean in PhysLib. You know Lean and
PhysLib and trust `Dimension` and `WithDim`; L0 has already shown what those dimensions
can and cannot distinguish.

# Pull

Two bodies are now in view, one inside each black-box oscillator: whose mass is this? Bare reals and bearer-free kinded values let one oscillator's mass enter another's formula. L1 indexes mass and stiffness by an oscillator bearer scoped to a nominal `Rig`, so its own `k/m` is accepted and cross-oscillator operations are refused. Each oscillator is the whole characterized by `ω₀`, which is why `k` and `m` share its index. One name is one system: records under that name are its states at different times, configurations, or rival estimates of it; comparing them is the point. Different names, R₁ and R₂, are distinct systems even when their parameters match. L2 opens each box into body and spring(s), revisits which component bears mass and stiffness, and considers the pair as a whole.

# Risks at this step

- *Cross-system contamination.* Oscillators A and B have the same kinds, so B's mass can enter A's frequency if the bearer is omitted; the cross-oscillator refusal is pinned at `HCP.L1_TwoBodies#refused_cross_oscillator`.
- *False identity.* Giving A and B one name makes two oscillators look like one system; the injective designation and its constant-name counterexample are pinned at `HCP.L1_TwoBodies#designation`.

*Further reading*
- `Exhibits/TwoRovers` (rovers A and B).
- `Exhibits/PointParticle`, finding 2.

# Small rigorous improvement

:::table +header
*
  * Question
  * Context change
  * Attribute change
  * Risk shown
  * PhysLib stage
*
  * There are two bodies now — whose mass is this?
  * Two particulars, Oscillator A and B, of one sort (harmonic oscillator); each black box contains one point-like body and its own wall spring. The oscillators do not interact. One name is one system; its records are states, configurations, or rival estimates to compare. R₁ and R₂ are distinct names even when parameters match. L2 opens each box into body and spring(s), and introduces their whole/part relations.
  * No new kinds: mass and stiffness share a rig-indexed oscillator bearer, allowing its `k/m` quotient.
  * B's mass can enter A's formula when only the kind is checked; one constant designation would collapse A and B into one system.
  * Stage 2: the kinded form carries its bearer.
:::

Under L0's assumptions, each oscillator is a homogeneous, rigid, point-like body on one
ideal, massless spring attached to a fixed, infinitely massive wall, along a line. The
oscillator's mass is its body's mass, and its stiffness is its spring's. The oscillator
is the whole characterized by `ω₀`, so `k` and `m` must carry the same oscillator index.
The two oscillators do not interact in L1. L2 revisits that assumption as it opens each
box into body and spring(s) and considers the pair as a whole.

# Learning path

:::table +header
*
  * #
  * Do
  * Checked by `HCP.L1_TwoBodies` anchor
  * Concept disclosed
*
  * 1
  * Put oscillator B's mass in oscillator A's bare-real frequency radicand.
  * `HCP.L1_TwoBodies#bare_real_cross_oscillators`
  * The cross-oscillator expression elaborates as `ℝ`.
*
  * 2
  * Form the same spring-constant/mass quotient from kinded, bearer-free values.
  * `HCP.L1_TwoBodies#kinded_bearer_free_cross_oscillators`
  * The registered `k/m` edge accepts values from different oscillators.
*
  * 3
  * Declare oscillators A and B, give both the harmonic-oscillator sort, and compare their sorts.
  * `HCP.L1_TwoBodies#oscillator_context_and_sort`
  * Two particulars instantiate one sort.
*
  * 4
  * Give the oscillators distinct designations and prove a constant designation is not injective.
  * `HCP.L1_TwoBodies#designation`
  * A valid `Designated` instance cannot collapse distinct oscillators.
*
  * 5
  * Index mass and stiffness by one rig-scoped oscillator, form its `k/m`, and compare the mass catalogue entries.
  * `HCP.L1_TwoBodies#oscillator_indexed_quantities`
  * The accepted quotient reads the oscillator's fields; the dedicated mass kind is shared.
*
  * 6
  * Try cross-oscillator substitutions and addition; compare two weighings of oscillator A at different times on R₁.
  * `HCP.L1_TwoBodies#refused_cross_oscillator`; `HCP.L1_TwoBodies#same_rig_estimate_difference`
  * Cross-oscillator operations and cross-rig addition are refused; the same-rig time states admit a typed mass difference whose magnitude reads the real fields. Total mass is meaningful, but whose total requires a whole; that is L2.
*
  * 7
  * Ask for the mass kind dedicated to a nominal object with no sort.
  * `HCP.L1_TwoBodies#refused_unsorted_object`
  * A nominal `Object` cannot supply the `Sorted` instance required by `dedicatedFor`.
:::

Worksheet: `HCP/Worksheets/L1_TwoBodies.lean` · Solution: `HCP/L1_TwoBodies.lean`

# Lesson

_1. Bare reals._ Put oscillator B's mass in oscillator A's frequency radicand. The
upstream oscillator accepts the cross-oscillator expression as a real:

```anchor bare_real_cross_oscillators
-- Bare reals: √(S₁.k / S₂.m) accepts oscillator A's stiffness and oscillator B's mass as a real; bare values cannot catch this cross-system radicand.
example (S₁ S₂ : ClassicalMechanics.HarmonicOscillator) : ℝ :=
  √(S₁.k / S₂.m)
```

_2. Kinded, but bearer-free._ The spring-constant/mass quotient also accepts values from
different oscillators. It is still a `Quantity`, with no oscillator index:

```anchor kinded_bearer_free_cross_oscillators
-- Bearer safety: A bearer-free Quantity omegaSquaredK accepts oscillator A's stiffness divided by oscillator B's mass; erasing the bearer leaves only the kind.
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

-- Same sort, distinct systems: Proves that sortOf assigns oscillator A and oscillator B the same sort, so sort alone does not identify either system.
example : Sorted.sortOf Oscillator.A = Sorted.sortOf Oscillator.B := rfl
```

_4. Designate without collapsing._ A designation gives each oscillator a nominal name.
`Designated` requires a proof, `designation_inj`, that the designation is injective: two
different oscillators never get the same name. Without that proof, anything keyed by name,
such as a report or a SysML export, could merge A and B into one system. This is the
false-identity risk. The instance below names A "oscillator A" and B "oscillator B" and
proves injectivity by cases. The theorem `constant_designation_not_injective` shows why a
lazy designation fails: the function that names every oscillator "oscillator" sends A and
B to the same name, so it is not injective, and no `Designated` instance can use it:

```anchor designation
instance : Designated Oscillator where
  designation
    | .A => ⟨"oscillator A"⟩
    | .B => ⟨"oscillator B"⟩
  designation_inj {x y} h := by
    cases x <;> cases y <;> first | rfl | exact absurd (System.mk.inj h) (by decide)

/-- Nominal identity: Proves that the constant designation gives oscillator A and oscillator B the same name, so it is not injective and cannot provide the `Designated` proof. -/
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

/-- Bearer safety: Proves that oscillator O's indexed omegaSquaredK magnitude equals O.k / O.m; the bearer index keeps stiffness and mass on the same oscillator. -/
theorem omegaSqOf_magnitude {r : Rig} (sys : TwoOscillators r) (o : OscillatorOf r) :
    (omegaSqOf sys o).magnitude = (sys.osc o.osc).k / (sys.osc o.osc).m := by
  rw [omegaSqOf, IndividualQuantity.div_magnitude, stiffnessOf, massOf]

def whole : Component := ⟨"whole"⟩

/-- Kind vs bearer: Proves that the mass kind dedicated to oscillator A's whole equals the kind dedicated to oscillator B's whole; only the bearer index distinguishes their masses. -/
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
-- Bearer safety: Refused: type mismatch between oscillator B's mass bearer and the required oscillator A bearer; this prevents substituting B's mass into an A-specific quantity.
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

-- Bearer safety: Refused: type mismatch between oscillator A's and oscillator B's mass bearers; this prevents adding across systems before introducing an assembly whole.
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

-- Bearer safety: Refused: type mismatch between oscillator A's stiffness bearer and oscillator B's mass bearer; this prevents a cross-oscillator k/m quotient.
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

-- Bearer safety: Refused: type mismatch between oscillator A on R₁ and oscillator A on R₂; this prevents conflating distinct rigs even when values match.
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

-- Same-name records: Constructs a massK IndividualQuantity about oscillator A on R₁, so earlier and later records of that rig can be compared.
#guard_msgs in
example (earlier later : TwoOscillators .R₁) :
    IndividualQuantity (⟨.A⟩ : OscillatorOf .R₁)
      ForPhysLib.ClassicalMechanics.massK ℝ :=
  oscillatorAMassDifference earlier later

/-- Same-name records: Proves that oscillator A's R₁ mass-difference magnitude is later mass minus earlier mass. -/
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
-- Bearer safety: Refused: no Sorted System instance lets Lean dedicate a mass kind to this nominal object; a name alone cannot supply a system sort.
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

# AI assistance contract

- Keep the contributor's vocabulary: oscillator, body, mass, spring, and bearer.
- Quote each Lean check from its anchored L1 region; do not redefine PhysLib or PKC declarations.
- Distinguish a bearer-free `Quantity` from an `IndividualQuantity` indexed by an oscillator.
- Distinguish the oscillator label from its `OscillatorOf r` bearer, which is scoped to a nominal rig identity.
- Treat one `Rig` name as one system: its records are states at different times, configurations, or rival estimates to compare; distinct rig names denote distinct systems.
- Treat each oscillator as the whole at L1; body and spring become separate bearers when L2 opens the box.
- Treat the guarded elaboration messages as evidence only for the refusals they actually show.

# Questions to ask the model so far

:::table +header
*
  * Question
  * Check
  * What the verdict means
*
  * Can oscillator B's mass enter A's bare-real frequency?
  * `bare_real_cross_oscillators`
  * Yes; the expression has type `ℝ`.
*
  * Does kinding alone prevent the cross-oscillator quotient?
  * `kinded_bearer_free_cross_oscillators`
  * No; the registered `springConstantK / massK` edge accepts the two `Quantity` values.
*
  * Are oscillator A and B different sorts?
  * `oscillator_context_and_sort`
  * No; both have sort `harmonic oscillator`.
*
  * Can both oscillators be given one constant designation?
  * `designation`
  * The function is not injective, so it cannot witness `Designated Oscillator`.
*
  * Does the shared oscillator index admit its own `k/m` and refuse cross-oscillator `k/m`?
  * `oscillator_indexed_quantities`, `refused_cross_oscillator`
  * Yes; same-oscillator division is accepted, while A's stiffness over B's mass is refused.
*
  * Does the object index keep their masses apart?
  * `refused_cross_oscillator`
  * Yes; assignment and addition across A and B are refused.
*
  * Can two weighings of oscillator A at different times be compared on R₁?
  * `same_rig_estimate_difference`
  * Yes; the typed difference has magnitude `(later.osc .A).m - (earlier.osc .A).m`.
*
  * Can same-named oscillator A masses from R₁ and R₂ be added when their parameters are identical?
  * `refused_cross_oscillator`
  * No; `OscillatorOf .R₁` and `OscillatorOf .R₂` are distinct bearers by nominal identity.
*
  * Can a nominal name reach a dedicated kind?
  * `refused_unsorted_object`
  * Not without a sort; the nominal `Object` has no `Sorted` instance.
:::

# System-context card

:::table +header
*
  * Scope
  * System or component
  * Sort / status
  * L1 assumptions and attributes
*
  * System
  * Oscillator A
  * One particular of sort `harmonic oscillator`
  * Black box: one homogeneous, rigid, point-like body on one ideal, massless wall spring; mass mA and stiffness kA.
*
  * System
  * Oscillator B
  * One particular of sort `harmonic oscillator`
  * Same L0 assumptions; mass mB and stiffness kB.
*
  * Relation
  * A and B
  * Distinct, designated oscillators
  * The oscillators do not interact; L2 revisits this assumption.
*
  * Inside each box
  * Body and spring
  * Not separately indexed in L1
  * The oscillator's mass is the body's mass; its stiffness is the spring's. L2 opens these components.
*
  * Outside
  * Walls
  * Fixed, infinitely massive walls
  * Each ideal spring has its own fixed-wall boundary.
*
  * Outside
  * Lines
  * One-dimensional lines of motion
  * Each oscillator's body remains constrained to its line.
:::

The Lean model takes each complete oscillator as its bearer, scoped to a nominal `Rig`:
`massOf`, `stiffnessOf`, and `omegaSqOf` share an `OscillatorOf r` index. One name is one
system; records under it are states at different times, configurations, or rival estimates
whose quantities are meant to be compared. R₁ and R₂ are distinct systems even when their
oscillator parameters match. The box opens into body and spring(s) at L2, where the question
of which component bears mass or stiffness becomes explicit.
