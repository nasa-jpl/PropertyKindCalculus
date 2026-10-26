import Verso
import VersoManual
import VersoBlueprint
import PropertyKindCalculusBlueprint.References

open Verso.Genre
open Verso.Genre.Manual
open Informal
open Verso.Code.External

set_option verso.exampleProject ".."
set_option verso.exampleModule "HCP.L0_BlackBox"

/-
---
hcp: 1
id: hcp-l0
persona: 'PhysLib contributor'
layer: PKC
pull: 'PhysLib accepts the wrong oscillator frequency when its parameters are bare reals; a dimension tag catches some mistakes but not differences of kind.'
improvement: 'Build-check one black-box oscillator and separate what bare reals, WithDim, and kinds can each distinguish.'
concepts:
  - informal: 'a body, spring, wall, and line of motion'
    formal: 'one system context with mass, stiffness, displacement, and frequency attributes'
    where: 'System-context card; Physlib.ClassicalMechanics.HarmonicOscillator'
  - informal: 'dimension tags on physical values'
    formal: 'WithDim d α carries dimension d in its type'
    where: 'Physlib.ClassicalMechanics.HarmonicOscillatorWithDim'
  - informal: 'frequency versus angular frequency'
    formal: 'distinct kinds with the same T⁻¹ dimension'
    where: 'PropertyKindCalculus.Iso80000.Part3; ForPhysLib.ClassicalMechanics.Metrology'
artifacts: ['Lean lesson HCP.L0_BlackBox', 'Blueprint chapter L0 — The black box']
tools: ['lake build HCP', 'python3 HCP/check-hcp.py']
exercises: 7
disclosure: ['bare-real reciprocal-frequency mistake', 'what WithDim checks', 'dimension/kind distinction', 'build-pinned refusals', 'system-context card']
owner: 'PKC methodology lead'
state:
  completed: []
---
-/

#doc (Manual) "L0 — The black box" =>
%%%
tag := "hcp-l0"
%%%

# Synopsis

## Purpose

Show a PhysLib contributor, on one oscillator (a rigid point body of mass m on an ideal spring of stiffness k fixed to a wall, moving in one dimension), what each level of typing checks. With bare `ℝ`, Lean accepts every expression built from m and k, so `√(m/k)` type-checks where `√(k/m)` was meant. With PhysLib's `WithDim`, each expression has a dimension in its type, so an expression of the wrong dimension fails to type-check, but two quantities of equal dimension are interchangeable. With PKC kinds, each quantity also has a kind in its type, so quantities of equal dimension but different kind, such as angular frequency (rad/s) and frequency (Hz), cannot be added. The rest of the ladder builds on this distinction.

## PKC vocabulary in scope

New at this step:
- `Quantity` — a magnitude of one fixed kind of property, with no bearer yet.
- `angularFrequencyDK` — a dimensioned angular-frequency kind (`.kind`, `.dim`).
- `angularFrequency`, `frequency` — two ISO 80000-3 kinds that share dimension T⁻¹.
- `massQ`, `springQ` — read PhysLib's oscillator mass and spring constant as kinded quantities.

## Verifiable properties

- The potential energy ½ k x² of PhysLib's `WithDim` oscillator has dimension M L² T⁻² (type-checked) `HCP.L0_BlackBox#potential_energy_dimension`.
- Under `WithDim`, `m/k` has dimension T² and `k/m` has dimension T⁻² (type-checked) `HCP.L0_BlackBox#quotient_dimensions`.
- The kinds angular frequency and frequency are unequal, and both have dimension T⁻¹ (theorem) `HCP.L0_BlackBox#distinct_kinds_same_dimension`.
- `ω + f`, for ω a `Quantity` of kind angular frequency and f a `Quantity` of kind frequency, fails to type-check: there is no `HAdd` instance for the two kinds (refused) `HCP.L0_BlackBox#refused_kind_addition`.
- `massQ S / springQ S`, the radicand of the inverted formula `√(m/k)`, fails to type-check: there is no `HDiv` instance dividing a mass by a spring constant (refused) `HCP.L0_BlackBox#refused_reciprocal_radicand`.

## Errors prevented

- Inverted formula: `√(m/k)` written where `√(k/m)` was meant. Bare reals accept it; with kinds, the quotient m/k fails to type-check (`HCP.L0_BlackBox#bare_reals`, `HCP.L0_BlackBox#refused_reciprocal_radicand`).
- Same dimension, different kind: an angular frequency ω (rad/s) added to a frequency f (Hz). `WithDim` accepts the sum because both have dimension T⁻¹; with kinds, it fails to type-check (`HCP.L0_BlackBox#frequency_alias`, `HCP.L0_BlackBox#distinct_kinds_same_dimension`, `HCP.L0_BlackBox#refused_kind_addition`).

# Persona

You are a PhysLib contributor: a physicist who writes Lean in PhysLib. You know Lean and PhysLib and trust `Dimension` and `WithDim`. This lesson begins in that vocabulary.

# Pull

The oscillator is one body on an ideal, massless spring fixed to an infinitely massive wall, moving along a line. The body is homogeneous, rigid, and point-like; those assumptions are revisited at L3. Its bare-real model has no type-level record of what mass and stiffness mean and accepts the reciprocal-frequency expression `√(m/k)` where `√(k/m)` was intended. A dimension tag can catch dimensional mistakes but cannot distinguish kinds that share a dimension. The system context comes before the attributes it needs.

# Risks at this step

- *Bare-real and dimension-only mistakes.* Bare reals accept `√(m/k)` where `√(k/m)` is the angular-frequency formula, and dimension-only types accept angular frequency plus cyclic frequency because both have dimension T⁻¹. The kinded checks pin these risks at `HCP.L0_BlackBox#bare_reals`, `HCP.L0_BlackBox#frequency_alias`, `HCP.L0_BlackBox#refused_kind_addition`, and `HCP.L0_BlackBox#refused_reciprocal_radicand`.

# Small rigorous improvement

At this level, treat the oscillator as one black box with one body, one ideal linear spring, a fixed wall, and a line of motion. The body is assumed homogeneous, rigid, and point-like; those assumptions are revisited at L3.

:::table +header
*
  * Question
  * Context change
  * Attribute change
  * Risk shown
  * PhysLib stage
*
  * Which quotient is the oscillator's angular frequency?
  * One oscillator, one body and spring.
  * Mass, stiffness, angular frequency.
  * Bare reals accept both `√(k/m)` and the mistaken `√(m/k)`.
  * Stages 0–1; HarmonicOscillator Basic and WithDim.
*
  * What does a dimension tag check?
  * Keep the same black box.
  * Potential energy carries the product dimension.
  * `WithDim` rejects assigning `m/k` to `k/m`'s dimension, but does not identify kinds.
  * PhysLib `HarmonicOscillatorWithDim`.
*
  * What does it not see?
  * Same one system.
  * Frequency and angular frequency share `T⁻¹`.
  * PhysLib `Frequency` has no kind distinction.
  * PhysLib `Optics.Frequency`; ISO 80000-3.
*
  * Which properties are these?
  * Record the measurement convention.
  * Frequency and angular frequency become separate kinds.
  * Same dimension does not imply same kind.
  * ForPhysLib Kinds and Metrology.
:::

At L0 the bearer stays informal: the System-context card section names one body, while the code uses values such as `Quantity k ℝ`. With only one of each part, no two bearers can yet be confused. L1 is where the bearer enters the type.

# Learning path

:::table +header
*
  * #
  * Do
  * Checked by `HCP.L0_BlackBox` anchor
  * Concept disclosed
*
  * 1
  * In the bare-real oscillator, write the reciprocal quotient under the square root.
  * `HCP.L0_BlackBox#bare_reals`
  * Bare reals do not distinguish the two formulas.
*
  * 2
  * Return the tagged potential energy at its declared dimension; inspect both quotient types and try the cross-assignment.
  * `HCP.L0_BlackBox#potential_energy_dimension`; `HCP.L0_BlackBox#quotient_dimensions`
  * `WithDim` accepts each quotient at its own dimension and rejects assigning `m/k` to `k/m`'s type.
*
  * 3
  * Pass an angular-frequency value typed as `WithDim T𝓭⁻¹ ℝ≥0` to a parameter typed as `Frequency`.
  * `HCP.L0_BlackBox#frequency_alias`
  * The alias accepts it because the dimensions and carrier types coincide; there is no kind distinction.
*
  * 4
  * Decide kind inequality and compare the paired dimensions.
  * `HCP.L0_BlackBox#distinct_kinds_same_dimension`
  * One dimension, two kinds.
*
  * 5
  * Try to add kinded angular frequency and frequency.
  * `HCP.L0_BlackBox#refused_kind_addition`
  * The kinded layer refuses cross-kind addition.
*
  * 6
  * Put the reciprocal mass/stiffness quotient under a square root in the kinded model.
  * `HCP.L0_BlackBox#refused_reciprocal_radicand`
  * The quotient fails before the square root: no registered edge.
*
  * 7
  * Write the L0 system context in prose.
  * This chapter's System-context card section
  * State the system boundary and assumptions before adding attributes.
:::

Worksheet: `HCP/Worksheets/L0_BlackBox.lean` · Solution: `HCP/L0_BlackBox.lean`

# Lesson

_1. Bare reals._ Write the reciprocal quotient in the upstream oscillator. Both
`√(k/m)` and `√(m/k)` elaborate as reals; the latter is accepted despite being the wrong
formula for angular frequency. A dimension library would reject the reciprocal quotient
because its dimension is not time⁻¹.

```anchor bare_reals
-- Bare reals: √(S.m / S.k) is accepted as a real although oscillator frequency uses √(S.k / S.m); the bare values cannot catch this reciprocal-radicand mistake.
example (S : ClassicalMechanics.HarmonicOscillator) : ℝ :=
  √(S.m / S.k)
```

_2. Dimensions._ Return the potential energy with the dimension declared by PhysLib.
Inspect both quotient result types, then try to assign `m/k` to the result type of `k/m`.
The build accepts each quotient at its own dimension and rejects that cross-assignment.
`WithDim` distinguishes the quotients by dimension, but it does not say which expresses
the intended physics.

```anchor potential_energy_dimension
-- Dimensions: `S.potentialEnergy x` is a `WithDim` value of dimension M·L²·T⁻²; it carries dimension, not an energy kind or oscillator bearer.
example (S : ClassicalMechanics.HarmonicOscillatorWithDim)
    (x : WithDim L𝓭 (EuclideanSpace ℝ (Fin 1))) :
    WithDim (M𝓭 * L𝓭 * L𝓭 * T𝓭⁻¹ * T𝓭⁻¹) ℝ :=
  S.potentialEnergy x
```

```anchor quotient_dimensions
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
```

_3. A dimension cannot distinguish kinds._ Pass the angular frequency to the PhysLib
frequency type: it is the same `WithDim T𝓭⁻¹ ℝ≥0` type. A dimension library accepts
interchange here because the types coincide.

```anchor frequency_alias
-- Kind vs dimension: A WithDim T⁻¹ value is accepted as Frequency; equal dimensions erase the distinction between cyclic and angular frequency.
example (ω : WithDim T𝓭⁻¹ ℝ≥0) : Frequency :=
  (fun f : Frequency => f) ω
```

_4. Name the kinds._ The angular-frequency kind and ISO 80000-3 frequency kind differ by
`decide`; the Metrology pairing gives them the same dimension by `rfl`. A dimension
library sees one dimension, while the kind layer retains the distinction.

```anchor distinct_kinds_same_dimension
-- Kind vs dimension: Proves that angular-frequency and frequency are distinct kinds even though both have dimension T⁻¹.
example :
    ForPhysLib.ClassicalMechanics.Kinds.angularFrequency ≠
      PropertyKindCalculus.Iso80000.Part3.frequency.kind := by decide

-- Kind vs dimension: Proves that angular frequency and frequency have equal dimension; equal dimension does not identify their kinds.
example :
    ForPhysLib.ClassicalMechanics.Metrology.angularFrequencyDK.dim =
      PropertyKindCalculus.Iso80000.Part3.frequency.dim := rfl
```

_5. Refuse unlike kinds._ Write the sum of kinded angular frequency and frequency. The
build pins the elaborator's refusal; a dimension-only library would permit the sum because
both have dimension `T⁻¹`.

```anchor refused_kind_addition
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
```

_6. Refuse the reciprocal radicand._ Put `m/k` beneath the square root using the
kinded oscillator attributes. Elaboration fails at the quotient because `mass / spring
constant` is not a registered edge; the square root is never formed. A dimension-only
library would accept the quotient as a value with some dimension.

```anchor refused_reciprocal_radicand
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
```

_7. Record the context._ The System-context card section of this chapter records the boundary and assumptions; no Lean data is needed for the prose context. At L0 the bearer remains informal and the code has quantities
such as `Quantity k ℝ`. There is one of each part, so no bearers can yet be confused;
L1 introduces the bearer as a type index.

# AI assistance contract

- Keep the contributor's terms: body, spring, wall, frequency, dimension.
- Quote each Lean check from its anchored lesson region; do not invent replacement declarations.
- State only what the build demonstrates. A guarded cross-assignment shows that `WithDim` distinguishes the quotient dimensions.
- Treat errors as evidence only when the pinned message is the elaborator's actual output.

# Questions to ask the model so far

:::table +header
*
  * Question
  * Check
  * What the verdict means
*
  * Does the bare-real model catch the reciprocal quotient?
  * `bare_reals`
  * No: both expressions have type `ℝ`.
*
  * Does `WithDim` distinguish `m/k` and `k/m`?
  * `quotient_dimensions`
  * Yes: the build accepts each at its own dimension and rejects the cross-assignment.
*
  * Can a dimension-only type tell frequency from angular frequency?
  * `frequency_alias`
  * No: both have type `Frequency`.
*
  * Do the kinds differ despite the shared dimension?
  * `distinct_kinds_same_dimension`
  * Yes: the kinds differ while their paired dimensions are equal.
*
  * Why does the kinded reciprocal quotient fail?
  * `refused_reciprocal_radicand`
  * `mass / springConstant` has no registered `KindDiv`, so no square-root argument is formed.
:::

# System-context card

:::table +header
*
  * Scope
  * System or component
  * Sort / status
  * L0 assumptions and attributes
*
  * System
  * The oscillator
  * Spring–mass oscillator
  * One body, one linear spring, a wall, and a line of motion.
*
  * Inside
  * Body
  * Homogeneous, rigid, point-like body
  * One mass; assumptions to be revisited at L3.
*
  * Inside
  * Spring
  * Linear spring
  * One spring; massless and ideal.
*
  * Outside
  * Wall
  * Fixed, infinitely massive wall
  * Boundary condition for the spring.
*
  * Outside
  * Line
  * One-dimensional line of motion
  * The motion is constrained to this line.
:::

This section records the bearer informally. The Lean expressions are dimension- or kind-indexed quantities without an object index; L1 introduces the bearer into the type.
