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

# Lesson


At L0, write one body on one ideal, massless spring to a fixed, infinitely massive wall,
with motion along a line. The body is assumed homogeneous, rigid, and point-like; these
assumptions are revisited at L3. The system context comes first, then the attributes it
needs.

_1. Bare reals._ Write the reciprocal quotient in the upstream oscillator. Both
`√(k/m)` and `√(m/k)` elaborate as reals; the latter is accepted despite being the wrong
formula for angular frequency. A dimension library would reject the reciprocal quotient
because its dimension is not time⁻¹.

```anchor bare_reals
example (S : ClassicalMechanics.HarmonicOscillator) : ℝ :=
  √(S.m / S.k)
```

_2. Dimensions._ Return the potential energy with the dimension declared by PhysLib.
Inspect both quotient result types, then try to assign `m/k` to the result type of `k/m`.
The build accepts each quotient at its own dimension and rejects that cross-assignment.
`WithDim` distinguishes the quotients by dimension, but it does not say which expresses
the intended physics.

```anchor potential_energy_dimension
example (S : ClassicalMechanics.HarmonicOscillatorWithDim)
    (x : WithDim L𝓭 (EuclideanSpace ℝ (Fin 1))) :
    WithDim (M𝓭 * L𝓭 * L𝓭 * T𝓭⁻¹ * T𝓭⁻¹) ℝ :=
  S.potentialEnergy x
```

```anchor quotient_dimensions
example (m : WithDim M𝓭 ℝ)
    (k : WithDim (M𝓭 * T𝓭⁻¹ * T𝓭⁻¹) ℝ) :
    WithDim (M𝓭 * (M𝓭 * T𝓭⁻¹ * T𝓭⁻¹)⁻¹) ℝ := m / k

example (m : WithDim M𝓭 ℝ)
    (k : WithDim (M𝓭 * T𝓭⁻¹ * T𝓭⁻¹) ℝ) :
    WithDim ((M𝓭 * T𝓭⁻¹ * T𝓭⁻¹) * M𝓭⁻¹) ℝ := k / m

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
example (ω : WithDim T𝓭⁻¹ ℝ≥0) : Frequency :=
  (fun f : Frequency => f) ω
```

_4. Name the kinds._ The angular-frequency kind and ISO 80000-3 frequency kind differ by
`decide`; the Metrology pairing gives them the same dimension by `rfl`. A dimension
library sees one dimension, while the kind layer retains the distinction.

```anchor distinct_kinds_same_dimension
example :
    ForPhysLib.ClassicalMechanics.Kinds.angularFrequency ≠
      PropertyKindCalculus.Iso80000.Part3.frequency.kind := by decide

example :
    ForPhysLib.ClassicalMechanics.Metrology.angularFrequencyDK.dim =
      PropertyKindCalculus.Iso80000.Part3.frequency.dim := rfl
```

_5. Refuse unlike kinds._ Write the sum of kinded angular frequency and frequency. The
build pins the elaborator's refusal; a dimension-only library would permit the sum because
both have dimension `T⁻¹`.

```anchor refused_kind_addition
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

_7. Record the context._ The prose system-context card is in `HCP/L0-black-box.md`; no
Lean card data is needed. At L0 the bearer remains informal and the code has quantities
such as `Quantity k ℝ`. There is one of each part, so no bearers can yet be confused;
L1 introduces the bearer as a type index.
