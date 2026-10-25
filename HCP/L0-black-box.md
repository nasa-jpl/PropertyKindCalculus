---
hcp: 1
id: l0-black-box
persona: 'PhysLib contributor'
layer: PKC
pull: 'PhysLib accepts the wrong oscillator frequency when its parameters are bare reals; a dimension tag catches some mistakes but not differences of kind.'
improvement: 'Build-check one black-box oscillator and separate what bare reals, WithDim, and kinds can each distinguish.'
concepts:
  - informal: 'a body, spring, wall, and line of motion'
    formal: 'one system context with mass, stiffness, displacement, and frequency attributes'
    where: '§7 System-context card; Physlib.ClassicalMechanics.HarmonicOscillator'
  - informal: 'dimension tags on physical values'
    formal: 'WithDim d α carries dimension d in its type'
    where: 'Physlib.ClassicalMechanics.HarmonicOscillatorWithDim'
  - informal: 'frequency versus angular frequency'
    formal: 'distinct kinds with the same T⁻¹ dimension'
    where: 'PropertyKindCalculus.Iso80000.Part3; ForPhysLib.ClassicalMechanics.Metrology'
artifacts: ['Lean lesson HCP.L0_BlackBox', 'L0 system-context card']
tools: ['lake build HCP', 'python3 HCP/check-hcp.py']
exercises: 7
disclosure: ['bare-real reciprocal-frequency mistake', 'what WithDim checks', 'dimension/kind distinction', 'build-pinned refusals', 'system-context card']
owner: 'PKC methodology lead'
state:
  completed: []
---

# L0 — The black box: one body, one spring, one line

## 1. Persona

You are a PhysLib contributor: a physicist who writes Lean in PhysLib. You know Lean and PhysLib and trust `Dimension` and `WithDim`. This lesson begins in that vocabulary.

## 2. Pull

The oscillator is a body on a spring, but its bare-real model has no type-level record of what mass and stiffness mean. It accepts the reciprocal-frequency expression `√(m/k)` where `√(k/m)` was intended. A dimension tag can catch dimensional mistakes; it cannot distinguish two kinds that share a dimension.

## 3. Small rigorous improvement

At this level, treat the oscillator as one black box with one body, one ideal linear spring, a fixed wall, and a line of motion. The body is assumed homogeneous, rigid, and point-like; those assumptions are revisited at L3.

| Question | Context change | Attribute change | Risk shown | PhysLib stage |
|---|---|---|---|---|
| Which quotient is the oscillator's angular frequency? | One oscillator, one body and spring. | Mass, stiffness, angular frequency. | Bare reals accept both `√(k/m)` and the mistaken `√(m/k)`. | Stages 0–1; HarmonicOscillator Basic and WithDim. |
| What does a dimension tag check? | Keep the same black box. | Potential energy carries the product dimension. | `WithDim` rejects assigning `m/k` to `k/m`'s dimension, but does not identify kinds. | PhysLib `HarmonicOscillatorWithDim`. |
| What does it not see? | Same one system. | Frequency and angular frequency share `T⁻¹`. | PhysLib `Frequency` has no kind distinction. | PhysLib `Optics.Frequency`; ISO 80000-3. |
| Which properties are these? | Record the measurement convention. | Frequency and angular frequency become separate kinds. | Same dimension does not imply same kind. | ForPhysLib Kinds and Metrology. |

At L0 the bearer stays informal: the card names one body, while the code uses values such as `Quantity k ℝ`. With only one of each part, no two bearers can yet be confused. L1 is where the bearer enters the type.

## 4. Learning path

| # | Do | Checked by `HCP.L0_BlackBox` anchor | Concept disclosed |
|---|---|---|---|
| 1 | In the bare-real oscillator, write the reciprocal quotient under the square root. | `HCP.L0_BlackBox#bare_reals` | Bare reals do not distinguish the two formulas. |
| 2 | Return the tagged potential energy at its declared dimension; inspect both quotient types and try the cross-assignment. | `HCP.L0_BlackBox#potential_energy_dimension`; `HCP.L0_BlackBox#quotient_dimensions` | `WithDim` accepts each quotient at its own dimension and rejects assigning `m/k` to `k/m`'s type. |
| 3 | Pass an angular-frequency value typed as `WithDim T𝓭⁻¹ ℝ≥0` to a parameter typed as `Frequency`. | `HCP.L0_BlackBox#frequency_alias` | The alias accepts it because the dimensions and carrier types coincide; there is no kind distinction. |
| 4 | Decide kind inequality and compare the paired dimensions. | `HCP.L0_BlackBox#distinct_kinds_same_dimension` | One dimension, two kinds. |
| 5 | Try to add kinded angular frequency and frequency. | `HCP.L0_BlackBox#refused_kind_addition` | The kinded layer refuses cross-kind addition. |
| 6 | Put the reciprocal mass/stiffness quotient under a square root in the kinded model. | `HCP.L0_BlackBox#refused_reciprocal_radicand` | The quotient fails before the square root: no registered edge. |
| 7 | Write the L0 context card in prose. | This section's §7 card | State the system boundary and assumptions before adding attributes. |

Worksheet: `HCP/Worksheets/L0_BlackBox.lean` · Solution: `HCP/L0_BlackBox.lean`

## 5. AI assistance contract

- Keep the contributor's terms: body, spring, wall, frequency, dimension.
- Quote each Lean check from its anchored lesson region; do not invent replacement declarations.
- State only what the build demonstrates. A guarded cross-assignment shows that `WithDim` distinguishes the quotient dimensions.
- Treat errors as evidence only when the pinned message is the elaborator's actual output.

## 6. Questions to ask the model so far

| Question | Check | What the verdict means |
|---|---|---|
| Does the bare-real model catch the reciprocal quotient? | `bare_reals` | No: both expressions have type `ℝ`. |
| Does `WithDim` distinguish `m/k` and `k/m`? | `quotient_dimensions` | Yes: the build accepts each at its own dimension and rejects the cross-assignment. |
| Can a dimension-only type tell frequency from angular frequency? | `frequency_alias` | No: both have type `Frequency`. |
| Do the kinds differ despite the shared dimension? | `distinct_kinds_same_dimension` | Yes: the kinds differ while their paired dimensions are equal. |
| Why does the kinded reciprocal quotient fail? | `refused_reciprocal_radicand` | `mass / springConstant` has no registered `KindDiv`, so no square-root argument is formed. |

## 7. System-context card

| Scope | System or component | Sort / status | L0 assumptions and attributes |
|---|---|---|---|
| System | The oscillator | Spring–mass oscillator | One body, one linear spring, a wall, and a line of motion. |
| Inside | Body | Homogeneous, rigid, point-like body | One mass; assumptions to be revisited at L3. |
| Inside | Spring | Linear spring | One spring; massless and ideal. |
| Outside | Wall | Fixed, infinitely massive wall | Boundary condition for the spring. |
| Outside | Line | One-dimensional line of motion | The motion is constrained to this line. |

The card records the bearer informally. The Lean expressions are dimension- or kind-indexed quantities without an object index; L1 introduces the bearer into the type.
