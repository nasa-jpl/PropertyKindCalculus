---
hcp: 6
id: l5-damping
persona: "PhysLib contributor"
layer: PKC
pull: "The oscillator loses energy. What must the model add, and how should it distinguish the damper's measurement from the whole oscillator's decay?"
improvement: "Add a nominal damped-oscillator system, designate its body, spring, and damper, and distinguish viscous damping from decay rate."
concepts:
  - informal: "damping makes mechanical energy decrease along a non-stationary solution"
    formal: "energy_dissipation_on_state and energy_not_conserved_on_state"
    where: "HCP.L5_Damping#energy_dissipation"
  - informal: "the damper's γ and the whole's δ are different kinds"
    formal: "dampingConstantOf, massOf, decayRateOf, and decayRateOf_magnitude"
    where: "HCP.L5_Damping#kinds_and_decay_rate"
  - informal: "decay rate and natural angular frequency share a dimension, not a kind"
    formal: "the accepted bare sum and the pinned kinded addition refusal"
    where: "HCP.L5_Damping#same_dimension_different_kinds"
  - informal: "the underdamped criterion is an explicit numerical comparison"
    formal: "underdamped_magnitude_test and the pinned kinded-order refusal"
    where: "HCP.L5_Damping#underdamped_regime"
  - informal: "same-name oscillator states can be compared, distinct names cannot"
    formal: "decayRateChange and decayRateChange_magnitude"
    where: "HCP.L5_Damping#same_oscillator_states"
artifacts: ['Lean lesson HCP.L5_Damping', 'HCP system-context card']
tools: ['lake build HCP', 'python3 HCP/check-hcp.py']
exercises: 5
disclosure: ['reuse PhysLib dissipation laws on HCP states', 'separate damper γ from whole-system δ', 'distinguish same-dimension kinds', 'make the underdamped comparison explicit', 'compare same-name states and refuse cross-system mixing']
owner: 'PKC methodology lead'
state:
  completed: []
---

# L5 — The oscillation dies out

## Synopsis

### Purpose

Optional. Add a viscous damper to oscillator A, so that its energy is no longer conserved. Three quantities are easy to confuse here: PhysLib's damping constant γ (kg/s); ISO 80000-3's damping coefficient δ = γ/(2m) (s⁻¹), which PhysLib calls the decay rate; and the angular frequency ω₀ (rad/s), which has the same dimension as δ. The lesson gives each its own kind, so adding δ to ω₀ fails to type-check. `decayRateOf` computes δ from one oscillator's γ and mass with `IndividualQuantity.div`, so oscillator B's mass cannot be used for oscillator A's δ.

### PKC vocabulary in scope

New at this step:
- `KindOfProperty` (`id`, `scale`) — define a kind of property; the lesson defines its own kind for γ.
- `ScaleType.ratio` — the scale type that licenses × and ÷.
- `dampingCoefficient` — ISO 80000-3 damping coefficient δ, dimension T⁻¹.
- `KindDiv`, `QuotientKind.ofRatio` — a curated quotient law, here δ = γ/(2m).
- `Quantity.add` — kind- and scale-gated addition.
- `IndividualQuantity.toQuantity` — forget the bearer.
- `angularFrequencyK` — the oscillator's ω.

Carried from earlier steps: DimensionedKind, `IndividualQuantity` and its `add`/`div`, `DifferenceKind.ofScale`, `SortOfSystem`, `Sorted`, `Designated`, `massK`, `springConstantK`.

### Verifiable properties

- The damped oscillator's energy decreases at the rate stated by PhysLib's energy-dissipation theorem (theorem) `HCP.L5_Damping#energy_dissipation`.
- `decayRateOf` divides A's γ by A's 2m, and its magnitude equals PhysLib's `decayRate`; using B's mass instead fails with a type mismatch (refused) `HCP.L5_Damping#kinds_and_decay_rate`.
- δ and ω₀ have the same dimension, T⁻¹, and adding them fails to type-check (refused) `HCP.L5_Damping#same_dimension_different_kinds`.
- PhysLib's `IsUnderdamped` is equivalent to δ < ω₀. Comparing the two as kinded quantities fails with a type mismatch, because their kinds differ; `IsUnderdamped` implies that the magnitude of δ is less than the magnitude of ω₀ (theorem) `HCP.L5_Damping#underdamped_regime`.
- Subtracting an earlier record of A's δ from a later one type-checks as an `IndividualQuantity` about A of the damping-coefficient kind, whose magnitude is the difference of the two decay rates; subtracting B's δ from A's fails with a type mismatch (type-checked) `HCP.L5_Damping#same_oscillator_states`.

### Errors prevented

- Similar names, different kinds: PhysLib's damping constant γ (kg/s) used as ISO's damping coefficient δ (s⁻¹) (`HCP.L5_Damping#kinds_and_decay_rate`).
- Same dimension, different kind: δ + ω₀, which dimensions alone accept (`HCP.L5_Damping#same_dimension_different_kinds`).
- Cross-system contamination: oscillator B's mass used in oscillator A's δ (`HCP.L5_Damping#kinds_and_decay_rate`).

## 1. Persona

You are a PhysLib contributor: a physicist who writes Lean in PhysLib. You know Lean,
PhysLib, `Dimension`, and `WithDim`. L0–L4 modeled an ideal, conservative oscillator;
this optional rung adds the damping that makes its energy decay.

## 2. Pull

The oscillator's motion fades. Add a damper, but do not confuse the damper's viscous
constant `γ` with the whole oscillator's decay rate `δ`. The nominal oscillator name
remains the system identity: one name is one system; records under that name are its
states at different times, configurations, or rival estimates of it—comparing them is
the point; distinct names are distinct systems.

## 3. Small rigorous improvement

| Question | Context change | Attribute change | Risk shown | PhysLib source |
|---|---|---|---|---|
| The oscillator loses energy. What must the model add, and how should it distinguish the damper's measurement from the whole oscillator's decay? | Add a damper to the oscillator and represent the whole as a nominally named `DampedRig`. | `γ` is measured on the damper and `m` on the body; both retain the whole oscillator's bearer. ISO damping coefficient `δ` and the damping regime belong to the whole. | Bare `γ < ω` and `δ + ω₀` compile despite wrong or distinct kinds; cross-system division and mixing A's and B's states are refused. | `DampedHarmonicOscillator.Basic`; ISO 80000-3 items 3-18, 3-24, and 3-25. |

L0–L4's conservation assumption ends here. The PhysLib dissipation law says that the
energy derivative is negative when the damper is active and the velocity is nonzero.
This rung is optional; the requirements lesson remains L6.

## 4. Learning path

| # | Do | Checked by `HCP.L5_Damping` anchor | Concept disclosed |
|---|---|---|---|
| 1 | Apply the upstream energy laws to the state stored in `DampedRig`. | `energy_dissipation` | The HCP wrapper does not restate the physics: it supplies its own `r.osc` to PhysLib's `energy_dissipation_rate` and `energy_not_conserved`. |
| 2 | Read `m` on the body and `γ` on the damper; form their typed decay-rate quotient on the whole oscillator. | `kinds_and_decay_rate` | Both readings retain bearer `o`; `m + m` expresses `2m` without dropping it. The local `KindDiv` licenses `γ/(m + m)`, and A's `γ` cannot be divided by B's mass. Bare `γ < ω` is accepted but wrong. |
| 3 | Compare `δ` with `ω₀` first as reals, then as kinds. | `same_dimension_different_kinds` | Both are `T⁻¹`, but damping coefficient and angular frequency are distinct kinds. The bare sum is accepted; kinded addition is refused. |
| 4 | State the underdamped criterion and make its erasure to real magnitudes visible. | `underdamped_regime` | PhysLib proves the decay-rate inequality; the kinded comparison is refused. The accepted magnitude comparison exposes the rad = 1 convention. |
| 5 | Compare earlier and later states of oscillator A; try to mix oscillator B. | `same_oscillator_states` | A typed difference measures A's change in decay rate; distinct nominal names cannot be combined. |

Worksheet: `HCP/Worksheets/L5_Damping.lean` · Solution: `HCP/L5_Damping.lean`

## 5. AI assistance contract

- Keep the lesson independent and use nominal `Osc | A | B` identity.
- Treat records under one name as states, configurations, or rival estimates of one
  system; compare them, and refuse different names.
- Keep `Body`, `Spring`, and `Damper` as designated particulars. Measure `γ` on the
  damper and `m` on the body, while retaining the whole oscillator as the bearer of both;
  place `δ` and the regime on the whole.
- Apply PhysLib laws to `r.osc`; every accepted HCP quantity must compute from the
  lesson's own state fields.
- Keep accepted formulas at the `IndividualQuantity` level; do not drop the oscillator
  bearer to build the decay-rate quotient.
- Keep the `γ` kind distinct from ISO 3-24 damping coefficient, even though the
  upstream formula relates them.
- Compare `δ` and `ω₀` by explicit magnitudes when showing the underdamped criterion;
  do not present their kinded comparison as licensed.
- Do not change ForPhysLib, PKC core, PhysLib, or Tutorial.

## 6. Questions to ask the model so far

| Question | Check | What the verdict means |
|---|---|---|
| Does the damper conserve mechanical energy? | `energy_dissipation` | No; with positive `γ` and nonzero velocity, the energy derivative is negative. |
| What does `γ` measure? | `kinds_and_decay_rate` | The viscous damping constant measured on the damper, not the ISO whole-system damping coefficient. |
| Can A's `γ` be divided by B's mass? | `kinds_and_decay_rate` | No; the quotient requires both quantities to share the same oscillator bearer. |
| What is `δ`? | `kinds_and_decay_rate` | PhysLib's `decayRate`, carried on the named whole and kinded as ISO 3-24 damping coefficient. |
| Can `δ` be added to `ω₀`? | `same_dimension_different_kinds` | Not as kinded quantities: both have dimension `T⁻¹`, but they are different kinds. |
| How is underdamping tested? | `underdamped_regime` | Compare magnitudes explicitly; the physical criterion is the dimensionless ratio `δ/ω₀ < 1`. |
| Can the damper-aging state be compared with another state of A? | `same_oscillator_states` | Yes; the typed change reads the later and earlier state fields. |
| Can A's `δ` be mixed with B's? | `same_oscillator_states` | No; distinct nominal names are distinct systems. |

## 7. System-context card

| Scope | System or component | Sort / status | L5 assumptions and attributes |
|---|---|---|---|
| System | Oscillator A or B | Nominal `Osc` | One name is one system; records under it are states, configurations, or rival estimates. Distinct names are distinct systems. |
| State | Damped oscillator | `DampedRig o` | Wraps the upstream damped oscillator; same-name records may describe different states. |
| Part | Body, spring, damper | Designated `PartOf o` | Mass `m` is measured on the body and viscous constant `γ` on the damper; both quantities retain the whole oscillator's bearer. The spring bears stiffness. |
| Attribute | Viscous damping constant | Custom ratio-scale kind | `γ` has units kg/s and is measured on the damper. |
| Attribute | Damping coefficient `δ` | ISO 80000-3, 3-24 | `decayRate`, in s⁻¹, belongs to the whole damped oscillator. |
| Attribute | Natural angular frequency `ω₀` | ISO 80000-3, 3-18 | Also `T⁻¹`, but a different kind from `δ`. |
| Regime | Underdamped | Whole-system predicate | `IsUnderdamped` is characterized upstream by `decayRate < ω`; the lesson compares real magnitudes explicitly. |
| Optional rung | L5 | Damping | L0–L4's no-dissipation assumption ends here. |
