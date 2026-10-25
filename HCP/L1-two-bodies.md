---
hcp: 2
id: l1-two-bodies
persona: 'PhysLib contributor'
layer: PKC
pull: 'Two bodies are now in view, one inside each oscillator: whose mass is this?'
improvement: 'Use nominal rig names: one name is one system, and its states, configurations, or estimates can be compared.'
concepts:
  - informal: 'two black-box harmonic oscillators, each with one body and wall spring'
    formal: 'Oscillator.A and Oscillator.B share oscillatorS'
    where: '§7 System-context card; HCP.L1_TwoBodies#oscillator_context_and_sort'
  - informal: 'the same kinded values without a bearer'
    formal: 'Quantity springConstantK ℝ / Quantity massK ℝ'
    where: 'HCP.L1_TwoBodies#kinded_bearer_free_cross_oscillators'
  - informal: 'a quantity about one particular oscillator'
    formal: 'IndividualQuantity o massK ℝ and IndividualQuantity o springConstantK ℝ share a rig-indexed OscillatorOf r bearer'
    where: 'HCP.L1_TwoBodies#oscillator_indexed_quantities'
  - informal: 'a catalogue entry shared by a sort'
    formal: 'dedicatedFor uses Sorted.sortOf rather than the object index'
    where: 'HCP.L1_TwoBodies#oscillator_indexed_quantities'
artifacts: ['Lean lesson HCP.L1_TwoBodies', 'L1 black-box oscillator card']
tools: ['lake build HCP', 'python3 HCP/check-hcp.py']
exercises: 7
disclosure: ['cross-oscillator bare-real substitution', 'bearer-free kinded quotient', 'oscillator sort and designation', 'same-oscillator k/m quotient', 'shared dedicated kind', 'cross-system refusals and same-rig time-state mass difference', 'nominal object has no sort']
owner: 'PKC methodology lead'
state:
  completed: []
---

# L1 — Two bodies

## Synopsis

### Purpose

Introduce the bearer: every quantity is about some particular system. With two black-box oscillators A and B, a quantity indexed by its oscillator lets A's own `k/m` through and refuses B's mass in A's formula; a nominal designation keeps A and B distinct systems even when their parameters match.

### PKC vocabulary in scope

New at this step:
- `SortOfSystem` — the universal category of a system, here "harmonic oscillator".
- `Sorted` (`sortOf`) — an object type whose objects know their sort.
- `Designated` (`designation`, `designation_inj`) — an object type whose objects have distinct nominal names.
- `IndividualQuantity` — a magnitude of kind `k` about one object `o`.
- `IndividualQuantity.add`, `IndividualQuantity.div` — same-object, kind-licensed arithmetic.
- `DifferenceKind.ofScale` — the difference law that licenses comparing two records of one quantity.
- `massK`, `springConstantK`, `omegaSquaredK` — the oscillator's kinds; k/m lands at `omegaSquaredK`.

Carried from earlier steps: `Quantity`, `massQ`, `springQ`.

### Verifiable properties

- Oscillators A and B have one sort (theorem) `HCP.L1_TwoBodies#oscillator_context_and_sort`.
- A and B have distinct designations, and a constant designation cannot be injective (theorem) `HCP.L1_TwoBodies#designation`.
- Oscillator A's own `k/m` type-checks at `omegaSquaredK` about A (type-checked) `HCP.L1_TwoBodies#oscillator_indexed_quantities`.
- Using B's mass where A's is expected is refused (refused) `HCP.L1_TwoBodies#refused_cross_oscillator`.
- Two records of oscillator A on rig R₁ give a typed change in A's mass (type-checked) `HCP.L1_TwoBodies#same_rig_estimate_difference`.
- An object type with no sort cannot bear a sorted quantity (refused) `HCP.L1_TwoBodies#refused_unsorted_object`.

### Errors prevented

- Cross-system contamination: oscillator B's mass entering oscillator A's frequency; bare reals and bearer-free kinds accept it, bearer-indexed quantities refuse it (`HCP.L1_TwoBodies#refused_cross_oscillator`).
- False identity: one name for both oscillators, so two systems are reported as one (`HCP.L1_TwoBodies#designation`).
- Unsorted bearer: a quantity about something that has no stated sort (`HCP.L1_TwoBodies#refused_unsorted_object`).

## 1. Persona

You are a PhysLib contributor: a physicist who writes Lean in PhysLib. You know Lean and
PhysLib and trust `Dimension` and `WithDim`; L0 has already shown what those dimensions
can and cannot distinguish.

## 2. Pull

There are two bodies now, one inside each black-box oscillator — whose mass is this? Bare
reals and bearer-free kinded values let one oscillator's mass enter another's formula.
L1 indexes mass and stiffness by an oscillator bearer scoped to a nominal `Rig`, so the
oscillator's own `k/m` is accepted and a cross-oscillator quotient is refused. One name is
one system: records under that name are its states at different times, its configurations,
or rival estimates of it; comparing them is the point. Different names, R₁ and R₂, denote
distinct systems even with identical oscillator parameters.

## Risks at this step

- **Cross-system contamination.** Oscillators A and B have the same kinds, so B's mass can be used in A's frequency if the bearer is omitted. The pinned cross-oscillator refusal is `HCP.L1_TwoBodies#refused_cross_oscillator`.
- **False identity.** Giving A and B one name makes two oscillators look like one system; the injective designation and its constant-name counterexample are pinned at `HCP.L1_TwoBodies#designation`.

**Further reading**
- `Exhibits/TwoRovers` (rovers A and B).
- `Exhibits/PointParticle`, finding 2.

## 3. Small rigorous improvement

| Question | Context change | Attribute change | Risk shown | PhysLib stage |
|---|---|---|---|---|
| There are two bodies now — whose mass is this? | Two particulars, Oscillator A and B, of one sort (harmonic oscillator); each black box contains one point-like body and its own wall spring. The oscillators do not interact. One name is one system; its records are states, configurations, or rival estimates to compare. R₁ and R₂ are distinct names even when parameters match. L2 opens each box into body and spring(s), and introduces their whole/part relations. | No new kinds: mass and stiffness share a rig-indexed oscillator bearer, allowing its `k/m` quotient. | B's mass can enter A's formula when only the kind is checked; one constant designation would collapse A and B into one system. | Stage 2: the kinded form carries its bearer. |

Under L0's assumptions, each oscillator is a homogeneous, rigid, point-like body on one
ideal, massless spring attached to a fixed, infinitely massive wall, along a line. The
oscillator's mass is its body's mass, and its stiffness is its spring's. The oscillator
is the whole characterized by `ω₀`, so `k` and `m` must carry the same oscillator index.
The two oscillators do not interact in L1. L2 revisits that assumption as it opens each
box into body and spring(s) and considers the pair as a whole.

## 4. Learning path

| # | Do | Checked by `HCP.L1_TwoBodies` anchor | Concept disclosed |
|---|---|---|---|
| 1 | Put oscillator B's mass in oscillator A's bare-real frequency radicand. | `HCP.L1_TwoBodies#bare_real_cross_oscillators` | The cross-oscillator expression elaborates as `ℝ`. |
| 2 | Form the same spring-constant/mass quotient from kinded, bearer-free values. | `HCP.L1_TwoBodies#kinded_bearer_free_cross_oscillators` | The registered `k/m` edge accepts values from different oscillators. |
| 3 | Declare oscillators A and B, give both the harmonic-oscillator sort, and compare their sorts. | `HCP.L1_TwoBodies#oscillator_context_and_sort` | Two particulars instantiate one sort. |
| 4 | Give the oscillators distinct designations and prove a constant designation is not injective. | `HCP.L1_TwoBodies#designation` | A valid `Designated` instance cannot collapse distinct oscillators. |
| 5 | Index mass and stiffness by one rig-scoped oscillator, form its `k/m`, and compare the mass catalogue entries. | `HCP.L1_TwoBodies#oscillator_indexed_quantities` | The accepted quotient reads the oscillator's fields; the dedicated mass kind is shared. |
| 6 | Try cross-oscillator substitutions and addition; compare two weighings of oscillator A at different times on R₁. | `HCP.L1_TwoBodies#refused_cross_oscillator`; `HCP.L1_TwoBodies#same_rig_estimate_difference` | Cross-oscillator operations and cross-rig addition are refused; the same-rig time states admit a typed mass difference whose magnitude reads the real fields. Total mass is meaningful, but whose total requires a whole; that is L2. |
| 7 | Ask for the mass kind dedicated to a nominal object with no sort. | `HCP.L1_TwoBodies#refused_unsorted_object` | A nominal `Object` cannot supply the `Sorted` instance required by `dedicatedFor`. |

Worksheet: `HCP/Worksheets/L1_TwoBodies.lean` · Solution: `HCP/L1_TwoBodies.lean`

## 5. AI assistance contract

- Keep the contributor's vocabulary: oscillator, body, mass, spring, and bearer.
- Quote each Lean check from its anchored L1 region; do not redefine PhysLib or PKC declarations.
- Distinguish a bearer-free `Quantity` from an `IndividualQuantity` indexed by an oscillator.
- Distinguish the oscillator label from its `OscillatorOf r` bearer, which is scoped to a nominal rig identity.
- Treat one `Rig` name as one system: its records are states at different times, configurations, or rival estimates to compare; distinct rig names denote distinct systems.
- Treat each oscillator as the whole at L1; body and spring become separate bearers when L2 opens the box.
- Treat the guarded elaboration messages as evidence only for the refusals they actually show.

## 6. Questions to ask the model so far

| Question | Check | What the verdict means |
|---|---|---|
| Can oscillator B's mass enter A's bare-real frequency? | `bare_real_cross_oscillators` | Yes; the expression has type `ℝ`. |
| Does kinding alone prevent the cross-oscillator quotient? | `kinded_bearer_free_cross_oscillators` | No; the registered `springConstantK / massK` edge accepts the two `Quantity` values. |
| Are oscillator A and B different sorts? | `oscillator_context_and_sort` | No; both have sort `harmonic oscillator`. |
| Can both oscillators be given one constant designation? | `designation` | The function is not injective, so it cannot witness `Designated Oscillator`. |
| Does the shared oscillator index admit its own `k/m` and refuse cross-oscillator `k/m`? | `oscillator_indexed_quantities`, `refused_cross_oscillator` | Yes; same-oscillator division is accepted, while A's stiffness over B's mass is refused. |
| Does the object index keep their masses apart? | `refused_cross_oscillator` | Yes; assignment and addition across A and B are refused. |
| Can two weighings of oscillator A at different times be compared on R₁? | `same_rig_estimate_difference` | Yes; the typed difference has magnitude `(later.osc .A).m - (earlier.osc .A).m`. |
| Can same-named oscillator A masses from R₁ and R₂ be added when their parameters are identical? | `refused_cross_oscillator` | No; `OscillatorOf .R₁` and `OscillatorOf .R₂` are distinct bearers by nominal identity. |
| Can a nominal name reach a dedicated kind? | `refused_unsorted_object` | Not without a sort; the nominal `Object` has no `Sorted` instance. |

## 7. System-context card

| Scope | System or component | Sort / status | L1 assumptions and attributes |
|---|---|---|---|
| System | Oscillator A | One particular of sort `harmonic oscillator` | Black box: one homogeneous, rigid, point-like body on one ideal, massless wall spring; mass mA and stiffness kA. |
| System | Oscillator B | One particular of sort `harmonic oscillator` | Same L0 assumptions; mass mB and stiffness kB. |
| Relation | A and B | Distinct, designated oscillators | The oscillators do not interact; L2 revisits this assumption. |
| Inside each box | Body and spring | Not separately indexed in L1 | The oscillator's mass is the body's mass; its stiffness is the spring's. L2 opens these components. |
| Outside | Walls | Fixed, infinitely massive walls | Each ideal spring has its own fixed-wall boundary. |
| Outside | Lines | One-dimensional lines of motion | Each oscillator's body remains constrained to its line. |

The Lean model takes each complete oscillator as its bearer, scoped to a nominal `Rig`:
`massOf`, `stiffnessOf`, and `omegaSqOf` share an `OscillatorOf r` index. One name is one
system; records under it are states at different times, configurations, or rival estimates
whose quantities are meant to be compared. R₁ and R₂ are distinct systems even when their
oscillator parameters match. The box opens into body and spring(s) at L2, where the question
of which component bears mass or stiffness becomes explicit.
