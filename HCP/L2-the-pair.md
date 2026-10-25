---
hcp: 3
id: l2-the-pair
persona: "PhysLib contributor"
layer: PKC
pull: "Once A and B are coupled, what bears the total mass and the oscillation frequency?"
improvement: "Open the oscillator boxes into parts and model the pair as a whole with sort-specific aggregation licenses."
concepts:
  - informal: "two bodies and three springs form a coupled pair"
    formal: "Body, Spring, PairId, CoupledPair π with signed extensions, and PartOf π with pairS"
    where: "§7 System-context card; HCP.L2_ThePair#opened_pair"
  - informal: "the pair bears the total mass"
    formal: "pairMass has the pair-indexed Composite.whole and assembles body masses"
    where: "HCP.L2_ThePair#pair_mass"
  - informal: "normal-mode frequency belongs to the coupled pair"
    formal: "angularFrequency dedicated to pairS, not bodyS or springS"
    where: "HCP.L2_ThePair#normal_mode"
  - informal: "parallel stiffness adds, but series stiffness does not"
    formal: "Assembles parallelS springConstantK, with no series license"
    where: "HCP.L2_ThePair#parallel_stiffness; HCP.L2_ThePair#refused_series_stiffness"
artifacts: ['Lean lesson HCP.L2_ThePair', 'L2 system-context card']
tools: ['lake build HCP', 'python3 HCP/check-hcp.py']
exercises: 8
disclosure: ['open the oscillator boxes and compare configurations', 'assemble the pair mass', 'refuse whole plus part', 'refuse angular-frequency assembly', 'dedicate the normal mode to the pair', 'assemble parallel stiffness', 'refuse series stiffness', 'check the aggregation licenses against measurements']
owner: 'PKC methodology lead'
state:
  completed: []
---

# L2 — The pair is a system too

## Synopsis

### Purpose

Open each oscillator into bodies and springs, and treat the coupled pair as a system of its own. The licence to add a quantity over parts belongs to the sort of the whole, not to the kind: a pair's mass is the sum of its bodies' masses, its normal-mode frequency is not, and stiffnesses add in parallel but not in series.

### PKC vocabulary in scope

New at this step:
- `Composite` (`whole`, `part`) — the object type of a whole and its parts.
- `Decomposition` (`atom`, `union`) — how a whole is carved into parts.
- `Assembles` — the aggregation licence, keyed by the sort of the whole and the kind.
- `assemble` — fold a licensed quantity over a decomposition.
- `Extensive` — a kind whose value over a union is the sum over its parts.
- `DedicatedKind`, `KindOfProperty.dedicatedTo` — a kind dedicated to one sort, such as the pair's normal-mode frequency.
- `Component` — a named component of a system's characterization.
- `displacementK` — spring extension; negative compressed, positive stretched.

Carried from earlier steps: `IndividualQuantity`, `IndividualQuantity.add`, `DifferenceKind.ofScale`, `SortOfSystem`, `Sorted`, `Designated`, `massK`, `springConstantK`.

### Verifiable properties

- The pair's mass assembles from body A's and body B's masses (type-checked) `HCP.L2_ThePair#pair_mass`.
- Adding the whole pair's quantity to one body's is refused (refused) `HCP.L2_ThePair#refused_whole_part`.
- Assembling angular frequency over the pair is refused: no licence (refused) `HCP.L2_ThePair#refused_frequency_assembly`.
- The normal-mode frequency is dedicated to the pair as a whole (type-checked) `HCP.L2_ThePair#normal_mode`.
- Parallel stiffness assembles; series stiffness is refused (refused) `HCP.L2_ThePair#parallel_stiffness`, `HCP.L2_ThePair#refused_series_stiffness`.
- Parallel assembly agrees with the measured stiffness; the series law gives 2 for springs of 6 and 3 (theorem) `HCP.L2_ThePair#parallelLaw`, `HCP.L2_ThePair#licenseCashed`, `HCP.L2_ThePair#seriesLaw`.

### Errors prevented

- Aggregating what does not aggregate: taking ω₊ as ω_A + ω_B (`HCP.L2_ThePair#refused_frequency_assembly`).
- Sort vs particular: adding stiffnesses of springs in series as if they were in parallel (`HCP.L2_ThePair#refused_series_stiffness`).
- Whole/part confusion: adding pair P's mass to body A's mass (`HCP.L2_ThePair#refused_whole_part`).

## 1. Persona

You are a PhysLib contributor: a physicist who writes Lean in PhysLib. You know Lean and
PhysLib and trust `Dimension` and `WithDim`; L0 and L1 have established the oscillator
context and the bearer-indexed quantities.

## 2. Pull

Once A and B are coupled, what bears the total mass and the oscillation frequency? L1's
black boxes open: body A and body B carry mass, springs kA, kC, and kB carry stiffness,
and the coupled pair is a system of its own sort. Each wall-spring oscillator supplies its
body's mass and wall-spring stiffness; kC is the new coupling spring. The L1 assumption that
the oscillators do not interact has fallen. Following L1, one `PairId` name is one system.
Records under that name are its states at different times, configurations, or rival estimates
of it; comparing their shared-bearer quantities is the point, and different names are
distinct systems, so P and Q remain distinct even when their parameters match. Mass is borne by each
body and stiffness by each spring; L1's oscillator-indexed `ω² = k/m` does not survive
coupling. The normal-mode frequency belongs to the pair. Each spring also has a signed
extension: negative means compressed and positive means stretched. Two configurations of
pair P can compare their coupling-spring extensions with a typed displacement difference.

## Risks at this step

- **Aggregation.** In one coupled pair P, the pair mass is assembled from bodies A and B, but their normal-mode frequencies do not add; the mass assembly and frequency refusal are pinned at `HCP.L2_ThePair#pair_mass` and `HCP.L2_ThePair#refused_frequency_assembly`.
- **Sort versus particular.** The license to add body masses belongs to the coupled-pair sort, and parallel stiffness adds where series stiffness does not; the lesson pins the accepted parallel case and refused series case at `HCP.L2_ThePair#parallel_stiffness` and `HCP.L2_ThePair#refused_series_stiffness`.

**Further reading**
- `Exhibits/PointParticle`.
- `CaseStudies/PointParticle`.
- `Composite.Assembles` with `Exhibits/TwoRovers`.

## 3. Small rigorous improvement

| Question | Context change | Attribute change | Risk shown | PhysLib stage |
|---|---|---|---|---|
| Once A and B are coupled, what bears the total mass and the oscillation frequency? | Open the L1 black boxes into bodies A and B and springs kA, kC, kB; kC joins A and B, so they interact. The coupled pair has its own sort and a nominal PairId independent of its parameters; spring configurations also carry signed extensions. | Per-part mass, stiffness, and displacement; total mass of the pair; normal-mode angular frequency of the pair; effective stiffness. | The pair's mass adds from its bodies, but normal-mode frequency and series stiffness do not; parallel stiffness adds under its own sort-specific license. | Stage 3: sort-specific assembly licenses. |

With B clamped, A is held by its wall spring kA and the coupling spring kC in parallel.
The total mass belongs to the pair whole; angular frequency does not add across the bodies,
and a normal mode is a property of the coupled whole. The parallel stiffness is extensive
for the parallel sort, while series stiffness is whole-proper rather than additive. At L3,
each body is still assumed rigid, homogeneous, and point-like, with its mass on the spring
axis; an imbalance would make it wobble.

## 4. Learning path

| # | Do | Checked by `HCP.L2_ThePair` anchor | Concept disclosed |
|---|---|---|---|
| 1 | Open the boxes into bodies A/B and springs kA/kC/kB, give each part a nominal pair-indexed bearer, and compare compressed/stretched kC configurations of pair P. | `HCP.L2_ThePair#opened_pair` | Mass belongs to a body, stiffness and signed extension belong to a spring; `extensionOf` has a typed same-pair difference. |
| 2 | Assemble both body masses into the pair whole. | `HCP.L2_ThePair#pair_mass` | The pair-specific whole mass is the sum of its parts' masses, read from the real fields. |
| 3 | Try to add the pair mass to body A's mass and to a pair with identical parameters but a different PairId. | `HCP.L2_ThePair#refused_whole_part` | Whole and part are distinct bearers; P and Q are different systems even when all parameter values and part names match. |
| 4 | Try to assemble the bodies' angular frequencies into the pair. | `HCP.L2_ThePair#refused_frequency_assembly` | Angular frequency has no `Assembles` license for the pair sort. |
| 5 | Give the normal mode its dedicated kind at the pair sort. | `HCP.L2_ThePair#normal_mode` | The normal mode is neither a body nor a spring property. |
| 6 | With B clamped, assemble kA and kC as springs in parallel. | `HCP.L2_ThePair#parallel_stiffness` | The parallel whole has the sum of the two stiffness magnitudes. |
| 7 | Try to assemble kA and kB as two springs chained end to end. | `HCP.L2_ThePair#refused_series_stiffness` | No series-sort assembly license is registered. |
| 8 | Check the aggregation licenses on the exhibited pairs: parallel kA–kC and series kA–kB. | `HCP.L2_ThePair#parallelLaw`; `HCP.L2_ThePair#seriesLaw`; `HCP.L2_ThePair#licenseCashed` | Parallel stiffness adds; series kA–kB gives 6 ∥ 3 = 2. Integer measurements are exact only for the exhibited pairs and do not model longer chains. |

Worksheet: `HCP/Worksheets/L2_ThePair.lean` · Solution: `HCP/L2_ThePair.lean`

## 5. AI assistance contract

- Use the HCP-owned `Body`, `Spring`, `PartOf`, and `CoupledPair` types; do not import or reuse the Tutorial model.
- Keep body mass, spring stiffness, and pair normal-mode frequency on their respective bearers.
- Give each spring a signed displacement-kind extension (negative when compressed, positive when stretched), and compare configurations under the same `PairId`.
- Treat the pair as a whole distinct from every body and spring part.
- State that the L1 no-interaction assumption falls here and that L3 revisits the on-axis, rigid-body assumption.
- Use sort-specific `Assembles` licenses: mass for the pair and stiffness for parallel springs, but neither angular frequency for the pair nor stiffness for springs in series.
- Treat guarded elaboration errors as evidence only for the refusals they show.

## 6. Questions to ask the model so far

| Question | Check | What the verdict means |
|---|---|---|
| Where does total mass live? | `pair_mass` | On `Composite.whole`; the two body masses assemble there. |
| Can compressed and stretched configurations of pair P be compared by kC extension? | `opened_pair` | Yes; the typed displacement difference has magnitude `stretched.extension .kC - compressed.extension .kC`. |
| Can a whole mass be added to one of its parts? | `refused_whole_part` | No; their composite object indices differ. |
| Can two pairs' whole masses be added when their parameters are identical? | `refused_whole_part` | No; nominal `PartOf .P` and `PartOf .Q` have distinct bearer types independent of parameter values. |
| Does angular frequency assemble across the pair's bodies? | `refused_frequency_assembly` | No; the pair sort has no angular-frequency license. |
| What sort bears the normal mode? | `normal_mode` | The dedicated kind is attached to `pairS`, not `bodyS` or `springS`. |
| What happens to stiffness when kA and kC act in parallel? | `parallel_stiffness`, `parallelLaw` | The effective magnitude is their sum, and the measurement is extensive. |
| May the same summation rule be used for springs in series? | `refused_series_stiffness`, `seriesLaw`, `licenseCashed` | No; kA–kB reads 6 ∥ 3 = 2, and a hypothetical sum license reports 9. The `Int` examples are exact only for the exhibited pairs, not longer chains. |

## 7. System-context card

| Scope | System or component | Sort / status | L2 assumptions and attributes |
|---|---|---|---|
| System | Coupled pair | `pairS`; composite whole | Bodies A and B interact through kC. The normal-mode angular frequency belongs to the pair. |
| Part | Body A | `Body.A`, sort `bodyS` | Homogeneous, rigid, point-like; mass mA lies on the spring axis. |
| Part | Body B | `Body.B`, sort `bodyS` | Homogeneous, rigid, point-like; mass mB lies on the spring axis. |
| Part | Wall spring kA | `Spring.kA`, sort `springS` | Linear spring from body A to the fixed wall; stiffness kA and signed extension (negative compressed, positive stretched). |
| Part | Coupling spring kC | `Spring.kC`, sort `springS` | Linear spring joining bodies A and B; stiffness kC and signed extension (negative compressed, positive stretched). |
| Part | Wall spring kB | `Spring.kB`, sort `springS` | Linear spring from body B to the fixed wall; stiffness kB and signed extension (negative compressed, positive stretched). |
| Outside | Walls and line | Fixed, infinitely massive walls; one-dimensional motion | The wall springs remain attached to fixed boundaries and both bodies move along the line. |

The Lean model keeps each body's oscillator as the source of its mass and wall-spring
stiffness; `kC` is the pair's new coupling field, and `extensionOf` indexes each signed
displacement by its spring part. One `PairId` name is one system: records under it are states
at different times, configurations, or rival estimates to compare; distinct names are
distinct systems.
`PartOf π` uses nominal identity, so identical parameter records under P and Q still yield
different pair part types. The `Measurement`
numeral is an `Int`: the series example is exact for kA–kB (6 ∥ 3 = 2), but these integer
numerals do not model longer chains. L3 revisits the assumption that each body is rigid,
homogeneous, and point-like with its mass on the spring axis: if the mass is off-axis, the
body wobbles.
