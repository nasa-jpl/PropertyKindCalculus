---
hcp: 3
id: l2-the-pair
persona: "PhysLib contributor"
layer: PKC
pull: "Once A and B are coupled, what bears the total mass and the oscillation frequency?"
improvement: "Open the oscillator boxes into parts and model the pair as a whole with sort-specific aggregation licenses."
concepts:
  - informal: "two bodies and three springs form a coupled pair"
    formal: "Body, Spring, Part, and CoupledPair with pairS"
    where: "§7 System-context card; HCP.L2_ThePair#opened_pair"
  - informal: "the pair bears the total mass"
    formal: "pairMass has the Composite.whole index and assembles body masses"
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
disclosure: ['open the oscillator boxes', 'assemble the pair mass', 'refuse whole plus part', 'refuse angular-frequency assembly', 'dedicate the normal mode to the pair', 'assemble parallel stiffness', 'refuse series stiffness', 'check the aggregation licenses against measurements']
owner: 'PKC methodology lead'
state:
  completed: []
---

# L2 — The pair is a system too

## 1. Persona

You are a PhysLib contributor: a physicist who writes Lean in PhysLib. You know Lean and
PhysLib and trust `Dimension` and `WithDim`; L0 and L1 have established the oscillator
context and the bearer-indexed quantities.

## 2. Pull

Once A and B are coupled, what bears the total mass and the oscillation frequency? L1's
black boxes open: body A and body B carry mass, springs kA, kC, and kB carry stiffness,
and the coupled pair is a system of its own sort. The wall-spring oscillators remain the
parts' models; kC is the new coupling spring. The L1 assumption that the oscillators do
not interact has fallen. Mass is borne by each body and stiffness by each spring; L1's
oscillator-indexed `ω² = k/m` does not survive coupling. The normal-mode frequency belongs
to the pair.

## 3. Small rigorous improvement

| Question | Context change | Attribute change | Risk shown | PhysLib stage |
|---|---|---|---|---|
| Once A and B are coupled, what bears the total mass and the oscillation frequency? | Open the L1 black boxes into bodies A and B and springs kA, kC, kB; kC joins A and B, so they interact. The coupled pair has its own sort. | Per-part mass and stiffness; total mass of the pair; normal-mode angular frequency of the pair; effective stiffness. | Whole/part confusion; aggregating a kind that does not aggregate (normal-mode frequency or series stiffness). | Stage 3: sort-specific assembly licenses; ForPhysLib Composition and the harmonic-oscillator square. |

With B clamped, A is held by its wall spring kA and the coupling spring kC in parallel.
The total mass belongs to the pair whole; angular frequency does not add across the bodies,
and a normal mode is a property of the coupled whole. The parallel stiffness is extensive
for the parallel sort, while series stiffness is whole-proper rather than additive. At L3,
each body is still assumed rigid, homogeneous, and point-like, with its mass on the spring
axis; an imbalance would make it wobble.

## 4. Learning path

| # | Do | Checked by `HCP.L2_ThePair` anchor | Concept disclosed |
|---|---|---|---|
| 1 | Open the boxes into bodies A/B and springs kA/kC/kB, and give the pair a sort of its own. | `HCP.L2_ThePair#opened_pair` | Mass belongs to a body and stiffness to a spring; the coupling spring is the new field. |
| 2 | Assemble both body masses into the pair whole. | `HCP.L2_ThePair#pair_mass` | The pair mass is the sum of its parts' masses, read from the real fields. |
| 3 | Try to add the pair mass to body A's mass. | `HCP.L2_ThePair#refused_whole_part` | Whole and part are distinct bearers and cannot be added. |
| 4 | Try to assemble the bodies' angular frequencies into the pair. | `HCP.L2_ThePair#refused_frequency_assembly` | Angular frequency has no `Assembles` license for the pair sort. |
| 5 | Give the normal mode its dedicated kind at the pair sort. | `HCP.L2_ThePair#normal_mode` | The normal mode is neither a body nor a spring property. |
| 6 | With B clamped, assemble kA and kC as springs in parallel. | `HCP.L2_ThePair#parallel_stiffness` | The parallel whole has the sum of the two stiffness magnitudes. |
| 7 | Try to assemble the two end-to-end springs as series stiffness. | `HCP.L2_ThePair#refused_series_stiffness` | No series-sort assembly license is registered. |
| 8 | Check the aggregation licenses against numerical measurements. | `HCP.L2_ThePair#parallelLaw`; `HCP.L2_ThePair#seriesLaw`; `HCP.L2_ThePair#licenseCashed` | Parallel stiffness is extensive; series stiffness is whole-proper, and registering its sum would lie. |

## 5. AI assistance contract

- Use the HCP-owned `Body`, `Spring`, `Part`, and `CoupledPair` types; do not import or reuse the Tutorial model.
- Keep body mass, spring stiffness, and pair normal-mode frequency on their respective bearers.
- Treat the pair as a whole distinct from every body and spring part.
- State that the L1 no-interaction assumption falls here and that L3 revisits the on-axis, rigid-body assumption.
- Use sort-specific `Assembles` licenses: mass for the pair and stiffness for parallel springs, but neither angular frequency for the pair nor stiffness for springs in series.
- Treat guarded elaboration errors as evidence only for the refusals they show.

## 6. Questions to ask the model so far

| Question | Check | What the verdict means |
|---|---|---|
| Where does total mass live? | `pair_mass` | On `Composite.whole`; the two body masses assemble there. |
| Can a whole mass be added to one of its parts? | `refused_whole_part` | No; their composite object indices differ. |
| Does angular frequency assemble across the pair's bodies? | `refused_frequency_assembly` | No; the pair sort has no angular-frequency license. |
| What sort bears the normal mode? | `normal_mode` | The dedicated kind is attached to `pairS`, not `bodyS` or `springS`. |
| What happens to stiffness when kA and kC act in parallel? | `parallel_stiffness`, `parallelLaw` | The effective magnitude is their sum, and the measurement is extensive. |
| May the same summation rule be used for springs in series? | `refused_series_stiffness`, `seriesLaw`, `licenseCashed` | No; series stiffness is whole-proper, and a hypothetical license admits a wrong sum. |

## 7. System-context card

| Scope | System or component | Sort / status | L2 assumptions and attributes |
|---|---|---|---|
| System | Coupled pair | `pairS`; composite whole | Bodies A and B interact through kC. The normal-mode angular frequency belongs to the pair. |
| Part | Body A | `Body.A`, sort `bodyS` | Homogeneous, rigid, point-like; mass mA lies on the spring axis. |
| Part | Body B | `Body.B`, sort `bodyS` | Homogeneous, rigid, point-like; mass mB lies on the spring axis. |
| Part | Wall spring kA | `Spring.kA`, sort `springS` | Linear spring from body A to the fixed wall; stiffness kA. |
| Part | Coupling spring kC | `Spring.kC`, sort `springS` | Linear spring joining bodies A and B; stiffness kC. |
| Part | Wall spring kB | `Spring.kB`, sort `springS` | Linear spring from body B to the fixed wall; stiffness kB. |
| Outside | Walls and line | Fixed, infinitely massive walls; one-dimensional motion | The wall springs remain attached to fixed boundaries and both bodies move along the line. |

The Lean model keeps each body's oscillator as the source of its mass and wall-spring
stiffness; `kC` is the pair's new coupling field. L3 revisits the assumption that each
body is rigid, homogeneous, and point-like with its mass on the spring axis: if the mass
is off-axis, the body wobbles.
