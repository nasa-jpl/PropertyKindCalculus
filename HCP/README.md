# Human Context Protocols

A **Human Context Protocol (HCP)** is the human counterpart of an AI model-context protocol. It names a persona, a pull in that person's vocabulary, one bounded rigorous improvement, a graded learning path, and an AI-assistance contract.

The intended persona here is a **PhysLib contributor**: a physicist who writes Lean in PhysLib, knows Lean and PhysLib, and trusts `Dimension` and `WithDim`. Lessons proceed by top-down refinement, interleaving system context and attributes: start with the broad system, express the properties of interest, then add parts or phenomena and the attributes needed to account for them.

## Lowe's square

| | Substantial (things) | Non-substantial (ways things are) |
|---|---|---|
| **Universal** | Sort of system — `SortOfSystem` | Kind of property — `KindOfProperty` |
| **Particular** | System or object — the index `o` | Individual quantity — `IndividualQuantity o k R` |

Dimension-only metrology lives in the right column. System context is the left column: sorts, particulars, names, parts, wholes, and what lies outside.

## Risks of unstated context

| # | Risk | What goes wrong | Existing refusal artifact |
|---|---|---|---|
| R1 | Cross-system contamination | Rover B's chassis mass enters rover A's total and still type-checks under `Dimension`. | `Exhibits/TwoRovers` |
| R2 | Wrong carving | Parts are under- or over-counted; "alternative carvings deliver alternative numbers." | `Exhibits/TwoRovers` (under-count caught), `Exhibits/Composition` |
| R3 | Aggregating what does not aggregate | `∑ p, p.velocity` has the same shape as `System.mass`. | `Exhibits/PointParticle`, `CaseStudies/PointParticle` |
| R4 | Sort and particular confused | *Rover 1* and *the rover fleet* become interchangeable; a license keyed by kind alone cannot tell a rigid assembly from a mixture. | `Composite.Assembles` keyed by sort; `Exhibits/TwoRovers` (mass licensed, angular velocity not) |
| R5 | False identity | A constant designation silently reports two particles as one system. | `Exhibits/PointParticle`, finding 2 (`Designated s.Particle` honestly absent) |
| R6 | Degenerate whole | `RigidBody ⟨0⟩` has zero mass and its centre of mass "is" the origin. | `Exhibits/Composition`, findings 2 and 5 |
| R7 | Unstatable scope | "Every spring" and "body A" cannot be stated over nominal objects, so a requirement has no scope. | `MetrologicalModularity` requirement-scope clause; retained `Tutorial.HarmonicOscillatorRequirements` |
| R8 | Observer left implicit | One carrier, three Galilean transformation laws. | `Exhibits/ReferenceFrame` (MOTIVATION M7) |

## The ladder

Each HCP step asks a question, changes context, changes attributes, shows the risk as a build artifact, and exercises a PhysLib stage.

| L | Refinement | Context change | New attributes | Risk shown | PhysLib stage, source | Status |
|---|---|---|---|---|---|---|
| 0 | **The black box.** One homogeneous, rigid, point-like body on one ideal spring to a wall, along a line. | One system; body and spring inside, wall outside; the wall is fixed and infinitely massive. | Mass, stiffness, displacement, ω vs f, period. | A kind is not a dimension: `ω + f` and mistaken `√(m/k)` pass the bare-real model. | Stages 0–1; upstream HarmonicOscillator Basic and WithDim; ForPhysLib Kinds and Metrology; Exhibit C. | Included here |
| 1 | **Two bodies.** One body inside each black-box oscillator. | Two particulars of the harmonic-oscillator sort; the oscillator is the bearer and gets an injective designation. | No new kinds: mass and stiffness share the oscillator index, so its `k/m` is accepted. | R1 contamination (body B's mass as body A's); R5 false identity; cross-oscillator `IndividualQuantity.div` is refused. | Stage 2: the kinded form carries its bearer; CaseStudies/HarmonicOscillator Attempt 4; blueprint L1. | Included here |
| 2 | **The pair is a system too.** | Opens each oscillator into body and spring(s); the pair's own sort, whole, and parts; springs in parallel vs in series. | Normal-mode frequency ω₊ (a whole-only property), total mass, effective stiffness. | R2/R3/R4: mass assembles; ω does not; stiffness assembles in parallel, not in series. | Stage 3: operator table (`ω² = k/m`); HCP `pairMass`/`parallelStiffness`; Composition finding 4. | Included here |
| 3 | **The body opens up.** Body A's centre of mass is off the spring axis, so the line of action misses it and the body wobbles. | Body A of pair P becomes a nominally indexed rigid composite with a left/right carving; a body-fixed frame enters beside the lab frame. | Per-half mass and position, centre of mass, inertia tensor, lab vs body angular velocity. | R6 degenerate whole (`RigidBody ⟨0⟩`); R3 (centre of mass is a weighted mean and ω is intensive, not summed); lab-ω fed where body-ω is required. L0's assumption returns as the solid-sphere special case `(2/5) m R²`. | Stages 2–3 on RigidBody; Exhibits RigidBody and Composition; upstream `CM-RB-sphereI` informal lemma is proved in `SolidSphereInertia.lean`. | Included here |
| 4 | **Out of the line.** Motion in 3-D space, seen by a moving observer. | Pair centres become points in `Space 3`; lab and cart frames are explicit contexts. | Position vector, displacement, distance, velocity per frame. | `distanceQ` erases the pair bearer; bare vectors accept three transport laws; kinded vectors enforce the role and frame. | Stages 0–4 on Space; Exhibit ReferenceFrame. | Included here |
| 5 | *(Optional)* **Losing energy.** Add a damper. | New component and particular. | Damping coefficient; `γ² − 4mk` regimes. | A regime test can type-check with wrong kinds. | Stage 1; upstream DampedHarmonicOscillator. | Planned |
| 6 | **What must hold.** | Requirement scope over the refined context. | Requirement, referent, gate. | R7 scope over nominal objects. | Stage 4; `Tutorial.HarmonicOscillatorRequirements`, Audits, `checked_by`. | Included here |

L1–L4 and L6 are included here. L1 makes each uncoupled black-box oscillator the bearer of
mass and stiffness; L2 opens the boxes into bodies and springs, adds the coupling spring,
and gives the pair its own sort and whole. L3 opens body A into nominally indexed halves,
shows that an off-axis centre of mass creates torque, and distinguishes body- from
lab-frame angular velocity. L4 replaces the one-dimensional, one-observer view with
state-indexed points and pair separation in 3-D, then makes the lab and cart observers
explicit. L6 gives requirements scopes over `pairS` and nominal object P: the scope can be
written because earlier levels named sorts and particulars. Optional L5 remains planned;
the no-dissipation assumption is still deferred. The full worked requirements example is
`examples/Tutorial/HarmonicOscillatorRequirements.lean`; L6 does not import it. The
`Tutorial` library remains the model-writer's separate track.

## Running checks

Run `lake build HCP` to compile the lessons and `python3 HCP/check-hcp.py` to validate front matter, learning-path counts, live anchors, and required sections.

## Jargon

- **HCP:** Human Context Protocol; a bounded, build-checked lesson that makes a human's system context explicit alongside the formal attributes.
- **Pull:** the persona's motivating problem, stated in that person's terms.
- **Lowe's square:** the distinction between universal/particular and substantial/non-substantial categories.
- **System context:** the sorts of things, particular objects, their names and composition, and what lies outside the system.
- **Sort of system:** the universal category of a system's substantial bearer.
- **Kind of property:** the universal category of a non-substantial property, distinct from its dimension.
- **Bearer:** the system or object a property is about; L1 indexes quantities by the whole oscillator, and L2 opens that box into body and spring bearers.
- **Dimension-only metrology:** type-level tracking of dimensions such as mass or time, without a separate property-kind identity.
- **Refinement step:** a question that changes context and attributes together, with a concrete risk artifact and PhysLib stage.
