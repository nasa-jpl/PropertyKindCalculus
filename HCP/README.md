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
| 1 | **Two bodies.** Two point masses, each with its own wall spring. | Two particulars of one sort; an object index; injective designation. | No new kinds: the same mass and spring-constant kinds, now per bearer. | R1 contamination (body B's mass as body A's); R5 false identity. | Stage 2: the kinded form carries its bearer; CaseStudies/HarmonicOscillator Attempt 4; blueprint L1. | Included here |
| 2 | **The pair is a system too.** | The pair's own sort; whole and its parts; springs in parallel vs in series. | Normal-mode frequency ω₊ (a whole-only property), total mass, effective stiffness. | R2/R3/R4: mass assembles (3 + 5 = 8), ω does not (ω₊ = 5 ≠ 2 + 4); stiffness assembles in parallel, not in series. | Stage 3: operator table (`ω² = k/m`); case study, `pairMass`/`stiffnessParallel`; Composition finding 4. | Planned |
| 3 | **The body opens up.** The mass is not homogeneous; its centre of mass is off-axis, so it wobbles. | The body becomes a composite with a carving; a body-fixed frame enters. | Mass distribution, centre of mass, inertia tensor, lab vs body angular velocity. | R6 degenerate whole (`RigidBody ⟨0⟩`); R3 (the centre of mass is a weighted mean, not a sum); lab-ω fed where body-ω is required (Exhibit A finding 2). L0's assumption returns as the solid-sphere special case `(2/5) m R²`. | Stages 2–3 on RigidBody; Exhibits RigidBody and Composition; `Kinded/RigidBody` (parallel-axis theorem = the offset); upstream `CM-RB-sphereI` informal lemma is proved in `SolidSphereInertia.lean`. | Planned |
| 4 | **Out of the line.** Motion in 3-D space, seen by a moving observer. | Origin, points vs vectors, the observer's frame. | Position vector, displacement, distance. | The bearer `distanceQ` erases is a pair of points; R8's one carrier has three Galilean laws. | Stages 0–3 on Space (compact recap of the finished ladder); Exhibit ReferenceFrame. | Planned |
| 5 | *(Optional)* **Losing energy.** Add a damper. | New component and particular. | Damping coefficient; `γ² − 4mk` regimes. | A regime test can type-check with wrong kinds. | Stage 1; upstream DampedHarmonicOscillator. | Planned |
| 6 | **What must hold.** | Requirement scope over the refined context. | Requirement, referent, gate. | R7 scope over nominal objects. | Stage 4; `Tutorial.HarmonicOscillatorRequirements`, Audits, `checked_by`. | Planned |

L1 is included here; it introduces two uncoupled bodies and their wall springs. The
coupling spring and pair-as-system refinement belong to L2. The `examples/Tutorial/`
files and `Tutorial` library remain the model-writer's separate track.

## Running checks

Run `lake build HCP` to compile the lessons and `python3 HCP/check-hcp.py` to validate front matter, learning-path counts, live anchors, and required sections.

## Jargon

- **HCP:** Human Context Protocol; a bounded, build-checked lesson that makes a human's system context explicit alongside the formal attributes.
- **Pull:** the persona's motivating problem, stated in that person's terms.
- **Lowe's square:** the distinction between universal/particular and substantial/non-substantial categories.
- **System context:** the sorts of things, particular objects, their names and composition, and what lies outside the system.
- **Sort of system:** the universal category of a system's substantial bearer.
- **Kind of property:** the universal category of a non-substantial property, distinct from its dimension.
- **Bearer:** the system or object a property is about; the card records it at L0 and L1 makes it a type index.
- **Dimension-only metrology:** type-level tracking of dimensions such as mass or time, without a separate property-kind identity.
- **Refinement step:** a question that changes context and attributes together, with a concrete risk artifact and PhysLib stage.
