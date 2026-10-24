import Verso
import VersoManual
import VersoBlueprint
import PropertyKindCalculusBlueprint.References
import PropertyKindCalculusBlueprint.Chapters.HCP.L0_BlackBox
import PropertyKindCalculusBlueprint.Chapters.HCP.L1_TwoBodies
import PropertyKindCalculusBlueprint.Chapters.HCP.L2_ThePair

open Verso.Genre
open Verso.Genre.Manual
open Informal

#doc (Manual) "Onboarding: Human Context Protocols" =>
%%%
tag := "hcp"
%%%

This part is for a _PhysLib contributor_: a physicist who writes Lean in PhysLib and
already knows Lean, PhysLib, `Dimension`, and `WithDim`. The method is top-down refinement:
begin with the broad system context, then state the attributes of interest, interleaving
context and attribute refinement as new subsystems or phenomena enter the model.

Lowe's four-category square separates substantial things from ways things are, and
universals from particulars:

:::table +header
*
  * Axis
  * Substantial things
  * Non-substantial ways things are
*
  * Universal
  * Sort of system — `SortOfSystem`
  * Kind of property — `KindOfProperty`
*
  * Particular
  * System or object — index `o`
  * Individual quantity — `IndividualQuantity o k R`
:::

The left column is system context; dimension-only metrology attends to the right.

:::table +header
*
  * Risk
  * What goes wrong
  * Existing artifact
*
  * R1 — Cross-system contamination
  * Rover B's chassis mass enters rover A's total and still type-checks under `Dimension`.
  * `Exhibits/TwoRovers`
*
  * R2 — Wrong carving
  * Parts are under- or over-counted; alternative carvings deliver alternative numbers.
  * `Exhibits/TwoRovers`; `Exhibits/Composition`
*
  * R3 — Aggregating what does not aggregate
  * `∑ p, p.velocity` has the same shape as `System.mass`.
  * `Exhibits/PointParticle`; `CaseStudies/PointParticle`
*
  * R4 — Sort and particular confused
  * Rover 1 and the rover fleet become interchangeable; a kind-only license cannot distinguish rigid assembly from mixture.
  * `Composite.Assembles` keyed by sort; `Exhibits/TwoRovers` (mass licensed, angular velocity not)
*
  * R5 — False identity
  * A constant designation silently reports two particles as one system.
  * `Exhibits/PointParticle`, finding 2
*
  * R6 — Degenerate whole
  * `RigidBody ⟨0⟩` has zero mass and its centre of mass "is" the origin.
  * `Exhibits/Composition`, findings 2 and 5
*
  * R7 — Unstatable scope
  * "Every spring" and "body A" cannot be stated over nominal objects, so a requirement has no scope.
  * `MetrologicalModularity` scope clause; retained `Tutorial.HarmonicOscillatorRequirements`
*
  * R8 — Observer left implicit
  * One carrier, three Galilean transformation laws.
  * `Exhibits/ReferenceFrame`; MOTIVATION M7
:::

The ladder starts with one black-box oscillator and adds a second oscillator as another
particular of the same sort. L2 opens each box into body and spring(s), then treats the
pair as a whole. Later steps open the body to its mass distribution, move out of the line,
optionally add damping, and finally state what must hold:

:::table +header
*
  * L
  * Refinement
  * Context change
  * New attributes
  * Risk shown
  * PhysLib stage/source
  * Status
*
  * 0
  * The black box: one homogeneous, rigid, point-like body on one ideal spring to a wall, along a line
  * One system; body and spring inside, wall outside; the wall is fixed and infinitely massive
  * Mass, stiffness, displacement, ω vs f, period
  * A kind is not a dimension: `ω + f` and mistaken `√(m/k)` pass the bare-real model
  * Stages 0–1; upstream oscillator Basic and WithDim; ForPhysLib Kinds and Metrology; Exhibit C
  * Included here
*
  * 1
  * Two bodies
  * Two particulars of sort harmonic oscillator; each black box contains one body and its wall spring; the oscillators remain uncoupled
  * Same kinds, now indexed by the oscillator whole; its mass and stiffness share an index
  * R1 contamination across oscillators; R5 false identity; cross-oscillator division is refused
  * Stage 2; CaseStudies/HarmonicOscillator Attempt 4; HCP L1
  * Included here
*
  * 2
  * Pair as a system
  * Opens each oscillator into body and spring(s); pair's own sort, whole and parts; coupling, parallel and series springs
  * Normal-mode frequency ω₊, total mass, effective stiffness
  * R2/R3/R4: mass assembles, ω does not, stiffness assembles in parallel but not in series
  * Stage 3; HCP `pairMass`/`parallelStiffness`, Composition finding 4
  * Included here
*
  * 3
  * Body opens up: inhomogeneous mass with an off-axis centre of mass, so it wobbles
  * Composite body, carving, body-fixed frame
  * Mass distribution, centre of mass, inertia tensor, frame-specific angular velocity
  * R6 degenerate whole; R3 weighted mean; wrong angular-velocity frame. L0's assumption returns as the solid-sphere special case `(2/5) m R²`.
  * Stages 2–3 on RigidBody; Exhibits RigidBody and Composition; `Kinded/RigidBody`; upstream `CM-RB-sphereI` informal lemma proved in `SolidSphereInertia.lean`
  * Planned
*
  * 4
  * Out of the line
  * Motion in 3-D, seen by a moving observer
  * Position vector, displacement, distance
  * The bearer erased by `distanceQ` is a pair of points; R8's one carrier has three Galilean laws
  * Stages 0–3 on Space; Exhibit ReferenceFrame
  * Planned
*
  * 5
  * Losing energy (optional)
  * Add a damper
  * Damping coefficient; `γ² − 4mk` regimes
  * Regime test can type-check with wrong kinds
  * Stage 1; upstream `DampedHarmonicOscillator`
  * Planned
*
  * 6
  * What must hold
  * Requirement scope over refined context
  * Requirement, referent, gate
  * R7 scope over nominal objects
  * Stage 4; `Tutorial.HarmonicOscillatorRequirements`, Audits, `checked_by`
  * Planned
:::

Every lesson line is quoted live from the `HCP` library through SubVerso anchors; the
blueprint build refuses drift. This HCP sequence replaces the earlier Tutorial chapters.
The `Tutorial.HarmonicOscillatorRequirements` example remains cited by
MetrologicalModularity. L1 introduces two uncoupled black-box oscillators, each containing
one body and its wall spring; the oscillator is the bearer of mass and stiffness. L2 opens
each box, adds the coupling spring, and makes the coupled pair a system of its own sort.
Mass is borne by the bodies, stiffness by the springs, and the normal-mode angular
frequency by the pair. L3 revisits the assumption that each body is rigid, homogeneous,
point-like, and balanced on the spring axis.

{include 1 PropertyKindCalculusBlueprint.Chapters.HCP.L0_BlackBox}

{include 1 PropertyKindCalculusBlueprint.Chapters.HCP.L1_TwoBodies}

{include 1 PropertyKindCalculusBlueprint.Chapters.HCP.L2_ThePair}
