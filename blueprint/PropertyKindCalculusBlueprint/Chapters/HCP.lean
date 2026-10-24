import Verso
import VersoManual
import VersoBlueprint
import PropertyKindCalculusBlueprint.References
import PropertyKindCalculusBlueprint.Chapters.HCP.L0_BlackBox
import PropertyKindCalculusBlueprint.Chapters.HCP.L1_TwoBodies
import PropertyKindCalculusBlueprint.Chapters.HCP.L2_ThePair
import PropertyKindCalculusBlueprint.Chapters.HCP.L3_TheBodyOpens
import PropertyKindCalculusBlueprint.Chapters.HCP.L4_OutOfTheLine
import PropertyKindCalculusBlueprint.Chapters.HCP.L5_Damping
import PropertyKindCalculusBlueprint.Chapters.HCP.L6_Requirements

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

The ladder starts with one black-box oscillator and adds a second oscillator as another
particular of the same sort. L2 opens each box into body and spring(s), then treats the
pair as a whole. Later steps open the body to its mass distribution, move out of the line,
optionally add damping, and finally state what must hold:

:::table +header
*
  * Ladder step
  * Refinement
  * Context change
  * New attributes
  * What goes wrong
  * PhysLib stage/source
  * Status
*
  * {ref "hcp-l0"}[L0 — The black box]
  * One homogeneous, rigid, point-like body on one ideal spring to a wall, along a line
  * One system; body and spring inside, wall outside; the wall is fixed and infinitely massive
  * Mass, stiffness, displacement, ω vs f, period
  * One oscillator. Bare reals accept the inverted period formula `√(m/k)`; `WithDim` refuses that but accepts angular frequency ω plus frequency f, which share dimension T⁻¹. Only distinct kinds refuse both.
  * Stages 0–1; upstream oscillator Basic and WithDim; ForPhysLib Kinds and Metrology; Exhibit C
  * Included here
*
  * {ref "hcp-l1"}[L1 — Two bodies]
  * One body inside each black-box oscillator
  * Two particulars of sort harmonic oscillator; each black box contains one body and its wall spring; the oscillators remain uncoupled
  * Same kinds, now indexed by the oscillator whole; its mass and stiffness share an index
  * Two separate oscillators, A and B. Cross-system contamination: with kinds but no bearer, B's mass can be used in A's frequency, because the kind is right. False identity: giving both oscillators one name makes them one system. Indexing each quantity by its oscillator refuses the first; an injective designation the second.
  * Stage 2; CaseStudies/HarmonicOscillator Attempt 4; HCP L1
  * Included here
*
  * {ref "hcp-l2"}[L2 — The pair is a system too]
  * The pair becomes a system in its own right
  * Opens each oscillator into body and spring(s); pair's own sort, whole and parts; coupling, parallel and series springs
  * Normal-mode frequency ω₊, total mass, effective stiffness
  * One coupled pair, opened into bodies A and B and springs kA, kC, kB. Aggregating what does not aggregate: the pair's mass is m_A + m_B, but its normal-mode frequency ω₊ is not ω_A + ω_B. Sort vs particular: the licence to add masses belongs to the sort 'coupled pair', not to the kind 'mass'; stiffnesses add in parallel but not in series.
  * Stage 3; HCP `pairMass`/`parallelStiffness`, Composition finding 4
  * Included here
*
  * {ref "hcp-l3"}[L3 — The body opens up]
  * Body A's centre of mass is off-axis, producing torque and wobble
  * Body A of pair P becomes a nominally indexed rigid composite with left/right halves; a body-fixed frame enters beside the lab frame
  * Per-half mass and position, centre of mass, inertia tensor, frame-specific angular velocity
  * Body A opened into two halves. Wrong carving: counting a half twice or leaving one out gives another mass. Weighted mean vs sum: the centre of mass is the mass-weighted mean of the halves' positions, and ω is the same for every half. Degenerate whole: a massless body has no centre of mass. Frames: the lab-frame ω put into the body-frame energy type-checks in PhysLib.
  * Stages 2–3 on RigidBody; Exhibits RigidBody and Composition; upstream `CM-RB-sphereI` informal lemma proved in `SolidSphereInertia.lean`
  * Included here
*
  * {ref "hcp-l4"}[L4 — Out of the line]
  * Motion in three dimensions, seen by a moving observer
  * Motion in 3-D, seen from the lab and a moving cart
  * Position vector, displacement, distance, velocity per frame
  * Pair P in 3-D, seen from the lab and a moving cart. Bearer erased: `distanceQ` cannot tell P's separation from Q's. Observer left implicit: one bare vector type accepts all three frame-conversion laws (displacement, velocity, relative position), though only one is right for each kind of vector.
  * Stages 0–4 on Space; Exhibit ReferenceFrame
  * Included here
*
  * {ref "hcp-l5"}[L5 — The oscillation dies out]
  * Add a damper (optional)
  * Add a damper to the nominally named oscillator
  * Damper `γ`, whole-system decay rate `δ`, and damping regime
  * Oscillator A with a damper. PhysLib's `γ` (kg/s), ISO's damping coefficient δ = γ/(2m) (s⁻¹), and ω₀ (rad/s) share symbols or dimensions; bare reals accept `γ < ω₀` and dimensions accept `δ + ω₀`.
  * Stage 1; upstream `DampedHarmonicOscillator`; ISO 80000-3 items 3-18 and 3-24
  * Included here (optional)
*
  * {ref "hcp-l6"}[L6 — What must hold]
  * What must hold
  * Requirement scope over refined context
  * Requirement, referent, gate
  * Requirements over pair P and the sort 'coupled pair'. Unstatable scope: without named sorts and particulars, 'every pair' and 'pair P' have nothing to quantify over; a scope naming a bare number is rejected.
  * Stage 4; `Tutorial.HarmonicOscillatorRequirements`, Audits, `checked_by`
  * Included here
:::

Every lesson line is quoted live from the `HCP` library through SubVerso anchors; the
blueprint build refuses drift. L1–L6 are included here, with L5 optional; the `Tutorial`
library remains the model-writer's separate track.

{include 1 PropertyKindCalculusBlueprint.Chapters.HCP.L0_BlackBox}

{include 1 PropertyKindCalculusBlueprint.Chapters.HCP.L1_TwoBodies}

{include 1 PropertyKindCalculusBlueprint.Chapters.HCP.L2_ThePair}

{include 1 PropertyKindCalculusBlueprint.Chapters.HCP.L3_TheBodyOpens}

{include 1 PropertyKindCalculusBlueprint.Chapters.HCP.L4_OutOfTheLine}

{include 1 PropertyKindCalculusBlueprint.Chapters.HCP.L5_Damping}

{include 1 PropertyKindCalculusBlueprint.Chapters.HCP.L6_Requirements}
