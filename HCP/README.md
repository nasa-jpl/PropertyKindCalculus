# Human Context Protocols

A **Human Context Protocol (HCP)** is the human counterpart of an AI model-context protocol. It names a persona, a pull in that person's vocabulary, one bounded rigorous improvement, a graded learning path, and an AI-assistance contract.

The intended persona here is a **PhysLib contributor**: a physicist who writes Lean in PhysLib, knows Lean and PhysLib, and trusts `Dimension` and `WithDim`. Lessons proceed by top-down refinement, interleaving system context and attributes: start with the broad system, express the properties of interest, then add parts or phenomena and the attributes needed to account for them.

## Lowe's square

| | Substantial (things) | Non-substantial (ways things are) |
|---|---|---|
| **Universal** | Sort of system — `SortOfSystem` | Kind of property — `KindOfProperty` |
| **Particular** | System or object — the index `o` | Individual quantity — `IndividualQuantity o k R` |

Dimension-only metrology lives in the right column. System context is the left column: sorts, particulars, names, parts, wholes, and what lies outside.

## The ladder

Each HCP step asks a question, changes context, changes attributes, shows the risk as a build artifact, and exercises a PhysLib stage.
The lessons are rendered in the blueprint's "Onboarding: Human Context Protocols" part.

| L | Refinement | Context change | New attributes | What goes wrong | PhysLib stage, source | Status |
|---|---|---|---|---|---|---|
| [L0](../blueprint/PropertyKindCalculusBlueprint/Chapters/HCP/L0_BlackBox.lean) | **The black box.** One homogeneous, rigid, point-like body on one ideal spring to a wall, along a line. | One system; body and spring inside, wall outside; the wall is fixed and infinitely massive. | Mass, stiffness, displacement, ω vs f, period. | One oscillator. Bare reals accept the inverted period formula `√(m/k)`; `WithDim` refuses that but accepts angular frequency ω plus frequency f, which share dimension T⁻¹. Only distinct kinds refuse both. | Stages 0–1; upstream HarmonicOscillator Basic and WithDim; ForPhysLib Kinds and Metrology; Exhibit C. | Included here |
| [L1](../blueprint/PropertyKindCalculusBlueprint/Chapters/HCP/L1_TwoBodies.lean) | **Two bodies.** One body inside each black-box oscillator. | Two particulars of the harmonic-oscillator sort; the oscillator is the bearer and gets an injective designation. | No new kinds: mass and stiffness share the oscillator index, so its `k/m` is accepted. | Two separate oscillators, A and B. Cross-system contamination: with kinds but no bearer, B's mass can be used in A's frequency, because the kind is right. False identity: giving both oscillators one name makes them one system. Indexing each quantity by its oscillator refuses the first; an injective designation the second. | Stage 2: the kinded form carries its bearer; CaseStudies/HarmonicOscillator Attempt 4; blueprint L1. | Included here |
| [L2](../blueprint/PropertyKindCalculusBlueprint/Chapters/HCP/L2_ThePair.lean) | **The pair is a system too.** | Opens each oscillator into body and spring(s); the pair's own sort, whole, and parts; springs in parallel vs in series. | Normal-mode frequency ω₊ (a whole-only property), total mass, effective stiffness. | One coupled pair, opened into bodies A and B and springs kA, kC, kB. Aggregating what does not aggregate: the pair's mass is m_A + m_B, but its normal-mode frequency ω₊ is not ω_A + ω_B. Wrong composition law: the licence to add masses belongs to the sort 'coupled pair', not to the kind 'mass'; stiffnesses add in parallel but not in series. | Stage 3: operator table (`ω² = k/m`); HCP `pairMass`/`parallelStiffness`; Composition finding 4. | Included here |
| [L3](../blueprint/PropertyKindCalculusBlueprint/Chapters/HCP/L3_TheBodyOpens.lean) | **The body opens up.** Body A's centre of mass is off the spring axis, so the line of action misses it and the body wobbles. | Body A of pair P becomes a nominally indexed rigid composite with a left/right carving; a body-fixed frame enters beside the lab frame. | Per-half mass and position, centre of mass, inertia tensor, lab vs body angular velocity. | Body A opened into two halves. Wrong carving: counting a half twice or leaving one out gives another mass. Weighted mean vs sum: the centre of mass is the mass-weighted mean of the halves' positions, and ω is the same for every half. Degenerate whole: a massless body's centre of mass evaluates to the origin, because Lean defines 1/0 = 0. Frames: the lab-frame ω put into the body-frame energy type-checks in PhysLib. | Stages 2–3 on RigidBody; Exhibits RigidBody and Composition; upstream `CM-RB-sphereI` informal lemma is proved in `SolidSphereInertia.lean`. | Included here |
| [L4](../blueprint/PropertyKindCalculusBlueprint/Chapters/HCP/L4_OutOfTheLine.lean) | **Out of the line.** Motion in 3-D space, seen by a moving observer. | Pair centres become points in `Space 3`; lab and cart frames are explicit contexts. | Position vector, displacement, distance, velocity per frame. | Pair P in 3-D, seen from the lab and a moving cart. Bearer erased: `distanceQ` cannot tell P's separation from Q's. Observer left implicit: one bare vector type accepts all three frame-conversion laws (displacement, velocity, relative position), though only one is right for each kind of vector. | Stages 0–4 on Space; Exhibit ReferenceFrame. | Included here |
| [L5](../blueprint/PropertyKindCalculusBlueprint/Chapters/HCP/L5_Damping.lean) | *(Optional)* **Losing energy.** Add a damper. | New component and particular. | Damper `γ`, whole-system decay rate `δ`, and damping regime. | Oscillator A with a damper. PhysLib's `γ` (kg/s), ISO's damping coefficient δ = γ/(2m) (s⁻¹), and ω₀ (rad/s) share symbols or dimensions; bare reals accept `γ < ω₀` and dimensions accept `δ + ω₀`. | Stage 1; upstream DampedHarmonicOscillator. | Included here (optional) |
| [L6](../blueprint/PropertyKindCalculusBlueprint/Chapters/HCP/L6_Requirements.lean) | **What must hold.** | Requirement scope over the refined context. | Requirement, referent, gate. | Requirements over pair P and the sort 'coupled pair'. Unstatable scope: without named sorts and particulars, 'every pair' and 'pair P' have nothing to quantify over; a scope naming a bare number is rejected. | Stage 4; `Tutorial.HarmonicOscillatorRequirements`, Audits, `checked_by`. | Included here |

L1–L6 are included here; L5 is optional. The `Tutorial` library remains the model-writer's separate track.

## Worksheets and solutions

Each lesson has an editable worksheet in `HCP/Worksheets/` and a complete solution at
`HCP/Lk_<Name>.lean`. The worksheet follows the same exercise order and retains the context
needed later; fill each `TODO:` in place. Build a worksheet with
`lake build HCP.Worksheets.Lk_<Name>`. The solution modules and their SubVerso anchors remain
the source for the blueprint chapters.

## Recipes

### Work through a lesson

Open `HCP/Worksheets/L1_TwoBodies.lean`, run
`lake build HCP.Worksheets.L1_TwoBodies`, and fill its `TODO:`s in place. Compare your work
with `HCP/L1_TwoBodies.lean` and the corresponding blueprint chapter.

### Check a lesson's vocabulary against the SBVR, and regenerate the renderings

With a checkout of SBVR.lean beside this repository (`cd ../SBVR.lean && lake build sbvr-check`):

```sh
python3 HCP/check-hcp.py --sbvr ../SBVR.lean/.lake/build/bin/sbvr-check --fix-sbvr
```

checks the chain (every lesson refines the one before it, every quantity term is bound to a
kind, every definition reads as Structured English), rewrites `HCP/sbvr/rendered/*.md`, and
reports any name a chapter lists as new that the SBVR does not word. Without `--fix-sbvr` a
stale rendering is an error; without `--sbvr` the committed renderings are still checked
against the chapters. To ask what a phrase means at a step, or what changed between steps:

```sh
../SBVR.lean/.lake/build/bin/sbvr-check kinds  HCP/sbvr/physlib-contributor.yaml
../SBVR.lean/.lake/build/bin/sbvr-check lookup HCP/sbvr/physlib-contributor.yaml L3 "frame"
../SBVR.lean/.lake/build/bin/sbvr-check drift  HCP/sbvr/physlib-contributor.yaml L1 L6
```

After adding or renaming a `KindOfProperty` a lesson reads, regenerate the catalogue
(`lake build Interchange Iso80000 ForPhysLib HCP && lake env lean scripts/emit-sbvr-kinds.lean`);
CI runs the same script with `SBVR_KINDS_CHECK=1` and fails when the committed catalogue is not
the harvest.

### Update the blueprint excerpts after editing a lesson

Run `python3 HCP/check-hcp.py --fix-excerpts` after changing a lesson source. Verso keeps a copy
of each anchor and only re-checks it when the chapter rebuilds, so cached chapters can hide drift.

## The ladder in SBVR

[`sbvr/physlib-contributor.yaml`](sbvr/physlib-contributor.yaml) is this ladder as an SBVR
chain, checked by [SBVR.lean](https://github.jpl.nasa.gov/Foundation/SBVR.lean)'s `sbvr-check`
(its `docs/HCP.md` is the concept): one vocabulary per lesson, `L0 ⊂ L1 ⊂ … ⊂ L6`, each including
the one before it, plus `PKC`, this repository's foundation vocabulary (system context, sort of
system, kind of property, dimension, object — the Jargon below). A lesson's *PKC vocabulary in
scope — new at this step* is the lesson's own terms with one definition each, written in SBVR
Structured English against the terms in scope; *carried from earlier steps* is the inclusion
closure and is not restated — a lesson that lists a carried term as new (L4's `DifferenceKind`,
L5's `KindOfProperty`) records an *adoption* of the earlier definition, so `sbvr-check` reports
drift if it is ever worded differently. Every `KindOfProperty` a lesson reads is a *quantity
term*, adopted from the catalogue [`sbvr/kinds.yaml`](sbvr/kinds.yaml), which
`scripts/emit-sbvr-kinds.lean` harvests from the Lean kinds in scope (ISO 80000-3/4, ForPhysLib's
classical mechanics, the lessons' own) — so a term such as `spring constant` or
`viscous damping constant` means exactly the kind the Lean code declares, with its scale.
The English term is preferred and the Lean name is a synonym (`individual quantity`, also
`IndividualQuantity`); dotted names appear in the definition's source.

SBVR is the only source of the vocabulary: [`sbvr/rendered/`](sbvr/rendered/) holds
`sbvr-check render`'s output for `PKC` and each lesson, and `check-hcp.py` requires every name a
chapter lists as new at its step to be worded there. The conversion's own findings are
recorded in the chain file's comments and as these follow-ups: the lessons' *Verifiable
properties* and *Errors prevented* as rules with evidence (no rule schema in a chain file yet),
and `PKC ⊂ Foundation` — the root vocabulary of
[engineering-foundation-architecture](https://github.jpl.nasa.gov/Foundation/engineering-foundation-architecture)
`docs/hcp/foundation.yaml` — once a chain file can include a vocabulary from another file.

## Running checks

Run `lake build HCP` to compile the solutions and `lake build HCPWorksheets` to compile all
worksheets (which intentionally contain `sorry` holes). Run `python3 HCP/check-hcp.py` to
validate chapter front matter, the ten required sections, Synopsis structure and vocabulary,
learning-path rows, live anchors, worksheet structure, synchronized blueprint anchor
excerpts, and that every name a chapter lists as new at its step is worded in the ladder's SBVR
renderings (`HCP/sbvr/rendered/`); add `--sbvr SBVR_CHECK` to check the chain itself.

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
