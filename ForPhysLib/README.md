# A metrology layer for PhysLib — a proposal

PhysLib's `Dimension` layer is the right bottom layer. This is a proposal for what sits
above it, why, and how to adopt it one directory at a time without a rewrite.

**The claim, in one paragraph.** PhysLib's metrological content is largely carried by
naming conventions — `angularVelocity` vs `bodyAngularVelocity`, `partitionFunction` vs
`mathematicalPartitionFunction`, `lagrangian t x v` vs `hamiltonian t p x` — and by prose
in docstrings, where the checker cannot reach it. The library says so itself, in three
separate modules. A *kind* layer above `Dimension` makes those distinctions types. It costs
ceremony, and this proposal is explicit about how much and where it is paid back.

## What is here

| file | what it is |
|---|---|
| [REQUIREMENTS.md](REQUIREMENTS.md) | 31+1 requirements in 9 tiers (MR32 appended after the first scoring pass), each with a stable heading to link to |
| [MOTIVATION.md](MOTIVATION.md) | 10 reasons, strongest first, each with a stable heading |
| [PLAN.md](PLAN.md) | the staged adoption ladder, the exhibits to build, and what to propose upstream |
| [CaseStudies/HarmonicOscillator](CaseStudies/HarmonicOscillator/README.md) | the worked benchmark: four attempts at typing the same physics, scored — `lake build ForPhysLib` |
| [Exhibits/](Exhibits) | six build-artifact exhibits, A–F; F is [physlib#1612](https://github.com/leanprover-community/physlib/pull/1612), a live PR that ties quantities to objects without a metrology layer |

## Where this came from

[physlib#1579](https://github.com/leanprover-community/physlib/pull/1579), where
jstoobysmith observed that the `Dimension`/`Unit` layer is under-used, suggested the
harmonic oscillator as a place to start, and the thread raised **ergonomics**. The case
study is that suggestion carried out — and it exposes both what dimensional analysis
structurally cannot do and what it costs to fix.

**What was surveyed.** The twelve `API-map.yaml` files under `PhysLib/SpaceAndTime` (Space,
Time, SpaceTime, TimeAndSpace, GalileanGroup, ReferenceFrame) and `PhysLib/ClassicalMechanics`
(RigidBody, Lagrangian, Pendulum, SimplePendulum, HarmonicOscillator/Geometric,
DampedHarmonicOscillator), together with the sources they point at. Everything asserted about
PhysLib in these documents was read from source; the case study is the part that compiles.

## How to read it in ten minutes

1. [Why now](MOTIVATION.md#m1-physlib-documents-the-gap-in-its-own-words) — the library's
   own three sentences.
2. [The one that decides it](MOTIVATION.md#m7-a-stated-api-requirement-that-cannot-be-satisfied-as-written)
   — `ReferenceFrame` asks for something that cannot be written at the current layering.
3. [Stage 1 is free](PLAN.md#stage-1-the-metrology-annex) — what adoption costs before any
   existing definition changes.
4. [The exhibit upstream chose](PLAN.md#exhibit-f-pointparticle--an-object-index-that-is-not-a-name)
   — physlib#1612 ties a force to its target with a *field*, and the layer gates the same
   objects with an *index*, on the PR's own data structures and with the PR unmodified.

Nothing in this proposal asks PhysLib to change a theorem statement.
