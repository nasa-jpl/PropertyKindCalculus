# The second campaign directory: `Physlib/Electromagnetism/Kinematics`, mirrored

The second directory of the three-directory campaign (see
[`PLAN.md`](../../PLAN.md#directory-2-electromagnetismkinematics)): the kinematics
chain, taken whole — eight files rooted at `EMPotential.lean`, from the four-potential
through the field strength to the boosts and the gauge transformations — plus the
six-file `Dynamics/` variational subtree (Lagrangian → Euler–Lagrange → Legendre →
Hamiltonian) — with the PhysLib files as the literal reference. Every module here *imports* the PhysLib module
it mirrors and builds the kinded layer on top — nothing upstream changes, or even
imports this.

This directory went second because it proves what the pilot could not: **joins and
frames where the physics forces them**. The spine everything hangs on: the library's
spacetime coordinate is `x⁰ = c·t` — a length — so the `φ/c` in `ofPotentials` is not a
convention but the move that makes the four-vector one kind, and the whole chain is one
frame-covariant object being read back into frame-bound kinds through one velocity
edge. The verdict: **no core change forced** — and, unlike the pilot, no upstream API
either: every capability the chain needed was already minted.

## The files

| file | ladder rung | what it holds |
|---|---|---|
| `Feasibility.lean` | before the ladder | F1–F5 as build artifacts: the field carrier stands up, the `/c` pinned, the interval scale refuses the ratio table, the boost law consumed whole, the gauge torsor |
| `Kinds.lean` | Stage 0 | 19 kinds — 14 catalogue lookups verbatim (Maxwell's sources and constants included), 5 mints; three teslas separated by `decide`; the interval scale pinned; no join, and that is a finding |
| `Metrology.lean` | Stage 1 | 24 `DimensionedKind` pairings — the lookups referencing the catalogue's own entries, the mints alone constructed — with the collisions visible, the Stage-0 lookup proved by `decide`/`rfl` (including that Part 7's `speedOfLight` is the *in-medium* kind, decidably not the chain's vacuum 6-35.2), twenty-five authored edge laws (Maxwell's seven and the variational six included), coverage pinned clean |
| `Kinded.lean` | Stage 2 | the re-authoring: the slices, `E = −∇φ − ∂ₜ𝐀` rebuilt and erasing by `rfl`, chart vs extent, the frame readings off the tensor, the boost's magnetic mirror, gauge invariance reaching the fields |
| `Operators.lean` | Stage 3 | three table registrations + the interval potential's torsor; the law-only majority named; the refusals are subtree boundaries |
| `Audits.lean` | Stage 4 | the directory namespace under CI: the 39-site boundary audit pinned, silent clean/ratchet/dimensional gates, a **12-crossing interior** gated empty, the ingest boundary measured |
| `Kinematics.checked_by.yaml` | Stage 4 | the API-map delta, keyed by the upstream `TODO` texts |
| `DistributionalTwin.lean` | the duplication finding | upstream's `Distributional/` chain re-spells the same physics at the distribution carrier — the twin's `E` is definitionally the chain's `−∇φ − ∂ₜ𝐀` (pinned by `rfl`), its readings land at the chain's existing kinds at **zero vocabulary cost** (the mint ratchet enforces it), and the missing smooth→distributional embedding — the statement a deduplication theorem needs — is pinned as a `#check_failure` |
| `Maxwell.lean` | the sources | the four laws kinded: every side on a Metrology edge, still **no join** (`ε₀∂ₜE` lands at the catalogue's own 6-8, so Ampère's right side is a same-kind sum); `J^μ` one kind because the time slot is `c·ρ`; `μ₀ε₀c²` dimensionless by `decide` — and the finding that upstream's four laws are **module-private** (the one file in the subtree with no `@[expose] public section`), so the proofs are re-run here against the exported API; the patch candidate is one line |
| `Dynamics.lean` | the variational subtree | Lagrangian → Euler–Lagrange → Legendre → Hamiltonian, kinded on six new edges: both Lagrangian terms at one minted density (`L = L_kin − A·J` a same-kind subtraction by `rfl`), both spellings of `δS/δA` at the Euler–Lagrange mint (upstream's own lemma), `H = π·∂₀A − L` same-kind by `rfl` with its 6-33 target *licensed by upstream's theorem*; `IsExtrema` unfolds to the kinded gradient's vanishing (`Iff.rfl`) — the hypothesis `Maxwell.lean`'s four laws consume; `FreeSpace.c = 1/√(ε₀μ₀)` read as a crossing; and the stale-`μ₀` TODO finding |

## The cost line

What the layer costs, measured — every number quoting a build artifact at this commit.

| | count | artifact |
|---|---|---|
| kinds | 24 — 16 catalogue lookups written as verbatim literals (IEC 80000-6 + ISO 80000-3; Maxwell adds 6-3, 6-8, 6-14.1, 6-26.1; Dynamics adds 6-33, 6-9), 8 local mints (the chart and extent entries, Maxwell's three derivative readings, and the variational three: the Lagrangian density, the variational gradient, the canonical momentum) | `Kinds.lean`; the `decide`/`rfl` blocks in `Metrology.lean` |
| dimensional pairings | 24, with the collisions visible in the registry: three kinds at the tesla, two at the volt, two at the energy density's J/m³, two at the current density's A/m², two at the linear current density's A/m | `Metrology.lean` |
| kind edges | 25 authored laws, of which 5 are table-registered (2 in `Feasibility.lean`, 3 in Stage 3) and 20 are law-only — their divisions live inside `fderiv`, `∫` and the variational `δ`, where no table sees them | `#kind_dimensional_coverage` pins in `Metrology.lean`/`Operators.lean`; the silent directory-wide `#kind_dimensional_clean` in `Audits.lean` |
| join entries | **0** — every sum the chain writes (`E = −∇φ − ∂ₜ𝐀`, the boost mixings, the gauge shift) is same-kind after an edge or a crossing | `Kinds.lean` header; the `#check_failure` beside each |
| boundary sites | 48 — 47 attested, 1 erasure-only, **0 raw mints**; by tier: 12 ingest, 32 crossings, 2 constants, 1 carrier-vocabulary, 1 emission | the pinned `#kind_boundary_audit` in `Audits.lean` |
| unkinded surface | interior: 0 positions across **12 end-to-end-kinded crossings** (gated); ingest boundary: 28 naked positions over 11 readings — all the potential structure, the evaluation points, the `SpeedOfLight`, or the one emitted field | the `#kind_unkinded` ledgers in `Audits.lean` |
| lines | 2,509 total, of which 1,071 are code (the rest is documentation, including the pinned audit reports); the mirrored source (the `Dynamics/` subtree now included) is 5,436 total, none of which changed | `wc -l`; comment-stripped count |
| proof debt | 0 `sorry`; every theorem here at `propext, Classical.choice, Quot.sound`; 2 theorems upstream never stated (`electricField_gaugeTransform`, `magneticFieldMatrix_gaugeTransform`) proved | `#print axioms` |

Two cost notes the table cannot carry. First, the per-declaration ceremony is the
pilot's — one `def`, one attestation, one (usually `rfl`) erasure — but the *shape* of
the cost moved: in a field theory the kind algebra mostly rides the analysis operators,
so the ceremony concentrates in a handful of derivative crossings rather than in table
entries. Second, the catalogue does almost all of the Stage-0 work here: 16 of 24 kinds
are lookups the build re-checks, against the pilot's 11 of 19.

## The findings

Each finding is a fact about the *source* that only became statable, or only became
checked, with the layer on.

1. **The `/c` is what makes the four-vector one kind.** The spacetime coordinate is
   `x⁰ = c·t` (a length — `toTimeAndSpace` stores `c·t`), so `A^μ = (φ/c, 𝐀)` is
   dimensionally uniform at the magnetic vector potential (6-32) *because of* the
   division `ofPotentials` writes — pinned by `rfl` at the time slot, certified in the
   catalogue's own dimension group (`voltage_per_speed_dim`).
2. **The catalogue's scale adjudicates where upstream's `ℝ` cannot.** Electric
   potential (6-11.1) is interval-scale *in the standard itself*; `ofRatio` is
   unprovable there, so the velocity edge lands only on the ratio-scale difference
   (6-11.2) and the potential's sole outbound arithmetic is the torsor's `−ᵥ`.
   Upstream, potential and potential difference are one `ℝ`.
3. **The chain's vocabulary is the standard's — except for the tensor.** Ten of twelve
   kinds are verbatim IEC 80000-6/ISO 80000-3 lookups (the gauge function included:
   `∂^μχ` sits at 6-32, so `χ` is a *magnetic flux*, item 6-22.1). The two mints are
   one finding twice: the standard catalogues frame-bound, gauge-fixed readings, so
   the gauge-dependent `∂A` entry and the frame-covariant `F` entry have no row to
   look up — three kinds at the tesla, separated only by kind.
4. **No join, anywhere — and that is the directory's structure.** The pilot needed a
   curated `KindJoin` for `T̂ + V̂`; this chain needs none: every sum its physics
   writes is same-kind after an edge or a crossing. The joins here are edge-mediated.
5. **Natural units are a silent default, at every definition.** `(c : SpeedOfLight :=
   1)` rides an optional argument on the whole chain and defaults invisibly at bare
   call sites (pinned); the kinded readings have no default to elide — the speed is a
   declared quantity threaded explicitly.
6. **In a field theory, most of the kind algebra rides the analysis operators.** Seven
   of twelve edges are law-only: their divisions live inside `fderiv` and `∫`, which
   no table sees — the pilot's `p̂²/m` precedent as the *majority* case, measured by
   the audit rather than prevented by the table.
7. **What survives a boost is the tensor's kind.** `E'_⊥ = γ(E + cβ·B)` and
   `B' = γ(B + (β/c)·E)` are consumed whole from upstream's own boost laws, each
   mixing licensed exactly through the velocity edge — while `E + B` refuses — and the
   transverse-transverse block is proved fixed. The `E` and `B` kinds are frame-bound
   readings; the extent's kind is the invariant (MR18 at theorem scale).
8. **Gauge invariance reaches the fields — and upstream does not say so.** Upstream
   proves the tensor gauge-invariant; the derived `electricField` and
   `magneticFieldMatrix` inherit it, but no upstream lemma states it. Proved here
   (`electricField_gaugeTransform`, `magneticFieldMatrix_gaugeTransform`, with
   `gaugeTransform_differentiable` en route), plus the torsor's own witness: a pure
   translation has zero extent (`pureGauge_extent_zero`). A candidate patch, in the
   pilot's orthonormality pattern.
9. **Once the potential is read in, the chain never touches a naked carrier.** Twelve
   crossings are kinded end to end — the interior contract, gated empty — inverting
   the pilot's two-interior/many-boundary ratio: the field theory's derivation tree
   runs *inside* the kind layer, and the boundary is exactly where PhysLib's carriers
   enter.

10. **The variational calculus never needs a join either — and its readings are the
    same-dimension discrimination at three more dimensions.** `L = L_kin − A·J`,
    `gradLagrangian = gradKineticTerm − gradFreeCurrentPotential`, and
    `H = π·∂₀A − L` are all same-kind subtractions after edges (the first and third
    pinned by `rfl`, the second by upstream's own lemma); and the three minted
    readings each sit at a catalogue dimension without being the catalogue kind — `L`
    at 6-33's J/m³ but gauge-dependent (`lagrangian_add_const` moves it), `δS/δA` at
    6-8's A/m² but not a current, `π` at 6-9's A/m but not a current through a line.
    The Hamiltonian alone lands *on* the catalogue (6-33), and upstream's
    `hamiltonian_eq_electricField_magneticField` is the license. One stale TODO
    surfaced: `KineticTerm.lean` and `Lagrangian.lean` still say `μ₀ = 1` is "a TODO
    to introduce", but every definition already takes `𝓕 : FreeSpace` — a two-line
    docstring patch candidate.

And one re-confirmation: the `rfl` bridge between catalogue lookups and Stage-0
literals again does not carry instance search (the pilot's finding 8) — Stage 2 needed
exactly one type ascription across it.

The offer of the gauge-invariance patch upstream is a human's to make
([AI-POLICY §3.1](https://github.com/leanprover-community/physlib/blob/master/AI-POLICY.md)).
