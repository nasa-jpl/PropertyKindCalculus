# The second campaign directory: `Physlib/Electromagnetism/Kinematics`, mirrored

The second directory of the three-directory campaign (see
[`PLAN.md`](../../PLAN.md#directory-2-electromagnetismkinematics)): the kinematics
chain, taken whole — eight files rooted at `EMPotential.lean`, from the four-potential
through the field strength to the boosts and the gauge transformations — with the
PhysLib files as the literal reference. Every module here *imports* the PhysLib module
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
| `Kinds.lean` | Stage 0 | 12 kinds — 10 catalogue lookups verbatim, 2 mints that are one finding twice; three teslas separated by `decide`; the interval scale pinned; no join, and that is a finding |
| `Metrology.lean` | Stage 1 | 12 `DimensionedKind` pairings with the collisions visible, the Stage-0 lookup proved by `decide`/`rfl`, twelve authored edge laws, coverage pinned clean |
| `Kinded.lean` | Stage 2 | the re-authoring: the slices, `E = −∇φ − ∂ₜ𝐀` rebuilt and erasing by `rfl`, chart vs extent, the frame readings off the tensor, the boost's magnetic mirror, gauge invariance reaching the fields |
| `Operators.lean` | Stage 3 | three table registrations + the interval potential's torsor; the law-only majority named; the refusals are subtree boundaries |
| `Audits.lean` | Stage 4 | the directory namespace under CI: the 27-site boundary audit pinned, silent clean/ratchet/dimensional gates, a **12-crossing interior** gated empty, the ingest boundary measured |
| `Kinematics.checked_by.yaml` | Stage 4 | the API-map delta, keyed by the upstream `TODO` texts |
| `DistributionalTwin.lean` | the duplication finding | upstream's `Distributional/` chain re-spells the same physics at the distribution carrier — the twin's `E` is definitionally the chain's `−∇φ − ∂ₜ𝐀` (pinned by `rfl`), its readings land at the chain's existing kinds at **zero vocabulary cost** (the mint ratchet enforces it), and the missing smooth→distributional embedding — the statement a deduplication theorem needs — is pinned as a `#check_failure` |

## The cost line

What the layer costs, measured — every number quoting a build artifact at this commit.

| | count | artifact |
|---|---|---|
| kinds | 12 — 10 catalogue lookups written as verbatim literals (IEC 80000-6 + ISO 80000-3), 2 local mints (the gauge-dependent chart entry and the frame-covariant extent entry — the readings the standard does not list because it catalogues frame-bound, gauge-fixed quantities) | `Kinds.lean`; the `decide`/`rfl` blocks in `Metrology.lean` |
| dimensional pairings | 12, with the collisions visible in the registry: three kinds at the tesla, two at the volt | `Metrology.lean` |
| kind edges | 12 authored laws, of which 5 are table-registered (2 in `Feasibility.lean`, 3 in Stage 3) and 7 are law-only — their divisions live inside `fderiv` and `∫`, where no table sees them | `#kind_dimensional_coverage` pins in `Metrology.lean`/`Operators.lean`; the silent directory-wide `#kind_dimensional_clean` in `Audits.lean` |
| join entries | **0** — every sum the chain writes (`E = −∇φ − ∂ₜ𝐀`, the boost mixings, the gauge shift) is same-kind after an edge or a crossing | `Kinds.lean` header; the `#check_failure` beside each |
| boundary sites | 27 — 26 attested, 1 erasure-only, **0 raw mints**; by tier: 11 ingest, 14 crossings, 1 carrier-vocabulary, 1 emission | the pinned `#kind_boundary_audit` in `Audits.lean` |
| unkinded surface | interior: 0 positions across **12 end-to-end-kinded crossings** (gated); ingest boundary: 28 naked positions over 11 readings — all the potential structure, the evaluation points, the `SpeedOfLight`, or the one emitted field | the `#kind_unkinded` ledgers in `Audits.lean` |
| lines | 1,560 total, of which 620 are code (the rest is documentation, including the pinned audit reports); the mirrored source is 3,214 total / 2,016 code, none of which changed | `wc -l`; comment-stripped count |
| proof debt | 0 `sorry`; every theorem here at `propext, Classical.choice, Quot.sound`; 2 theorems upstream never stated (`electricField_gaugeTransform`, `magneticFieldMatrix_gaugeTransform`) proved | `#print axioms` |

Two cost notes the table cannot carry. First, the per-declaration ceremony is the
pilot's — one `def`, one attestation, one (usually `rfl`) erasure — but the *shape* of
the cost moved: in a field theory the kind algebra mostly rides the analysis operators,
so the ceremony concentrates in a handful of derivative crossings rather than in table
entries. Second, the catalogue does almost all of the Stage-0 work here: 10 of 12 kinds
are lookups the build re-checks, against the pilot's 10 of 18.

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

And one re-confirmation: the `rfl` bridge between catalogue lookups and Stage-0
literals again does not carry instance search (the pilot's finding 8) — Stage 2 needed
exactly one type ascription across it.

The offer of the gauge-invariance patch upstream is a human's to make
([AI-POLICY §3.1](https://github.com/leanprover-community/physlib/blob/master/AI-POLICY.md)).
