# The third campaign directory: `Physlib/ClassicalMechanics`, two subtrees mirrored

The third directory of the three-directory campaign (see
[`PLAN.md`](../PLAN.md#directory-3-classicalmechanics--the-harmonicoscillator-and-rigidbody-subtrees)):
the `HarmonicOscillator` subtree (with `Solution.lean` and the `Geometric/` files) and
the `RigidBody` subtree, with the PhysLib files as the literal reference. Every module
here *imports* the PhysLib module it mirrors and builds the kinded layer on top —
nothing upstream changes, or even imports this.

This directory went third because it proves what neither predecessor could:
**same-dimension discrimination at theorem scale**. Where directory 2 was one
frame-covariant object ranging over many dimensions, classical mechanics is many kinds
crowded onto few dimensions — six kinds at the joule, two ω's at `T⁻¹`, two clocks at
`T` — and everything upstream types at `ℝ` or `EuclideanSpace ℝ (Fin 1)`, so every one
of those coincidences is invisible there. The stress test the campaign named for it —
`equationOfMotion_tfae` surviving verbatim — passed at the strongest possible grade.
The verdict: **no core change forced, no upstream API needed — and the subtree's one
`sorry` is discharged.**

## The files

| file | ladder rung | what it holds |
|---|---|---|
| `Feasibility.lean` | before the ladder | F1–F6 as build artifacts: the radicand edge and the refused reciprocal, the first join with the Lagrangian refused beside it, the M6 collisions refused, the tfae consumed, the trig boundary, König as the second join |
| `Kinds.lean` | Stage 0 | 22 kinds — 17 catalogue lookups verbatim, 5 mints in two findings; six joules, two ω's, two clocks separated by `decide`; the four-edge two-level lattice; `lagrangian_no_edge` |
| `Metrology.lean` | Stage 1 | 22 `DimensionedKind` pairings with ten rows colliding, the 17-lookup agreement by `decide`, fourteen authored edge laws, coverage pinned clean |
| `Kinded/HarmonicOscillator.lean` | Stage 2 | the re-authoring: the Legendre kinetic witness, **the pentad closed by the upstream proof term**, the trajectory from its data with normal form and periodicity, conservation at the watt, the geometric metric at one reading |
| `Kinded/RigidBody.lean` | Stage 2 | the functional's moments with the parallel-axis theorem consumed, the two ω-tensors, `v = V + ω × r` fully table-expressed, the rotational contraction, the motion-preservation theorems |
| `Operators.lean` | Stage 3 | seven registrations on their Stage-1 laws, each demonstrated at a source equation; the `@[kindConst]` full turn; the shared-letter refusal at the table |
| `Audits.lean` | Stage 4 | the directory namespace under CI: the 42-site boundary audit pinned, silent clean/ratchet/dimensional gates, a nine-member interior gated empty, the 30-reading ingest boundary measured |
| `ClassicalMechanics.checked_by.yaml` | Stage 4 | the API-map delta, keyed by the upstream `TODO` texts and the one `@[sorryful]` lemma |
| `SolidSphereInertia.lean` | after the ladder | **the patch candidate**: upstream's `sorry` — the solid sphere's inertia tensor is `(2/5) m R² · 1` — discharged |

## The cost line

What the layer costs, measured — every number quoting a build artifact at this commit.

| | count | artifact |
|---|---|---|
| kinds | 22 — 17 catalogue lookups written as verbatim literals (ISO 80000-4 and -3, down to the phase angle and the period duration), 5 mints in two findings: the input datum `k` and its `k/m` radicand; the Lagrangian and König's two kinetic species | `Kinds.lean`; the `decide`/`rfl` blocks in `Metrology.lean` |
| dimensional pairings | 22, with the collisions visible in the registry: **six kinds at the joule**, two at `T⁻¹`, two at `T` — ten of twenty-two rows collide | `Metrology.lean` |
| kind edges | 14 authored laws, of which 13 are table-registered (6 in `Feasibility.lean`, 7 in Stage 3) and **1** is law-only — conservation's `∂ₜE`, riding `fderiv` | `#kind_dimensional_coverage` pins in `Metrology.lean`/`Operators.lean`; the silent directory-wide `#kind_dimensional_clean` in `Audits.lean` |
| join entries | **2**, on a two-level lattice that composes: `T + V` at mechanical energy (the total energy and the on-trajectory Hamiltonian), translational + rotational at kinetic energy (König) | the `KindJoin` instances in `Feasibility.lean`; `Kinds.lean`'s lattice |
| boundary sites | 42 — 29 ingests, 8 crossings, 1 constant, 3 emissions, 1 carrier-vocabulary; **0 raw mints**, every attestation's reason in the pin | the pinned `#kind_boundary_audit` in `Audits.lean` |
| unkinded surface | interior: 0 positions across a **9-member** end-to-end-kinded scope (gated); ingest boundary: 72 naked positions, 68 flows over 30 readings — the system structures, the data structures, the coordinates | the `#kind_unkinded` ledgers in `Audits.lean` |
| lines | 2,509 total, of which 1,104 are code (the rest is documentation, including the pinned audit reports); the mirrored source is 3,814 total / 1,718 code, none of which changed | `wc -l`; comment-stripped count |
| proof debt | 0 `sorry` here — and **1 upstream `sorry` discharged** (`solidSphere_inertiaTensor`, the two subtrees' only one); eighteen key theorems, pentad and discharge included, at `propext, Classical.choice, Quot.sound` | `#print axioms` |

One cost note the table cannot carry: the boundary is *wide* here by the physics'
nature — upstream's objects are structures of bare reals, so every reading is a
boundary site — while the interior is thin (the algebra between readings is short).
Directory 2 had the opposite shape. The per-declaration ceremony is unchanged from the
pilot: one `def`, one attestation, one (usually `rfl`) erasure.

## The findings

Each finding is a fact about the *source* that only became statable, or only became
checked, with the layer on.

1. **Six kinds at one dimension — the promised four, and König's two.** The campaign
   table promised four energies at the joule; the vocabulary needed six: kinetic
   (4-28.2), potential (4-28.1), mechanical (4-28.3), the Lagrangian, and the
   translational/rotational split. Ten of the registry's twenty-two rows collide with
   another row; upstream, every one of the ten is `ℝ`.
2. **The pentad survives verbatim — at the strongest grade.** All five formulations of
   the equation of motion re-stated with kinded readings (Newton through the `m·a`
   product, Hamilton's momentum trajectory through the kinded canonical momentum, both
   variational integrands *being* the Lagrangian mint and the kinded Hamiltonian by
   `rfl`), and the kinded `List.TFAE` is closed by `S.equationOfMotion_tfae xₜ hx` **as
   the literal proof term**: every kinded spelling erases definitionally, so the
   upstream proof is the proof.
3. **The mints are the system's inputs and the standard's structural gap.** The
   catalogue reaches further than expected — phase angle, period duration, angular
   frequency *and* angular velocity are all lookups — but it has no item for the spring
   constant (the bare-real input datum where Exhibit C found `√(m/k)` as well-typed as
   the right recipe; the ladder refuses `m/k` before any root is taken) and none for
   the Lagrangian: the standard names the *sum* of the comparable pair and not its
   difference. `lagrangian_no_edge` makes "no home at the join" a theorem about the
   lattice.
4. **Two joins, and they compose.** The pilot needed one curated join, directory 2
   none, this directory two — `T + V` at mechanical energy and König's split at kinetic
   energy — on a two-level lattice where a König summand specializes mechanical energy
   transitively. The joins sit exactly where the physics adds across kinds, and
   nowhere else: `L + E` refuses at the same joule.
5. **The shared letter `ω`, separated three ways.** The oscillator's angular frequency
   (3-18) and the rigid body's angular velocity (3-12) share a dimension and a letter;
   the layer separates them by `decide` (Stage 0), exhibits them as a registry
   collision (Stage 1), and *discriminates them at the table* (Stage 3): the rigid
   body's `ω` contracts with the angular momentum, the oscillator's is refused.
6. **Classical point mechanics is scalar-multiplicative almost everywhere.** Thirteen
   of fourteen edges are table-registered with scalar call sites; only conservation's
   `∂ₜE` stays law-only. Directory 2's majority case (kind algebra riding the analysis
   operators) is here the exception — the shape of the cost tracks the physics.
7. **The trig boundary became literal because the gate refused anything less.**
   `#kind_boundary_clean` refused the trajectory composite's inline `.magnitude` reads
   during authoring; the fix that satisfies it is the honest design — `cosPhase` and
   `sinPhase` as tagged `@[kindEmission]` declarations, the one sanctioned place a
   phase leaves the layer to enter `Real.cos` — and the phase itself exists only
   through the `ω·t` edge. In the same spirit the period's `2π` is a declared
   `@[kindConst]` full turn at 3-7, and `T = 2π/ω` is one `/` that is *definitionally*
   upstream's `period`.
8. **The complex embedding is licensed by an edge.** The amplitude–phase inverse packs
   `(x₀, v₀/ω)` into one `ℂ` — legitimate exactly because `v₀/ω` came through the
   velocity/angular-frequency edge, so both components are displacements; `‖z‖` is the
   amplitude (a displacement) and `arg z` the phase. The kinded reading erases to
   upstream's `fromInitialConditions` by `rfl`.
9. **The collisions of M6 close as refusals.** The momentum of a momentum
   (`toCanonicalMomentum : E ≃ₗ E` between identical types), the force fed the
   canonical momentum, the Hamiltonian with `p` and `x` swapped (the collision behind
   `hamiltonian_eq`'s transposed `funext t x p`), and the substrate's
   position-plus-momentum — all pinned compiling upstream, all refused kinded.
10. **The kind layer separates kinds, not frames — and says so.** The lab and
    body-frame angular-velocity tensors both read at 3-12, and their sum still
    elaborates (pinned as scope honesty, not hidden): frame discrimination is
    Exhibit A's `toFrameScalar` machinery. What the layer *does* check here: the
    skew-symmetry is a same-kind negation, and the conjugation `Ω_body = Rᵀ Ω R` stays
    inside the kind because the orientation's entries are dimensionless direction
    cosines — the frame change is numeral work.
11. **The functional's moments are the boundary.** `RigidBody.ρ` is a linear functional
    on test functions, and each moment read off it (the mass, the centre of mass, the
    inertia entries) is an ingest whose kind is mass times the test function's; the
    parallel-axis theorem is then a *same-kind sum* at 4-7, consumed with upstream's
    proof verbatim, and `v = V + ω × r` is fully table-expressed — two edge products
    and a same-kind subtraction per cross-product component.
12. **The subtree's one `sorry` is discharged — the patch candidate.**
    `solidSphere_inertiaTensor` (`(2/5) m R² · 1`, `@[sorryful]` upstream) is proved in
    `SolidSphereInertia.lean`: the off-diagonal moments vanish under a
    coordinate-reflection isometry, the diagonal moments agree under a coordinate swap,
    and the radial integral reduces by Mathlib's Haar-to-sphere machinery — with
    PhysLib's own `volume_metricBall_three_real` supplying the unit-ball volume, of
    which only the positivity survives to the final ratio. In the pilot's
    orthonormality pattern.

And one re-confirmation: the `rfl` bridge between the probe kinds and Stage 0's
literals again does not carry instance search (the pilot's finding 8) — the Stage-2
composites cite the Metrology laws explicitly where no instance is registered, and one
type ascription rides each table spelling.

The offer of the solid-sphere patch upstream is a human's to make
([AI-POLICY §3.1](https://github.com/leanprover-community/physlib/blob/master/AI-POLICY.md)).
