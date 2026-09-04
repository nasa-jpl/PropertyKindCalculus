# Plan

How to get from [the requirements](REQUIREMENTS.md) to something a PhysLib maintainer can
merge, in an order where the cheap and uncontroversial parts come first and each stage is
useful on its own.

---

## Status ledger

Last updated 2026-09-04. One table each way, so "what is done and what is left" never
has to be reconstructed from the Status lines scattered below.

### Done

| item | where it lives |
|---|---|
| Exhibits A–F | `Exhibits/`; per-exhibit **Status: built** lines below |
| The full ladder (Stages 0–4) for `SpaceAndTime/Space` | Sequencing item 3; per-stage Status lines below |
| Campaign directory 1 — `QuantumMechanics/HarmonicOscillator`, whole | `QuantumMechanics/HarmonicOscillator/` + README cost line; includes the two patch candidates (`Orthonormality`, `Heisenberg`) |
| Campaign directory 2 — `Electromagnetism/Kinematics` | `Electromagnetism/Kinematics/` + README cost line |
| Campaign directory 3 — `ClassicalMechanics` HO + RigidBody subtrees | `ClassicalMechanics/` + README cost line; the subtree's one `sorry` discharged |
| Decision-ladder step (i): the unit-side parametrization | **merged upstream** — physlib PR #1481, 2026-08-05 |
| The ClassicalMechanics patch offer, materialized | physlib fork branch `solid-sphere-inertia` (2 commits, all upstream gates green); PR draft at `scratchpad/physlib-pr-solid-sphere-inertia.md` |
| Decision-ladder step (ii), drafted | the Stage-1 ask at `scratchpad/physlib-ask-stage1.md` |
| The object-type parameterization: `IndividualQuantity` over an arbitrary object type, `Designated`, `Composite`/`Assembles`/`assemble` | PKC core + `CompositeReal`; blueprint chapter *The object type*; `MiniObjectTypes`, `Tests/Core/Composite`, Exhibit F |
| Case study 2 — `PointParticle` (physlib#1612): four typings of one physics, ergonomics a scored axis; the win-win is the *dependent target field* | `CaseStudies/PointParticle/` — Common + Attempts 1–4 + Scorecard + README |
| The mereological sort: `SortOfSystem` + `Sorted`, `Composite σ P`, `Assembles σ k`; statue/clay + rigid-vs-mixture volume probes; `smulK`, `resultantOver`/`assembleAll`, `transpose`, `IndividualQuantity.neg`, `Designated.ofInjective`/`.prod` | PKC core + `CompositeReal`; blueprint *The object type* §generality; probes in `Tests/Core/Composite` + `MiniObjectTypes` |
| The `DedicatedKind` correction, decided 2026-09-04 and migrated: `sort : SortOfSystem` stores what Dybkær Ch. 20's definition asks for ("kind-of-property with given sort of system…", verified verbatim against the vendored PDF); `dedicatedFor`/`dedicatedFor_congr` close the instantiation square; `distinct_of_sort` replaces the by-particular distinctness; TwoRovers' term reads `"rover — chassis ; mass"` with the particular carried by the object index; the self-index gains a `sorts` table and the `systems` table drops its dedicated-kinds column | PKC core `DedicatedKind`; Index harvest; `MiniDedicatedKind` §6, `MiniWriteOnce`, Iso 80000 Part 3 §9, `Tests/Core/{KindStructure,Index}`; TwoRovers + Scorecard + Attempt4Pkc; blueprint *Dedicated kinds-of-property* |
| The Lowe correspondence, explicit and cited: corners in each docstring, edges + the derivative diagonal in the blueprint's *The object type* chapter; formal entry from Nicolas's verified BibTeX (OUP 2005, DOI) in `References.lean`; two chapter entries from the vendored *Ontology, Modality, and Mind* (OUP 2018) — Simons (exemplification definable; cited at the diagonal) and Heil (Lowe's immanentism; cited for the universals-as-catalogue-entries stance). Marmodoro's "Whole, but not One" flagged as a possible future pass for `Composite`/`Assembles` (unite vs unify; a whole carries no count principle) | blueprint `References.lean` + *The object type*; year corrected 2006→2005 per the verified citation |

### Open

| item | whose move |
|---|---|
| Push PKC `main` (ahead of `maap/main`) | Nicolas |
| Decide where the maintainer browses ForPhysLib — the only remote is the MAAP GitLab; a public mirror or rendered docs may be needed | Nicolas |
| Push fork branch `solid-sphere-inertia`; post its PR(s) from the draft | Nicolas (AI-POLICY §3.1) |
| Review + post the Stage-1 ask | Nicolas (AI-POLICY §3.1) |
| Decision-ladder step (iii): the Stage-0+1 PR for `SpaceAndTime/Space` | Claude drafts it if question 2 of the ask gets a yes |
| Materialize the QM patch offer (Orthonormality + Heisenberg) and the EM gauge pair as fork branches | Claude, on request — same recipe as `solid-sphere-inertia` |
| Held physics — ALL SIX DELIVERED: σ_p moment (saturation unconditional); L_z = m·ℏ; degeneracy; `LadderOperators.lean` (the eleven-TODO stub); `DistributionalTwin.lean` (the duplication finding); `Maxwell.lean` (the four laws kinded + the module-private finding) | done 2026-09-01 |
| The last two held items — the `Dynamics/` variational subtree (`Kinematics/Dynamics.lean`: 2 lookups + 3 mints + 6 edges, the whole variational calculus same-kind, `H` at 6-33 by upstream's theorem, the stale-`μ₀`-TODO finding) and the RF/AC annex promoted to ladder form (`Electromagnetism/Annex/`: 17 kinds all lookups zero mints, 5 edges consumed from the catalogue's `DefiningRelations`, the refused `P + Q`, the dB budget on 6-45). Nothing remains held | done 2026-09-02 |
| Decide whether anything from Exhibit F is offered to physlib#1612, and in what form | Nicolas (AI-POLICY §3.1) |
| Re-point Exhibit F's `Replica` at the real `PointParticle.System` once #1612 merges | Claude, on request |
| Campaign wrap-up artifact (cross-directory scorecard) | undecided whether wanted |

---

## The shape of the proposal

**Additive, per-directory, monotone.** Nothing here asks PhysLib to change a theorem
statement, and nothing asks for a library-wide flag day. The unit of adoption is a module
root, and a directory that has adopted nothing is not failing anything —
[MR31](REQUIREMENTS.md#mr31-adoption-is-scoped-and-monotone).

**The layers compose rather than compete.** PhysLib's `Dimension` is the right bottom layer.
PKC consumes it through the forgetful functor `DimensionedKind.toDimension`; there is no
proposal to replace or modify it.

---

## The adoption ladder

### Stage 0. The kind vocabulary

One `kinds/` file per directory: `KindOfProperty` declarations, Mathlib-free, imported by
nothing — each lookup *being* the corresponding `Iso80000` catalogue entry's own kind
projection, so a lookup cannot drift from the standard; only the mints are constructed. A
kind carries an id, a `ScaleType`, and an examination principle.

**Cost to existing code: none.** Nothing imports it yet.

**The asymmetry that makes this cheap for PhysLib.** The soil-moisture model had to *invent*
its vocabulary, because remote-sensing kinds are largely dimension-one and absent from
ISO 80000. PhysLib's kinds are already catalogued: PKC's `iso80000/` library covers Parts
3–13, with Part 5 (54 items) carrying thermodynamic vs Celsius temperature and the
entropy/heat-capacity collision at one dimension *and* one unit, and Part 6 (85 items)
carrying electric potential (interval) vs potential difference (ratio). **For PhysLib,
Stage 0 is mostly a lookup rather than a design.** That removes the largest single component
of the cost [MR11](REQUIREMENTS.md#mr11-authoring-ergonomics) measured.

Alongside it, `examination/` — the physics that individuates each kind — mirroring `kinds/`
file for file, under the organising rule *a kind lives in the file named by its own
examination principle*.

**Status: Done for `SpaceAndTime/Space`** — `ForPhysLib.Kinds.Space` (six ISO 80000-3
kinds, each `Iso80000.Part3`'s own entry, the position/displacement pair distinct by
`decide`) with `ForPhysLib.Examination.Space` mirroring it file for file (the catalogue's
principles, `examinedBy` proved by `rfl`, the distinctness derived from the principles
alone). Landed with Sequencing item 3.

### Stage 1. The metrology annex

A `metrology/` module pairing each kind with its PhysLib `Dimension` as a `DimensionedKind`,
plus `#kind_dimensional_coverage` pinned over the module root with `#guard_msgs`.

**Cost to existing code: none.** No existing definition changes.

**And it already finds things.** It catches `Temperature.β`, whose docstring claims "Energy"
for an inverse energy. It confirms `γ² − 4mk`. It converts roughly 140 files' worth of prose
dimension claims into statements a build can fail on —
[M10](MOTIVATION.md#m10-the-first-stage-is-free-and-already-finds-things).

**This is the stage to propose first, and possibly the only one to propose at first.** It is
the whole argument in a form that costs a maintainer nothing to accept.

**Status: Done for `SpaceAndTime/Space`** — `ForPhysLib.Metrology.Space`: six
`DimensionedKind` pairings, the Stage-0 lookup proved against `Iso80000.Part3` (`decide`
on the kinds, `rfl` on the dimensions), the directory's two-edge kind algebra authored,
and `#kind_dimensional_coverage` pinned clean over it. Landed with Sequencing item 3.

### Stage 2. Kinded re-authoring, with definitional erasure

The kinded form becomes the authored form; the naked form is `rfl`-equal to `.magnitude` of
it.

**Cost: existing theorem *statements* survive**, because the naked spelling is definitionally
the erasure. This is the invariant that makes the transition non-disruptive to a library
whose value is its proofs.

**Status: Done for `SpaceAndTime/Space`** — `ForPhysLib.Kinded.Space`: the directory's
four length-readings authored kinded (`distanceQ`, `positionQ`, `displacementQ`,
`lengthOf`), each mint carrying its boundary tier; the naked form is `rfl`-equal to
`.magnitude` (`rawDistance_eq_dist`), and the invariant is exhibited rather than claimed
— PhysLib's `Space.dist_eq`, Mathlib's `dist_triangle` and `dist_eq_norm_vsub` close
kinded goals verbatim, while distance + length and position + displacement stop
elaborating (`#check_failure`).

### Stage 3. The operator table

`KindMul`/`KindDiv` instances registered once per model, with scoped `HMul`/`HDiv` so that
`m * (ω * ω) * (x * x)` elaborates through the table and an unregistered pair **fails to
elaborate**.

**Cost: authoring style.** This is where [MR11](REQUIREMENTS.md#mr11-authoring-ergonomics) is
paid down, and it must be demonstrated with the operator idiom, never the longhand witness
form — see [MR28](REQUIREMENTS.md#mr28-kind-generic).

**Status: Done for `SpaceAndTime/Space`** — `ForPhysLib.Operators.Space`: the two Stage-1
laws registered as `KindMul`/`KindDiv` instances, `a * b : Quantity area ℝ` and
`arc / radius : Quantity planeAngle ℝ` elaborating through the table, `spanArea`
composing the Stage-2 author-forms with `rfl` erasure — and two refusals pinned:
`area · area` (unregistered) and `distance · distance` (dimensionally admissible, never
sanctioned — curation per kind, not per dimension). `#kind_dimensional_coverage` is
re-pinned clean over the registrations, rendered `[table]`.

### Stage 4. Audits and the API map

`#kind_boundary_audit`, `#kind_unkinded` with the Mathlib-interface tier
([MR30](REQUIREMENTS.md#mr30-the-unkinded-surface-is-measured)), `#kind_mint_ratchet` scoped
to the module root, and the `checked_by:` field in the directory's `API-map.yaml`
([MR29](REQUIREMENTS.md#mr29-every-satisfied-requirement-has-a-machine-checkable-witness)).

**Cost: CI.**

**Status: Done for `SpaceAndTime/Space`** — `ForPhysLib.Audits.Space`: the boundary audit
and its crossings enumeration pinned (five sites, all tagged), `#kind_boundary_clean` and
`#kind_mint_ratchet` passing silently over the Kinded and Operators scopes, and the
unkinded ledger read over two declared contracts — the *interior* gated empty
(`#kind_unkinded_clean`), the *ingest boundary* measured at eight naked positions, every
one a `Space d` point or the emitted `ℝ`: MR30's Mathlib-interface tier, counted rather
than hidden. The `checked_by:` delta proposed for the directory's `API-map.yaml` sits
beside the module as `Audits/Space.checked_by.yaml`. **The ladder now stands complete,
Stage 0 through Stage 4, for its first directory.**

---

## Exhibits to build

Six, ordered by what they demonstrate. Each must produce build artifacts per rule 2 of the
[rules of engagement](#rules-of-engagement) — a `#check_failure`, a theorem exhibiting the
wrong answer, or an `example` showing that something which should be rejected type-checks.
A–E were chosen from the surveyed sources; F was chosen by upstream, being a live PR that
reaches the same question from the other side.

### Exhibit A. RigidBody

**Source.** `ClassicalMechanics/RigidBody/{AngularVelocity,Motion,KineticEnergy,AngularMomentum}.lean`

**Requirements.** [MR1](REQUIREMENTS.md#mr1-dimensional-homogeneity),
[MR17](REQUIREMENTS.md#mr17-a-vector-quantity-is-one-quantity),
[MR18](REQUIREMENTS.md#mr18-frame-covariance-and-what-survives-it),
[MR19](REQUIREMENTS.md#mr19-an-indexed-family-is-not-a-set-of-vector-components),
[MR25](REQUIREMENTS.md#mr25-dimension-generic),
[MR26](REQUIREMENTS.md#mr26-frame-generic),
[MR28](REQUIREMENTS.md#mr28-kind-generic)

**What it shows.** The lab/body angular-velocity mismatch that
[M5](MOTIVATION.md#m5-a-correctness-constraint-enforced-by-not-using-an-abbreviation)
describes, plus `comTrajectory`, `centerOfMassVelocity` and `linearMomentum` all typed
`Time → Space d`, so position `+` momentum compiles.

**The tension to raise carefully.** `ReferenceFrame`'s doc insists *"no point is automatically
the zero point"*, while `Space/Origin.lean` supplies `Zero (Space d)` because the vector-space
structure is needed. PKC's extent/position split resolves this **without removing the `Zero`
instance** — the roles separate at the kind layer while the carrier keeps everything Mathlib
needs. That is the shape of the whole proposal in miniature, and it should be presented that
way rather than as a criticism.

**Where the ceremony visibly returns something.** `angularVelocityTensor` is defined for all
`d`; `angularVelocity` only at `d = 3`, and everything downstream inherits `d = 3`. A
kind-generic statement of the König split over `Variance.rank2` for the inertia tensor and
`Variance.vector` for `ω` is dimension-generic for free. Build this exhibit for that reason
as much as for the defect.

**Status: built** — `ForPhysLib/Exhibits/RigidBody/Findings.lean`. The three findings stand
as `example`s against the imported sources: position `+` momentum and velocity `+` position
at `Space 3`; the body-fixed inertia tensor contracted with the *spatial* `ω` (and the
lab + body sum); the pointwise `ω * ω`. The counter-form `rotationalContraction` states
`ω · (I ω)` once — kind-, dimension- and carrier-generic, exercised verbatim at `n = 7` —
and a `#check_failure` closes each finding; `rotationalContraction_eq_physlib` bridges the
body-frame form back to `2 * rotationalKineticEnergy ω_body` in two lines, and
`koenigTwiceTotal` states the König split with its halves read in *different* frames,
joined only through `toFrameScalar`.

### Exhibit B. ReferenceFrame

**Source.** `SpaceAndTime/ReferenceFrame.lean` + `ReferenceFrame/API-map.yaml`

**Requirements.** [MR17](REQUIREMENTS.md#mr17-a-vector-quantity-is-one-quantity),
[MR18](REQUIREMENTS.md#mr18-frame-covariance-and-what-survives-it),
[MR26](REQUIREMENTS.md#mr26-frame-generic),
[MR29](REQUIREMENTS.md#mr29-every-satisfied-requirement-has-a-machine-checkable-witness),
[MR30](REQUIREMENTS.md#mr30-the-unkinded-surface-is-measured)

**What it shows.** [M7](MOTIVATION.md#m7-a-stated-api-requirement-that-cannot-be-satisfied-as-written)
— the unwritten requirement 16 asks for a single induced transformation law where there are
three, so the layer arrives as a design input rather than a retrofit.


**And a second, quieter finding in the same file.** `IsInertial.velocity` has the *same type*
as the displacement it is defined from:

```lean
origin_moves_uniformly :
  ∃ velocity, ∀ t₁ t₂, frame.origin t₂ -ᵥ frame.origin t₁ = (t₂ - t₁).val • velocity
def IsInertial.velocity (h : frame.IsInertial) : EuclideanSpace ℝ (Fin d)
```

The defining equation is dimensionally correct only because `.val` erased `Time` to a bare `ℝ`
first — the L = T · L·T⁻¹ balance is carried *by* the erasure rather than checked *through*
it. This is the canonical instance of
[MR30](REQUIREMENTS.md#mr30-the-unkinded-surface-is-measured)'s Mathlib-interface tier, and
the exhibit should report it as such rather than as a defect: the erasure is how the scalar
action becomes available at all.

**The shape of the change is small.** `Vector` gains a parameter; `componentEquiv` is where
the kind is dropped and it stays exactly where it is; every instance — `AddCommGroup`,
`Module`, `TopologicalSpace`, `NormedAddCommGroup`, `InnerProductSpace` — survives *per kind*,
and the `Fact frame.IsMetricConserved` machinery is untouched. The current `Vector` is the
erasure.

**Status: built** — `ForPhysLib/Exhibits/ReferenceFrame/Findings.lean`. The three candidate
laws (`geometricTransport`, `boostTransport`, `originShiftTransport`) all inhabit
`F.Vector → G.Vector`, and one `example` applies all three to the same vector — the finding
that requirement 16's "the induced transformation law" is three laws the type cannot tell
apart. The design input follows in the same file: `KVector` is `Vector` with a kind index,
`kComponentEquiv` still the definitional place the kind is dropped, `AddCommGroup`/`Module`
transferred per kind by the same one-liners, and `kBoostTransport` rejecting a displacement
by `#check_failure`. Finding 2 lands at the MR30 tier as promised: `origin_displacement_eq`
discharges the API map's undone requirement 17 with PhysLib's own proof term and every
erasure a visible `.magnitude`, and `#kind_unkinded` pins the exhibit's own boundary at
2 positions / 2 flows (both `Time`). `ReferenceFrame.checked_by.yaml` carries the proposed
map delta for both entries.

### Exhibit C. HarmonicOscillator

**Source.** `ClassicalMechanics/HarmonicOscillator/Basic.lean`,
`DampedHarmonicOscillator/`, `Pendulum/SimplePendulum/Basic.lean`

**Requirements.** [MR1](REQUIREMENTS.md#mr1-dimensional-homogeneity)–[MR5](REQUIREMENTS.md#mr5-scale-type-gates-the-operators),
[MR11](REQUIREMENTS.md#mr11-authoring-ergonomics),
[MR27](REQUIREMENTS.md#mr27-carrier-generic),
[MR28](REQUIREMENTS.md#mr28-kind-generic)

**What it shows.** [M6](MOTIVATION.md#m6-names-are-load-bearing-and-unchecked) — the
`funext t x p` transposition, and the `lagrangian`/`hamiltonian` argument-order collision that
makes it possible. Plus bare-real system parameters: `HarmonicOscillator { m k : ℝ }`,
`SimplePendulum { m ℓ g : ℝ }`, where `√(k/m)` and `√(m/k)`, `√(g/ℓ)` and `√(ℓ/g)` are equally
well-typed. And two more collisions in the same file: `S.force` accepts a momentum, and
`toCanonicalMomentum : E ≃ₗ[ℝ] E` carries a velocity to a momentum between identical types.

**Why it matters most.** This is the continuity with
[the case study](CaseStudies/HarmonicOscillator/README.md): the same system, now in PhysLib's
own authoring, so the ergonomic comparison is against real library code rather than against a
reconstruction. It is where `½ m ⟪v,v⟫` and `√(k/m)` must be shown at close to today's reading
weight, and where the same definition must be instantiated at `ℝ` and at `Float32` with
agreement as a theorem. **If that cannot be shown here, the MR11 objection stands and the
proposal should say so.**

**Status: built** — `ForPhysLib/Exhibits/HarmonicOscillator/Findings.lean`. The four
findings stand as compiling probes against the real files: the Hamiltonian called with
`p` and `x` swapped (the collision behind `hamiltonian_eq`'s transposed `funext t x p`);
`S.force` fed the canonical momentum; the momentum of a momentum through
`toCanonicalMomentum : E ≃ₗ E`; and `√(m/k)` / `√(ℓ/g)` as well-typed as the correct
recipes. The MR11 answer is measured, not asserted: five base kinds, one `kind_algebra`
block, two hand-registered entries joining at `energyK`, a scoped `SMul` restoring the
`½` — then `(1/2 : ℝ) • (m * (v * v))` against PhysLib's `1 / (2 : ℝ) * S.m * ⟪v, v⟫_ℝ`,
and `√((S.k / S.m).magnitude)` (one `.magnitude`, one attestation) against `√(S.k / S.m)`,
with `ω_sq` proved by PhysLib's own proof term. Every finding closes as a
`#check_failure` — the reciprocal dies *before* the root, `m / k` being no edge of the
algebra — and `kineticE` instantiates unchanged at `ℝ` and `Float32` with the magnitude
law one carrier-quantified `rfl` and a `#guard` executing at binary32 (MR27; the MR15
scope honesty unchanged from the case study).

### Exhibit D. TwoRovers

**Not a refactor.** Built *on* Exhibits A–C, to make the cost of *not* having Tier 7 visible
without asking PhysLib to adopt it.

**Requirements.** [MR20](REQUIREMENTS.md#mr20-a-quantity-belongs-to-a-named-part-of-a-named-system)–[MR24](REQUIREMENTS.md#mr24-a-dedication-carries-provenance),
[MR27](REQUIREMENTS.md#mr27-carrier-generic), and
[MR7](REQUIREMENTS.md#mr7-object-identity)–[MR9](REQUIREMENTS.md#mr9-whole-system-quantities)
at system scale.

**Two rovers, not one.** This is the point of the exhibit. Declare `rover1` and `rover2` as
distinct `System`s, each with a chassis, four wheels, four drive motors and a mast, each part
a `Component`, each part-mass a `DedicatedKind` quantity. Then three things must hold, and
each is a separate artifact:

1. **The total is a theorem.** `rover1.totalMass` is *proved* equal to the sum of the masses
   of rover 1's own components. Not a definition that happens to add the right things — a
   theorem, so that changing the parts list changes what must be proved.
2. **Cross-system contamination does not compile.** Substituting any of rover 2's component
   masses into rover 1's total is a `#check_failure`. This is the requirement that a single
   rover cannot express: with one system there is no way to distinguish "the sum of the parts"
   from "the sum of some masses of the right dimension", because every mass in scope is a
   correct summand.
3. **Under-counting is caught.** Omitting a component of rover 1 from the sum also fails, so
   the total cannot silently drop a wheel.

And the two-sidedness of [MR21](REQUIREMENTS.md#mr21-assembly-is-licensed-per-kind-and-two-sided)
must be exhibited alongside: rover 1's total mass is licensed and *sums*; rover 1's body-frame
angular velocity is **not** the sum of its components' angular velocities, and that sum must
be rejected. A scheme that gets (2) by forbidding (1) has failed.

The remaining tier-7 requirements ride on the same construction: wheelbase and total angular
momentum about the assembly's own centre of mass as whole-system quantities
([MR22](REQUIREMENTS.md#mr22-whole-system-quantities-are-not-part-quantities)); motor-to-wheel
torque naming both endpoints, so a torque for the left wheel cannot be delivered to the right
([MR23](REQUIREMENTS.md#mr23-interface-quantities-carry-both-systems-they-join)); each parameter
tagged measured, specified, derived or assumed
([MR24](REQUIREMENTS.md#mr24-a-dedication-carries-provenance)).

**This construction is not speculative.** The same five tier-7 requirements are already
discharged at scale in the author's soil-moisture model, whose `METROLOGICAL_RIGOR.md` records
the pattern against a system with many more parts than a rover. Exhibit D's job is not to
discover whether `System`/`Component`/`DedicatedKind` holds up under an assembly — that is
known — but to show a PhysLib reader what it buys, on a system built out of PhysLib's own
rigid-body mechanics.

**Status: built** — `ForPhysLib/Exhibits/TwoRovers/Findings.lean`. Two `System`s, ten
`RoverPart`s each, every part mass an object-indexed quantity and the §20 triple rendered
(`"rover 1 — chassis ; mass"` by `rfl`, cross-rover distinctness by
`DedicatedKind.distinct_of_system`). The three artifacts hold as promised:
`rover1_total_is_sum` proves the stated total against the assembled parts list;
rover 2's chassis mass neither adds to rover 1's nor splices into its assembly
(`#check_failure` ×2); `undercount_caught` proves the nine-part sum that drops a wheel is
not the total. Two-sidedness (MR21): mass carries the `Assembles` licence and sums, and
the sum of the parts' angular velocities fails to *elaborate* — no licence, no instance.
The wheelbase is the system's own quantity and refuses part-level addition (MR22); the
motor-to-wheel torque names both endpoints and cannot be delivered to the other wheel
(MR23); every mass carries a measured/specified/derived/assumed tag with the "what rests
on an assumption?" audit a `decide` (MR24); and `assemble`, carrier-generic, executes at
`Float32` under a `#guard` (MR27).

### Exhibit E. Electromagnetism — the confirmation exhibit

**Built last, and on purpose after the machinery.** Exhibits A–D were designed before the
benchmark forced `kind_algebra`, `SpecializationLift` and `Level` into the core; E is the
application that *confirms the approach*: the machinery the oscillator minted, played
against a real PhysLib directory it was not minted from, on defects that are in the source
today and on physics PhysLib does not have yet.

**Requirements.** [MR4](REQUIREMENTS.md#mr4-same-dimension-kinds-stay-apart),
[MR11](REQUIREMENTS.md#mr11-authoring-ergonomics),
[MR14](REQUIREMENTS.md#mr14-complex-valued-quantities),
[MR18](REQUIREMENTS.md#mr18-frame-covariance-and-what-survives-it)–[MR19](REQUIREMENTS.md#mr19-an-indexed-family-is-not-a-set-of-vector-components),
[MR32](REQUIREMENTS.md#mr32-specialization-keeps-kinds-comparable), and R13's level
machinery.

**The genuine problems, all verifiable in `Physlib/Electromagnetism/` as it stands:**

1. **An electric field *is* a magnetic field.** `Basic.lean` declares
   `abbrev ElectricField (d := 3) := Time → Space d → EuclideanSpace ℝ (Fin d)` and
   `abbrev MagneticField` with the *same* right-hand side — abbreviations, so
   `example : ElectricField 3 = MagneticField 3 := rfl` holds and a function expecting
   `E` accepts `B` with no error; `ChargeDensity := Time → Space → ℝ` likewise accepts any
   scalar field. This is [M5](MOTIVATION.md#m5-a-correctness-constraint-enforced-by-not-using-an-abbreviation)'s
   theme — correctness resting on *not being an abbreviation* — recurring at the heart of
   a second directory, and it is the exhibit's opening build artifact, in PhysLib's own
   terms.
2. **The dimension layer cannot fix it in every basis.** In SI, `E` and `B` differ
   dimensionally (by a velocity); in Gaussian-CGS — expressible since PhysLib's
   `Dimension` became basis-parametric (physlib#1441, PR 1447, merged) — they share one
   dimension, so a `WithDim` repair of problem 1 is *basis-relative*. Kinds are not: the
   probe declares `E` and `B` as distinct kinds over the *Gaussian* basis, where the
   dimensions provably coincide — MR4 on a directory that actually exercises the
   parametric bases.
3. **Natural units are a silent default.** `electricField (c : SpeedOfLight := 1)` — the
   unit system rides in an optional argument that defaults at every call site. The kinded
   re-authoring makes the choice a stated, greppable declaration rather than an elision.
4. **A potential is a position, not a value.** The scalar potential is gauge-dependent;
   PhysLib rightly proves invariance of the field strength, but the potential's own values
   still carry no trace of the convention. The torsor pattern (`Level`'s `sub`/`shift`,
   the affine sibling) states it: potential *differences* are the physical extents.
5. **The green field.** PhysLib has no AC or RF physics at all — no impedance, no phasors,
   no power factor, no link budgets. That is where the new machinery bites first-hand:
   impedance at the complex carrier (MR14); **dBm, dBW and field levels** on `LevelKind`
   (dBm ≠ dBW by decide, the energetic combination, a worked RF link budget — probes
   already standing in the core test suite); and the AC power family — active, reactive,
   apparent, one dimension, three unit strings (`W`, `var`, `VA`) — as a specialization
   lattice, with a deliberate **curation contrast**: energy registered `T + V` at its join
   (MR32), while this family registers *no* join sum, because `P + Q` is the domain error
   (powers orthogonal, `S² = P² + Q²`) — comparable kinds whose sum is refused is the same
   machinery exercised in the opposite direction, and the pair is the proof that the join
   table is curation rather than a loophole.

**Deliverables, per rule 2.** (i) The abbreviation probe against PhysLib's own modules —
the swap that type-checks today, then the kinded vocabulary (one `kind_algebra` block —
MR11's answer measured on a real directory) where it fails. (ii) The Gaussian-basis probe:
kinds apart where dimensions provably coincide. (iii) The RF/AC annex: impedance, the
link budget on `LevelKind`, and the AC-power lattice with the refused join. E–B mixing
under boosts stays with the field-strength tensor, as PhysLib already has it — the kind
layer records what survives a boost (MR18), it does not re-derive electrodynamics.

**Status: built** — `ForPhysLib/Exhibits/Electromagnetism/Findings.lean`. All five problems
stand as artifacts. (1) `ElectricField 3 = MagneticField 3` by `rfl`, `expectsE B` accepted,
a temperature field accepted as a `ChargeDensity` — and the kinded swaps all
`#check_failure`. (2) A Gaussian–CGS basis is stood up on PhysLib's own parametric
`Dimension`; `dimE = dimB` is proved (`M^½ L^-½ T⁻¹` both) while
`electricFieldK ≠ magneticFieldK` decides — the repair `WithDim` cannot make
basis-stable. (3) The `(c : SpeedOfLight := 1)` default probed at a bare call site; the
kinded answer is one attested declaration. (4) The scalar potential at *interval* scale:
differences licensed, `QuotientKind.ofRatio` refused at the gate. (5) The annex: phasor
impedance as `v / i` at `Complex Float` through the table; `dBm ≠ dBW` by `decide` with
gains one kind by `rfl`, `dBm + dBm` structurally unavailable, and a worked link budget
exact at `Int` (30 → +3 → −100 → +2 = −65 dBm); the AC power lattice comparable by
`MutuallyComparable` with `P + Q` refused (no join registered) and `S² = P² + Q²` the
licensed combination — while the energy family in the same file registers `KindJoin` and
`T + V` elaborates. The same table says yes and no on the same page: curation, not a
loophole.

### Exhibit F. PointParticle — an object index that is not a name

**The live PR.** [physlib#1612](https://github.com/leanprover-community/physlib/pull/1612)
(head `3ae4ae20`, unmerged) ties a quantity to an object *without* a metrology layer:
`Force` carries a `target` field, `InternalForce` a `source`, and a system's particles are a
`Multiset` coerced to a type. It is the first place upstream has needed the question this
proposal's Tier 3 asks, and it answers it a different way — so it is the exhibit that tests
whether the layer fits an object PhysLib designed rather than one we did.

**Requirements.** [MR7](REQUIREMENTS.md#mr7-object-identity)–[MR10](REQUIREMENTS.md#mr10-a-record-does-not-defeat-the-gate),
[MR21](REQUIREMENTS.md#mr21-assembly-is-licensed-per-kind-and-two-sided)–[MR22](REQUIREMENTS.md#mr22-whole-system-quantities-are-not-part-quantities).

**What #1612 gets right, and it is not nothing.** The `target` field ties a force to an
object at all, which upstream had no way to say; the multiset keeps multiplicity, so two
identical particles are two particles; and the objects are runtime-quantifiable, so
`∀ particle : particles` is a statement Newton's laws can be *fields* of. None of that is
available from a naming convention, and the assessment records it in full.

**What it cannot check, and the three are one cause.** `target` is a *field*, not an index,
so nothing about a force's type says whose it is: `netForce` filters on `target` with a
`Classical` equality test at the value level, and the type system is not consulted. The kind
is absent entirely — a displacement, a velocity and a force of one particle are all
`frame.Vector`, and their sums elaborate. And the aggregate definitions
(`System.mass`, `System.momentum`, and the sums a next PR will write for momentum
conservation) are unlicensed folds: `∑ p, p.velocity t` is as well-typed as
`∑ p, p.momentum t`.

**What the exhibit shows.** That the layer applies to #1612's *own* data structures, with
#1612 unmodified and PhysLib unchanged — because the object index of `IndividualQuantity`
was generalized from the nominal `System` to an arbitrary type, and a particle of a multiset
is a perfectly good index. Three findings, each a build artifact:

1. **The gate holds on an anonymous object.** Two particles' masses do not add; particles of
   two systems do not add; and a displacement and a force *of one particle* do not add — this
   last at the frame-vector carrier, with the carrier registered first so the refusal is about
   the kind and not about a missing instance. No `DecidableEq`, no designation, no new field
   upstream, and **no kinded vector type**: the gate is on the quantity, over PhysLib's own
   carrier.
2. **The particle cannot be *named*, and the layer says so.** `Designated s.Particle` does not
   synthesize — neither `System` nor `Particle` carries an identity field — and, since
   `Designated` carries an injectivity obligation, the instance an author would write instead
   (every particle to one name) is not writable either. The §20 systematic term is therefore
   unavailable here, and wanting it is a *PhysLib-side* ask for a label field, to be made
   separately if at all.
3. **Assembly, and the PR's own totals recovered by `rfl`.** `Composite s.Particle` gives the
   whole a place to live (MR22); `assembleAll` under an `Assembles` license gives the total;
   and `(totalMass s).magnitude = s.mass` and `(totalMomentum s t).magnitude = s.momentum t`
   are both `rfl`. The layer adds a gate and changes no arithmetic. The sums that would be
   wrong — the particles' velocities, the particles' positions — have no license and do not
   elaborate (MR21).

**Status: built** — `ForPhysLib/Exhibits/PointParticle/Findings.lean`. Nine `#check_failure`s,
each verified to fail for exactly one reason, and the two `rfl` erasures above. The PR is not
in this repository's pinned PhysLib, so the exhibit reproduces its *shape* — the
multiset-of-particles system, the coerced particle type, the `∑ p : s.Particle` aggregates —
and says so; the PR's three files themselves were compiled verbatim out of tree against the
same PhysLib commit, which is where the refusals were first established. When #1612 merges,
the replica should be deleted and its uses re-pointed at the real
`ClassicalMechanics.PointParticle.System`.

**What this exhibit is *not*.** It is not a review of #1612 and not a request that #1612
change. Everything above holds with the PR exactly as written; the layer is additive, per
[MR31](REQUIREMENTS.md#mr31-adoption-is-scoped-and-monotone). If any of it is to reach the
PR's author it is as an offer, and posting is a human's (AI-POLICY §3.1).

### Ranking

| | exhibit | why it earns its place |
|---|---|---|
| 1 | **A · RigidBody** | highest defect density; the one place a real correctness constraint is enforced by authoring convention |
| 2 | **B · ReferenceFrame** | a stated requirement that is not satisfiable without the layer — design input, not retrofit |
| 3 | **C · HarmonicOscillator** | continuity with the case study; where MR11 must be paid down or conceded |
| 4 | **D · Two rovers** | the reach argument; the only exhibit about capability rather than defects |
| 5 | **E · Electromagnetism** | the confirmation: machinery minted by the benchmark, applied to a directory it was not minted from |
| 6 | **F · PointParticle** | the live test: a PR that ties quantities to objects without the layer, and objects PhysLib designed rather than we did |

---

## What a maintainer would and would not sign

Asked directly, because the proposal is worthless if the answer is "none of it".

**Already their own position — these are quotations, not proposals.**

- [MR26](REQUIREMENTS.md#mr26-frame-generic) — `ReferenceFrame`'s module doc asks for exactly
  this. The requirement is that there be somewhere to supply it.
- [MR29](REQUIREMENTS.md#mr29-every-satisfied-requirement-has-a-machine-checkable-witness) —
  they built the API maps. The proposal is one field.
- [MR4](REQUIREMENTS.md#mr4-same-dimension-kinds-stay-apart) and
  [MR5](REQUIREMENTS.md#mr5-scale-type-gates-the-operators) — `Time/Basic.lean` states the
  defect in its own module doc.
- [MR25](REQUIREMENTS.md#mr25-dimension-generic) — already practised, and the places it lapses
  are the places this layer would reach.

**Likely agreement, but the demonstration has to come first.**

- [MR28](REQUIREMENTS.md#mr28-kind-generic), because it is the *answer* to the ergonomic
  objection rather than a restatement of it. This has to be shown — an `OperatorTable` idiom
  where the formula reads the way it reads today — or the objection stands and is correct.
- [MR27](REQUIREMENTS.md#mr27-carrier-generic), if framed as *reach* rather than as rigour. It
  is a large ask: the library is `noncomputable` by construction.
- [MR30](REQUIREMENTS.md#mr30-the-unkinded-surface-is-measured), **provided the
  Mathlib-interface tier is in from the start.** A report that scores every `fderiv` call as a
  defect will be read as hostile, correctly.

**Contested, and should be presented as such.**

- [MR23](REQUIREMENTS.md#mr23-interface-quantities-carry-both-systems-they-join) and
  [MR24](REQUIREMENTS.md#mr24-a-dedication-carries-provenance) are systems engineering, not
  physics. A maintainer is entitled to say they are out of scope, and should be *offered* the
  option of having them live entirely in the layer above.

**The resulting split.** Tiers 1–6 and 9 proposed to the library; Tier 7 demonstrated on top
of it in Exhibit D, so the cost of not having it is visible without anyone being asked to pay
it; Tier 8 proposed as the thing that makes the rest affordable.

---

## Sequencing

1. **Exhibit A**, because it has the highest defect density and the clearest single finding.
2. **Exhibit B**, because it converts the proposal from criticism into design input.
3. **Stage 0 + Stage 1 for one directory** — `SpaceAndTime/Space` is the right first choice:
   small, foundational, and its API map already contains the `LengthUnit` requirement that
   makes [MR29](REQUIREMENTS.md#mr29-every-satisfied-requirement-has-a-machine-checkable-witness)
   concrete. **Done** — `ForPhysLib.Kinds.Space` / `Examination.Space` / `Metrology.Space`:
   six ISO 80000-3 kinds (the position/displacement pair the directory's own torsor keeps
   apart, named at the kind level), the lookup proved against `Iso80000.Part3` by `decide`,
   and `#kind_dimensional_coverage` pinned clean over the directory's two authored edges.
   The ladder has since been climbed to the top for this directory: Stages 2–4
   (`Kinded`, `Operators`, `Audits`) carry their own Status lines in the ladder above.
4. **Exhibit C**, which is where the ergonomic question is settled either way.
5. **Exhibit D**, because it depends on the others and argues a different point.
6. **Exhibit E**, last — the confirmation pass: it presupposes the minted machinery
   (`kind_algebra`, `SpecializationLift`, `Level`) and its whole value is showing that
   machinery solving problems it was not built against.

All six items now stand: the five exhibits are built — each carries a **Status: built**
line in its section above — and the ladder is complete for its first directory.

Nothing goes upstream before Stage 1 exists for at least one directory, because Stage 1 is
the part that costs a maintainer nothing and therefore the part that should arrive first.

---

## The three-directory campaign

The ladder is complete for one directory and the exhibits probe four more — but every
completed *stage* stands on geometry. `SpaceAndTime/Space` is the right first directory for
exactly the reasons that make it the wrong last one: small, foundational, nearly
dimension-one. The maintainer's obvious next question is *"fine for geometry — what does
this cost on actual physics?"*, and the campaign answers it on three directories, each
re-authored with the PhysLib files as the literal reference, each chosen because it proves
something the Space ladder cannot:

| | directory | scope | what it uniquely proves |
|---|---|---|---|
| 1 | `QuantumMechanics/HarmonicOscillator` | all 8 files (~1.7k lines; `LadderOperators` is a stub of TODOs) | the capability frontier: kinds over an operator-valued carrier at `ℂ`, half-power dimensions, nondimensionalization as a kind-level event |
| 2 | `Electromagnetism` | the `Kinematics` chain (potentials → fields → boosts → gauge) | joins and frames where the physics forces them — Exhibit E's five findings paid down as a ladder rather than probed |
| 3 | `ClassicalMechanics` | the `HarmonicOscillator` and `RigidBody` subtrees | same-dimension discrimination at theorem scale: four energies at one dimension, with `equationOfMotion_tfae` as the verbatim-survival stress test |

### The campaign's four rules

**1. Mirror-and-import, never rewrite.** Each campaign module *imports* the PhysLib module
it mirrors and builds the kinded layer on top: the Stage-2 invariant (the naked form is
`rfl`-equal to `.magnitude`) is exhibited per directory, PhysLib's own theorems close
kinded goals verbatim, and the refusals are pinned beside them. A side-by-side rewrite
would invite a 20k-line diff review and read as "your library is wrong"; the annex form
invites accepting a directory of new files that changes nothing. Where the existing
carrier genuinely cannot support the layer — the requirement-16 situation of Exhibit B —
that is recorded as a design-input *finding* in the M-series style, never silently
rewritten around.

**2. Representative subtrees, not every file.** `ClassicalMechanics` and
`Electromagnetism` are ~10k lines each; the campaign takes the subtrees named above and
says so. A maintainer extrapolates from three honest subtrees; nobody reads 78 files
either way. `QuantumMechanics/HarmonicOscillator` is taken whole because it is small and
because it is the frontier.

**3. The campaign is evidence; the ask stays Stage 1.** "PKC belongs in PhysLib" is a
conclusion the campaign may some day support — it is not the proposal, and the dependency
argument for it is not even clean until the unit-side parametrization (the
`parametrize-unit` branch — the unit sibling of the parametric `Dimension B`, whose PRs
#1447 and #1521 are already merged upstream) lands too. The decision ladder for the
maintainer is unchanged from
[the shape of the proposal](#the-shape-of-the-proposal): (i) the unit-side
parametrization PR first — self-contained, independently valuable; (ii) ForPhysLib
presented as a *browsable downstream artifact* — three directories re-authored, every
theorem statement surviving, findings and costs measured — with the question put to the
maintainer being *where they want that conversation*, not whether to merge anything;
(iii) the first mergeable unit stays Stage 0 + Stage 1 for one directory. And the
standing constraint: every message to the maintainer is drafted to a file and posted by
a human (AI-POLICY §3.1).

**4. The pilot goes first because it can falsify.** The quantum oscillator's quantities
are partial linear operators on a Hilbert space (`Q.HS →ₗ.[ℂ] Q.HS`), its scalars are
`ℂ`, its characteristic length is built from half-integer-dimension intermediates, and
its `ξEquiv` rescaling is textbook nondimensionalization. None of that had faced the
calculus. If the pilot forces core changes, they land in PKC first — which would be the
third time this benchmark changed the calculus rather than the scorecard, and per rule 5
of the [rules of engagement](#rules-of-engagement) that is the instrument working.

### The cost line

The one number a maintainer needs that nobody publishes: what the layer costs, measured.
Each campaign directory ships a README whose cost table counts, against the mirrored
source, (i) kinds minted (base vs derived-by-`kind_algebra`), (ii) operator-table and
join entries, (iii) attestations and visible `.magnitude` crossings, and (iv) lines of
ceremony per line of physics re-authored — every number quoting a build artifact, per
rule 2 of the [rules of engagement](#rules-of-engagement). This is
[MR11](REQUIREMENTS.md#mr11-authoring-ergonomics) paid down in public, directory by
directory.

### Layout: directory-major, mirroring the source

The Space ladder keeps its stage-major tree (`Kinds/Space.lean`, `Metrology/Space.lean`,
…) as the reference implementation of the ladder itself. Campaign directories are
**directory-major**: the module path mirrors the PhysLib path, and the files inside are
named by stage —

```
ForPhysLib/QuantumMechanics/HarmonicOscillator/
  Feasibility.lean     the pilot's capability probes (before any ladder stage)
  Kinds.lean  Metrology.lean  Kinded.lean  Operators.lean  Audits.lean
  README.md            the findings and the cost line
```

— because the unit of adoption is a module root and a maintainer browses by physics
area: `ForPhysLib/QuantumMechanics/HarmonicOscillator/Kinded.lean` reads as *what
`Physlib/QuantumMechanics/HarmonicOscillator` becomes*.

### The pilot: `QuantumMechanics/HarmonicOscillator`

Feasibility before ladder: the capability questions are answered as build artifacts in
`Feasibility.lean` before any stage is climbed, because each one could force a core
change and the cheap time to find out is before the campaign is committed to.

- **F1 — the operator carrier.** `Quantity` stood up at `Q.HS →ₗ.[ℂ] Q.HS`: `T̂` and
  `V̂` wrapped at kinetic/potential kinds, `T̂ + V̂` elaborating through the curated
  `KindJoin` at energy and *definitionally equal* to PhysLib's `hamiltonian`
  (`hamiltonianOpQ_eq`, a `rfl`); the sum of `T̂` with the momentum-squared operator
  refused (`#check_failure`). The `(2·m)⁻¹ • p̂²` construction is the named crossing: a
  dimensionful scalar rides Mathlib's `SMul` where no table can see it — the
  [MR30](REQUIREMENTS.md#mr30-the-unkinded-surface-is-measured) tier, recurring at an
  operator carrier.
- **F2 — half-power dimensions.** The library spells the same characteristic length both
  ways: root-first in the `d`-dimensional file (`ξ i = √ℏ/(√m·√ωᵢ)`, whose intermediates
  carry half-integer dimension and are named by no kind — half-power kinds are
  deliberately absent) and radicand-first in the 1D file (`ξ = √(ℏ/(m·ω))`, whose
  radicand is a two-edge `kind_algebra` chain landing at length²). The probe builds the
  radicand-first form kinded with one attested root, equal to PhysLib's `ξ` (`xiQ_eq`),
  and proves the respelling from PhysLib's own `ξ_sq` in one line
  (`xi_radicand_first`) — only one of the two spellings survives kinding, and the 1D
  file already writes that one.
- **F3 — the SI numeral.** `Constants.ℏ` is `⟨1.054571817e-34, _⟩` — the unit system
  (J·s) committed by docstring prose alone, the QM twin of Exhibit E's `(c := 1)`,
  pinned by `rfl`; the kinded form is one attested action quantity naming the crossing.
  And the 1D oscillator's docstring promises "three real parameters … a value of
  Planck's constant `ℏ`" while the structure carries two fields and takes ℏ from the
  global constant — a prose finding for the directory README.
- **F4 — the eigenvalues.** `ℏ ωᵢ (nᵢ + ½)` kinded per mode — action × angular frequency
  landing at energy through the table, the dimensionless `nᵢ + ½` on the scoped numeral
  action — with the mode sum proved equal to PhysLib's `eigenEnergy`
  (`eigenEnergy_eq_sum_modes`; magnitude-level, because aggregating a mode *family* at
  the kind layer is Stage-2 work, and `Extensive`'s licensed aggregation is the
  machinery it will use).

**Held for the ladder, deliberately.** The `ξEquiv` nondimensionalization (a kind-level
reading of a dimensionful rescaling), the Schwartz-space eigenfunctions, and the
`LadderOperators` stub — a green-field co-authoring opportunity in the RF-annex style:
`a`, `a†` and `N` are dimensionless, and the file does not exist yet to be re-authored.

**Status: built** — `ForPhysLib/QuantumMechanics/HarmonicOscillator/Feasibility.lean`:
F1–F4 close as the artifacts named above. The base kinds are **catalogue lookups**, not
local mints — the Stage-0 asymmetry exercised: mass (4-1), action (4-32), angular
frequency (3-18) and the kinetic/potential/mechanical energy family (4-28.1–3) come from
`Iso80000` Parts 3 and 4, and the characteristic length is a species in Part 3's own
`lengthSpecies` pattern; only what the standard does not list (the radicand chain, the
momentum-squared mint) is local. The feasibility verdict is *no core change
forced* — with one deliberate upstream exception: the carrier vocabulary an operator type
needs went to the core as `Carrier.ofZeroAdd` (a smart constructor, not an instance, so
the curated per-application carrier discipline is unchanged) rather than living in the
probe.

**Status: Stages 0–1 climbed** — `Kinds.lean`: eleven kinds, eight of them catalogue
lookups written as verbatim literals, plus the length species and the named mints (each
mint saying why the standard does not list it); the three-energy collision decided; the
directory's lattice with `T̂`/`V̂` mutually comparable at mechanical energy — the pair the
Hamiltonian joins. `Metrology.lean`: twelve `DimensionedKind` pairings, the Stage-0
lookup proved against `Iso80000` Parts 3–4 (`decide` on kinds, `rfl` on dimensions), six
authored edges — the radicand chain (`ℏ/m`, then `/ω`), `ξ·ξ` landing back in the
radicand, `ℏ·ω` an energy, `p̂·p̂`, and `p̂²/m` a kinetic energy (the law the source's
`SMul` spelling cannot consume) — with `#kind_dimensional_coverage` pinned clean over
all six.

**And the pilot discharges the first item of the upstream TODO list.**
`Orthonormality.lean` proves `eigenstates_orthonormal` — the `@[sorryful]` lemma opening
`Eigenstates.lean`'s TODO list — statement verbatim, sorry-free (axioms: `propext`,
`Classical.choice`, `Quot.sound`). The missing piece was exactly the sorry's own hint:
the `Space d` product-splitting lemma (`integral_prod_coord`, ~25 lines from
`Space.basis`'s measure-preserving repr plus Mathlib's unconditional n-variable Fubini);
the 1D content is PhysLib's own `physHermite_orthogonal_cons`/`physHermite_norm_cons`
with `eigenCoeff`'s normalization cancelling exactly. This is rule 1's "patch, not a
finding" delivered at theorem scale: the mirror directory that costs PhysLib nothing
also *pays* something. The offer upstream is a human's to make (AI-POLICY §3.1).

**The Stage-2 metrological TODO slate — what the upstream list could not ask for.**
`Eigenstates.lean` opens with six analysis TODOs; each casts a metrological shadow the
analysis statement cannot express, because the vocabulary to state it does not exist
without the kind layer — a sentence that belongs in the directory README verbatim. The
slate, each item with the artifact it owes (rule 2 of the
[rules of engagement](#rules-of-engagement)):

- **M-T1 — the wavefunction's half-power dimension** (from orthonormality, discharged).
  The Born density `|ψ|²` is the kinded object — a probability density over position,
  dimension `L⁻ᵈ` — and ψ is its attested root at `L^(−d/2)`: F2's radicand-first rule
  recurring at the states themselves, visible in the source as the `1/√ξᵢ` each
  `eigenCoeff` carries. *Artifact* (`Kinded.lean`): the density kinded; the
  orthonormality integrand exhibited as density × volume = dimension one; the quantum
  numbers `n` looked up from `Iso80000.Part10` (items 10-13.x), not minted.
- **M-T2 — nondimensionalization and the silent reference** (from the ladder shift).
  `a = (x/ξ + iξp/ℏ)/√2` is the textbook nondimensionalization event: two ratio edges
  landing at dimension one, `N = a†a` a Part-10 count, the shift `±1` a count operation.
  And the eigenvalues `ℏωᵢ(nᵢ+½)` inherit the silently declared potential zero
  (`V(0) = 0` at equilibrium — a convention riding in a definition, the `c := 1`
  pattern again); only the spacings are reference-free. *Artifact* (`Kinded.lean`):
  eigenvalue *differences* landing in a spacing kind through `DifferenceKind`; the
  zero-point energy read against the declared reference; the missing declaration
  recorded as a finding.
- **M-T3 — the eigenvalue equation is the operator→scalar bridge** (from the TISE).
  `Ĥψ = Eψ` equates an energy-kinded *operator* quantity with an energy-kinded *scalar*
  acting through Mathlib's `SMul` — F1d's crossing recurring on the right-hand side of
  the subject's defining equation. *Artifact* (`Kinded.lean`): the kinded TISE
  connecting `hamiltonianOpQ` (F1) with `modeEnergyQ` (F4) through the eigenstate, the
  `E •` crossing attested — statable now, while the analysis TISE stays open upstream.
- **M-T4 — the measurand vocabulary** (from spectrum and self-adjointness). New
  vocabulary rather than re-authoring, and application-generic, so the vocabulary
  itself lives in the PKC core: `PropertyKindCalculus/Measurand.lean` is VIM's
  measurand as a kinded interface — estimate at `k`, variance at the squared kind
  through a carried `ProductKind k k k₂` edge, the indication predicate, σ and the
  `estimate ± σ` bounds derived once for every model (the R14 attachment point). The
  directory then supplies the *quantum realization*: self-adjointness is the
  mathematical form of *observable*, i.e. the measurand; the spectrum is the set of
  possible **indications**, carrying the operator's kind; `⟪ψ, Ĥψ⟫` is the
  expectation — an energy, GUM's best estimate — the variance an energy², its σ the
  core's attested root (radicand-first again). *Artifact*
  (`PropertyKindCalculus/Measurand.lean` + the directory's `Measurand.lean`): the
  vocabulary minted in the Mathlib-free core and realized on `hamiltonianOpQ`.

**The second patch, delivered.** Heisenberg's `σ_x · σ_p ≥ ℏ/2` turned out to be a
theorem upstream owns every part of and has never joined: the abstract Robertson bound
(`Operators/Uncertainty.lean`), the canonical commutator (`Commutation.lean`), and the
self-adjoint position operator all exist there, the bound is instantiated nowhere, and
`ℏ/2` appears nowhere else in the library. `Heisenberg.lean` proves
`heisenberg_uncertainty` — `ℏ/2 ≤ σ_xᵢ σ_pᵢ` for every normalized Schwartz state, in
upstream's own vocabulary, sorry-free — and the ground state's position side,
`σ_x = ξᵢ/√2`, by the same Hermite–Gaussian machinery as the orthonormality discharge
(`H₁ = 2X` turns the moments into `integral_hermite_pair` rows). The kind layer then
closes the loop: position becomes a PKC `Observable`/`Measurand` (its self-adjointness
is *proved* upstream, so unlike the Hamiltonian's no hypothesis rides along), the
kinded bound runs the product through Stage 3's `length · momentum → action` entry,
and saturation at the ground state is exact: the momentum moment
`σ_p(ψ₀) = ℏ/(√2 ξᵢ)` follows from the Gaussian's eigen-relation
`𝐩 ψ₀ = (iℏ/ξᵢ²) • 𝐱 ψ₀` (one `HasFDerivAt` computation), which carries the
already-proved position moments through `𝐩`.

**Held with the spherical/ladder green field.** The `L_z = m·ℏ` crossing — an *angular
momentum* equated with a count times a constant catalogued as *action*, the catalogue's
own same-dimension pair (4-11 / 4-32) played at theorem scale, `IsqLift`'s torque/energy
move on a new pair; and degeneracy as a Part-10-style count — one line, not a
workstream.

**Status: ladder complete, Stage 0 through Stage 4, plus both patches — the pilot is
done.** Stage 3 (`Operators.lean`): the directory's seven remaining edges registered as
`KindMul`/`KindDiv` instances at the kinds the quantities actually carry (instance
search does not cross the `rfl` bridge between the two kind spellings — a finding),
with PhysLib's own `ξ_sq` closing the table-built erasure, three refusals pinned, and
coverage re-pinned over the table; Stage 1 grew the two edges the uncertainty work
needs (`x·x` and `x·p`, coverage at ten). Stage 4 (`Audits.lean`): the whole directory
namespace under CI — probe files tier-tagged too — with the 20-site boundary audit and
crossings registry pinned, boundary-clean + mint-ratchet + dimensional-clean silent,
the end-to-end-kinded interior gated empty (the gate refused `ξEquiv`'s crossing during
authoring — correctly), the 15-position ingest boundary measured, and the
`checked_by.yaml` delta keyed on the upstream TODO texts. The README carries the
findings and the measured cost line. Axiom profile of every theorem in the directory:
`propext, Classical.choice, Quot.sound`.

**Status: Stage 2 climbed — the slate's first four items delivered.** Stages 0–1 grew
the vocabulary the slate needs (quantum number as a Part-10 lookup; the dimensionless
coordinate, Born density, volume element, probability and energy-squared mints; two new
edges — `x/ξ` and `energy · energy` — with the coverage pin at eight, all coherent).
`Kinded.lean` delivers the re-authoring and M-T1–M-T3: the eigenvalue as a
`DifferenceKind`-licensed fold over the mode family erasing to `eigenEnergy`; the
`d`-dimensional ξ radicand-first, its erasure to the root-first source *being* the F2
respelling; `ξEquiv` read as the `x/ξ` edge run backwards; the Born density kinded with
`∫ρ dV = 1` a theorem off the discharged orthonormality (ψ itself named by no kind — the
half-power rule at the states) and the `L⁻ᵈ·Lᵈ = 1` coherence parametric in `d`, which
is why the density pair has no registry pairing; the level spacing `ℏωᵢ` through the
scale-gated `Quantity.sub` (reference-free) against the zero-point energy that reads on
the *pinned* silent `V(0) = 0` (`potential_zero_at_equilibrium`); and `SatisfiesTISE`
with the `E •` crossing attested once (`energySMul`). M-T4's vocabulary is PKC's at
both levels: the core owns the measurand (`PropertyKindCalculus/Measurand.lean` — the
VIM interface with estimate, variance gated by the carried square edge, indications,
and σ/`upper`/`lower` derived once), the Mathlib-facing layer owns its operator
realization (`PropertyKindCalculus/Observable.lean` — a self-adjoint operator
quantity over any `RCLike` field, with `Observable.toMeasurand` the identification),
and the directory's `Measurand.lean` only instantiates — the Hamiltonian at `𝕜 = ℂ`
on the Stage-1 square edge with the eigenvalue set as indications, and
`expectation_eigenstate` — the vocabulary composing across F1, the fold, M-T3 and the
discharged orthonormality, conditional on exactly the two open upstream TODOs it
names. Axiom profile of every theorem named here: `propext, Classical.choice,
Quot.sound`.

### Directory 2: `Electromagnetism/Kinematics`

The chain, taken whole — eight files, ~3.2k lines, `EMPotential.lean` at the root and
everything else derived from it: the potential split into `ScalarPotential`/`VectorPotential`,
the `FieldStrength` tensor, the `ElectricField`/`MagneticField` readings, `Boosts`, and
`GaugeTransformation`. What this directory uniquely proves: **joins and frames where the
physics forces them** — Exhibit E's five problems paid down as a ladder rather than probed.

The structural fact the whole plan hangs on, read from `toTimeAndSpace` and to be pinned as
the first feasibility artifact: the library's spacetime coordinate is `x⁰ = c·t` — a
*length* — so `SpaceTime d` is dimensionally uniform, and the `φ/c` in `ofPotentials` is
not a convention but the move that makes the four-vector `A^μ = (φ/c, 𝐀)` a *single kind*:
the magnetic vector potential (item 6-32, a catalogue lookup). Everything the chain then
does is one homogeneous tensor being read back into frame-bound kinds through one velocity
edge, and the feasibility questions follow that spine:

- **F1 — the classical-field carrier, and the abbreviation paid down at the chain's own
  types.** `Quantity` stood up at `Time → Space d → EuclideanSpace ℝ (Fin d)` (a field of
  vectors — `Carrier.ofZeroAdd` over Mathlib's pointwise instances) and at the *structure*
  `ElectromagneticPotential d` (upstream's own `AddCommGroup`). `E` and `B` wrapped at the
  Part-6 kinds over the same naked carrier; Exhibit E's swap — `expectsE B` accepted, a
  temperature accepted as a charge density — re-run and `#check_failure`ed at the types the
  chain actually uses. [MR19](REQUIREMENTS.md#mr19-an-indexed-family-is-not-a-set-of-vector-components):
  the wrap is of the whole field; components stay plain indexing under it.
- **F2 — one homogeneous tensor, two readings, one velocity edge.** `scalarPotential` is
  `c · A⁰` — the 6-32 → 6-11 crossing *is* multiplication by the speed of light, and
  upstream's `ofPotentials_scalarPotential` closes the kinded round trip. The same edge
  recurs one level up: `F = ∂A − ∂A` is uniformly at the flux-density dimension (`∂` is a
  per-length operation on a length-coordinate spacetime), the spatial block *is* the
  magnetic field (`fieldStrengthMatrix_inr_inr_eq_magneticFieldMatrix`), and the electric
  reading exists only through the crossing: `E_i = −c · F⁰ᵢ`
  (`electricField_eq_fieldStrengthMatrix`). `E` and `B` remain distinct kinds — the
  Gaussian-basis point, [MR4](REQUIREMENTS.md#mr4-same-dimension-kinds-stay-apart) — so the
  tensor's entries carry a *third*, frame-covariant kind that erases to both.
- **F3 — the silent numeral, now load-bearing.** `(c : SpeedOfLight := 1)` rides an
  optional argument on *every* definition in the chain — `scalarPotential`,
  `vectorPotential`, `electricField`, `magneticField`, `magneticFieldMatrix` — and defaults
  at every bare call site; Exhibit E pinned this once, the ladder must now carry the
  declared alternative through every re-authored definition. One attested quantity at
  6-35.2, declared once, consumed everywhere.
- **F4 — boosts are the forced joins.** `E'_⊥ = γ(E + cβ·B)` sums an electric-field reading
  with a velocity-scaled magnetic one — a sum that elaborates *only* through F2's edge —
  and `B' = γ(B + (β/c)·E)` is its mirror
  (`electricField_apply_x_boost_succ`, `magneticFieldMatrix_apply_x_boost_zero_succ`).
  [MR18](REQUIREMENTS.md#mr18-frame-covariance-and-what-survives-it) answered at theorem
  scale: the kind that survives a boost is the tensor's; the `E` and `B` kinds are
  frame-bound readings, licensed to mix exactly where the physics mixes them.
- **F5 — gauge freedom is the interval scale, and χ is a flux.** The catalogue itself
  records electric potential (6-11.1) as interval-scale; upstream now *proves* the torsor
  structure — `gaugeTransform_zero` and `gaugeTransform_gaugeTransform` are the additive
  action, `toFieldStrength_gaugeTransform` says the field strength is the reference-free
  extent. And the gauge function is not dimensionless: `∂^μ χ` lands at 6-32, so `χ` is a
  *magnetic flux* field (6-22.1 — a lookup, not a mint). Exhibit E problem 4's torsor
  pattern, paid down at the four-potential with the group action already proved upstream.

**The ladder then follows the pilot's stages** — `Kinds.lean` (Part-6 lookups should
dominate; the field-strength kind is the expected mint, saying why the standard does not
list a frame-covariant entry), `Metrology.lean` (the velocity edge in both directions, the
per-length derivative edges `∇φ`, `∂ₜ𝐀`, `∇×𝐀`, coverage pinned), `Kinded.lean` (the
re-authored chain: potential → fields → the boost laws → gauge as the scale-gated
subtraction), `Operators.lean`, `Audits.lean`, `README.md` with the cost line —
directory-major at `ForPhysLib/Electromagnetism/Kinematics/`, every module importing the
PhysLib module it mirrors.

**Delivered in full.** The `Dynamics/` variational subtree is kinded
(`Kinematics/Dynamics.lean`): both Lagrangian terms at one minted density, both
spellings of `δS/δA` at the Euler–Lagrange mint, the Legendre pair with the
Hamiltonian's 6-33 target licensed by upstream's own theorem, `IsExtrema` unfolding to
the kinded gradient's vanishing (the hypothesis `Maxwell.lean`'s laws consume), and
one stale TODO found (`μ₀ = 1` is announced as "a TODO to introduce" in two module
docstrings while every definition already takes `𝓕 : FreeSpace` — a two-line patch
candidate). The RF/AC annex is promoted from Exhibit E to ladder form
(`Electromagnetism/Annex/`, five files): 17 kinds all catalogue lookups with zero
mints, half the edges consumed from `Part6.DefiningRelations`, phasor circuits
through the operator table at the complex carrier, the refused `P + Q` beside the
licensed quadrature, and the dB link budget rooted at the catalogue's 6-45. Maxwell's equations themselves are delivered:
`Maxwell.lean` kindes the four laws (four new lookups, three derivative mints, seven
edges; still no join — `ε₀∂ₜE` lands at the catalogue's own 6-8) and found that
upstream's four laws are *module-private* (the one file in the subtree missing
`@[expose] public section`) — a one-line patch candidate. The `Distributional/` twin's duplication finding is delivered:
`DistributionalTwin.lean` pins the re-authored law by `rfl`, prices the twin's kind cost
at zero, and pins the missing smooth → distributional embedding as the statement a
deduplication theorem still needs.

**Status: feasibility built** — `ForPhysLib/Electromagnetism/Kinematics/Feasibility.lean`:
F1–F5 close as the artifacts named above. The Stage-0 vocabulary is **lookups only** —
every kind the file needs is in IEC 80000-6, the mirror image of the pilot's mint-heavy
opening (the one expected mint, the field-strength tensor's frame-covariant entry kind,
is deferred to `Kinds.lean`). The velocity edge is registered twice (6-32-side landing at
the ratio-scale 6-11.2, tesla-side landing at 6-10) with all four dimensional
certificates discharged by `decide` in the catalogue's own dimension group, and the
interval-scale 6-11.1 *refusing* both `ofRatio` forms — the catalogue's scale
adjudicating where upstream's `ℝ` cannot. The chain's own derived `magneticField` is
accepted as an `ElectricField` (F1a) and the kinded swap refused; the `/c` is pinned at
`ofPotentials`'s time slot by `rfl` and `scalarPotential = c·A⁰` closed round-trip by
upstream's own lemma; the bare-call-site default is pinned; the boost law is consumed
whole (`boost_reads_through_the_edge` — upstream's `electricField_apply_x_boost_succ`
erasing the kinded `γ·(E + c·(β·B))`, with `E + B` refused beside it); and the gauge
torsor is three theorems off upstream's own invariance and group-action lemmas, with the
gauge function at 6-22.1. Axiom profile of every theorem: `propext, Classical.choice,
Quot.sound`.

**Status: Stages 0–1 climbed** — `Kinds.lean`: twelve kinds, **ten of them catalogue
lookups written as verbatim literals** (IEC 80000-6 plus the three Part-3 coordinates —
the mirror image of the pilot's mint-heavy opening) and exactly two mints, the same
finding twice: the standard catalogues frame-bound, gauge-fixed readings, so the
gauge-dependent `∂A` entry and the gauge-invariant, frame-covariant `F` entry have no
row to look up. Three kinds at the tesla and two at the volt, separated by `decide`;
the 6-11.1 interval scale pinned by `rfl`; no `KindJoin` — every sum the chain writes
is same-kind after an edge or a crossing, and that contrast with the pilot's `T̂ + V̂`
is recorded as a finding. `Metrology.lean`: twelve `DimensionedKind` pairings with the
repeated dimensions visible in the registry, the Stage-0 lookup proved against
`Iso80000` Parts 3 and 6 (`decide` on kinds, `rfl` on dimensions, the mints' tesla
checked against the catalogue's), and twelve authored edges — the velocity edge both
ways, the three derivative edges of `E = −∇φ − ∂ₜ𝐀` and `B = ∇×𝐀` (the gradient edge
stated at the potential's *differences*: a derivative of an interval-scale quantity is
a difference quotient), the chart edge, the tensor's electric reading, both boost
mixings, the gauge edge, and the Poincaré-gauge line integrals — with
`#kind_dimensional_coverage` pinned clean over all twelve.

**Status: Stage 2 climbed** — `Kinded.lean` re-authors the chain in its own derivation
order. The slices are named crossings (`timeSlice` re-parameterizes by `c·t ↦ t` where
no table sees it). The electric field is *built from its parts* and erases
definitionally: `−∇φ` and `∂ₜ𝐀` as two attested derivative crossings — the gradient one
carrying the scale fact that a derivative of the interval-scale potential is a
difference quotient — and their same-kind difference *is* upstream's `electricField` by
`rfl`. The curl and matrix readings erase by `rfl` too. The chart/extent pair delivers
the two mints: `derivQ` at the gauge-dependent kind, `fieldStrengthQ` at the
frame-covariant one, with `pureGauge_extent_zero` (a pure translation has zero extent —
upstream's `toFieldStrength_ofGradient` at the kinded reading) witnessing that the
antisymmetrization is what erases the gauge dependence; the frame-bound readings come
off the tensor exactly as Stage 1's edges say (`electricReadingQ` = `−c·F⁰ⁱ` through
the registered edge, `magneticReadingQ` the spatial block). The boost ledger closes:
the magnetic mirror `B' = γ(B + (β/c)·E)` consumed whole through the downward edge, and
the transverse-transverse block proved fixed. And **gauge invariance reaches the
fields**: `electricField_gaugeTransform` and `magneticFieldMatrix_gaugeTransform` are
proved here and stated nowhere upstream — a candidate patch in the orthonormality
pattern — then consumed at the kinded readings. Axiom profile of every theorem:
`propext, Classical.choice, Quot.sound`. One instance-search note for Stage 3: the
`rfl` bridge between Feasibility's catalogue lookups and Stage 0's literals again does
not carry instance search (the pilot's finding 8) — `boostedBQ` needed one type
ascription across it.

**Status: Stage 3 climbed** — `Operators.lean` registers the three remaining edges
that have scalar call sites (`φ-difference/c`, `c·F⁰ⁱ`, `E/c`; the two upward entries
predate it in Feasibility), with the coverage re-pinned over the table. The seven
law-only edges stay laws, and that is the directory's Stage-3 finding: in a field
theory the *majority* of the kind algebra rides `fderiv` and `∫` where no table sees
it — the pilot's `p̂²/m` precedent as the common case, left to the audit stage to
measure. The interval potential gets its torsor: `potentialSubQ` (`−ᵥ` to the
ratio-scale extent) feeds the `φ/c` entry while `φ/c` on the potential itself is
refused — the only outbound arithmetic 6-11.1 has. `electricReadingFromTable` shows
the one-`*` spelling is *definitionally* Stage 2's call-site witness, with upstream's
lemma closing its magnitude; the boost's downward mixing is one `/`. The refusals are
subtree boundaries: `E·B` (Poynting needs `μ₀` — `Vacuum/`), `F·F` (the Lagrangian
density — `Dynamics/`), and chart + extent (same tesla, no join: antisymmetrization is
a crossing, never an addition).

**Status: Stage 4 climbed** — `Audits.lean` puts the whole directory namespace under
CI: the 24-site boundary audit and crossings registry pinned (12 crossings, 10
ingests, 1 emission, 1 carrier-vocabulary tier — every attestation's reason column in
the pin), boundary-clean + mint-ratchet + dimensional-clean silent, and the unkinded
ledger *inverting the pilot's ratio*: **twelve** crossings are kinded end to end (the
interior, gated empty — once the potential is read in, the chain's whole derivation
tree runs inside the kind layer) against eleven measured boundary readings where
PhysLib's carriers enter. The `Kinematics.checked_by.yaml` delta keys on the upstream
TODO texts — the constructor-properties TODO now points at the two gauge-invariance
lemmas upstream does not state, and the `FieldStrength` refactor TODOs are noted as a
dependency of the mirror, not claims about it.

**Status: directory 2 complete — ladder, patch candidate, README.** The README carries
nine findings and the measured cost line (12 kinds — 10 lookups; 12 laws, 5 tabled, 7
law-only; 0 joins; 24 boundary sites, 0 raw mints; a 12-crossing gated interior against
28 measured boundary positions; 1,560 lines / 620 code against an unchanged
3,214-line source; 0 sorry). The directory's patch candidate is the gauge-invariance
pair (`electricField_gaugeTransform`, `magneticFieldMatrix_gaugeTransform`) — theorems
the chain's own TODO asks for and upstream does not state — whose offer upstream is a
human's to make (AI-POLICY §3.1). Next: directory 3, the `ClassicalMechanics`
`HarmonicOscillator` + `RigidBody` subtrees.

### Directory 3: `ClassicalMechanics` — the `HarmonicOscillator` and `RigidBody` subtrees

The scope campaign rule 2 names: two subtrees, taken whole. `HarmonicOscillator/` is
`Basic.lean` (the energies, the Lagrangian and Hamiltonian formulations, and
`equationOfMotion_tfae`), `Solution.lean` (trajectories, four initial-condition
parametrizations, amplitude–phase normal form, periodicity), and the three `Geometric/`
files (the configuration manifold, the mass Riemannian metric, geometric trajectories) —
2,582 lines. `RigidBody/` is `Basic.lean` (the mass-distribution functional, centre of
mass, inertia tensor, parallel-axis theorem), `Motion.lean`, `AngularVelocity.lean`,
`AngularMomentum.lean`, `KineticEnergy.lean` (König in three forms), and
`SolidSphere.lean` — 1,232 lines. What this directory uniquely proves:
**same-dimension discrimination at theorem scale** — four energies at one dimension,
with `equationOfMotion_tfae` as the verbatim-survival stress test.

The structural fact this plan hangs on, the inverse of directory 2's: where the EM chain
was one frame-covariant object whose entries range over many dimensions, classical
mechanics is **many kinds crowded onto few dimensions**. Within these two subtrees alone:
at the joule, kinetic energy (4-28.2), potential energy (4-28.1), mechanical energy
(4-28.3), and the Lagrangian — with the catalogue's own moment of force (4-12.1) sitting
at the same `MDim.energy` one aisle over; at `T⁻¹`, the oscillator's angular *frequency*
(3-18) and the rigid body's angular *velocity* (3-12) — two different catalogue items
that both subtrees write with the same letter `ω`. Everything upstream types at
`ℝ` or `EuclideanSpace ℝ (Fin 1)`, so every one of these coincidences is invisible
there; the exhibits (A and C) probed the resulting collisions, and this directory pays
them down as a ladder. The feasibility questions:

- **F1 — the bare-real input data, and the reciprocal that must die before the root.**
  `HarmonicOscillator { m k : ℝ }`: the mass is a lookup, but the spring constant has no
  ISO 80000 item — a *mint* at `M·T⁻²` — and `ω = √(k/m)` is the directory's kind-level
  event (the pilot's ξ pattern: mint the radicand, attest the root, erase by upstream's
  own `ω_sq`). Exhibit C's finding — `√(m/k)` as well-typed as the correct recipe — must
  close here as a ladder refusal: `m / k` is no edge of the algebra.
- **F2 — four energies, one dimension, and the sum that outruns the difference.**
  `E = T + V` is the pilot's curated `KindJoin`, now at PhysLib's own `energy`;
  `hamiltonian_eq_energy` erases the kinded Hamiltonian to the same join. But the
  Lagrangian `L = T − V` is *not* the join sum, and the join table has no subtraction —
  deliberately: the standard's vocabulary has a home for the sum of the comparable pair
  (mechanical energy) and none for its difference, which is why the Lagrangian is a mint.
  Same dimension, four kinds, two of them local — the directory's title finding.
- **F3 — the collisions of M6, paid down as refusals beside the re-authoring.**
  `toCanonicalMomentum : E ≃ₗ[ℝ] E` carries a velocity to a momentum between *identical
  types*; its kinded twin is kind-changing (`m·v`, the 4-8 edge), so the momentum of a
  momentum refuses. `S.force` fed the canonical momentum refuses. The
  `hamiltonian`/`lagrangian` argument-order collision — the one behind `hamiltonian_eq`'s
  transposed `funext t x p`, which compiles upstream *because* `p` and `x` share a type —
  becomes a `#check_failure` at the kinded signature.
- **F4 — the tfae is the stress test.** `equationOfMotion_tfae` gathers five
  formulations — Euler–Lagrange, Newton, Hamilton, two variational principles — and the
  campaign invariant is that the kinded layer consumes it *verbatim*: each formulation
  re-authored with its mixed-kind sides elaborating through the table (`m·a = F` through
  the 4-9.1 edge; `p = m·v` through 4-8; `H` through F2's join), each pairwise equivalence
  closed by `.out` of the upstream lemma, nothing re-proved.
- **F5 — two ω's, the trig boundary, and the complex number that packs two lengths.**
  `ω·t` lands at the phase angle (3-7) — the edge that licenses `cos`/`sin` at the
  boundary; `T = 2π/ω` at the period duration (3-14). The amplitude–phase inverse embeds
  `(x₀, v₀/ω)` as one complex number — licensed exactly because `v₀/ω` is a *length*
  (the velocity/angular-frequency edge), so `‖z‖` is the amplitude and `arg z` the
  phase. And the directory registry pins angular frequency ≠ angular velocity by
  `decide` — the two subtrees' shared letter, separated.
- **F6 — the functional ingest, the second join, and frame honesty.** `RigidBody.ρ` is a
  linear functional on test functions: each moment read off it is an ingest whose kind is
  the product of mass with the test function's kind (mass at `1`, length at `x i` over
  the mass for the centre of mass, moment of inertia at the quadratic). `L = I·ω` and
  `T_rot = ½ ω·(I·ω)` are table edges at 4-7/4-11/3-12. König's split is the directory's
  *second* join: translational and rotational kinetic energy as species of 4-28.2,
  summing at their parent — against directory 2's zero joins, this directory is where
  curation earns its keep. Frame honesty per Exhibit A: `angularVelocity` and
  `bodyAngularVelocity` are both readings at 3-12 — the kind layer separates kinds, not
  frames, and the exhibit's `toFrameScalar` machinery is where the frame discrimination
  lives.

And the directory has a patch-candidate slot before any file is written:
`solidSphere_inertiaTensor` — `(2/5) m R² • 1` — is `@[sorryful]` upstream, the only
`sorry` in either subtree. The pilot's `Orthonormality.lean` pattern applies: attempt the
discharge as a standalone file after the ladder; if the ball integrals resist, record the
attempt honestly and hold.

The layout: one directory, one vocabulary — the four-energies point *is* directory-level,
so Stage 0/1 are shared and only Stage 2 splits by subtree, mirroring the source inside
the stage the way the Space ladder's stage-major tree does:

```
ForPhysLib/ClassicalMechanics/
  Feasibility.lean     F1–F6 as build artifacts, both subtrees probed
  Kinds.lean  Metrology.lean          Stages 0–1: the one vocabulary, the collisions pinned
  Kinded/HarmonicOscillator.lean      Stage 2 for the oscillator chain
  Kinded/RigidBody.lean               Stage 2 for the rigid-body chain
  Operators.lean  Audits.lean         Stages 3–4 over the whole directory namespace
  ClassicalMechanics.checked_by.yaml  README.md
```

Held, deliberately: `DampedHarmonicOscillator/` and `Pendulum/` stay with Exhibit C
(probed, not re-authored — rule 2); `EulerLagrange.lean` and `HamiltonsEquations.lean`
are machinery the subtrees import, not members of them; `FreeParticle/`, `Vibrations/`,
`Scattering/`, `WaveEquation/`, `OrbitalMechanics/` are out of the named scope.

**Status: feasibility built** — `ForPhysLib/ClassicalMechanics/Feasibility.lean`
answers all six questions as build artifacts. F1: the `k/m` radicand through a
registered edge, the root attested and erased to `S.ω` by `rfl` and to the radicand by
upstream's `ω_sq`; `m/k` refused; both `√` recipes pinned well-typed upstream. F2: the
`T + V` join at mechanical energy erasing to `S.energy` by `rfl`, the on-trajectory
Hamiltonian erased onto the same join by `hamiltonian_eq_energy`, the Lagrangian mint's
crossing erased by upstream's own equality, and `L + E` refused at the same joule. F3:
all three M6 collisions pinned compiling upstream and refused kinded (momentum of a
momentum, force fed a momentum, the swapped Hamiltonian), plus the substrate's
position-plus-momentum. F4: `equationOfMotion_tfae` consumed verbatim — the kinded
Newton reading (`m·a` through the table at component 0) equivalent to
`EquationOfMotion` by `.out 0 1`, only component bookkeeping proved here. F5: `ω·t`
to the phase angle and `v₀/ω` to displacement as one-`*`/one-`/` probes; the period
crossing and the amplitude's complex packing both erasing by `rfl` to upstream's
`period` and `fromInitialConditions`; the two ω's separated by `decide`. F6: the
mass-distribution functional's moments ingested (mass, inertia entries), `L = I·ω`
contracted through the table and closed by `angularMomentum_eq_inertiaTensor_mulVec`,
and König consumed as the *second* join — translational + rotational at kinetic
energy, closed by the body-frame König theorem — with the lab + body `ω` sum pinned as
scope honesty (kinds separate kinds, not frames).

**Status: Stages 0–1 climbed** — `Kinds.lean` and `Metrology.lean`. Stage 0: 22 kinds,
17 verbatim catalogue literals (ISO 80000-4 and -3, down to the phase angle and the
period — each lookup the catalogue's own entry, examination principles included) and 5
mints in two findings (the input datum `k` + its radicand; the Lagrangian + König's
two species); six kinds at the joule with the collisions separated by `decide`
(including the shared-letter `ω` pair and duration/period); the four-edge two-level
lattice with both joins' comparability facts and the transitive
`rotational ⊑ mechanical`; `lagrangian_no_edge` making "the difference without a
home" a theorem about the lattice. Stage 1: 22 `DimensionedKind` pairings — six rows
at `MDim.energy`, two at `T⁻¹`, two at `T`, ten of twenty-two colliding — the
17-lookup identification definitional (`rfl`) and every dimension `rfl` (the mints' dimensions
checked against the catalogue's arithmetic: Hooke fixes the spring constant, the
radicand shares 3-13's dimension as a different kind); thirteen authored edge laws,
each a formula the subtrees write, with `#kind_dimensional_coverage` pinned clean
over all thirteen.

**Status: Stage 2 climbed, both subtrees** — `Kinded/HarmonicOscillator.lean` and
`Kinded/RigidBody.lean`, one namespace, with the 21-example `rfl` bridge stated once.
The oscillator half: the kinetic energy authored through the Legendre edge
(`½⟪p,v⟫` — two table products, one numeral) erasing to `½m⟪ẋ,ẋ⟫` by the inner
product's one-component expansion; **the pentad passed at the strongest grade** — all
five formulations of the equation of motion re-stated with kinded readings (Newton
through the table, Hamilton's momentum trajectory through the kinded canonical
momentum, both variational integrands *being* the Lagrangian mint and the kinded
Hamiltonian by `rfl`) and the `List.TFAE` closed by `S.equationOfMotion_tfae xₜ hx`
**as the literal proof term**, because every kinded spelling erases definitionally;
the trajectory authored from its data (phase and `v₀/ω` edges, numeral trig, same-kind
sum) with the normal form and the periodicity consumed at the same reading;
conservation as a kind statement (`∂ₜE` read at the *watt*, vanishing on shell); and
the geometric subtree at one reading (the mass metric is `2T`, upstream's coordinate
formula the erasure). The rigid-body half: the functional's moments ingested and the
**parallel-axis theorem consumed** as a same-kind sum at 4-7; the two ω-tensors both
at 3-12 with skew-symmetry a same-kind negation and the conjugation riding the
numeral action (direction cosines are dimensionless); the Landau–Lifshitz
`v = V + ω × r` with the cross product *fully table-expressed* (two edge products and
a same-kind subtraction per component — Stage 1 grew the `ω·r` edge for it, the
pilot's stage-growth pattern, coverage re-pinned at fourteen); the rotational energy
contracted through the table (three `I·ω`, three `ω·L`, one numeral) erasing by
upstream's own `T = ½ω·L`; and the motion-preservation theorems consumed at the
ingests (mass, centre-of-mass tracking, the solid sphere's zero first moment).

**Status: Stage 3 climbed** — `Operators.lean` registers the seven remaining edges
with scalar call sites (`⟪p,v⟫`, `p/m`, Hooke's `k·x`, the amplitude–phase `ω·A`, the
period's `phase/ω`, the decomposition's `ω·r`, the contraction's `ω·L`; six predate it
in Feasibility), each demonstrated at a source equation — Hooke one `*` closed by
`force_eq_linear`, the period one `/` that is *definitionally* upstream's `period`
(with `2π` a declared `@[kindConst]` full turn at 3-7, not a naked numeral), the
amplitude–phase velocity, the end-to-end table spelling of the kinetic witness, the
one-`*` rotational contraction, the one-`/` inverse momentum. Exactly **one** of the
fourteen laws stays law-only — conservation's `∂ₜE`, riding `fderiv` — inverting
directory 2's majority: classical point mechanics is scalar-multiplicative almost
everywhere. No interval scale exists in this directory, so the whole discrimination
burden falls on kind identity — and the refusals show it: the *oscillator's* `ω`
times `L` is refused (the shared-letter pair, discriminated at the table), `E·t` is
refused (the action is the pilot's kind), `F·v` is refused (power delivery is an
upstream `informal_lemma`, not formalized surface). Coverage re-pinned: seven
`[table]` rows, clean.

**Status: Stage 4 climbed** — `Audits.lean` puts the whole directory namespace under
CI: the **42-site** boundary audit and crossings registry pinned (29 ingests, 8
crossings, 1 constant, 3 emissions, 1 carrier-vocabulary — every attestation's reason
in the pin; all four tiers present, and the `@[kindConst]` full turn plus the two
trig emissions are firsts for the campaign), boundary-clean + mint-ratchet +
dimensional-clean silent, the nine-member kinded interior gated empty, and the
30-reading ingest boundary measured (72 naked positions, 68 flows). The gate earned
its keep during authoring: it refused `trajectoryFromDataQ`'s inline `.magnitude`
reads, which forced the trig boundary to become *literal* — `cosPhase`/`sinPhase` as
tagged `@[kindEmission]` declarations, the one sanctioned place a phase leaves the
layer to enter `Real.cos`. The ledger's shape is the directory's own: point mechanics
has a *thin interior and a broad boundary* (every reading of upstream's bare-real
structures is a boundary site; the algebra between readings is short) — directed
opposite to directory 2's deep interior. The `ClassicalMechanics.checked_by.yaml`
delta keys on the upstream TODO texts (the geometric-model TODO at the consumed
coordinate erasure; the configuration-space-API TODO at the consumer datapoint; the
continuous-linear-maps TODO as a mirror dependency) and names the `@[sorryful]`
`solidSphere_inertiaTensor` as the patch-candidate slot. Axiom profile of fifteen key
theorems, pentad included: `propext, Classical.choice, Quot.sound`.

**Status: the patch candidate is discharged** —
`ForPhysLib/ClassicalMechanics/SolidSphereInertia.lean` proves upstream's
`@[sorryful]` `solidSphere_inertiaTensor` (`(2/5) m R² • 1`), sorry-free at
`propext, Classical.choice, Quot.sound` — the two subtrees' only `sorry`, in the
pilot's orthonormality pattern. The proof is the textbook computation carried by
three facts, each mechanized once: the off-diagonal moments vanish under the
coordinate-reflection isometry (conjugated through `Space.basis.repr`,
measure-preserving by Mathlib's `LinearIsometryEquiv.measurePreserving`,
ball-preserving by `norm_map`); the diagonal moments agree under the
coordinate-swap isometry, so each is a third of `∫‖x‖²`; and the radial integral
reduces by `integral_fun_norm_addHaar` to `3·vol(B₁)·∫₀^R r⁴`, with the ball volume
scaling as `R³·vol(B₁)` (`Measure.addHaar_closedBall`) — PhysLib's own
`volume_metricBall_three_real` supplies `vol(B₁) = 4π/3`, though only its
positivity survives to the final ratio. The offer upstream is a human's to make
(AI-POLICY §3.1).

**Status: directory 3 complete — ladder, patch, README — and with it the
three-directory campaign.** The README carries twelve findings and the measured cost
line (22 kinds — 17 lookups, 5 mints; 22 pairings with ten colliding rows; 14 laws,
13 tabled, 1 law-only; 2 joins on a composing lattice; 42 boundary sites, 0 raw
mints; a 9-member gated interior against a 30-reading measured boundary; 2,509 lines
/ 1,104 code against an unchanged 3,814-line source; 0 sorry here and 1 upstream
sorry discharged). The directory's patch candidate is `SolidSphereInertia.lean`; the
stress-test verdict is the pentad closed by the upstream proof term. All three
campaign directories now stand — the operator-valued frontier (QM/HO), the
frame-covariant chain (EM/Kinematics), and same-dimension discrimination at theorem
scale (CM) — each with a full ladder, a measured cost line, and a patch candidate;
the ask stays Stage 1, per campaign rule 3.


---

## Layout

What exists today is marked ✓; the rest is what this plan builds.

```
ForPhysLib.lean                    ✓ the library root
ForPhysLib/
  README.md                        ✓ the overview
  REQUIREMENTS.md                  ✓ 31+1 requirements, 9 tiers
  MOTIVATION.md                    ✓ 10 reasons + a coda
  PLAN.md                          ✓ this file
  CaseStudies.lean                 ✓
  CaseStudies/                     ✓ a system typed several ways and scored
    HarmonicOscillator.lean        ✓   the aggregator
    HarmonicOscillator/            ✓   README.md beside the five sources it scores
      Attempt1Reals.lean           ✓   Attempt2Dimension.lean ✓
      Attempt3Tagged.lean          ✓   Attempt4Pkc.lean ✓   Scorecard.lean ✓
  Kinds.lean  Kinds/                 ✓ Stage 0: KindOfProperty lookups = the catalogue's own entries, Mathlib-free
    Space.lean                       ✓   the first directory: SpaceAndTime/Space
  Examination.lean  Examination/     ✓ the physics that individuates them, mirroring Kinds/ file-for-file
    Space.lean                       ✓   principles declared, examinedBy proved, distinctness derived
  Metrology.lean  Metrology/         ✓ Stage 1: DimensionedKind pairings + pinned coverage
    Space.lean                       ✓   the Stage-0 identification with Iso80000.Part3, definitional
  Kinded.lean  Kinded/               ✓ Stage 2: the kinded author-forms, naked = `.magnitude` by rfl
    Space.lean                       ✓   four length-readings; PhysLib/Mathlib theorems close kinded goals verbatim
  Operators.lean  Operators/         ✓ Stage 3: KindMul/KindDiv registrations — `*`/`/` through the table
    Space.lean                       ✓   two entries, two refusals; coverage re-pinned over the table
  Audits.lean  Audits/               ✓ Stage 4: pinned boundary audit, silent gates, measured ledger
    Space.lean                       ✓   five sites tagged; interior gated empty, ingest boundary measured
    Space.checked_by.yaml            ✓   the API-map delta: checked_by for four existing requirements
  Exhibits.lean  Exhibits/           ✓ one directory per exhibit above
    RigidBody.lean  RigidBody/       ✓   A: three findings probed and closed; the contraction bridged back
    ReferenceFrame.lean  ReferenceFrame/ ✓   B: three laws one type, closed by KVector; req 17 discharged kinded
      Findings.lean  ReferenceFrame.checked_by.yaml ✓
    HarmonicOscillator.lean  HarmonicOscillator/ ✓  C: four findings closed; MR11 measured; ℝ/Float32 by one rfl
    TwoRovers.lean  TwoRovers/       ✓   D: totals proved, contamination and undercount refused, licence two-sided
    Electromagnetism.lean  Electromagnetism/ ✓ E: five problems closed; the annex built on the minted machinery
  QuantumMechanics.lean  QuantumMechanics/ ✓ the campaign, directory-major (see “The three-directory campaign”)
    HarmonicOscillator.lean  HarmonicOscillator/ ✓ the pilot directory, mirroring the PhysLib path
      Feasibility.lean               ✓   F1–F4 as build artifacts
      Kinds.lean  Metrology.lean      ✓   Stages 0–1: the lookup written, then proved; coverage pinned
      Kinded.lean                     ✓   Stage 2: licensed-fold eigenvalue, Born density, spacings, kinded TISE
      Measurand.lean                  ✓   M-T4: PKC's measurand + observable vocabulary, instantiated on Ĥ
      Operators.lean                  ✓   Stage 3: the table; PhysLib's ξ_sq closes the table-built erasure
      Audits.lean                     ✓   Stage 4: 20-site audit pinned; silent gates; interior gated, boundary measured
      HarmonicOscillator.checked_by.yaml ✓ the API-map delta, keyed on the upstream TODO texts
      README.md                       ✓   the findings and the measured cost line
      Orthonormality.lean             ✓   the upstream sorryful `eigenstates_orthonormal`, discharged
      Heisenberg.lean                 ✓   the second patch: ℏ/2 ≤ σ_x·σ_p proved; ground-state σ_x = ξᵢ/√2; kinded bound
  Electromagnetism.lean  Electromagnetism/ ✓ the campaign's second directory (see “Directory 2”)
    Kinematics.lean  Kinematics/     ✓ the chain: potentials → fields → boosts → gauge
      Feasibility.lean               ✓   F1–F5 as build artifacts
      Kinds.lean  Metrology.lean     ✓   Stages 0–1: lookups + two mints; twelve edges, coverage pinned
      Kinded.lean                    ✓   Stage 2: the chain re-authored; E rebuilt by rfl; gauge reaches the fields
      Operators.lean                 ✓   Stage 3: three entries + the torsor demo; law-only majority named; refusals = subtree boundaries
      Audits.lean                    ✓   Stage 4: 24-site audit pinned; silent gates; 12-crossing interior gated empty
      Kinematics.checked_by.yaml     ✓   the API-map delta, keyed on the upstream TODO texts
      README.md                      ✓   the findings and the measured cost line
  ClassicalMechanics.lean  ClassicalMechanics/ ✓ the campaign's third directory (see “Directory 3”)
    Feasibility.lean                 ✓   F1–F6 as build artifacts, both subtrees probed
    Kinds.lean  Metrology.lean       ✓   Stages 0–1: one vocabulary; six joules, two ω's; fourteen edges, coverage pinned
    Kinded/HarmonicOscillator.lean   ✓   Stage 2: the pentad closed by the upstream proof term; trajectory, conservation, geometry
    Kinded/RigidBody.lean            ✓   Stage 2: the functional's moments; parallel axis consumed; ω×r table-expressed
    Operators.lean                   ✓   Stage 3: seven entries; the shared-letter ω refused at the table; one law stays law-only
    Audits.lean                      ✓   Stage 4: 42-site audit pinned; silent gates; interior gated, boundary measured
    ClassicalMechanics.checked_by.yaml ✓ the API-map delta, keyed on the upstream TODO texts + the sorryful lemma
    README.md                        ✓   the findings and the measured cost line
    SolidSphereInertia.lean          ✓   the upstream sorryful `solidSphere_inertiaTensor`, discharged
  Scorecard.lean                     ✓ verdicts re-derived so the tables cannot drift from the files
```

`lake build ForPhysLib` builds all of it. The library takes the package directory as its
`srcDir`, so the tree above *is* the module path — `ForPhysLib.CaseStudies.HarmonicOscillator.Attempt4Pkc`
is at `ForPhysLib/CaseStudies/HarmonicOscillator/Attempt4Pkc.lean`, and a reader browsing the
proposal is never navigating a mirror of PKC's own namespace to reach it.

That constraint is also why the directory names are what they are: a module's name is its
directory path, so every component must be a legal Lean identifier — no hyphens, no lowercase
package-style names. `CaseStudies` is plural because the oscillator is not meant to be the
only one.

The `Kinds/` ↔ `Examination/` mirroring follows the soil-moisture model's organising rule:
*a kind lives in the file named by its own examination principle*.

---

## What this benchmark did to PKC's own requirements

Scoring PKC by the same rules cut both ways: the MR list turned out to *validate* PKC's
requirement catalogue — adversarially, since every restated requirement had to survive three
rival designs and a shipping library — and the validation found the catalogue short. Five
requirements were minted from it (R21–R25: erasure and operator-table purity from MR11,
rendering from MR12, system-scale dedication from MR20, provenance from MR24, audit scope
from MR30/MR31), and the full trace in both directions now lives in the blueprint's
*Requirement validation — the ForPhysLib benchmark* section, beside the traceability matrix
it feeds.

**Deliberately not minted.** Two MRs stay out of PKC's catalogue on purpose:

- [MR23](REQUIREMENTS.md#mr23-interface-quantities-carry-both-systems-they-join) — interface
  quantities naming both systems they join. PKC has no interface machinery to annotate; a
  catalogue row with no possible annotation is exactly the drift the traceability matrix
  exists to prevent. Exhibit D's motor-to-wheel torque is where the machinery would first be
  needed, so that exhibit is also the gate: MR23 enters the catalogue when its first
  declaration does.
- [MR25](REQUIREMENTS.md#mr25-dimension-generic) — genericity over the geometric dimension
  `d`. Same rule. The current `Frame`/`InFrame` layer is written at fixed `n`; the
  kind-generic König split in Exhibit A is the construction that would force the
  generalization, and it gates the requirement.

**Requirements the benchmark never reached.** R13 (scale-spanning units), R14 (the
uncertainty ladder), R15 (numerical adequacy) and R18 (coverage intervals) have no MR
counterpart — a reflection of the survey's scope, not of their standing: twelve API maps
in two mechanics directories, and one oscillator, simply never present the phenomena.

R2 (the specialization lattice) *was* the fifth: the oscillator's `H = T + V` is a
specialization family the MR list never interrogated. It has since graduated —
[MR32](REQUIREMENTS.md#mr32-specialization-keeps-kinds-comparable), appended after the
first scoring pass, now asks, with probes in all four attempts and the scorecard. What
they exposed was a **PKC work item**, not a PhysLib one: `Specializes` was consumed by no
quantity-level operation, so the licensed sum at the join — `T + V` landing at the kind
both terms provably specialize — was missing machinery, the specialization twin of
`Extensive`'s licensed aggregation. That machinery has since landed
(`PropertyKindCalculus.SpecializationLift`: `Quantity.widen`, the curated `KindJoin`
table, the sum and the comparison at the join), and the MR32 probes flipped ⚠️ → ✅ — the
second time this benchmark changed the core library rather than the scorecard. MR11 is
now the one requirement PKC itself does not sweep, and `kind_algebra`
(`PropertyKindCalculus.KindAlgebra`, likewise minted here) has pushed its residue to the
kind equations themselves.

Rather than an exhaustive search of all 572 files for evidence, the
honest instrument is the same one used everywhere else in this plan: a case study each,
hypothetical until built, chosen so the requirement is load-bearing rather than decorative.

- **R2, at PhysLib scale — the first law of thermodynamics as a bookkeeping problem.**
  MR32 validated R2 on one oscillator; this is the study that would validate it on a
  library directory. Heat, work, internal
  energy, enthalpy: all energy, all one dimension, and the entire content of
  `ΔU = Q − W` is *which* energy crossed *which* boundary *how*. PhysLib's
  `Thermodynamics/` carries these distinctions in names today. A case study writing the
  first law over energy's specialization lattice — heat and work comparable to energy,
  never to each other — would exercise comparability-without-identity exactly where a
  physicist already respects it by hand.
- **R13 — sound pressure level.** The decibel is the canonical scale-spanning unit
  (ISO 80000-8): `20·log₁₀(p/p₀)` is neither base nor derived, and adding two SPLs is the
  classic domain error. PhysLib has no acoustics directory yet — which makes this the
  *green-field* case study: the first module written kinded from the start, rather than
  re-authored. The groundwork has since landed (`PropertyKindCalculus.Level`): a level is
  a *construction* over a ratio root kind — reference and power/root-power role as kind
  identity, levels ordinal-as-a-kind so `L₁ + L₂` is structurally unavailable, differences
  landing in a reference-free gain kind, and the role-independent energetic combination —
  not a fifth scale type. The same machinery is what a kinded treatment of PhysLib's
  *electromagnetism* needs first: dBm vs dBW (same root, same role, different reference —
  different kinds) and field level vs power level (same dB figure, disambiguated by kind)
  are already probes in the core test suite.
- **R14 — measuring g with PhysLib's own pendulum.** `SimplePendulum` gives
  `g = 4π²ℓ/T²`; a case study that takes measured `ℓ` and `T` *with uncertainties* and
  propagates to `u(g)` — GUM linearization checked against Monte Carlo, the ladder's
  nesting as the correctness statement — turns a formalized equation into a metrology
  result. This is the shortest path from "PhysLib proves theorems" to "PhysLib processes
  measurements", and R15 rides on it: whether `Float32` is adequate *at the scale of
  those input uncertainties* is precisely the question the pairing makes askable.
- **R18 — accepting a rover's IMU.** Exhibit D's provenance tags
  ([MR24](REQUIREMENTS.md#mr24-a-dedication-carries-provenance)) mark parameters
  *measured*; acceptance is the next step — is the measured gyro bias within tolerance,
  with what coverage? A conformity decision over the two-rover assembly connects the
  systems tier to the uncertainty tier, and is the case study closest to how an applied
  organisation would actually consume the stack.

None of these is scheduled before the four exhibits; they are listed so the unvalidated
requirements are named, with the instrument that would validate each, instead of quietly
inheriting the benchmark's confirmation.

---

## Rules of engagement

These exist so the comparison is a comparison and not a strawman parade.

1. **Each attempt gets the best available version of its own idea**, including defences its
   advocates would actually raise.
2. **A failure is a build artifact.** Either a `#check_failure` probe, a theorem exhibiting
   the wrong answer, or an `example` demonstrating that something which should be rejected
   type-checks. No requirement is scored on prose — **including every claim in
   [MOTIVATION.md](MOTIVATION.md), which is currently prose and must become probes.**
3. **Over-rejection counts as failure.** A scheme that rejects `m_chassis + m_wheels` has not
   satisfied [MR21](REQUIREMENTS.md#mr21-assembly-is-licensed-per-kind-and-two-sided).
4. **No attempt is asked to do the others' job.** `WithDim` is not criticised for failing
   object identity — it fails it because `Dimension` is a free abelian group, which is exactly
   what makes it good at Tier 1.
5. **PKC is scored by the same rules.** It loses [MR11](REQUIREMENTS.md#mr11-authoring-ergonomics)
   outright as a ⚠️, it *failed* two Tier 6 requirements when they were written, and it was
   ⚠️ on MR32 at first scoring — each time the core library changed rather than the
   scorecard (`SpecializationLift` and `kind_algebra` are the MR32 and MR11 repairs). A
   benchmark its own author cannot lose is not a benchmark.
6. **PhysLib is not scored against requirements it never adopted.** Tiers 7 and 8 are
   requirements for *applying* PhysLib, not defects in it. Exhibits A–C report defects against
   PhysLib's own stated intent — its docstrings, its API maps, its module docs — and nothing
   else. Exhibit D reports no defects at all; Exhibit E reports both — the abbreviation and
   the silent `c := 1` are defects against stated intent, the RF/AC annex is capability on
   physics PhysLib does not yet have, and the two are kept as separate artifacts.
