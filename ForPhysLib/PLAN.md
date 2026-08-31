# Plan

How to get from [the requirements](REQUIREMENTS.md) to something a PhysLib maintainer can
merge, in an order where the cheap and uncontroversial parts come first and each stage is
useful on its own.

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

One `kinds/` file per directory: bare `KindOfProperty` declarations, Mathlib-free, imported
by nothing. A kind carries an id, a `ScaleType`, and an examination principle.

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
kinds, ids/scales/principles verbatim from `Iso80000.Part3`, the position/displacement
pair distinct by `decide`) with `ForPhysLib.Examination.Space` mirroring it file for file
(principles declared, `examinedBy` proved by `rfl`, the distinctness derived from the
principles alone). Landed with Sequencing item 3.

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

### Stage 4. Audits and the API map

`#kind_boundary_audit`, `#kind_unkinded` with the Mathlib-interface tier
([MR30](REQUIREMENTS.md#mr30-the-unkinded-surface-is-measured)), `#kind_mint_ratchet` scoped
to the module root, and the `checked_by:` field in the directory's `API-map.yaml`
([MR29](REQUIREMENTS.md#mr29-every-satisfied-requirement-has-a-machine-checkable-witness)).

**Cost: CI.**

---

## Exhibits to build

Five, ordered by what they demonstrate. Each must produce build artifacts per rule 2 of the
[rules of engagement](#rules-of-engagement) — a `#check_failure`, a theorem exhibiting the
wrong answer, or an `example` showing that something which should be rejected type-checks.

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

### Ranking

| | exhibit | why it earns its place |
|---|---|---|
| 1 | **A · RigidBody** | highest defect density; the one place a real correctness constraint is enforced by authoring convention |
| 2 | **B · ReferenceFrame** | a stated requirement that is not satisfiable without the layer — design input, not retrofit |
| 3 | **C · HarmonicOscillator** | continuity with the case study; where MR11 must be paid down or conceded |
| 4 | **D · Two rovers** | the reach argument; the only exhibit about capability rather than defects |
| 5 | **E · Electromagnetism** | the confirmation: machinery minted by the benchmark, applied to a directory it was not minted from |

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
4. **Exhibit C**, which is where the ergonomic question is settled either way.
5. **Exhibit D**, because it depends on the others and argues a different point.
6. **Exhibit E**, last — the confirmation pass: it presupposes the minted machinery
   (`kind_algebra`, `SpecializationLift`, `Level`) and its whole value is showing that
   machinery solving problems it was not built against.

Nothing goes upstream before Stage 1 exists for at least one directory, because Stage 1 is
the part that costs a maintainer nothing and therefore the part that should arrive first.

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
  Kinds.lean  Kinds/                 ✓ Stage 0: bare KindOfProperty, Mathlib-free
    Space.lean                       ✓   the first directory: SpaceAndTime/Space
  Examination.lean  Examination/     ✓ the physics that individuates them, mirroring Kinds/ file-for-file
    Space.lean                       ✓   principles declared, examinedBy proved, distinctness derived
  Metrology.lean  Metrology/         ✓ Stage 1: DimensionedKind pairings + pinned coverage
    Space.lean                       ✓   the Stage-0 lookup proved against Iso80000.Part3 by decide
  Kinded.lean  Kinded/               ✓ Stage 2: the kinded author-forms, naked = `.magnitude` by rfl
    Space.lean                       ✓   four length-readings; PhysLib/Mathlib theorems close kinded goals verbatim
  Exhibits/                          one directory per exhibit above
    RigidBody/  ReferenceFrame/  HarmonicOscillator/  TwoRovers/  Electromagnetism/
  Scorecard.lean                     verdicts re-derived so the tables cannot drift from the files
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
