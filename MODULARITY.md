# MODULARITY.md — Metrological modularity: metrology modules as a library-level capability

> Status: **M0, M1, M1b, M2, M3 (PKC + SMM), M4 landed** (PKC v0.104.0–v0.108.0 + SMM
> validation, 2026-09-05); M2b, M5, M6 open (M3's SMW derivation rides M6's SMW pass).
> Assessment baseline 2026-09-05.
> Audience: PKC maintainers.
> Scope: make "metrology module" a first-class, machine-checked construct in PKC —
> an interface of kinds, input/output quantities and parameters, whose *behavior* is a
> measurement model: the equations constraining the output quantities with respect to the
> input quantities — and validate the capability by applying it across
> `soil-moisture-model` (SMM, the model tier) and `soil-moisture-workflows` (SMW, the
> deployment tier). Generic API lands in PKC first; the downstream repos validate, they do
> not host the capability.

---

## 1. The paradigm and its name

**Metrological modularity**: organize science software as *metrology modules*. A metrology
module is a unit whose

1. **interface** is a declared boundary of kind-typed ports — input quantities, output
   quantities, parameters, configuration, conditional outputs, nominal properties (a
   functionally relevant label ports at a nominal-scale kind), and module-valued ports (a
   functional argument ports at its kind signature — modules may be parameters of modules;
   see §4.2);
2. **behavior** is a *measurement model* in the VIM sense — VIM4 2CD (2023-07-31) §2.12
   [VIM3: 2.48]: "mathematical relation among all quantities known to be involved in a
   measurement", general form `h(Y, X₁, …, Xₙ) = 0` — attached to the boundary as a
   checked theorem edge, not as prose;
3. **implementation** is a *measurement function* (VIM4 2CD §2.13 [VIM3: 2.49] — "f may
   symbolize an algorithm"): a carrier-parametric kinded `def` whose relation to the
   measurement model is `equals`, `inverts`, `refines`, or `boundedBy` a declared tolerance;
4. **licenses** are stated per carrier rung — because laws transfer across the carrier
   ladder and side conditions do not (the R10 rule; see §4.1);
5. **mereology** is declared — each output port carries its aggregation class
   (extensive / quasi-extensive / conditionally extensive / intensive / whole-proper /
   count-keyed-by-sortal), and the license to distribute the module's computation over a
   carving (tiles, blocks, shards) is *derived* from that declaration, not assumed.

The name deliberately pairs the discipline (metrology — the interface vocabulary is
Dybkær/VIM kinds and quantities, the spec vocabulary is the VIM measurement model) with the
software principle (modularity — boundaries, contracts, composition). The unit is a
"metrology module"; its spec clause is "the measurement model"; its implementation clause is
"the measurement function".

Why the *relational* form matters: VIM's general form is implicit, `h(Y, X) = 0`, and Note 1
of §2.12 says the measurand's value is *inferred* from it. A retrieval module's honest spec
is therefore "output satisfies the forward model's equation" (or inverts it, or lands within
δ of doing so) — not "output is what this loop computes". The paradigm asks that the loop be
demoted to evidence *for* the relation, with the relation as the published behavior.

## 2. What already exists (assessment baseline, 2026-09-05)

Established by a three-repo survey (read-based; any item that becomes load-bearing for a
design decision below gets a compile probe before we rely on it). The paradigm is not
speculative — the interface half is built and kernel-checked at all three tiers:

**PKC — the interface objects and their judgments.**
- `Provenance.Contract` (`PropertyKindCalculus/Provenance.lean`): members + ports, each port
  `⟨node, kind, role⟩`, roles `input | config | param | output | conditional`. Decidable
  `Contract.agrees` (declared boundary = computed boundary), `Contract.discharges` (the tier
  ladder — a `param` is *bound* or *restated*, never forgotten), `Contract.propagation`
  (`Influence.lean` — theorem-backed non-influence). `#kind_contract_decide` and
  `#kind_assembly_decide` emit kernel theorems.
- `Provenance.Relation` (same file): the spec edge — `left`/`right` contracts, a
  `RelationKind ∈ {inverts, refines, equals, boundedBy}`, a theorem `witness` checked by
  `#kind_relation` (must be a `theorem`, sorry-free, conclusion-shape-checked for `.equals`
  and `.boundedBy`, and must mention members of both boundaries).
- The boundary-mint discipline: `BoundaryAudit.lean` five-tier attributes, `#kind_boundary_audit`,
  the harvest (`KindIncidence.lean`), the self-index (`index/`), `CertifiedIngest.lean`
  (`KindAdmissible`, `CertifiedQuantity`, `IngestContract` + JSON emission).
- The mereology layer: `Mereology.lean` (`Decomposition`, import-free), `Extensivity.lean`
  (`Extensive`/`Intensive`/`WholeProper` + refutations), `Recarving.lean`
  (`leafSum_invariant`; counts are not properties of the whole), `Composite.lean`
  (`Assembles` — aggregation licensed per *sort*), `Aggregation.lean` (`WeightedCarving`,
  `mk?`, `licenses_agree_of_exact`), `uncertainty/…/QuasiExtensive.lean` (per-join tolerance
  `joins · t` — the same statement as `DagBound.errBound`).
- The uncertainty ladder (UNCERTAINTY.md, Stages 0–4 done): GUM ⊂ Willink ⊂ SSPRC, `DagBound`,
  `MeanBound`, `Budget`/`BudgetDag`, `Adequacy`.

**SMM — the model tier is the working instantiation, not a demo.** Seven declared boundaries; 135 kinds; 180
tagged boundary sites under standing gates (`#kind_boundary_clean`, `#kind_mint_ratchet`,
`#kind_scc_clean`); parameter records at kinds (`MironovCoeffs` — 21 fields, each at its own
kind); the `ConfigKinds` tier for budgets/boxes/thresholds; calibration provenance through
the examination calculus (`grmdmLabFit` as the coefficient table's provenance). The
exemplary relational specs exist: `retrieval_well_posed_boxQ` (`src/kernel/r_lut_kinds.lean`
— ∃! solution of `fwd sm = r` in the box, forward quantified over), `solveSPD4Q_correct`
(output characterized by the equation it solves), `mvOfEpsReQ_inverts_nkToEps_mixedNK`
(retrieval ∘ forward = id, exact). One live `Relation` (`retrieveReflInvertsDielectric`).

**SMW — the deployment tier erases declarations, with drift checks.** `src/deploy/dps_contract.lean`
(kind-typed registration; YAML generated and byte-held by `lake exe dps_interface`);
SMM `src/algorithm/contracts.lean` (`IngestContract` per `.npy` boundary, JSON face, `#guard`
pins in every CLI); the fit-provenance episode as the paradigm's proof of concept — the
`PARAM_BOUND_HIT` defect was fixed as an *interface* change (per-pixel `n_valid` and
`cond_pivot` condition planes on `stage2FitOut`), demonstrating "conditions travel at the
granularity the value is produced".

## 3. The gap (what "library-level capability" still requires)

1. **The spec attaches by string and is nearly unused.** `Relation.witness` and
   `Contract.members` are names; there is no `Relation` composition, no accumulated
   side-condition record, and `.inverts`/`.refines` get no conclusion-shape check. Outside
   PKC's tests there is one `Relation` in the wild. *(The checks and the side-condition
   record landed in M1 — v0.104.0; composition stays out of scope (§8), and "one edge in
   the wild" stays true until M5.)*
2. **Bounded behavior is not an interface clause.** Fixed-iteration solvers (Newton at 12
   steps, the 8-sweep loss fixed point) and the LUT gather satisfy their equations only
   approximately; their accuracy today is measured prose (`resampleMaxErrQ`, header tables),
   not a declared `boundedBy` clause with a kinded tolerance. *(The clause exists as of
   M1 — a `boundedBy` edge names a `Quantity`-typed tolerance declaration, pinned probes
   included; declaring the SMM solvers' edges is M5.)*
3. **Side conditions have no interface slot.** The `conditional` role records that cases
   exist, not the predicate that decides them; a relation's carrier rung and transfer status
   are not declared. *(Closed as capability by M1+M2: `hypotheses` on the edge, `deciders`
   on the contract — SMM's LUT boundaries name `inValidityDomainQ` — and the per-rung
   `licenses` clause; adoption across the seven boundaries is M5.)*
4. **The uncertainty stack and the contract stack are disjoint.** Nothing in `uncertainty/`
   imports `Provenance`; `Influence.influencers` names itself "the term list of an
   uncertainty budget" and nothing consumes it.
5. **No output port declares its aggregation class**, so every distribution decision
   (sharding, tiling, stitching, block averaging, checkpoint resume) rests on an implicit
   extensivity claim the library could check.
6. **The data plane is unverified at run time.** SMW's `.npy` sidecars are hand-typed Python
   dicts no Lean CLI reads; channel semantics are re-established at compile time by `#guard`
   pins, so a foreign file with a permuted layout is accepted silently.
7. **(closed)** ~~Functionally relevant nominal properties are invisible at the
   boundary.~~ Adjudicated 2026-09-05 — a functionally relevant nominal property *must*
   port (§4.2) — and the capability turns out to be built and validated: `Polarization`
   is `@[kindNominal polarizationKind]`-registered
   (`src/algorithm/dielectric/kinds/fresnel.lean`), the label is a declared `.param` of
   `dielectricForwardBoundary` and a bound `.config` of the deployed tiers, and the
   `match` that consumes it is a `select` edge of the graph. What M2 actually found to
   fix was prose: the `dielectricForwardBoundary` docstring still described the
   pre-registration state ("the polarization does not port"), contradicting the port
   list beside it — corrected in M2's SMM pass.
8. **Functional arguments carry kind signatures but have no port form.** The weighted fit
   threads `atten : AttenQ α` — already the kind-typed arrow `Quantity paramB α →
   Quantity vegetationIndex α → Quantity vegetationAttenuation α`
   (`src/algorithm/avs/weighted/kinds.lean`) — through seven definitions, and its two
   suppliers (`attenuationQ`, the fused `attenFusedQ`) are interchangeable by proof; yet
   the boundary can say none of it (`avs_fit_linearized.lean`: it "states no kind and does
   not port"). Adjudicated 2026-09-05: a function ports at its kind signature — a
   module-valued port (§4.2, built in M2b).

## 4. Doctrine constraints (settled; the design must respect them)

Each constraint was established by a concrete artifact, cited here so it can be re-checked
rather than believed.

4.1 **Laws transfer across the carrier ladder; side conditions do not.** The *carrier
    ladder* is the family of types one kinded kernel is instantiated at — `ℝ` to specify,
    `FP32` (the Flocq-modeled binary32) to bound rounding, `Float`/`IEEE32Exec` to execute,
    `CudaT` to run batched, `TapeBuilder` to record — related rung to rung by
    `CarrierRefinement E S` (`PropertyKindCalculus/QuantityRefinement.lean`: `toSpec`,
    `round`, and the law that forgetting an exec `+` equals rounding the spec `+`).
    - *A law that transfers*: every identity of the weighted mean crosses from `ℝ` to FP32
      at the cost of one rounding step per join — `mean_fp32_within_errBound`
      (`uncertainty/…/Adequacy/MeanBound.lean`) reads the bound off `dag_fp32_error_bound`
      (`…/Adequacy/DagBound.lean`).
    - *A side condition that does not*: `WeightedCarving.total_ne_zero`
      (`PropertyKindCalculus/Aggregation.lean`). Over `ℝ` it constrains the exact total;
      over FP32 it constrains the *rounded fold* — and neither implies the other.
      Executable witnesses (`tests/…/Uncertainty/MeanBound.lean`): weights `2²⁴, 1, −2²⁴`
      sum exactly to 1 while the binary32 fold is exactly `+0` (spec license holds, exec
      fails); weights `2²⁴, 1, 1, −(2²⁴+2)` sum exactly to 0 while the fold is `−2` (exec
      holds, spec fails — a finite, plausible mean for a mean that does not exist, with no
      error signal).
    - *The repairs*: `licenses_agree_of_exact` (rounding is the identity — counts,
      indicator weights) and `licenses_agree_of_nonneg` (nonnegative on-grid weights). SMM
      instantiates one each in `src/kernel/block_average.lean`: `blockAverageNanSafe`
      divides by a `Nat` tally (the exact repair); `blockAverageNanSafeCuda` divides by a
      float avgpool of a `{0,1}` indicator field (the nonneg repair).
    Hence §1 clause 4: a module's relation edge declares its license per rung or routes
    through a repair.

4.2 **Everything functionally relevant ports; not everything ports as a quantity.** The
    governing principle (adjudicated 2026-09-05): if a value influences a module's result,
    it must appear at the declared boundary — a value that genuinely could not port would
    be irrelevant to the module, and an irrelevant argument is unnecessary. So the port
    language spans more than quantities, and each non-quantity class has its own port form:
    - a *nominal property* ports at a nominal-scale kind. `polarization : Polarization` on
      `fresnelReflectivityCoreQ` (`src/algorithm/dielectric/model/branchless.lean`) selects
      the Γ formula, and it ports: `Polarization` is registered as the designation set of
      `polarizationKind` (`@[kindNominal]`, `kinds/fresnel.lean`), the label is a declared
      `.param` of `dielectricForwardBoundary` and a bound `.config` of the deployed tiers
      (`nisarPolarization`), and the `match` consuming it is a `select` edge — equality on
      a designation, the one operation the nominal scale licenses (`NominalValue k R`,
      Dybkær §12.4/§13.2.1). So two deployments differing in `.HH` versus `.VV` differ in
      their declared bindings. The doctrine sentence is the general rule the registration
      implements; gap 7 records the stale-prose defect M2's SMM pass corrected;
    - a *kind-polymorphic member* ports at kind *variables* — generics over kinds.
      `npInterpQ`/`uniformLerpQ`/`uniformFetchQ` (`src/kernel/r_lut_tables.lean`)
      implement interpolation and table lookup once, for any pair of kinds: tabulated
      values at some kind `k`, the lookup axis at another `kAxis`, both universally
      quantified. Like a type-polymorphic signature, the interface names no concrete kind
      but pins the *pattern* of agreement — the query must arrive at the axis kind, the
      result leaves at the values kind — so a query at the wrong kind is a type error even
      though the kinds are variables the caller instantiates;
    - an *axis extent* — the length of an array axis — is itself a quantity at its own
      kind, ported with role `.param`. The LUT scope holds two counts, the resampled row
      count (`nR`) and the forward-sweep sample count (`nSM`); at the carrier level both
      are bare `Nat`s, so swapping them builds a wrong-sized table with no error — exactly
      the confusion kinds exist to close, closed by per-axis kinds (`tableRowKind`, …;
      port `invResampleUniformQ/nR.q`). This rests on the count-port decision (`Nat` is a
      carrier — a count accumulates like any quantity), and the role is `.param` because a
      row count is a resolution knob the deployment fixes, not a per-datum input;
    - an *attested exit* is not an argument class at all — it is the honest boundary form
      for an interior step the calculus cannot follow. In `texRetrieveQ` the gather is, in
      deployment, GPU texture-unit interpolation — not expressible as kinded arithmetic —
      so magnitudes leave the calculus and the result re-enters through `Quantity.attest`,
      a *reviewed* re-mint carrying its recorded review reason: an assertion someone
      signed, not a derivation ("the model's one exit from the calculus"). The ports
      principle governs arguments; an exit is interior, and it is already first-class
      interface data (`Contract.exits`; dropping one fails the discharge check). The
      interface obligation is disclosure: the boundary declares that the guarantee chain
      contains a reviewed assertion, and where;
    - a *functional argument* ports at its kind signature, as a **module-valued port**
      (adjudicated 2026-09-05). The weighted fit threads `atten : AttenQ α`, and `AttenQ`
      is already the kind-typed arrow `Quantity paramB α → Quantity vegetationIndex α →
      Quantity vegetationAttenuation α` (`src/algorithm/avs/weighted/kinds.lean` — typed
      precisely so "the `(b, ndvi)` operand swap the naked `α → α → α` allowed is a type
      error"). A kind-typed signature *is* an anonymous contract — input kinds, output
      kind — so the port form declares it, and binding the port supplies a module whose
      boundary agrees with it. A function is not a property value; this is the one port
      class whose payload is a contract rather than a kind, and it is what makes the
      paradigm closed under abstraction: modules may be parameters of modules. Built in
      M2b.

4.3 **Where a step is computed is a deployment choice the equations do not determine.**
    `fresnelGeomOfAngleQ` produces the incidence geometry (`kx2`, `k0zr`) that
    `fresnelReflectivityCoreQ` consumes, yet *no wire runs between them* inside the
    dielectric scope: `sin` is the one transcendental the tape backend lacks, so batched
    carriers compute the geometry once, off the pixel batch, and hand it in. The contracts
    already state this honestly — the geometry is an `.output` of the producer and a
    `.param` of the consumer. The constraint on the design: composition machinery must not
    fuse a producer/consumer pair merely because their equations chain — one measurement
    model admits several placements.

4.4 **A module's semantic relationships are invisible to its structural ones.**
   The library relates boundaries in two ways. 
   
   - *Structurally, through shared code*:

    `Contract.discharges` holds when the outer module is built out of the inner one — its
    members call it and bind its open parameters (the tier ladder: application discharges
    algorithm). 
    
   - *Semantically, through theorems*: 
   
    "this module inverts that one" is a claim about behaviors. 
    The constraint: the semantic claim is often unstatable structurally, 
    and the three Stage-3 retrievals span the whole spectrum:

    * the Newton retrieval *contains* its forward (`newtonStepQ` evaluates `rOfSmQ` every
      step), so containment judgments see the pair;
    * the closed-form retrieval (`retrieve_refl`) contains **none** of the dielectric
      forward's members — it implements the paper-derived inverse formulas directly, so
      the two modules are structural strangers and every containment judgment is
      vacuously silent about them;
    * the LUT retrieval evaluates the forward only while *building* its table
      (`fwdHHAtQ`); the deployed gather holds the table, and the forward is gone.
      
    Yet the scientific claim has one shape in all three cases: the output solves
    `fwd sm = r` — exactly, or within a declared δ. (That exact-versus-approximate axis
    is a *separate* dimension, carried by `RelationKind` and the M1 tolerance clause; this
    constraint is about how the claim *attaches*, not how strong it is.) The only
    mechanism that states the claim uniformly across all three structural situations is
    the theorem edge — for the closed form, the one live `Relation`
    (`retrieveReflInvertsDielectric`, witness `mvOfEpsReQ_inverts_nkToEps_mixedNK`). This
    is why the `Relation` layer is load-bearing, not decorative: a module system built
    only from containment and refinement could not express what a retrieval module is
    *for*.

4.5 **Boundaries may be consumer-declared.** The prep stage's true composition is:
    block-average on the source grid (a Lean kernel) → GDAL reprojection on the host
    (Python/rasterio — no Lean counterpart, none planned) → noise floor (a Lean kernel);
    SMW's `tile_prep` runs its executable *twice*, on either side of that host warp. An SMM
    `def` composing the two Lean kernels would assert a composite that is false of the real
    pipeline, so SMM deliberately declares none, and the stage boundary
    (`prepTileBoundary`, in SMW's `src/deploy/dps_contract.lean` tier) is declared in the
    *consumer* repo over SMM's kernel ports. The module scheme accommodates this asymmetry;
    it does not erase it.

4.6 **Kinds under-discriminate inside derivation clusters — so some modules get less free
    checking than others.** An SCC is not a module, and the two partition different
    things:
    * a *module* partitions **declarations** — code, with a boundary of ports; it lives
      in the value-flow graph;
    * `#kind_scc` partitions a **kind vocabulary** — the command takes a namespace, so
      each repo runs it over its own. The numbers quoted here are SMM's
      (`#kind_scc SoilMoisture`, `src/examples/kind_scc_examples.lean` — not ISO 80000,
      which is PKC's `iso80000/` catalogue, and not PKC's core kinds): nodes are the
      model tier's 135 declared kinds, edges its 468 *licensed derivation edges*
      (operator-table entries and authored `ProductKind`/`QuotientKind` witnesses), and a
      strongly connected component is a set of kinds mutually reachable through licensed
      products and quotients (7 clusters of size ≥ 2; the harvest is import-closure
      sensitive, which is why the counts are `#guard_msgs`-pinned).
    Kinds are shared vocabulary appearing in many modules' ports and interiors, so an SCC
    neither sits inside a module nor spans modules — the partitions are orthogonal. What
    couples them is *incidence*: the type system refuses a mis-wiring exactly when the
    confused kinds have **no licensed path** between them, i.e. lie in different SCCs. 
    
    A module whose ports and interior draw kinds from many SCCs therefore gets strong
    checking for free — the dielectric chain (moisture, permittivity, wavenumber,
    reflectivity all mutually unreachable) is like this. 
    
    A module operating largely *inside one* SCC gets little: 
    the fit's working vocabulary is one 22-kind cluster
    (`pureNumber`, `backscatter`, `reflectivity`, `paramA/B/C`, the Gram and gradient
    kinds, …) where licensed quotients and products chain, so an expression with the
    wrong *provenance* can still land at the expected *kind* and typecheck. 
    
    The compensations — *compensation* here means whatever restores the discrimination
    the kind algebra cannot supply where a module's working kinds co-inhabit one SCC —
    come in two families. *Graph surgery* changes the vocabulary so the types refuse
    again, and SMM has done it twice: the dimension-one *role split* (`pureNumber` /
    `attenuationExponent` / `vegetationAttenuation` — one kind split into three roles),
    and *curated quotient targets* (the same σ⁰/σ⁰ shape lands at different kinds for
    ∂/∂a and ∂/∂d, by declaration). *Pinned evidence* leaves the graph alone and checks
    values instead: `#guard` value pins, `#check_failure` refusal probes, bit-parity
    goldens, evidence-tier attests, and ultimately the spec edge — the guarantee shifts
    from "ill-typed" to "checked". 
    
    The design consequence is an audit the library should provide (M1b, the
    *SCC-footprint report*): for a declared boundary, show which SCC each port and
    interior kind belongs to, so a footprint that collapses into a single cluster is
    flagged for compensation rather than noticed by accident. And a footprint spanning
    many SCCs is *necessary, not sufficient* — three confusions are invisible to the SCC
    analysis and need their own report columns:
    * **same-kind ports** — two ports at one kind swap without any kind graph noticing,
      however separated the clusters (`s0` and `d` are both `backscatter` in
      `stage3RetrieveIn`; `rSlice` and `r` are both `reflectivity` on
      `retrieveSmFromRQ`); the probe's separately counted within-kind edges are this
      class, and role wrappers / named record fields are its compensation;
    * **crossings and attests** — an authored crossing (`clayPctOfMassFraction`, the
      2π f→ω witness) connects kinds *by review*, and an attested mint can land anything
      anywhere, so a module heavy in either has review-strength rather than
      type-strength discrimination even across clusters;
    * **the erased region** — after `.magnitude` egress nothing kinded protects the
      wires at all (M6's territory; the byte-identity and contract gates are that
      compensation).
    The footprint's verdict line therefore answers one question per module: *where does
    this module's guarantee actually come from?*

4.7 **Judge by axiom profile and pinned probes, not by a green build.** *Axiom profile*: a
    theorem is judged by `#print axioms` — a `sorry` anywhere in its dependency tree
    surfaces as `sorryAx`, and a green build does not surface it (warnings scroll by;
    `native_decide` slips in `ofReduceBool`). The convention pins the expected profile with
    `#guard_msgs` — e.g. the uncertainty capstones pin
    `[propext, Classical.choice, Quot.sound]`, gated by
    `tests/…/Uncertainty/Capstones.lean`. *Pinned probes*: `#guard_msgs` freezes a
    command's exact output, for reports (`#kind_boundary_audit`'s 180-site table in SMM's
    `src/examples/boundary_audit_examples.lean`) and refusals alike, and `#check_failure`
    pins that an ill-kinded term is *rejected* (SMM's clay↔SM argument-swap probes in
    `src/examples/dielectric_examples.lean`) — so a guarantee that silently stops holding
    fails the build instead of surviving as prose. Every M-stage construct lands with both.
    Source code cites requirements/blueprint sections — never this plan's M-tags.

## 5. Requirements (proposed rows for `requirements/…/Catalogue.lean`)

- **R26 (evidence, expressiveness)** — *A module's behavior is a checked measurement model.*
  A declared boundary can carry relation edges whose witnesses are kernel-checked theorems;
  every `RelationKind` has a conclusion-shape check; a `boundedBy` edge names a kinded
  tolerance; every edge declares the carrier rung it is stated at and its transfer status.
- **R27 (evidence, verifiable)** — *A module's distribution is licensed by declared
  extensivity.* Output ports carry aggregation classes; recarving/sharding a module's batch
  axis is licensed by theorem from those declarations, with the quasi-extensive tolerance
  tied to the FP32 rounding budget where the carrier demands it.

The nominal-port (M2) and module-valued-port (M2b) capabilities amend the existing R23/R24
port vocabulary rather than adding rows: a port may carry a nominal-scale kind or a kind
signature, and functional relevance obliges one.

## 6. Staged plan (each stage shippable, rigor-first, validated downstream)

### M0 — Doctrine, name, requirements *(PKC)*
**Status: DONE — v0.106.0 `46fef6e3` (2026-09-05).** The blueprint chapter
*Metrological modularity* (five clauses; lean-linked nodes `def_contract`,
`def_relation`, `def_relation_kind`, `def_relation_license`; the mereology clause
cross-links the extensivity chapter and names its port wiring as the one clause not yet
built); catalogue rows R26 (expressiveness, annotated on the landed edge machinery) and
R27 (verifiable, deliberately unaddressed until M3 — the traceability matrix now reads
"of the 20 verifiable requirements, 19 are proved; of the 7 expressiveness requirements,
4 are demonstrated", which is the honest form); `@[vim4 "2.12"/"2.13"]` anchors on
`Provenance.Relation`/`RelationKind`. Gates met: blueprint `lake build` green (7385
jobs), `blueprint-gen` renders (html-single + PDF), `check-doc-pins` all four checks
pass (headline updated to 27 chapters), no new axioms.

This document; blueprint chapter *Metrological modularity* stating §1's five clauses with
lean-linked nodes for the existing constructs (Contract, Relation, the boundary tiers, the
mereology layer); catalogue rows R26/R27; the VIM4 §2.12/§2.13 anchors added to the
blueprint references from the vendored PDF.
**Gate:** blueprint builds + `blueprint-gen`; `check-doc-pins` counts; no new axioms.

### M1 — Harden the spec edge *(PKC core)*
**Status: DONE — v0.104.0 `fdd69223` (2026-09-05).** All four deliverables landed:
per-kind conclusion-shape checks (`inverts` demands the round trip in the statement,
`refines` an equality under at least one bound hypothesis), `boundedBy` naming a
`Quantity`-typed tolerance declaration at the governed port's kind, the `hypotheses`
record checked against the witness statement, and the `relations` self-index +
`#kind_relations` (violations render as ✗ rows, so the pin is the gate). The design
decision below resolved as recommended — the edge stays string-addressed data with
elaborator checks, no `Prop` field. Gate met: the five standing relation probes re-pass
byte-identically, and pinned acceptance + refusal probes cover all four kinds
(`tests/Core/KindRelation.lean`, `KindIncidence.lean`, `Index.lean`).

Conclusion-shape checks for `.inverts` (composition-equality shape) and `.refines`;
`boundedBy` upgraded to name a *declaration* whose type is a `Quantity` at the governed
output port's kind (a tolerance is a quantity, not a float in prose); a `hypotheses` record
on `Relation` (named side conditions, harvested); a `relations` self-index table and
`#kind_relations` report.
**Design decision (recommendation: keep the string-addressed data layer + elaborator
checks).** A `spec : Prop` field on a typed module structure cannot be harvested or
rendered, and the typed-authoring precedent (`Measurand.IsIndication`, `KindAdmissible.Holds`)
already covers the cases where a Prop field is natural. The elaborator command is the join:
it turns a name-addressed claim into a kernel-checked fact at pin time.
**Gate:** pinned acceptance + refusal probes for all four kinds; the existing five test
relations re-pass byte-identically.

### M1b — The SCC-footprint audit *(PKC core + SMM validation)*
**Status: DONE — PKC v0.105.0 `1f6ed66d` + v0.106.2 `4b241baf`, SMM
`src/examples/kind_footprint_examples.lean` (2026-09-05).** `#kind_footprint` reports all
three §4.6 columns with the single-cluster collapse flagged and a pinnable verdict line
(`tests/Graph/Bridge.lean` drives every section non-vacuously); kinds are deduplicated by
graph vertex, same-kind groups key on the resolved vertex, and an unresolvable kind (a
kind variable, an ambiguous short name such as the LAVS/GAVS `paramB` twins, or an
out-of-scope kind) is named as unresolved rather than misread. The SMM run pins all seven
boundaries: the dielectric chain spans 18 components; the fit's report names exactly which
seven of its kinds co-inhabit the 22-kind cluster (`backscatter`, `paramA`, `paramC`,
`pureNumber`, `reflectivity`, `sumSqBk`, `vegetationIndex`) plus its 13 same-kind groups
and 7 review-strength sites — the compensations, named, not passed silently; the LUT
boundaries carry their gather attest and four exits. Prerequisite absorbed: SMM did not
compile against PKC main past the v0.101.0 Dybkær/Lowe rework, so the sort-valued
`System` declarations were retyped `SortOfSystem` (`emInterface`, `soilWater`,
`stage3NewtonSystem`, the `(s ill : …)` binders) — the sorts they always were.

`#kind_footprint <Boundary>`: read a declared contract against the kind graph and report
the three §4.6 columns — the SCC partition of the boundary's port and interior kinds
(single-cluster collapse = flagged for compensation, not noticed by accident); same-kind
port groups (swappable regardless of SCC separation, checked against their role-wrapper /
record-field compensations); and crossing/attest incidence among the members (the
review-strength sites) — closing with a `#guard_msgs`-pinnable verdict line naming where
the module's guarantee comes from. Needs only existing machinery (Contract + the harvest +
the SCC computation); independent of M1.
**Validation (SMM):** the report over all seven declared boundaries — expected shape: the
dielectric chain multi-SCC with low same-kind multiplicity; the fit single-cluster (the
documented worst case, its verdict naming the role split, the curated targets, and the
goldens); the LUT flagged for its attest. Gives the standing SCC-cluster adjudication item
a per-module work order.
**Gate:** pinned footprint reports per boundary; the fit's verdict names its compensations
rather than passing silently.

### M2 — Interface slots for what the calculus already knows *(PKC core + SMM validation)*
**Status: DONE — v0.104.0 `fdd69223` + SMM validation (2026-09-05).** The `License`
clause (per carrier rung beyond the witness's own, `exact`/`nonneg` via a named repair
theorem or `restated` by a named per-rung witness — a rung claimed with neither is a
pinned refusal, discharging the first gate below) and the conditional port's decider
(`deciders` on `Contract`, checked to govern a conditional port and to exist) landed in
PKC; SMM's two LUT boundaries now name `inValidityDomainQ` as the decider of
`retrieveSmFromRQ/result.some`, pinned in their `#kind_contract` reports. The
nominal-port slot needed no new mechanism: the adjudicated doctrine was already
implemented — mechanism (b), `@[kindNominal polarizationKind]` on `Polarization`, landed
in SMM `935f692` (2026-08-24) with the port on `dielectricForwardBoundary` and the
`select` edge — and what M2's SMM pass actually delivered was the correction of the
stale "polarization does not port" docstring beside that port list, plus the pinned
`#kind_ports fresnelReflectivityCoreQ` showing the port
(`src/examples/kind_footprint_examples.lean`). The second gate holds as the standing
unkinded-inventory pins (`#kind_unkinded` / `#kind_unkinded_clean`).

Three slots, each surfacing existing calculus knowledge at the boundary:
- **Nominal ports (§4.2, gap 7).** A functionally relevant nominal property ports at its
  nominal-scale kind. Mechanism decision (recommendation: (b), call sites unchanged):
  (a) retype the argument at `NominalValue k R`, or (b) register the bare inductive as a
  nominal carrier at a declared kind (a `@[kindCarrier]`-style registration that names the
  kind). The harvest then ports it, and `Contract.agrees`/`Contract.discharges` cover it —
  so the deployment that binds `.HH` does so at a declared, discharged config port, and the
  HH/VV twin deployments finally differ in their declared bindings.
  **Validation (SMM):** `polarizationKind` (nominal scale) + the polarization port on the
  dielectric/Fresnel boundaries. Gate: recorded tapes and generated megakernels stay
  byte-identical (the `match`-iota precedent from the P4b flip), and `#kind_ports` now
  shows the port — pinned.
- **The conditional port's predicate:** an optional reference to the `KindAdmissible`/
  domain declaration that decides the cases (shape stays; the decider becomes data).
- **The `License` clause on relation edges:** the carrier rung (`ℝ` / `FP32` / exec) and
  the transfer status (`exact` via `licenses_agree_of_exact` / `nonneg` via
  `licenses_agree_of_nonneg` / `restated` — independently stated per rung). §4.1 becomes
  machine-visible at the boundary.
**Gate:** a relation claiming transfer with no repair and no restatement is a pinned
refusal; a functionally relevant nominal argument that remains unported stays visible in
the harvest's unkinded inventory — a worklist, no longer a resting place.

### M2b — Module-valued ports *(PKC core + SMM validation)*
A port whose payload is a *kind signature* — an anonymous contract of input kinds and an
output kind — rather than a single kind; a functional argument ports at it (§4.2, gap 8).
Three pieces:
- **The port form.** `Port` admits a signature payload, and the harvest derives it
  mechanically when the argument's type is spelled with kinded arrows — `AttenQ` needs no
  annotation; the type is the declaration.
- **The discharge extension.** `Contract.discharges` covers module-valued params: the
  binding supplies a member whose own boundary agrees with (or `refines`) the declared
  signature, so *which* module a deployment bound is declared and checked, not implicit.
- **Interchangeability as a spec edge.** Two suppliers of one signature relate by an
  `equals`/`refines` `Relation`; for `atten`, the existing bit-for-bit fused ≡ composed
  equivalence becomes the edge's witness rather than folklore.
**Validation (SMM):** the `atten` port on `avsFitLinearizedBoundary` declares the `AttenQ`
signature; `attenuationQ` and `attenFusedQ` both check against it; the deployed binding is
discharged. **Gate:** `#kind_ports` shows the signature port (pinned); recorded tapes and
generated megakernels stay byte-identical.

### M3 — Extensivity clause and the distribution license *(PKC core + SMM/SMW validation; R27)*
**Status: DONE (PKC + SMM) — v0.107.0 `abf11ebb` + SMM `6f98755` (2026-09-05); the SMW
derivation rides M6's SMW pass.** `Provenance.AggregationClass` carries the §13.5
vocabulary plus the three extended classes the v0.103.0 note asked for
(`countKeyed`/`extensiveAbout`/`interfaceLicensed`, each naming its sortal, transport,
or cancellation law); `Contract.aggregations` is the clause, `checkAggregations` the
hygiene (a class governs a produced port; a quasi-extensive tolerance is a `Quantity`
at that port's kind; every carried name exists), rendered in every `#kind_contract`
report and pinned by acceptance + refusal probes. The core theorem is
`Recarving.distribution_license` — one re-carving of the batch axis, every
declared-extensive output's total preserved — with the §13.5.2 price
(`Recarving.leafSum_within`: both carvings' joins times the per-join tolerance) in the
uncertainty layer. R27 moves to *proved*; the traceability headline reads all 20
verifiable requirements proved. **SMM validation:** the four retrieval outputs at
`volumetricWaterContent` are declared `intensive` (a fraction never sums over a pixel
carving), the fit's cost plane `extensive` (the map-reduce license for sharding the
objective — the θ outputs deliberately claim nothing). What the survey found against
the plan's expectations: `block_average`/`merge_nanmean` are `@[carrierVocab]`
array-tier kernels with no declared contracts *by design* (§4.5 — the prep stage
boundary is consumer-declared in SMW), and no declared SMM boundary produces a count
port, so the `countKeyed` class validates in PKC's probes and its SMM/SMW
instantiation (the `n_valid` plane on `stage2FitOut`) lands with the SMW pass in M6.
The all-NaN and exact-zero refusals re-pass untouched (`Tests/Uncertainty/MeanBound`).

Output ports declare aggregation class, referencing `Extensivity`/`Recarving`/`Assembles`/
`QuasiExtensive`. Core theorem: a module whose batched outputs are all declared extensive
commutes with recarving of the batch axis (`Recarving.leafSum_invariant` lifted to the
boundary); the quasi-extensive case carries `joins · t` with `t` from the coverage/rounding
budget.
**Validation:** SMM declares classes for `block_average`, `merge_nanmean`, and the stage
egress ports (`n_valid` is a count-keyed-by-carving condition — the class that does *not*
survive recarving, and the reason it must travel per pixel). SMW derives the shard/stitch
license (`TILE_SHARDS`, checkpoint-marker granularity) from the declared classes instead of
holding it as convention.
**Gate:** the two aggregation failure modes (all-NaN carving; exact-zero rounded total)
remain pinned refusals at the module level.

### M4 — Join the uncertainty budget to the boundary *(PKC; first `uncertainty/` ⇄ `Provenance` import)*
**Status: DONE — v0.108.0 `5b0c4b7c` (2026-09-05).** `BoundaryBudget.lean` is the
join: `PortBudget` attaches a term list to one produced port, and `#kind_budget`
checks it against the assembled graph — the port produced and at the stated kind, the
assembly acyclic (`Provenance.acyclic`, path-finiteness as the well-formedness of the
sum), every term an influencing source (`Provenance.influencers`, the term list of an
uncertainty budget by its own name). The combined line is the quadrature of the terms
through `combinedQ`, computed rather than stored, and influencing sources the budget
does not carry render as `unbudgeted source(s)` — what the model is not propagating
is in the report. The gate is met by the Water-Cloud capstone: its boundary declared
and agreeing, the rung-5 contributions attached (combined = rung 3's GUM `u_c`,
guarded), the four calibration parameters honestly unbudgeted, the `k = 2` coverage
tolerance declared as a `Quantity` at the output kind (exactly what a `boundedBy`
edge names — the `coverageBound_stdUnc` sourcing), and the attachment rendered by the
self-index's `port-budgets` table, pinned.

`Influence.influencers` becomes the term list it names: a budget (`Uncertainty.Budget` /
`BudgetDag`) attaches to a contract's output port over the propagation edges;
`IncidenceQuiver`'s path-finiteness is the well-formedness of that sum. A `boundedBy`
relation may source its tolerance from a coverage-derived quantity (R18's
`coverageBound_stdUnc` precedent).
**Gate:** one worked module (the Water-Cloud capstone from UNCERTAINTY.md Stage 4) carries
budget-per-output-port, rendered by the self-index.

### M5 — The field campaign *(SMM)*
A relation edge per declared boundary (seven): `equals`/`inverts` where exact
(`retrieveReflInvertsDielectric` exists; add the well-posedness edge for the LUT boundary
and the solver edge for the Cholesky/fit boundary), `boundedBy` with a kinded, attested
tolerance where behavior is approximate (LUT via a `resampleMaxErrQ`-derived declaration;
the 12-step Newton and 8-sweep inversion via measured bounds, attested with harvested review
reasons). **Stretch (decision: Nicolas):** prove fixed-iteration residual bounds (a
contraction argument would upgrade `boundedBy` from attested to proved) — worth costing only
after the attested form is landed and rendering.
**Gate:** `#kind_relations` over `SoilMoisture.*` is a pinned report; the technical
reference renders the relations table.

### M6 — Deployment-plane erasure *(SMW + SMM `contracts.lean`)*
Extend the declaration → erasure → drift-check pattern from the argv plane (where
`dps_interface` already holds YAML byte-exact) to the data plane: generate the `.npy`
sidecar JSON from `IngestContract` (extend `scripts/emit_contracts.lean`; the Python packers
consume the generated document instead of hand-typing dicts), and validate on read in the
Lean CLIs (`npy_io` checks the sidecar's interface string and channel names against the
compiled contract). Closes the one seam where a foreign file with permuted channels is
accepted silently.
**Gate:** a permuted-channel tile is a run-time refusal with a legible contract diff; the
existing compile-time `#guard` pins stay.

## 7. Status ledger

| Stage | Deliverable | Owner | Status |
|---|---|---|---|
| M0 | Doctrine + blueprint chapter + R26/R27 rows | PKC | **Done** — v0.106.0 `46fef6e3` (2026-09-05) |
| M1 | Spec edge hardened (+ shape checks, kinded tolerance, hypotheses, index) | PKC | **Done** — v0.104.0 `fdd69223` (2026-09-05) |
| M1b | SCC-footprint audit (`#kind_footprint` per boundary) | PKC → SMM | **Done** — PKC v0.105.0 `1f6ed66d` + v0.106.2 `4b241baf`; SMM `kind_footprint_examples` pins all seven boundaries (2026-09-05) |
| M2 | Nominal ports + conditional predicate + per-rung license clause | PKC → SMM | **Done** — v0.104.0 + SMM deciders/docstring/pinned port (2026-09-05); the nominal capability itself landed in SMM `935f692` (2026-08-24) |
| M2b | Module-valued ports (function arguments at kind signatures) | PKC → SMM | Open |
| M3 | Extensivity clause + distribution-license theorem | PKC → SMM/SMW | **Done (PKC + SMM)** — v0.107.0 `abf11ebb` + SMM `6f98755` (2026-09-05); SMW derivation rides M6 |
| M4 | Budget ⇄ boundary join | PKC | **Done** — v0.108.0 `5b0c4b7c` (2026-09-05) |
| M5 | Relations across SMM's seven boundaries | SMM | Open — M1's `#kind_relations` gate now exists |
| M6 | Sidecar generated + validated (data-plane drift check) | SMW + SMM | Open |

**Decisions owned by Nicolas:** the paradigm/file name (this doc assumes *metrological
modularity*); the M2 nominal-port mechanism ((a) retype the argument vs (b) register the
carrier — the plan recommends (b)); R26/R27 wording at catalogue time; the M5 stretch
(prove vs attest iteration bounds). The M1 design decision is settled by v0.104.0 as
recommended: the edge is string-addressed data with elaborator checks, no `Prop` field.

## 8. Out of scope

Re-proving the tape/CSE/ABI execution chain (already sorry-free; the kind layer's
contribution is `rfl` erasure, and the emitted `.cu` text remains the named residual trust
gap); a `Relation` composition *algebra* (compose by proving the composite theorem and
declaring a new edge — an algebra is worth building only after M5 shows which compositions
recur); Lean-side replacements for the host GDAL/pyproj bridges (§4.5 accommodates them);
any change to physlib/TorchLean upstreams.
