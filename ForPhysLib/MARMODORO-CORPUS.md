# The Marmodoro corpus — where "whole, but not one" bites in PhysLib

A survey to ground one decision: how much of Marmodoro's unite/unify distinction PKC
should carry formally, given what PhysLib actually contains. The distinction is flagged
as a possible future pass in [the plan](PLAN.md); this document is the corpus that
decision asked for.

**Provenance.** PhysLib scanned at commit `c17844a6` (fork/master, 2026-09-04), all of
`Physlib/`, `PhyslibAlpha/`, `QuantumInfo/`, plus the PR #1612 diff. Sites were located
by fan-out search; a sample of every load-bearing claim below (the `RigidBody` shape, the
`informal_lemma` bridges, the hydrogen docstring, `Ensemble.mix`, `TenQuanta.reduce` and
its preservation lemmas, the `N : ℝ` entropy, the `nsmul` docstring, `class Entropy`,
the `HAdd` unit discard, `WithDim`'s `Add`, `Superadditive`) was verified against the
source verbatim. **Nothing here is verified by compilation.** Any claim promoted into an
exhibit or an upstream communication must first be compiled; the "tension findings" in
§5 are text observations, not established bugs. Per AI-POLICY §3.1, this corpus is
internal — nothing in it is posted anywhere.

---

## 1. The claims being tested (Marmodoro 2018, verified against the vendored volume)

From "Whole, but not One", ch. 4 of *Ontology, Modality, and Mind* (OUP 2018, eds.
Carruth, Gibb, Heil; the volume is vendored under `References/`), quoted verbatim:

* **Unite vs. unify** (§3): "physical structure unites; while metaphysical structure
  unifies. The former brings about wholes, the latter unities. But wholes are not
  always unities."
* **No count principle from structure** (§3): "Physical structures are 'numberless', in
  the sense that they do not bring with them a count principle. It is an open question
  how many entities a physical structure is, which is not determined by the structure,
  or even the structure's being a whole."
* **Carvings** (§3): "Alternative carvings of the world deliver alternative numbers of
  entities" — her examples: a squad of soldiers vs. one army unit, a swarm vs. one
  superorganism, the 64 chess squares counted many ways.
* **Structural vs. substantial powers** (§4): "the structural power is what constitutes
  the electron; whereas the substantial power *is* the electron." Unification happens
  "under the individuation principle of the sortal", and "[e]very science individuates
  its own individual subjects or substances."

The operational translations used for the scan:

1. Where does a whole-system quantity come from part quantities, and what licenses it?
2. Where is a plurality treated as ONE bearer, and what licenses the oneness?
3. Where does a count principle appear — and from what?
4. Where does one physical situation appear under two carvings, and is the pair related?

---

## 2. Where PKC already stands

The distinction is not foreign to PKC — the layering already is it, unsaid:

| Marmodoro | PKC carrier | status |
|---|---|---|
| Physical structure (unites; numberless) | `Decomposition O` — a carving; `Measurement O` values arbitrary carvings; `extensive_additive` quantifies over **all** decompositions, so the total is carving-invariant | formal |
| Metaphysical unification (sortal individuation) | Declaring `σ : SortOfSystem` and instantiating `Composite σ P` / a `Sorted` instance — the model's claim, made once; `Composite σ P` adds exactly one whole, and the same parts under two sorts are two different types with different licenses | formal |
| The license to aggregate | `Assembles σ k` (keyed by the sort of the whole; content = the scale gate) + `assemble_eq_measured` cashing it against §13.5 extensivity; `mixing_subadditive` as the refutation exhibit | formal |
| Substantial (whole-proper) powers | Dedicated kinds at the whole's sort — Attempt4Pkc's `"coupled oscillator pair — normal mode + ; angular frequency"` is one — but **nothing marks a kind as whole-proper**, i.e. borne by the whole yet produced by no aggregation | informal only |
| Identity disciplines | `Designated` (injectivity is the content) vs. its honest absence for structural object types | formal |
| Intensive kinds (Dybkær §13.5's other branch) | One line of prose in `Extensivity.lean` — "constant under composition (temperature, density)" — **no construct, no law** | prose only |
| Weighted-mean aggregation (center of mass) | nothing | absent |
| Re-carving (same whole, two part descriptions) | nothing (the transpose is the only re-indexing, deliberately) | absent |
| Count kinds (a count as a quantity of a sort) | nothing; standing project rule "a count is a predicate" points the same way | absent |

---

## 3. The PhysLib corpus, by finding

### F1 — Wholes whose oneness is primitive, with the parts absent from the representation

* `Physlib/ClassicalMechanics/RigidBody/Basic.lean:42` — `RigidBody d` is **one field**:
  `ρ : C^⊤⟮…⟯ →ₗ[ℝ] ℝ`, a mass functional. No particles, no index set — parts occur only
  as bound points inside integrands. Mass is `ρ 1`; `centerOfMass`, `inertiaTensor`,
  `angularVelocity` (`AngularVelocity.lean:65,107`), `angularMomentum` (`L = Iω`),
  `kineticEnergy` all hang off the one functional. Oneness is not derived; it is the
  primitive.
* `Physlib/FluidDynamics/Basic.lean:51–66` — densities are primitive `abbrev`s
  (`Time → Space d → ℝ`), never a ratio or limit over a region; no parcel, no molecule,
  no discrete→continuum bridge anywhere in `FluidDynamics/`.
* `Physlib/Thermodynamics/IdealGas/Basic.lean:34` — Sackur–Tetrode-shaped entropy over
  bare reals, **`N : ℝ`** — the count is a continuous bulk parameter; no system object.
* `Physlib/Electromagnetism/Basic.lean:55` — `EMSystem` holds two vacuum constants;
  despite the name it bears no fields, charges, or system.

### F2 — The parts→whole bridge exists, but almost never formally

* Every "total force / total torque / `∑ Fᵢ·vᵢ`" statement in classical mechanics lives
  in `informal_lemma`s: `RigidBody/Basic.lean:189` (ω is carving-independent), `:202`
  (the CoM "moves as if all mass were concentrated at that point"), `:215,:222` (totals),
  `:327` (`P = ∑ Fᵢ·vᵢ = F_tot·V + M·ω` — the parts appear here and only here), `:334`
  (normal modes). The licenses Marmodoro asks about are exactly the statements PhysLib
  has not formalized.
* `Physlib/QuantumMechanics/Hydrogen/Basic.lean:18` — the flagship composite-as-one: the
  atom is a *single-particle* system whose mass "= mₑmₚ/(mₑ + mₚ)" **in the module
  docstring only**. `reducedMass` does not exist anywhere in the library; the two-body →
  effective-one-body re-individuation is unformalized.
* `Physlib/StatisticalMechanics/CanonicalEnsemble/Basic.lean:148` — the library's most
  explicit composition operator, `HAdd (CanonicalEnsemble ι1) (CanonicalEnsemble ι2)
  (CanonicalEnsemble (ι1 × ι2))`, is **total and unconditioned**: it keeps only the first
  system's `phaseSpaceunit` under a docstring saying the addition "is only physically
  meaningful if the two systems share the same `phase_space_unit`"; the side condition
  reappears as hypotheses on downstream lemmas (`partitionFunction_add` `:627`,
  `helmholtzFreeEnergy_add` `:704`). The whole is formed unconditionally; the license is
  deferred per theorem.
* The extensivity theorems that do exist are per-quantity, hand-proved, and share no
  abstraction: `meanEnergy_add`/`_nsmul` (`:528,:544`), `helmholtzFreeEnergy_add`,
  `chargeSum_add` (`PhyslibAlpha/…/TwoHDM/Invariants.lean:342`), `ofFieldOpList_append`
  (`QFT/PerturbationTheory/WickAlgebra/Basic.lean:376`). There is no way to ask whether
  a new quantity is aggregable.
* `QuantumInfo/Entropy/Axiomatized/Defs.lean:243` — **`class Entropy` axiomatizes
  exactly the license** (`of_kron : f (ρ ⊗ σ) = f ρ + f σ`) — and no instance of it was
  found by search; `Sᵥₙ(ρ⊗σ) = Sᵥₙρ + Sᵥₙσ` is not proved anywhere (only subadditivity
  and SSA are, `Entropy/SSA.lean:1202,1190`). The one construct shaped like PKC's
  `Assembles` is dead code.
* The structural precedent that shows the door is open:
  `Physlib/Units/WithDim/Basic.lean:66` — `Add (WithDim d M)` exists only within one
  fixed dimension `d`. PhysLib already accepts type-gated addition on the *dimension*
  axis; it has nothing on the (sort-of-whole, kind-of-property) axis.

### F3 — Count principles: bare scalars, never connected to what they count

* `CanonicalEnsemble.dof : ℕ` ("for N particles in 3D, this is 3N") with `dof_add`,
  `dof_nsmul` — the count is additive under composition and is used only as a
  normalization exponent. `NVEHamiltonian.N : ℕ` is a free index nothing composes.
  `TightBindingChain.N : Nat`; `ACCSystemCharges.numberCharges : ℕ`; and F1's `N : ℝ`.
* No count is ever *derived* — from a cardinality, a physical situation, anything.
* `Physlib/Units/ISQBridge.lean:121–135` — the library **proves** that re-carving the
  quantity space from ISQ to its default LTMCT basis destroys amount-of-substance
  irrecoverably ("cannot be recovered once dropped"). The mole exists as a unit
  magnitude (`SIUnitChoices.lean:178`); Avogadro's number appears nowhere; the count
  principle and the amount principle never meet. This is the SI's own point: amount of
  substance is a count **of a specified elementary entity** — a count keyed by a sortal.

### F4 — Three identity disciplines for parts, unmarked and mixed

* **Labeled** (`Fin n`): `IdealGas` particles ("distinguishable", said so at
  `MicroCanonicalEnsemble/IdealGas.lean:20`), `CanonicalEnsemble.nsmul` ("distinguishable
  copies"), `MState.npow`, `ACCSystem.Charges`, tight-binding sites.
* **Multiplicity without identity** (`Multiset`/`Sym`): `FluxesFive`, `TenQuanta`
  ("a multiset of `(q, M, N)` for each particle"), and the one genuinely bosonic
  discipline in the repo — `LadderSystem`'s `CountFun d n ≃ Sym (Fin d) n`
  (`OccupationBasis.lean:68`) with the multiset dimension count `(d+n−1).choose n`.
* **Identity without multiplicity** (`Finset`): `ChargeSpectrum.Q5/Q10`; the map
  `Quanta.toCharges` (`Multiset → Finset`) is a formal forgetting of the count.
* Where the discipline is *load-bearing*, PhysLib states it as invariance:
  `ACCSystemGroupAction` demands proofs the physics is relabeling-invariant;
  `StandardModel/…/Permutations.lean:31` is an explicit `Sₙ`-per-species group; and
  `IsViable` (`FTheory/SU5/Quanta/IsViable.lean:80`) *requires* `Nodup` — viability
  demands that charges individuate, i.e. a condition under which the plurality has a
  determinate count.
* Tension: the `CanonicalEnsemble` module doc claims the `h^dof` normalization prevents
  "ambiguities such as the Gibbs paradox", yet every particle collection is
  distinguishable, no `1/N!` appears in the repo, and the ideal-gas free energy at
  `IdealGas.lean:177` has the non-extensive form. (Text observation; verify by
  computation before any use.)

### F5 — Alternative carvings: present everywhere, related almost nowhere

* **Licensed, in one corner of string theory**: `TenQuanta.reduce`
  (`FTheory/SU5/Quanta/TenQuanta.lean:154`) merges matter curves of equal charge — fewer
  entities, same physics — and `decompose` (`:606`) splits one curve into indiscernible
  ones; `reduce_sum_eq_sum_toCharges` (`:236`) and `anomalyCoefficient_of_reduce`
  (`:1082`) prove every additive functional and the anomaly are carving-invariant.
  **This is the purest "alternative carvings deliver alternative numbers of entities,
  and the physics doesn't care" in the library — with the license proved.**
* **Stated, in a docstring**: `QuantumInfo/States/Ensemble.lean:62` — "generically, a
  single mixed state has infinitely many ensembles that mixes into it"; reinforced by
  `mix_congrMEnsemble_eq_mix` (member relabeling is physically idle). Entanglement of
  formation (`Entanglement.lean:232`) is an infimum **over all many-carvings**.
* **Formalized as arithmetic on one whole**: König (`kineticEnergy_eq_translational_
  add_rotational`), the parallel-axis theorem (`inertiaTensorAbout_eq_centerOfMass_
  add_pointMass` — the library's one theorem relating two aggregations of one whole),
  space-frame vs. body-frame ω, `purify` (oneness by enlargement), partial traces with
  `traceLeft_prod_eq` (the whole is recoverable from the parts only for product states),
  and the entropy *defects* `qConditionalEnt`/`qMutualInfo` — names for the failure of
  additivity, with no name for additivity.
* **Present and unremarked**: a `d`-dimensional `HarmonicOscillator` re-read as a
  `LadderSystem` Fock space (`LadderOperators.lean:180`) — one particle ↔ a symmetric
  power of quanta; localized vs. Bloch bases of the tight-binding chain;
  `LatticeModels/Basic.lean:14` names the real-space/momentum-space relation as an open
  design issue.
* **Absent**: normal modes (`LinearTriatomic.lean` is a TODO; the coupled-spring file
  has the cross term `x₀x₁` on screen and never diagonalizes), reduced mass, bound
  states, the CoM frame (frames exist; none is ever built from a body), phonons and
  quasiparticles (one docstring mention), discrete→continuum limits.

### F6 — Aggregation modes are invisible in the types

Total mass (integral of 1), center of mass (**weighted mean** — a ratio of integrals,
defined at `RigidBody/Basic.lean:57` outside its `mass ≠ 0` license), inertia
(**arrangement-dependent**, axis-parameterized — the one site where that dependence is
syntactically visible), `linearMomentum` (mass × mean velocity, not `∑ pᵢ`), ideal-gas
energy (plain sum), anomaly coefficients (multiplicity-weighted, then quadratic and
**cubic** sums over species), `koszulSign` (order-dependent product), von Neumann
entropy (subadditive only) — all land in the same undifferentiated `ℝ`/matrix,
distinguished by identifier alone. `Mixable`/`ProbDistribution.expect_val` is an
abstract weighted-mean aggregator; `Superadditive` + Fekete
(`QuantumInfo/ForMathlib/Superadditive.lean`) is the one place extensivity-in-a-count
is a *concept* rather than a per-quantity lemma.

### Empty categories (each an absence finding)

Reduced mass; formal total force/torque/momentum of a many-part system; total charge
(no `∫ρdV`, no Gauss flux); density as a limit; control-volume/integral conservation in
fluids; entropy `_add`/`_nsmul` (energy and free energy have them, entropy does not);
thermodynamic homogeneity `S(λU,λV,λN) = λS`; composition of microcanonical systems;
`Sᵥₙ` additivity; capacity superadditivity (docstring goal only); FLRW density sums
(TODO); every multi-part classical composite (double pendulum `sorry`, triatomic TODO,
scattering TODO); and **any mereological vocabulary at all** — "extensive",
"intensive", "aggregate", "mereology" have zero occurrences in the library.

---

## 4. What this buys the campaign

The corpus supports one headline: **PhysLib has abundant physical structure and almost
no formalized statement of what licenses oneness or aggregation — and in the four
places it wrote one anyway (`TenQuanta.reduce`'s preservation lemmas, the permutation-
invariance structures, `ISQBridge`'s irrecoverability, `class Entropy`'s dead axiom),
it had to invent the pattern locally each time.** PKC's `Assembles`-shaped licensing is
the shared abstraction those four corners are groping toward, and `WithDim`'s
dimension-gated `Add` is the precedent showing the host library already accepts
type-gated addition on one axis. The pitch writes itself: dimensions gate *what kind of
number*; sorts gate *what kind of whole*.

Named consumers per candidate PKC construct, from the corpus:

| candidate | PhysLib consumers found | count |
|---|---|---|
| Whole-proper (substantial) kinds: borne by the whole, produced by no aggregation | ω, `inertiaTensor`, `L`, `T_rot`; temperature, pressure, entropy of an ensemble; normal-mode frequencies (TODO'd); transport coefficients; EoF | many |
| Intensive branch of §13.5 (constant under composition, hypothesis explicit) | temperature, pressure, densities, `κl`/`κe`, every field quantity | many |
| Weighted-mean license (the CoM mode) | `centerOfMass`, `centerOfMassVelocity`, `linearMomentum`, `meanEnergy`, `Mixable`/`expect_val` | several |
| Re-carving with invariance obligations (the `reduce` pattern, generalized) | `TenQuanta.reduce`/`decompose` (exists, locally), reduced mass (absent), normal modes (absent), Bloch, Fock, partial trace | several, two of them absences PKC could fill |
| Count kinds (a count as a quantity dedicated to a sort — the SI's "specified elementary entity") | `dof`, `N`, `numberCharges`, `numChiral… = 3`, mole↔Avogadro (absent) | several |

---

## 5. Options and recommendation

* **Option 1 — say it (prose + citation).** State the layering explicitly — the
  Extensivity layer is Marmodoro's *united* physical structure (carvings, numberless,
  invariance quantified over all decompositions); `Composite σ P`/`Sorted` is her
  *unification under the individuation principle of the sortal*; `Assembles σ k` is the
  license her distinction says a whole cannot supply for itself — in the blueprint's
  object-type chapter and the three module docstrings, with a verified `InProceedings`
  entry for the chapter. Cost: an afternoon. Risk: none.
* **Option 2 — the two cheap formal pieces with pre-existing justification.**
  (a) The intensive branch of §13.5, which PKC owes Dybkær independently of Marmodoro:
  the law "constant under composition" with its hypothesis (homogeneity/equilibrium)
  explicit — the hypothesis is where "the dependencies that develop between the
  components" become formal content. (b) The negative-license pattern for a
  whole-proper kind, mirroring `mixing_subadditive`: e.g. angular velocity over a rigid
  sort — licensed as a dedicated kind of the sort, refuted as an aggregate. Cost: days.
  Risk: low; both have PKC-internal consumers already.
* **Option 3 — campaign exhibit against the corpus.** A RigidBody/#1612 case study
  showing the three-way split the types can carry — assembles (mass, momentum),
  whole-proper (ω, inertia), neither (the coupled-spring cross term) — plus the
  weighted-mean license the CoM needs. This is the artifact a maintainer could weigh,
  in the style of the existing case studies. Cost: an exhibit-sized effort.
* **Option 4 — new machinery, each piece only with a named consumer.** The re-carving
  construct (generalize the `reduce` pattern: a map between part descriptions of one
  σ-whole + the obligation that licensed aggregates are preserved) and count kinds.
  These are real but heavier, and the corpus shows the consumers; sequence them behind
  a decision on Options 1–3.

**Recommendation: do Options 1+2 now, hold Option 3 until there is a concrete physlib
conversation to aim it at, and gate each Option 4 piece on a named consumer.** The
DedicatedKind correction followed exactly this shape (corpus → cheap principled core
change → exhibits) and landed cleanly.

## Status ledger

| item | owner | state |
|---|---|---|
| Corpus (this document) | Claude | Done 2026-09-04 |
| Scope decision: which of Options 1–4 | Nicolas | **Open** |
| Marmodoro `InProceedings` entry in `References.lean` (verified against the vendored volume, same pattern as Simons/Heil) | Claude, on a yes to Option 1 | Open |
| Compile-verification of any corpus claim promoted into an exhibit or communication | Claude, per claim | standing rule |
