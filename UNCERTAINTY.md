# UNCERTAINTY.md — A rigor-first plan for uncertainty & numerical adequacy in PKC

> Status: **Stages 0–4 implemented & CI-checked** (reference layer, GUM/Willink, autograd `cᵢ`,
> the ladder theorems T1–T5, the executable SSPRC pipeline, the numerical-adequacy layer — the
> executable `Adequacy` carrier plus the theorems A1 absorption, A2 Sterbenz, A3 verdict soundness
> over `ℝ` — the **universal capstone A3′** (`DagBound`: FP32 measurand ≈ `ℝ` over an input box up
> to a DAG-additive rounding budget, exact when flag-free), over a binary32 `+`/`−` evaluation DAG,
> **A2 lifted to the genuine binary32 format** (Stage 3.2: a TorchLean PR adds
> `neural_generic_format_FLT_sterbenz`/`FP32.sub_exact_of_sterbenz` for the FLT/`fexp32` gradual-underflow
> format, grounded in PKC as `Fp32Grounding.round32_sterbenz_exact` — `round₃₂(u−v)=u−v` for near-equal
> representable operands), and the **executable↔spec bridge** (Stage 3.3: a second TorchLean PR gives
> the computable `IEEE32Exec` model an executable ULP query `ulpExp?` proved equal to `ulp₃₂` and an absorption
> test `absorbs` certified against `round₃₂`, grounded in PKC as `ExecBridge.exec_verdict_sound` — the
> computed adequacy verdict is provably the specified one)), the **kind-typed Axis-U significance
> wiring** (Stage 3.4: `Adequacy.Significance.analyzeQ` runs one carrier-raw write-once kernel at
> `TapeBuilder .scalar` and `Adequacy` from *one* `InputDist` list, folding the autograd `cᵢ` and the
> descriptor's `uᵢ` into the carrier-generic kinded GUM budget of `Uncertainty.Budget` — one
> descriptor, both areas, every budget quantity a `Quantity k R`), and the **autograd-soundness
> upgrade** (Stage 3.5: a third TorchLean PR connects the runtime reverse pass to Mathlib's Fréchet
> derivative — `backwardDenseFrom_compileAux_adjoint_fderiv` in
> `NN/Proofs/Autograd/Runtime/Link/FDeriv.lean` proves the executable dense reverse pass on a
> compiled graph returns, on the input prefix, exactly `(fderiv ℝ eval x)† seed`; PKC's
> `Sensitivity.gradient` now invokes that very entry point, `Tape.backwardDenseFrom`, with its
> public signature unchanged), and the **direct-simulation closure** (Stage 3.6: the `PRSim`
> spike's five obligations are theorems — the vectorization homomorphisms
> `mulSpec_ofVecT`/`addSpec_ofVecT`; the value-free totality `backwardDenseFrom_ok` (the dense
> reverse pass returns `.ok` on any value-correct tape whose backward closures are *shape-total*,
> a hypothesis the eager `leaf`/`add`/`mul` constructors are proved to provide); and the endpoint
> `direct_PR_soundness_compiled` as the `Γ`-prefix `ArrCorr` corollary of the Stage-3.5 theorem —
> `Experiments/PRSimulation.lean`, now indexed in `UncertaintyRigor`, sorry-free — **and the
> eager-provenance closure** (`Experiments/EagerProvenance.lean`: `EagerBuilds` relates the tape
> the runtime constructors `leaf`/`add`/`sub`/`mul` actually build to its P-graph, and
> `backwardDenseFrom_eager_eq_compiled` proves that tape's total dense reverse pass computes
> exactly the compiled tape's — so `direct_PR_soundness_eager` puts the fderiv endpoint on the
> *eagerly built* tape, no compilation involved). Both `×`/`÷` DAG extensions are now realized —
> the kinded budget DAG (`BudgetDag`, residual 2) and the FP32-adequacy DAG (`DagBound`, Area 2);
> only Stage 4 (scale) remains design/plan, scoped in §6.
> Audience: PKC maintainers.
> Scope: augment PropertyKindCalculus in two coupled areas —
> (1) **uncertainty quantification** (UQ) of model outputs from input uncertainties, and
> (2) **numerical adequacy** of the floating-point representation of a science model.
> Both are realized *through PKC's existing carrier-parametric quantity design*, and both
> are driven by **one shared uncertainty descriptor** attached to quantities.
>
> Expanding the dependency on TorchLean is in-scope and expected (autograd functional API,
> the `NeuralFloat`/`FP32` error lemmas, the sound `RInterval` carrier, FFT kernels).

---

## Status at a glance (updated 2026-09-06)

*The scannable tracker. Full detail lives in [§6](#6-staged-plan-each-stage-is-shippable-testable-rigor-first)
(stages) and its **Remaining work** subsection (residuals). This table is the index — when a row here
changes, update the detailed prose too (one-source-of-truth, Blueprint Rule 4).*

**Stages** — every stage below is built & CI-checked **except Stage 4**. Autograd soundness is
complete (the reverse pass is proved the adjoint of the Fréchet derivative at `ℝ`, on the eagerly
built tape).

| Stage | Deliverable | Status |
|---|---|---|
| 0 | Types + MCM + paper-reproduction `#guard`s | ✅ |
| 1 | GUM/Willink linearized methods + autograd `cᵢ` + T1/T2 | ✅ |
| 2 | SSPRC pipeline + T3/T4/T5 (the nested ladder) | ✅ |
| 3 | Numerical-adequacy carrier + A1 absorption / A2 Sterbenz / A3 verdict | ✅ |
| 3.1 | Universal capstone A3′ — the `+`/`−` forward-error DAG (`DagBound`) | ✅ |
| 3.2 | A2 lifted to genuine binary32 (FLT Sterbenz) — *TorchLean PR* | ✅ |
| 3.3 | Executable↔spec bridge over `IEEE32Exec` — *TorchLean PR* | ✅ |
| 3.4 | Axis-U coupling + kinded GUM budget (`Budget`) | ✅ |
| 3.5 | Autograd soundness (reverse pass = fderiv adjoint) — *TorchLean PR* | ✅ |
| 3.6 | Direct-route completion + eager-provenance closure | ✅ |
| 3.7 | The weighted mean at binary32 — the aggregation mode that divides (`MeanBound`) | ✅ |
| 3.8 | Flag-freedom relocated to the exact evaluation (`ExactRepresentable`) and its regime exhibited | ✅ |
| 3.9 | §7's `CarrierRefinement` consolidation decided and its meeting point checked (`RefinementBridge`) | ✅ |
| 4 | Scale — GPU SSPRC/MCM on `CudaT`, `Nᵢ` allocation, science-model capstone | ✅ — batched SSPRC (`SsprcBatched` + `ssprc_batched_parity` exe) and batched MCM (`McmBatched` + `mcm_batched_parity` exe), both gated by CI; sensitivity-driven `Nᵢ` allocation (`Allocation` + `DegenhardtAllocation` example, `#guard`-checked); science-model capstone (`WaterCloudModel` — one WO1 Water-Cloud-Model forward through the whole pipeline, `#guard`-checked) |

**Residuals / loose threads** (from the four honest residuals scoped after Stage 3.6):

| # | Thread | Status | If reopened → next step |
|---|---|---|---|
| 1 | Autograd ops beyond the arithmetic core + `TapeM`/`StateT` sugar | ✅ CLOSED 2026-08-03 | (follow-up) upstream the generic `TapeM` reduction layer to TorchLean |
| 2 | Kinded `×`/`÷` **budget** DAG (`BudgetDag`, Area 1) | ✅ CLOSED 2026-08-03 · v0.24.0 | — (honest limits: per-occurrence independence; `ofRatio`-liberal witnesses) |
| 2′ | FP32-**adequacy** `×`/`÷` DAG (`DagBound`, Area 2) — *distinct from #2* | ✅ LANDED · v0.25.0; flag-freedom relocated to the exact evaluation and its regime exhibited | the no-absorption regime — a *different conclusion* (resolution, not equality), lifting `Adequacy.resolve` along the DAG |
| 3 | `Float`-vs-`ℝ` carrier gap | ✅ discharged in kind (Stages 3–3.3) | per-model application only; no separate deliverable |
| 4 | `hᵢ`/HVP Taylor surrogate; trig VJP nodes (`sin/cos/tanh/sinh/cosh`) | ▫ optional | fund only if a model needs 2nd-order surrogates or transcendental diff |
| 5 | `AdequacyReport`'s counts are **path multiplicities**, not site counts (`merge` adds; no node identity) | ▲ OPEN — [§7](#7-risks--open-decisions); pinned in `AdequacyLimits` | replace the two `Nat` fields with `Bool`s and `merge` with `||` — the sound content, 4 `#guard`s + 2 reads move |
| 6 | A **0th-order `sqrt`** replaces a fixed point's damping factor with `1` (the arithmetic is fine) | ▲ OPEN — [§7](#7-risks--open-decisions); pinned in `AdequacyLimits` | one derivative per transcendental, `u(√x) = u(x)/(2√x)` etc. — the same coefficients `Budget.contributionQ` uses |

**What to pick up next** (rough priority):

1. **Stage 4 — Scale. ✅ CLOSED.** Both batched propagators are on `CudaT` and both are gated:
   `SsprcBatched.run` (one launch per input, because SSPRC's construction is per-input) and
   `McmBatched.run` (one launch for the whole propagation, because MCM samples the joint directly).
   A build-time `#guard` of a `CudaT` result is impossible here — see the Stage-4 note in §6 — so
   each is checked by a compiled executable that links the native code and asserts parity with its
   scalar reference, and CI now runs both rather than leaving them to be run by hand. The remaining
   two slices landed earlier: the sensitivity-driven **`Nᵢ` allocation** (`Allocation.allocate`, a
   pure `List Nat` that ranks inputs by `|cᵢ|·uᵢ` and largest-remainder-splits the budget;
   `#guard`-checked in `DegenhardtAllocation`), and the soil-moisture **science-model capstone**
   (`WaterCloudModel` — one write-once Water-Cloud-Model forward driven through the Float forward,
   the autograd Jacobian, GUM/Willink, SSPRC, and the allocation; `#guard`-checked).
2. **TorchLean PR — the generic `TapeM` reduction layer** (residual #1's recorded follow-up):
   ✅ **written and verified**, awaiting a human to push and post it (AI-POLICY §3.1). Branch
   `tapem-run-lemmas` off `upstream/main` in the TorchLean checkout, purely additive (+501/−0):
   `TapeM.opM`, the three `opM_run_*` lemmas, `run_bind_inv`/`exec_inv`, and the `run_<op>_ok` family
   for all 31 tape-threading wrappers, every one generic in the carrier. PR body drafted at
   `scratchpad/torchlean-pr-tapem-run-lemmas.md`. After it merges `TapeMBridge.lean` shrinks to the
   demo + endpoint, and what it keeps arrives generic rather than fixed at `ℝ`.
3. **Area-2 refinement** — the *relocation* half is done: `ExactRepresentable` states flag-freedom on
   the exact `ℝ` evaluation, `flagFree_iff_exactRepresentable` proves the two conditions cut out the
   same inputs, and `AdequacyDag`'s doubling chain discharges one — so the flag-free theorems are
   about an inhabited regime now, not only about a hypothesis. What remains is the genuinely weaker
   no-absorption regime, which needs a different *conclusion*: rounding is allowed, equality of the
   variations is then false, and the statement becomes a resolution one lifting `Adequacy.resolve`
   along the DAG (thread #2′).
4. **The two adequacy-carrier limits (threads #5, #6)** — found by scoring the first real model at
   the carrier, reduced to a handful of lines each in
   `UncertaintyExamples.AdequacyLimits`, and argued in §7. Neither is a soundness bug and both are
   limits on *reading* a report, but #6 decides where the carrier may be used at all: the
   cancellation half is unusable wherever a transcendental supplies a loop's damping. Take #5's
   `Nat → Bool` repair first — it is small, it is exactly the sound content, and it removes a
   public field whose obvious reading is wrong.
5. **Ergonomics** — `attribute [local irreducible]` on *all* activation scalar specs to cut
   `AutogradDirectSim`'s ~25-min elaboration; the `safeLog` `EagerBuilds.unary` instance.

---

## 0. The one-paragraph thesis

A science model in PKC is written **once** as a carrier-polymorphic kernel `f` over
`[NumCarrier α]` ([`Paradigm/NumCarrier.lean:37`](PropertyKindCalculus/PropertyKindCalculus/Paradigm/NumCarrier.lean#L37)).
We add **two orthogonal parametrization axes** on top of that single source:

* **Axis N (numeric carrier `R`)** — *how* the numbers are represented: `ℝ` (proof),
  `FP32` (binary32 rounding spec), `RInterval` (rigorous ranges), `IEEE32Exec` (bit-exact),
  `CudaT`/Tensor (GPU), `Float` (fast CPU), `TapeBuilder` (autograd).
* **Axis U (uncertainty descriptor / "noise")** — *what is known about the input's dispersion*:
  a per-quantity `InputDist` carrying moments/cumulants, an inverse-CDF, and a support range.

Every point in the `N × U` grid is a meaningful computation of the *same* model, and — the
point of the whole exercise — **the value-added properties compose**: you can prove the linear
limit (`ℝ`), execute on GPU (`CudaT`), get sensitivities (`TapeBuilder`), and *certify no
floating-point information loss at the scale of the input uncertainties* (`FP32`/`RInterval`),
all from one model definition. No competing metrology tool offers that product.

---

## 1. Principles (these come first and constrain every design choice)

* **P1 — Write once, interpret many.** No method or check may require rewriting the model.
  Everything is an *interpretation of the WO1 kernel at a carrier* or a *value of a method
  structure*. This is the existing PKC contract; we do not break it.

* **P2 — Uncertainty is a property of a quantity (VIM/GUM).** A measured value carries a
  dispersion. We model this exactly as PKC already models kinds: an **additive** descriptor
  `InputDist` alongside the magnitude, never a change to `Quantity k R`.

* **P3 — The UQ methods form a *provably nested ladder*.** GUM ⊂ Willink ⊂ SSPRC is not a slogan;
  it is a chain of **monoid homomorphisms** between the methods' contribution types (§3.1, §3.5),
  all resting on one theorem: cumulant additivity under independent summation
  (Willink eq. 3, `κ_r(Σ aⱼ Zⱼ) = Σ aⱼ^r κ_r(Zⱼ)`). Each coarser method must be *proven* to
  agree with the projection of the finer one.

* **P4 — Numerical adequacy is defined relative to the input uncertainties.** "No information
  loss" is meaningless in the abstract; it is precise once we say *loss of what, at what scale*.
  The scale is exactly the input dispersion from Axis U. Hence Areas 1 and 2 **share the
  `InputDist` descriptor** — they are one design, not two.

* **P5 — Every method and predicate has an `ℝ` specification and a proven carrier bound.**
  Rigor-first: we write the spec over the proof carrier `ℝ`, then relate each executable carrier
  to it by a *theorem*, not by testing. Optimizations (surrogates, GPU) are justified by a bound,
  never asserted.

* **P6 — Follow PKC's representational convention** (README §"Representational conventions",
  the lines you highlighted): **meta-concepts → `structure`/`class`; specific instances → values
  (`def`), open-world.** So `InputDist` and `UncertaintyMethod` are structures; `normal`,
  `triangular`, `gum`, `willink`, `ssprc` are *values* an application can extend.

---

## 2. Architecture: two orthogonal axes and the value-proposition matrix

### 2.1 Axis N — the numeric carrier (already exists; we add two consumers)

The carrier tower is unchanged. What this plan does is *assign each carrier a job* in the
uncertainty/adequacy story and light up the two currently-idle carriers (`TapeBuilder`,
`RInterval`).

| Carrier | What it computes | **Value-added property** | Status |
|---|---|---|---|
| `ℝ` | exact symbolic reals ([`QuantityReal.lean:25`](PropertyKindCalculus/dimension/PropertyKindCalculus/QuantityReal.lean#L25)) | **Proof** — specs, ladder-nesting theorems, adequacy soundness | exists |
| `TapeBuilder` | `cᵢ=∂f/∂Xᵢ`, `hᵢ=∂²f/∂Xᵢ²`, HVP, Jacobian ([`TapeCarrier.lean`](PropertyKindCalculus/torch/PropertyKindCalculus/Torch/Paradigm/TapeCarrier.lean)) | **Sensitivity** — GUM/Willink coefficients, contribution ranking, nonlinearity gauge, Taylor surrogates for SSPRC | ✅ `cᵢ` wired (`Sensitivity.lean`, Stage 1); `hᵢ`/HVP Taylor-surrogate deferred (optional, off the Stage-2 exit path) |
| `FP32` | round-on-ℝ binary32; half-ULP & `(1+δ)` bounds | **No information loss / numerical adequacy** — certify swamping/cancellation-free; quantify approximation error | carrier exists; adequacy layer new |
| `RInterval` | sound magnitude enclosures on the FP32 grid | **Rigorous ranges** — bound operand magnitudes for adequacy; verified output bounds | exists in TorchLean; unused by PKC |
| `IEEE32Exec` | bit-exact binary32 | **Executable certification** — real bits match the spec (finite fragment) | exists |
| `CudaT`/Tensor | float32 device buffers | **Fast GPU execution** — batched SSPRC/MCM propagation, large models | exists |
| `Float` | host double | **Fast CPU reference / prototyping** | exists |
| `Complex R`, `Fin n → R` | functorial carriers | vector/complex quantities for free | exists |

### 2.2 Axis U — the uncertainty descriptor (new, additive)

```lean
-- meta-concept (structure); carrier-parametric so it exists at ℝ (proofs) and Float (exec)
structure InputDist (R : Type) [MathCarrier R] where
  mean           : R          -- E(Xᵢ)
  stdUnc         : R          -- u(Xᵢ);   κ₂ = stdUnc²
  fourthCumulant : R          -- wᵢ       (Willink Table 1; 0 for Normal)
  thirdCumulant  : R := 0     -- κ₃ᵢ      (asymmetry, Willink §5)
  invCDF         : R → R      -- inverse CDF: systematic/random sampling (SSPRC/MCM)
  support        : Option (R × R) := none   -- rigorous range → numerical adequacy (Axis N/FP32)

-- specific distributions are VALUES (open-world, per README convention), constants from Willink Table 1
def InputDist.normal     (μ σ : R) : InputDist R := { mean := μ, stdUnc := σ, fourthCumulant := 0, … }
def InputDist.uniform    (μ δ : R) : InputDist R := { stdUnc := δ / sqrt 3,  fourthCumulant := -(4*δ^4)/30, support := some (μ-δ, μ+δ), … }
def InputDist.triangular (μ δ : R) : InputDist R := { stdUnc := δ / sqrt 6,  fourthCumulant := -(δ^4)/60,   support := some (μ-δ, μ+δ), … }
def InputDist.arcsine    (μ δ : R) : InputDist R := { stdUnc := δ / sqrt 2,  fourthCumulant := -(3*δ^4)/8,  support := some (μ-δ, μ+δ), … }
-- … laplace, scaledT ν, etc.
```

A quantity carrying such a descriptor:

```lean
structure UncertainQuantity (k : KindOfProperty) (R : Type) [MathCarrier R] where
  value : Quantity k R
  dist  : InputDist R
```

`UncertainQuantity` is *parallel* to `Quantity` — additive metadata, no change to the carrier
tower, exactly the pattern the roadmap already used for `QuantityVector`.

### 2.3 How the axes compose (the actual value proposition)

The WO1 model `f` is instantiated:

* at **`Float`/`CudaT`** to *evaluate* (SSPRC/MCM sample propagation; GPU-batched: all `Nᵢ`
  samples of input `i` = one kernel launch);
* at **`TapeBuilder`** to *differentiate* (GUM/Willink coefficients `cᵢ`; nonlinearity `hᵢ`);
* at **`ℝ`** to *prove* (ladder nesting; adequacy soundness);
* at **`FP32` + `RInterval`** to *certify* (numerical adequacy given the `InputDist.support`).

The same `InputDist` feeds the UQ method (Area 1) *and* the adequacy check (Area 2). That shared
descriptor is the architectural hinge of this whole document.

---

## 3. Area 1 — Uncertainty quantification

### 3.1 The unifying abstraction

All three methods (plus MCM) are the same three-step pipeline —
**extract per-input contribution → combine independent contributions → summarize** —
differing only in the *contribution type* and how each step is realized:

| Method | `Contribution` | `extract` (per input) | `combine` | `summarize` |
|---|---|---|---|---|
| **GUM/LPU** | `R` (variance κ₂) | `cᵢ² · uᵢ²` | `(+)` | `u_c`, Gaussian/t interval |
| **Willink** | `Cumulants` (κ₂,κ₄,κ₃) | `(cᵢ²uᵢ², cᵢ⁴wᵢ, cᵢ³κ₃ᵢ)` | pointwise `(+)` | `(u_Y, γ_Y)` → **Pearson** percentile |
| **SSPRC** | `DeviationPDF` | samples `a_{i,j}=f(…,x_{i,j},…)−R`, reconstruct (DDE) | **convolution** | reconstruct measurand PDF |
| *(MCM ref)* | `EmpiricalPDF` | joint random sampling (no separation) | — | empirical PDF |

The `combine` operation is a **commutative monoid** on `Contribution`, and *that monoid law is
the independence assumption made explicit* (P4/P5). We encode the pipeline as the meta-structure
and the methods as values:

```lean
structure UncertaintyMethod (R : Type) [MathCarrier R] where
  Contribution : Type
  combine      : Contribution → Contribution → Contribution   -- comm. monoid (independence)
  empty        : Contribution
  extract      : Model R → InputDist R → Contribution          -- may consult autograd / sampling
  summarize    : Contribution → OutputUncertainty R
  -- laws (proof obligations, P5):
  combine_comm  : ∀ a b, combine a b = combine b a
  combine_assoc : ∀ a b c, combine (combine a b) c = combine a (combine (combine b c) …)
  empty_combine : ∀ a, combine empty a = a

def gum     : UncertaintyMethod R := …   -- Contribution := R
def willink : UncertaintyMethod R := …   -- Contribution := Cumulants
def ssprc   : UncertaintyMethod R := …   -- Contribution := DeviationPDF (combine := convolve)
def mcm     : UncertaintyMethod R := …   -- reference; joint sampling
```

Top-level driver (independence is a *typed precondition*, not an assumption in prose):

```lean
def propagate (m : UncertaintyMethod R) (f : Model R)
    (inputs : List (UncertainQuantity k R)) (indep : Independent inputs) :
    OutputUncertainty R :=
  m.summarize <| (inputs.map (fun q => m.extract f q.dist)).foldl m.combine m.empty
```

### 3.2 The role of TorchLean autograd (precise, not overstated)

**SSPRC is derivative-free by construction** — its core loop is sampling + reconstruction +
convolution. Autograd is *not* the SSPRC engine. It earns its place in exactly three spots:

1. **GUM & Willink coefficients** `cᵢ = ∂f/∂Xᵢ` at the reference `E(Xᵢ)` — one reverse pass gives
   all `cᵢ` (`NN/API/Public/Autograd/Core.lean`, `func.grad`/`model.gradInputs`). This *is* the
   `extract` step for the two linearized methods.
2. **Per-input Taylor surrogates for SSPRC** (the paper's own "simplified model per influence
   quantity", §2 3rd concept). Along input `i` the model is 1-D; `aᵢ(δ) ≈ cᵢδ + ½hᵢδ²` with
   `hᵢ` from `hvp`/`hessian` (`Autodiff.lean`) pushes the `Nᵢ` samples through a polynomial
   instead of the full model. `hvp` doubles as a **nonlinearity gauge** deciding, per input,
   whether the surrogate is safe or full sampling is required.
3. **Sensitivity-driven sample allocation / early stop** — rank inputs by `|cᵢ|·uᵢ`, spend `Nᵢ`
   where it matters, drop negligible inputs (the paper's §4 adaptive extension).

Honest boundary: autograd does **not** reduce SSPRC's count of full model evaluations except via
(2), which trades exactness for a local model and is only valid for mildly-nonlinear inputs.

### 3.3 Rigor spine — the ladder is a chain of monoid homomorphisms

The nesting claims of P3 become concrete theorems: each is a *hom* from a finer `Contribution`
monoid onto a coarser one, plus agreement of `summarize` in the appropriate limit.

* **T1 — Cumulant additivity** (foundation, Willink eq. 3). For independent contributions,
  `κ_r(combine a b) = κ_r a + κ_r b`. Proven over `ℝ`.
* **T2 — GUM = Willink at κ₄=0.** `κ₂ : Cumulants → R` is a monoid hom; when all `wᵢ = 0` the
  Willink shape `γ_Y = 0`, its Pearson closure is the normal, and `summarize` reduces to GUM's
  Gaussian interval. ⟹ `gum` is the `κ₂`-projection of `willink`.
* **T3 — Willink = linearized-SSPRC truncated at κ₄.** `cumulantsOf : DeviationPDF → Cumulants`
  (convolution ↦ cumulant addition, T1) is a monoid hom; for a *linear* model the SSPRC deviation
  distributions have exactly `κ₂ = Σcᵢ²uᵢ²`, `κ₄ = Σcᵢ⁴wᵢ`. ⟹ `willink` is the truncated-cumulant
  projection of linearized `ssprc`; the Pearson step is the only approximation.
* **T4 — SSPRC reference = mean for affine models.** `R = f(E(X))` equals `E(Y)` when `f` is affine;
  the gap `E(Y) − R` is the nonlinearity signature (the thing SSPRC captures and the linearized
  methods miss). Proven over `ℝ`.
* **T5 — Convolution ↔ all-order cumulant addition.** The mathematical bridge underpinning T3,
  stated once and reused.

These five theorems *are* the deliverable's claim to rigor. They also give free cross-validation:
on any model where all `T`-hypotheses hold, the three methods must agree numerically.

### 3.4 Correlation (honest scope)

The `combine` monoid law encodes **independence**. GUM (clauses 5.2.x) and Willink §4.4 handle
certain correlations by *re-parameterizing* — a shared influence quantity becomes its own input,
restoring independence of the rest. SSPRC cannot handle correlated inputs at all (paper §4).
Plan: make `Independent inputs` a required argument (T-level precondition); provide the shared-
influence re-parameterization as a *constructor* on the input list; leave genuine covariance
propagation (Willink eqs. 17–21) as a documented future extension.

---

## 4. Area 2 — Numerical adequacy of the floating-point representation

### 4.1 The principle, precisely

> **Numerical adequacy.** A floating-point representation (`FP32`) is *adequate* for a science
> model `f` given input ranges/uncertainties iff evaluating `f` in that representation loses no
> information that is **significant at the scale of the input uncertainties**.

"Significant at the scale of the input uncertainties" is what makes this checkable and what ties
it to Area 1: the yardstick is `cᵢ·uᵢ` and `InputDist.support`, both already carried.

### 4.2 Sub-properties, each grounded in existing TorchLean lemmas

TorchLean's float layer is a native **Flocq port** (`NN/Floats/NeuralFloat/*`). The foundational
lemmas we need are proven; the adequacy theorems are thin wrappers we author on top.

| Sub-property | Meaning | Grounding lemma (**exists**) | To build |
|---|---|---|---|
| **No absorption / swamping** | in `a ⊕ b`, neither operand's uncertainty falls below ½ulp(sum) | `neuralRound_nearestEven_point` (`Rounding/Order.lean:227`) + `neuralUlp_le_abs_of_generic` (`Analysis/Ulp.lean:112`) + `neuralUlp_mono_pos` (`Ulp.lean:138`); already used this way at `Error/Addition.lean:75` | the absorption theorem `\|round₃₂(x+y) − x\| ≤ …` under a magnitude gap |
| **Exact cancellation, amplified uncertainty** | `a ⊖ b`, `a≈b`: subtraction is *exact* (no rounding) but *relative* uncertainty blows up | FLX Sterbenz `neural_generic_format_FLX_sterbenz` (`Analysis/Sterbenz.lean:146`) + FLT↔FLX transport (`Error/Multiplication.lean:157`); **FP32/FLT instance ✅ Stage 3.2** (`neural_generic_format_FLT_sterbenz`, `FP32.sub_exact_of_sterbenz`) | ~~FP32/FLT Sterbenz instance~~ (done); the relative-amplification bound (UQ-level, from `cᵢ`) |
| **Bounded accumulated rounding error** | total FP noise over the whole evaluation ≤ a fraction of the output uncertainty | `(1+δ)` model `neural_round_relative_error_ulp` (`Error/Bounds.lean:139`); FP32 `u=2⁻²⁴` `round_relative_error_of_normal` (`FP32/Error.lean:79`); per-op `add/sub/mul/div_abs_error` (`FP32/Error.lean:99–148`) | DAG-composition of per-op bounds; comparison to `u_Y` |
| **Adequate dynamic range** | no overflow/underflow on the input box | `RInterval` sound enclosures (`Interval/Quantized.lean`), `minNormal=2⁻¹²⁶`, `ieeeMaxFinite` (`FP32/Core.lean:150,160`) | range check vs. `InputDist.support` |
| **No serialization loss** | a magnitude written as decimal text and read back is the *same* magnitude — and where it is not, it moved the way its role permits | `Decimal.showExact?` (the check is the specification), `LowerBound.roundedDown_safe` / `UpperBound.roundedUp_safe` (`Bounds`/`Decimal`), `Adequacy.Serialization.displacement_eq_zero_of_exact` — **✅ done** | carrier instances beyond binary64 (a binary32 one is 9 significant digits and the same code); a scientific-notation renderer if a magnitude below ≈`10⁻²⁹⁰` ever needs writing |

Half-ULP workhorse already available: `FP32.round_abs_error : |round₃₂ x − x| ≤ eps₃₂ x`
(`FP32/Error.lean:73`), `eps₃₂ x = ulp₃₂ x / 2`. Error-free transforms
(`FP32.add_residual_isRepresentable`, `FP32/Error.lean:111`) give exact residuals for
compensated-summation reasoning if we want tighter accumulation bounds.

**The fifth row is graded differently from the other four, and that is the point of having it.**
The first four are roundings the carrier *forces*: the width is what it is, half a ulp is the
price of the operation, and the right question is whether the loss is invisible at the scale of
`u` — which is §4.1's principle exactly. The fifth is a rounding at the **edge** of the
evaluation, where the digits are *chosen*, and there the same question gives the wrong answer
three times over. The error is avoidable, so spending budget on it buys nothing. It is
systematic rather than dispersive — identical on every read of that value, forever — so
`u_c² = Σ cᵢ²u(xᵢ)²` is the wrong machine for it and a budget that absorbed it would be
reporting a bias as a dispersion. And for a magnitude with a **role**, it is not a size question
at all: a floor written up by one part in a million has stopped being a floor, and no tolerance
reaches that, because what broke is the direction. So the criterion is exactness, with one
exception granted to bounds — a shortening that gives slack away still holds — and the verdict
type has four outcomes rather than a Boolean for precisely that reason
(`Adequacy.Serialization.SerializationVerdict`).

It is deliberately **not** a counter in `AdequacyReport`. That report accumulates sites found
while a model runs at the `Adequacy` carrier, and that carrier never serializes: the boundary is
crossed before it is seeded and after it has finished. A third counter there would let an
evaluation that is adequate throughout be reported inadequate for something that happened before
it started, and would have `merge` combine boundary crossings that never composed.

### 4.3 Numerical adequacy *as a carrier* (the PKC-idiomatic move)

Because every model is WO1 over `[NumCarrier α]`, we get the adequacy analysis **for free** by
instantiating at a new analysis carrier — no model rewrite (P1):

```lean
structure Adequacy (R : Type) where
  value       : R
  range       : RInterval        -- sound magnitude enclosure (formatRounder binaryRadix fexp32)
  uncertainty : R                -- uncertainty contribution carried to this point
  report      : AdequacyReport   -- accumulated absorption/cancellation sites + margins

instance : NumCarrier (Adequacy R) where
  add x y := -- range via RInterval.add (sound: Interval/Quantized.lean mem_add:123);
             -- check swamping: if min(x.unc, y.unc) < eps₃₂ near range.absMax → record violation
  sub x y := -- Sterbenz ⇒ exact; check a≈b ⇒ record relative-amplification warning
  mul x y := …
  …
```

Instantiating a model at `Adequacy` runs it over **sound** interval semantics
(`RInterval` soundness theorems) with ulp-tracking and emits a certificate:
*"no significant absorption on this input box"* or a concrete witness site. Two rigor levels:

* **Runtime certificate** (the carrier above): decidable check over sound semantics — tractable,
  the pragmatic first target.
* **Symbolic theorem** (`ℝ` + FP32): `∀ inputs ∈ box, NoAbsorption f` proven once per model —
  strongest, per-model effort, built on the §4.2 absorption theorem. Aspirational capstone.

### 4.4 The coupling to Area 1

`InputDist.support` supplies the input box the `RInterval` carrier propagates; `cᵢ·uᵢ` (from the
autograd `extract` of Area 1) supplies the significance scale for absorption. **One descriptor,
both areas.** A model that is UQ-analyzed is *simultaneously* adequacy-checkable with no extra
inputs — which is the deep reason to build these together rather than as two features.

### 4.5 Rigor spine — adequacy soundness

* **A1 — Absorption theorem** (to build; levers in §4.2): quantifies swamping under a magnitude gap.
* **A2 — FP32 Sterbenz** (to build; transport from FLX): exact subtraction in the near-equal regime.
* **A3 — Adequacy soundness capstone:** if the `Adequacy` carrier reports *no* violation on box `B`,
  then for all inputs in `B` the `FP32` measurand's uncertainty equals the `ℝ` measurand's
  uncertainty up to a proven bound (`RInterval` soundness ∘ per-op `abs_error` ∘ A1). This is the
  theorem that makes "no information loss" a *proof*, not a heuristic. Realized per-site (A3
  `verdict_sound`); the universal-box form is Stage 3.1.

### 4.6 The verified TorchLean FP32 / RInterval / carrier API surface (2026-07-15)

Before implementing Stage 3 we swept the two dependency trees (PKC core spine; the TorchLean
`combined` package under `.lake/packages/TorchLean`) for the exact signatures the adequacy layer
builds on. The findings below are what the Stage-3 design and sub-stages 3.1–3.3 rest on — recorded
here because they are non-obvious and drive the deferral decisions.

**Bottom line.** TorchLean's `FP32`/Flocq layer is a **`noncomputable` ℝ-level specification**, not
an executable float, and there is **no FLT/FP32-level Sterbenz** — only FLX. Both facts drove the
architecture: the executable carrier runs over Lean `Float`; the `ℝ` rigor is a self-contained grid/
FLX model *grounded* in (not built on) the TorchLean lemmas, whose statement shapes are exactly right.

* **A — PKC carrier classes.** `NumCarrier` (`Paradigm/NumCarrier.lean:37`) `extends Zero One Add Sub
  Mul Div Min Max, MathCarrier, Coe Nat` — 10 parents, **no own fields** (so `instance : NumCarrier
  Adequacy := {}` closes once the parents are supplied; note `Coe Nat`, not `NatCast`). `MathCarrier`
  (`QuantityFunction.lean:71`) is a **flat 10-field** class (`exp log sin cos sinh cosh tanh sqrt abs`
  + `pi`). `instance : MathCarrier Float` exists; core does **not** declare `NumCarrier Float` (only
  the Torch lib does) — hence `Uncertainty.Carriers`.

* **B — FP32 rounding + error lemmas** (namespace `TorchLean.Floats.FP32`, `NN/Floats/FP32/`).
  `FP32 := NF binaryRadix fexp32 rnd32` where `fexp32 = FLTExp (−149) 24` (FLT, gradual underflow, **no
  upper bound**); an `FP32` is a wrapped real `⟨v⟩`. All `noncomputable`: `round₃₂ ulp₃₂ eps₃₂ : ℝ → ℝ`
  (`Notation.lean`, `eps₃₂ x = ulp₃₂ x / 2` confirmed). Usable and proven, exactly the shapes we want:
  `round_abs_error (x) : |round₃₂ x − x| ≤ eps₃₂ x` (`Error.lean:73`); per-op
  `{add,sub,mul,div}_abs_error (a b) : |(a∘b).val − (a.val∘b.val)| ≤ eps₃₂ (a.val∘b.val)`
  (`Error.lean:99–148`); `round_relative_error_of_normal` (unit roundoff `2⁻²⁴`, `Error.lean:79`);
  `add_residual_isRepresentable` (an EFT, `Error.lean:111`).

* **C — Absorption levers.** `neuralRound_nearestEven_point (x)` (`Rounding/Order.lean:227`) — the
  rounded value is *globally nearest* among representables; `neuralUlp_le_abs_of_generic`,
  `neuralUlp_mono_pos` (`Analysis/Ulp.lean:112,138`). These realize A1 on the real binary32 grid (the
  self-contained grid model localizes them; `Fp32Grounding` re-exports `round_abs_error`).

* **D — Sterbenz.** Originally **only** `neural_generic_format_FLX_sterbenz (prec) (0<x)(0<y)(x≤2y)(y≤2x) …`
  (`Analysis/Sterbenz.lean:146`, `FLXExp prec` — fixed precision) and its one-sided helper. **Stage 3.2's
  TorchLean PR adds the FLT/FP32 lift** (`Analysis/SterbenzFLT.lean`): `neural_generic_format_FLT_sterbenz`
  (regime split — FIX grid on the subnormal side, FLX transport on the normal side, plus the helper
  `neural_generic_format_FLX_to_FLT_of_normal`) and the corollary `FP32.sub_exact_of_sterbenz` /
  `round32_sub_exact_of_sterbenz` (`FP32/Sterbenz.lean`), grounded in PKC via `Fp32Grounding`.

* **E — Sound intervals** (namespace `TorchLean.Floats.Interval`, `Interval/Quantized.lean`).
  `structure RInterval (lo hi : ℝ)`; `x ∈ I ↔ lo ≤ x ≤ hi`. Operations take a `Rounder` (outward
  rounding; canonical `formatRounder`, `noncomputable`). Soundness: `RInterval.mem_{add,sub,mul}
  (hx : x ∈ A)(hy : y ∈ B) : x∘y ∈ RInterval.∘ R A B` (`:123,133,147`). This is the range-analysis
  backbone for the Stage 3.1 capstone and Stage 3.4 support-box propagation.

* **F — computability.** *Everything* FP32/Flocq is `noncomputable` (`rnd32`, all `round₃₂/ulp₃₂/eps₃₂`,
  every `NF` arithmetic instance). The executable model is the **separate** `IEEE32Exec` structure,
  connected to `FP32` only by bridge lemmas (`Bridge/FP32*`, `RuntimeApprox`), not defeq. ⟹ the runtime
  host-`Float` `Adequacy` carrier is inherently uncertifiable (opaque FFI). **✅ Stage 3.3 (done):** the
  certified executable check runs on `IEEE32Exec` instead — a second TorchLean PR adds `IEEE32Exec.ulpExp?`
  (bit-level ULP query, its answers proved `= ulp₃₂`; it answers on exactly the finite fragment) and `absorbs` (float32 sum unchanged),
  proved sound against `round₃₂` (`round32_add_eq_left_of_absorbs`), re-exposed in PKC as
  `ExecBridge.exec_verdict_sound`. The residual `Float32 ↔ IEEE32Exec` step is an upstream *assumption
  typeclass* (`RuntimeFloat32MatchesIEEE32Exec`), not an axiom — the irreducible hardware trust boundary.

> **Note — Sterbenz, and the `FLX`/`FLT`/`FP32` formats (terminology used throughout Stage 3).**
>
> *Sterbenz* is **Pat H. Sterbenz**, author of *Floating-Point Computation* (Prentice-Hall, 1974), a
> foundational text on floating-point error analysis. **Sterbenz's lemma:** if two floating-point
> numbers `x`, `y` are within a factor of two of each other (`y/2 ≤ x ≤ 2y`, both positive), then
> `x − y` is *exactly representable* in the same format — the subtraction incurs **zero rounding
> error**. Intuition: their exponents differ by at most one, so they lie on a common grid, and the
> difference — no larger than either operand — fits at that precision. This is the "no new rounding
> noise" half of the cancellation story; its treacherous companion is that the leading digits cancel,
> so any *pre-existing relative uncertainty* in the operands is amplified — catastrophic cancellation
> (the `relUnc_amplifies` side of A2). `flx_sterbenz` is exactly this lemma, proved over `ℝ`.
>
> *`FLX` / `FLT` / `FP32`* are **Flocq** format names (Flocq = the Coq floating-point library of
> Boldo & Melquiond; TorchLean's float layer is a native port, so the names carry over). They are
> three points on a realism spectrum — `FP32 ⊂ FLT ⊂ FLX`:
> * **`FLX`** — fixed precision, *unbounded eXponent*: no overflow, no underflow (an idealization).
> * **`FLT`** — fixed precision with a *minimum exponent* → gradual underflow (subnormals): what real
>   IEEE formats are (`FLTExp emin prec`).
> * **`FP32`** — IEEE-754 **binary32** (single precision), the one `FLT` instance TorchLean writes
>   `fexp32 = FLTExp (−149) 24` (24-bit significand; smallest subnormal `2⁻¹⁴⁹`).
>
> Why the distinction matters here: TorchLean proves Sterbenz **only for `FLX`** (group D above), the
> idealized unbounded-exponent format. Binary32 is an `FLT` format, so applying the theorem to the
> format that actually runs means lifting `FLX → FLT`, re-checking the argument survives the
> gradual-underflow region (it does — subnormals are uniformly spaced — but it is a real formalization
> step, not free). That lift is **Stage 3.2**, scoped as a TorchLean PR because it is a fact about
> TorchLean's Flocq port, not about PKC. Until then, `flx_sterbenz` is the honest self-contained `ℝ`
> analogue.

---

## 5. Module layout

Two Lake libraries over one `uncertainty/` source tree. `Uncertainty` (Stage 0) is Mathlib- and
TorchLean-free — it depends only on the core spine, and its module list is *explicit* so the
Stage-1 rigor modules can share the tree and namespace without being swept in. `UncertaintyRigor`
(Stage 1) carries `Ladder` (over Mathlib's `ℝ`) and `Sensitivity` (over TorchLean autograd); the
dependency expansion lands there, so `lake build Uncertainty` stays toolchain-only. Legend: ✅ built
& CI-checked, ▫ planned.

```
uncertainty/PropertyKindCalculus/Uncertainty/
  Carriers.lean         ✅ NumCarrier Float (so a WO1 kernel runs at Float; core lacks it)
  Sampling.lean         ✅ splitmix64 PRNG + inverse-CDF quantiles (shared by MCM & SSPRC)
  InputDist.lean        ✅ MomentData + InputDist; normal/uniform/triangular/arcsine as VALUES
  UncertainQuantity.lean✅ Quantity k R paired with its InputDist
  Mcm.lean              ✅ Monte Carlo reference propagator → (E(Y), u(Y))
  Combine.lean          ✅ gumStdUnc, willinkCombine, Pearson k₉₅/k₉₉ (eqs. 6/7)   [Area 1]
  EvidenceKinds.lean    ✅ the kind vocabulary of the two modules below:            [Area 1]
                           probability, coverageFactor, degreesOfFreedom, indicationCount — four
                           kinds, not one "dimensionless", because k = Φ⁻¹(1−p) and ν = n−1 put each
                           in the others' slots; plus the expansion / band-reading / cost-ratio laws
  Roles.lean            ✅ an estimate is NOT its dispersion, at the type level     [Area 1]
                           — the two live at the same kind (u of a length is a length), sit
                           adjacent in every evidence record, and are passed positionally, so
                           nothing but this stops them being exchanged: and exchanging them reads
                           a band of 42 u as 1/42, in the safe-looking direction. Estimate and
                           Dispersion are role wrappers exactly as Bounds' endpoints are, and the
                           algebra is what the distinction is FOR — no `Add` on a Dispersion,
                           because uncertainties combine in quadrature; no `Add` on an Estimate,
                           because a sum of estimates is a model; a deviation of two Estimates is
                           a plain value; and y ∓ U comes back as a LowerBound / UpperBound, so
                           Decimal's role-directed rounding applies to a coverage interval unsaid
  Evidence.lean         ✅ evidence ACROSS repeated measurements of one measurand   [Area 1]
                           (Combine is across contributors WITHIN one budget): GUM 4.2 Type A from
                           n indications, t-based coverage factor (COMPUTED — Lanczos lgamma, Lentz
                           continued fraction, bisection — with Table G.2 as its oracle),
                           Welch–Satterthwaite ν_eff over Budget's own contributions,
                           inverse-variance pooling — with Type B → Type A as a DISPLACEMENT,
                           since pooling a statement of ignorance would anchor the estimate forever
  Conformity.lean       ✅ ISO/IEC Guide 98-4 (JCGM 106): the guard band as an      [Area 1]
                           OUTPUT. Tolerance/acceptance limits as Bounds.lean roles (a band's sign is
                           fixed by the endpoint's role, so guarded acceptance cannot silently become
                           guarded rejection); coverage factor from a stated consumer's risk; that
                           risk from the two costs of being wrong; readBand — coverage, or a
                           systematic the model does not carry? THREE POSTERIORS, and choosing is a
                           reading of the evaluation: §9.5.2's Gaussian; the t at the evidence's own
                           ν (riskForFactorAt — a CHOSEN 4.5u band buys 5.4e-3 at ν=4, not 3.4e-6);
                           and GUM 4.3.7's rectangular, which is BOUNDED, so the Gaussian prices a
                           tail the evaluation denies and asks for a limit outside its own bracket
  Ssprc.lean            ✅ executable SSPRC: systematic sampling, separated        [Stage 2]
                           propagation, empirical deviation dists, discrete convolution (Float)
  Method.lean           ▫ UncertaintyMethod structure + monoid laws               [Area 1 core, deferred]
  Sensitivity.lean      ✅ autograd bridge: cᵢ via TapeBuilder reverse tape; 3.5 retarget onto the
                           soundness-covered total entry `Tape.backwardDenseFrom`  [Axis N, Stages 1+3.5]
  Ladder.lean           ✅ T1 (cumulant additivity), T2 (gum = willink|κ₄=0) / ℝ  [rigor, Stage 1]
  ConformityLadder.lean ✅ why an acceptance limit may TIGHTEN itself / ℝ         [rigor, Area 1]
                           A(u) = L − k·u is antitone in u and never passes L; and the risk AT
                           that limit is Q(k) — INDEPENDENT of u, since band and uncertainty
                           shrink together — so a rule built for a target risk runs it at every
                           stage of evidence, cold start included. The fleet's speedup is then a
                           corollary of a risk bound. Q abstract; both posterior families qualify
  Convolution.lean      ✅ Dist/conv over ℝ; T5 (convolution adds cumulants),      [rigor, Stage 2]
                           T3 (willink = linearized-ssprc|κ₄), T4 (affine R = E(Y)) — sorry-free
  QuasiExtensive.lean   ✅ Dybkær §13.5.2 over ℝ: additivity to within a NAMED     [rigor, Area 1]
                           per-join tolerance; |whole − Σparts| ≤ joins·t over a carving; §13.5.1
                           recovered exactly at t = 0 (both directions); volume-on-mixing refutes
                           every t < 4, so §13.5.3 reads as §13.5.2 with a tolerance the
                           conditions set; `join_within_tolerance` sources t from R18's Chebyshev
                           bound, so the tolerance is a coverage factor and not a choice
  Adequacy.lean         ✅ executable Adequacy NumCarrier over Float: ulp₃₂,        [Area 2, Stage 3]
                           swamping + cancellation checks, isAdequate verdict (Mathlib/Torch-free)
  Adequacy/Grid.lean       ✅ local uniform-grid rounding spec over ℝ (gridRound, OnGrid, ½-ulp bound)
  Adequacy/Absorption.lean ✅ A1 absorption (`absorb`) + converse (`resolve`) — half-ulp is the exact threshold
  Adequacy/Sterbenz32.lean ✅ A2 self-contained FLX Sterbenz (`flx_sterbenz`) + grid exactness + rel-unc amplification
  Adequacy/Soundness.lean  ✅ A3 verdict soundness (`verdict_sound`: flag ⟺ contribution lost) — sorry-free
  Adequacy/Fp32Grounding.lean ✅ binary32 grounding: re-exports TorchLean's (noncomputable) FP32 round/ulp/
                           per-op + sound RInterval lemmas the grid model localizes; + Stage-3.2 Sterbenz
                           grounding (`round32_sterbenz_exact`, `sub32_exact_of_sterbenz` over `fexp32`)
  Adequacy/DagBound.lean   ✅ A3′ universal capstone (Stage 3.1): FP32 `+`/`−` evaluation DAG (`evalFP32`
                           vs `evalExact`), forward-error accumulation (`dag_fp32_error_bound`), box
                           faithfulness (`dag_fp32_box_faithful`) + flag-free exactness — sorry-free.
                           Stage 3.8 adds `ExactRepresentable` (flag-freedom read off the exact `ℝ`
                           evaluation) and `flagFree_iff_exactRepresentable`: the same inputs, stated
                           where a reader can check them, and minimal because `round32` fixes exactly
                           the representable reals (`Fp32Grounding.round32_eq_self_iff`)
  Adequacy/RefinementBridge.lean ✅ which bridge carries which half of A3′ (§7's consolidation
                           decision, recorded and checked): the algebraic route (`CarrierRefinement`)
                           supplies the equation and hence the exactness regime, the metric route
                           (`*_abs_error`) supplies the bound. `refinementFixes_iff_exactRepresentable`
                           proves the two vocabularies agree; `toSpec_box_exact` is A3′'s exact case
                           in the bridge's own terms
  Adequacy/MeanBound.lean  ✅ the weighted mean at binary32: a `WeightedCarving` compiled into the DAG
                           (`meanExpr`), so `mean_fp32_within_errBound` bounds the grid-computed mean
                           against the exact real mean of the same data. The mean's one `div` node needs
                           TWO licenses — the rounded total and the exact total — and neither implies the
                           other (BOTH directions witnessed), so `specCarving` takes the spec-side one as
                           an argument. `licenses_agree_of_nonneg` is the repair: both failures need
                           cancellation, so nonnegative grid weights make the two conditions equivalent
                           (`fp32Round_add_ge` is the only fp fact it needs) — sorry-free
  Adequacy/ExecBridge.lean ✅ exec↔spec bridge (Stage 3.3): re-exposes the computable `IEEE32Exec`
                           ULP query `ulpExp?` (answers proved `= ulp₃₂`, `exec_ulp_grounds`) and absorption test `absorbs`
                           certified against `round₃₂` (`exec_verdict_sound`) — the computed verdict is the
                           specified one; over `ℝ`/`IEEE32Exec`, sorry-free
  Budget.lean              ✅ kinded GUM budget (Stage 3.4, Mathlib/Torch-free, **carrier-generic `[NumCarrier R]`**):
                           the three roles a naked `Float` conflates get kinds — input uncertainty `stdUncQ : Quantity kᵢ R`,
                           sensitivity `sensitivityQ : Quantity (kₒ/kᵢ) R`, contribution `contributionQ : Quantity kₒ R` gated by
                           `ProductKind kₛ kᵢ kₒ` (the GUM units cancellation as a typecheck), combined `combinedQ : Quantity kₒ R`
                           — one budget × any carrier: `ℝ` (prove laws), `Float` (run), `Adequacy` (adequacy-check the quadrature)
  BudgetDag.lean           ✅ kinded ×/÷ budget DAG (residual 2, Mathlib/Torch-free, carrier-generic): `BudgetExpr R k`
                           carries a `ProductKind`/`QuotientKind` witness in every `mul`/`div` node (heterogeneous input
                           kinds; an ill-kinded tree is unwritable); `valueQ` / `propagateQ` (per-node GUM two-term
                           quadrature; the division's `(|y|·u_b)/|b|` term goes through the transposed core-spine witness
                           `QuotientKind.toProductKind`) / `contribsQ` (per-leaf contributions flattened to the root kind);
                           `EstimateQ` + its `InputDist` seeding
  BudgetDagLaws.lean       ✅ the DAG law layer over `ℝ` (scoped `instNumCarrierReal`): the collapse capstone
                           `propagateQ_unc_eq_combinedQ` — the node-wise threaded quadrature telescopes *exactly* to the
                           flat `combinedQ` of `contribsQ` (leaf nonnegativity the only hypothesis; totalized `x/0 = 0`
                           needs no divisor side condition) + the relative-quadrature textbook corollaries — sorry-free
  Adequacy/Significance.lean ✅ Axis-U coupling (Stage 3.4): seeds the (Float) `Adequacy` carrier from the descriptor
                           (`ofInputDist`); `analyzeQ (h : ProductKind kₛ kᵢ kₒ)` instantiates one carrier-raw WO1 kernel at
                           both `TapeBuilder .scalar` (for `cᵢ`) and `Adequacy` (for the verdict) and folds them into a
                           kind-typed `CouplingResultQ kₒ` (contributions + combined = `Quantity kₒ`; no naked field swap)
  Adequacy/Serialization.lean ✅ the fifth sub-property (§4.2): the rounding at the EDGE of an evaluation, where a
                           magnitude crosses to decimal text and back. `SerializationVerdict` has four outcomes because
                           the same text against the same magnitude is adequate or not depending on the ROLE it plays
                           (`verdictOfValue` / `verdictAtLower` / `verdictAtUpper`); `displacement` reports the crossing
                           in the budget's own terms as *evidence*, never as a tolerance, and
                           `displacement_eq_zero_of_exact` is the theorem that an exact crossing costs nothing.
                           Stage 0 — the whole content is `PropertyKindCalculus.Decimal`'s reader against the value
  Experiments/PRSimulation.lean ✅ direct P↔R simulation, closed (Stage 3.6): the vectorization homomorphisms
                           (`mulSpec_ofVecT`/`addSpec_ofVecT`, `Shape` induction); the value-free `.ok` totality of
                           `backwardDenseFrom` via the `AccShapeAligned` fold invariant under `BackwardShapeWF`
                           (shape-total closures — provided, constructor by constructor, by the eager
                           `Tape.leaf`/`add`/`mul`); `ForwardSim` inhabited by compiled tapes; and the endpoint
                           `direct_PR_soundness_compiled` = the `Γ`-prefix `ArrCorr` corollary of the Stage-3.5
                           theorem — sorry-free, no fold re-derivation (the adjoint enters only through 3.5)
  Experiments/EagerProvenance.lean ✅ eager-tape provenance, closed (Stage 3.6 addendum): `EagerBuilds g x t` =
                           the tape the eager constructors build for graph `g` (leaves = `addLeaves`, one
                           `Tape.add`/`sub`/`mul` call per node); `backwardDenseFrom_eager_eq_compiled` — that tape's
                           reverse pass computes exactly the compiled tape's (compiled dense folds by the upstream
                           accumulation bridge, eager sparse folds by `addGradAll_toAnyArray_single`, the two
                           context updates identified through flatten-injectivity + the §2 homomorphisms,
                           push-invariance restricting the extended loop to the prefix — never re-deriving the
                           fold); hence `direct_PR_soundness_eager`: the fderiv endpoint on the eagerly built
                           tape itself — sorry-free
  Allocation.lean          ✅ sensitivity-driven sample allocation (Stage 4, Mathlib/Torch-free): `wᵢ=|cᵢ|·uᵢ`
                           contributions → drop negligible inputs (`dropRatio`) → largest-remainder split of the
                           budget (`Σ Nᵢ = total` exactly) → a pure `List Nat` feeding `Ssprc`/`SsprcBatched` `ns`.
                           `#guard`-checked (unlike CudaT) in `DegenhardtAllocation`
  McmBatched.lean          ✅ batched Monte Carlo propagator (Stage 4, TorchLean `CudaT`): all `n` joint
                           draws in ONE launch — MCM samples the joint directly, so unlike SSPRC there is
                           nothing to hold fixed and nothing to iterate over. `sampleColumns` reproduces
                           `Mcm.run`'s interleaved PRNG order, so the parity harness compares two
                           evaluations of one experiment rather than two experiments. Verified by the
                           `apps/` exe `mcm_batched_parity`, which CI runs
  SsprcBatched.lean        ✅ batched SSPRC propagator (Stage 4, TorchLean `CudaT`): runs the WO1 kernel at
                           `CudaT (Shape.dim Nᵢ .scalar)` — input i's Nᵢ systematic samples as one batch
                           tensor, one launch per input (a GPU kernel per op under `-K cuda`, the portable CPU
                           float32 stub otherwise), `E(Aᵢ)`/`Var(Aᵢ)` via `Buffer.reduceMean`; `E(Y)`/`u(Y)`
                           combine as in `Ssprc.run`. In the small lib `UncertaintyBatch`; CudaT can't be
                           `#guard`ed at build (§6), so it is verified by the `apps/` exe `ssprc_batched_parity`
```

Stage 3.2 also adds two **TorchLean** modules (upstream PR, branch `flt-fp32-sterbenz` off `upstream/main`,
merged into the fork's `combined`): `NN/Floats/NeuralFloat/Analysis/SterbenzFLT.lean`
(`neural_generic_format_FLT_sterbenz` + the `FLX→FLT`-normal helper) and `NN/Floats/FP32/Sterbenz.lean`
(`round32_sub_exact_of_sterbenz`, `FP32.sub_exact_of_sterbenz`). Stage 3.3 adds one more **TorchLean**
module (second upstream PR, branch `ieee32exec-ulp` off `upstream/main`, merged into `combined`):
`NN/Floats/IEEEExec/Bridge/FP32/Ulp.lean` (`IEEE32Exec.ulpExp?` + `neuralBpow_eq_ulp32_of_ulpExp?_eq_some`,
`absorbs` + `round32_add_eq_left_of_absorbs{,_of_isFinite}`). PKC pins TorchLean at that `combined` rev. (Note: upstream
`lean-dojo/TorchLean` main has since reorganized the whole `IEEEExec` tree; both PRs branch off the
pre-reorg base that the fork's `main`/`combined` still track, so opening them against current upstream
requires porting to the new `Semantics/`/`Rounding/` layout.)

Stage-3 modules split by dependency exactly as Stages 1–2: `Adequacy.lean` (the executable carrier,
`Float`) lives in the Mathlib/Torch-free `Uncertainty` library (Stage 0 stays 18 jobs, toolchain-only);
`Adequacy/*` (the `ℝ` rigor + the TorchLean grounding) lives in `UncertaintyRigor`. The carrier is the
`Float` *mirror* of the `ℝ` grid spec, exactly as `Ssprc` mirrors `Convolution`.

### 5.1 Worked examples (`examples/` tree, library `UncertaintyExamples`)

Each example reproduces a **headline number from a source paper** as a `#guard`, so the library
building under CI is what makes the claim true rather than asserted (the project's reflection-
tests discipline). Kept in the `examples/` source tree so no *library* module carries `#eval`.

```
examples/PropertyKindCalculus/UncertaintyExamples/
  DegenhardtFictive.lean  ✅ Degenhardt §3.1  Y=(X₁+X₂²)X₃ : MCM E(Y)/u(Y) + GUM cross-check
                             → R=11.25, MCM 11.60/1.70, GUM u_c=1.662 (non-linearity gap shown)
  WillinkGaugeBlock.lean  ✅ Willink Table 4 gauge block : cumulants method
                             → u_Y=33.4nm, γ_Y=0.124, h₀.₉₉=87.6nm (vs GUM's 93nm)
  DegenhardtSensitivity.lean ✅ Stage-1 autograd cᵢ over the WO1 fictive kernel: reproduces the
                             hand-supplied [5, 5, 2.25] and GUM u_c=1.662 (TorchLean-backed)
  LadderNesting.lean      ✅ T1/T2 (gum = willink|κ₄=0) applied over ℝ + Float shadow of the
                             collapse; #print axioms shows sorry-free (Mathlib-backed)
  DegenhardtSsprc.lean    ✅ Stage-2 SSPRC run: E(Y)=11.5875 / u(Y)≈1.686 at 300 evals (~67× fewer
                             than MCM's 20000); recovers the non-linear mean GUM misses; runConv cross-check
  DegenhardtAllocation.lean ✅ Stage-4 sensitivity-driven `Nᵢ` allocation: w=[1.00,1.30,0.28] → alloc 300
                             = [117,151,32] (X₂ dominant, X₃ minor); drop demo; SSPRC on the allocated ns
                             reproduces 11.5875/1.686 even at a 120-eval (60%-cut) budget — all `#guard`
  WaterCloudModel.lean    ✅ Stage-4 capstone, KINDED end-to-end (SMM ConfigKinds/AvsKinds discipline):
                             one WO1 Water-Cloud-Model forward σ⁰=a·ndvi·(1−τ)+τ·(c·mv+d), τ=exp(−2b·ndvi),
                             with 9 role-named kinds + witnessed algebra, calib constants (a,c,d,2) as
                             kinded quantities in a `WcmConfig` structure (sole numerals), every variable a
                             `Quantity k`/`UncertainQuantity k`, `.magnitude` only at the emission boundary,
                             `#check_failure` kind-safety probes. Through the whole pipeline — forward
                             (0.047089), autograd Jacobian=closed forms 6 dp ([0.0861,0.0206,0.0129]) via
                             kinded `exp`, GUM u_c≈0.002847, SSPRC recovers the +0.0001 exp-curvature mean
                             offset, allocation ranks soil moisture dominant & drops the canopy rate (alloc
                             300=[197,91,12]); self-contained; all `#guard`
  SsprcNesting.lean       ✅ T3/T4/T5 applied over ℝ (willink cumulants (41,−1186), affine ⇒ E(Y)=R);
                             #print axioms shows sorry-free (Mathlib-backed)
  AdequacySwamping.lean   ✅ Stage-3 executable Adequacy carrier: `bias + x` swamped under a 10⁸
                             accumulator / clean under 100; `a − b` catastrophic-cancellation flagged / clean
                             separated — one WO1 kernel per hazard, checked for free (Float, #guard)
  AdequacyLadder.lean     ✅ Stage-3 A1/A2/A3 theorems applied to concrete values over ℝ (round₈(80+1)=80;
                             3−2 of FLX 24 is FLX 24; the verdict biconditional); #print axioms sorry-free
  AdequacyDag.lean        ✅ Stage-3.1 A3′ capstone on concrete DAGs (3-input accumulator, add/sub variant,
                             5-input tree): box faithfulness + flag-free exactness; #print axioms sorry-free
  AdequacySterbenz32.lean ✅ Stage-3.2 A2 at the genuine binary32 format: round₃₂(u−v)=u−v and
                             (a−b).val=a.val−b.val for near-equal representable FP32; sub32 bound → 0;
                             ties to the FLX 24 fact; #print axioms sorry-free (TorchLean-backed)
  AdequacyExecBridge.lean ✅ Stage-3.3 exec↔spec bridge: `ulpExp?`/`absorbs` RUN on IEEE32Exec bit patterns
                             (#guard: ulp=4 at 2²⁵, ulp=8 at 10⁸; 1 absorbed, 4/8 survive) + `exec_verdict`
                             proving the verdict = round₃₂ spec; #print axioms sorry-free (TorchLean-backed)
  AdequacyCoupling.lean   ✅ Stage-3.4 kind-typed budget: one `analyzeQ` on the Degenhardt descriptors gives kinded
                             contributions cᵢ·uᵢ=[1.0,1.30,0.28] at `measurandY` whose quadrature `combined` reproduces the
                             GUM u_c=1.662359 EXACTLY; `#check_failure` probes show the conflations (sensitivity↔uncertainty,
                             heterogeneous quadrature, field swap) are type errors; a 10⁸-accumulator swamps a contribution
                             (1 absorption) + `verdict_sound` at s=1; the same `combinedQ` run at R:=Adequacy adequacy-checks
                             its own quadrature (clean 0 / swamped 1); #print axioms sorry-free
  AutogradDirectSim.lean  ✅ Stage-3.6 closure probe: the homomorphisms at a 3-vector shape; the compiled
                             product graph x₀*x₁ with `direct_PR_soundness_compiled` + its inhabited `ForwardSim`;
                             an eager two-leaf/`mul` tape with `BackwardShapeWF` discharged constructor by
                             constructor; `EagerBuilds` witnessing that tape + `direct_PR_soundness_eager` on it
                             (the endpoint with no compilation involved); #print axioms pins = classical trio only
  BudgetDagDensity.lean   ✅ residual-2 closure probe: block density ρ = m/((l·w)·h) — five distinct kinds through one
                             ×/÷ budget (untypeable under `analyzeQ`'s single shared input kind); #guards reproduce the
                             hand-computed GUM (ρ=2500, contributions [1.0, 2.5, 5.0, 25.0], u_c=√657.25≈25.637) and the
                             Float shadow of the collapse; #check_failure probes (operand swap, heterogeneous quadrature,
                             kind-permuted builder); the applied ℝ collapse + capstone axiom pin = classical trio
  DegenhardtAfm.lean      ▫ Degenhardt §3.2 AFM indenter PAF, ~70× efficiency (Stage 4/scale)
  WillinkAsymmetric.lean  ▫ Willink §5 asymmetric input (κ₃) + Type-A t-cases (Stage 1)
```

TorchLean surface newly imported at Stage 1+ (dependency expansion, explicitly in-scope):
`NN.API.Public.Autograd` / `NN.Runtime.Autograd.TorchLean.Autodiff` (grad/hessian/hvp),
`NN.Floats.FP32.{Error,Notation}` + `NN.Floats.NeuralFloat.*` (ulp/round lemmas),
`NN.Floats.Interval.Quantized` + `Rounders` (`RInterval`, `formatRounder`),
and FFT kernels under `NN/Runtime/Autograd/Engine/Cuda/Ops/*` for SSPRC's convolution (§3.1).

---

## 6. Staged plan (each stage is shippable, testable, rigor-first)

* **Stage 0 — Types + reference numbers. ✅ DONE (built & CI-checked).** `Carriers` (NumCarrier
  Float), `Sampling`, `InputDist`/`UncertainQuantity`, `Mcm`, `Combine` (GUM + Willink). Two
  paper-grounded examples pass as `#guard`s: Degenhardt's fictive `Y=(X₁+X₂²)X₃` (MCM
  E(Y)≈11.60, u(Y)≈1.70 vs ground truth 11.5875/1.691; GUM u_c=1.662 showing the non-linearity
  gap) and Willink's gauge block (u_Y=33.4nm, γ_Y=0.124, h₀.₉₉=87.6nm). *Exit met:* numbers
  reproduce both papers. `lake build Uncertainty UncertaintyExamples` is green.

* **Stage 1 — Linearized methods + autograd + nesting proofs. ✅ DONE (built & CI-checked).**
  `Ladder.lean` proves **T1** (cumulant additivity, via the `Cumulants` commutative monoid) and
  **T2** (`gum = willink|κ₄=0`: `willinkCumulants_kappa2` = the κ₂-projection is GUM, and
  `gum_eq_willink_of_normal` = the all-Gaussian Willink 95% half-width equals `1.96·u_c`) over `ℝ`.
  `Sensitivity.lean` wires `TapeBuilder`→`cᵢ` via TorchLean's reverse-mode tape (Route B: the WO1
  kernel is instantiated at `α := TapeBuilder .scalar`, no rewrite; `TapeM.backwardScalar` reads
  the coefficients). Both live in the new `UncertaintyRigor` Lake library. *Exit met:* T2 is a
  theorem (`#print axioms` → `[propext, Classical.choice, Quot.sound]`, no `sorryAx`); autograd
  reproduces the fictive model's `[5, 5, 2.25]` to machine precision and its GUM `u_c = 1.662359`
  exactly; the Willink Pearson interval reproduces Table 4 (Stage-0 `WillinkGaugeBlock`).
  Deferred to later stages: the full `UncertaintyMethod` structure and T3–T5 (they need SSPRC,
  Stage 2); `hᵢ`/`hvp` nonlinearity gauges (Stage 2 surrogates).

* **Stage 2 — SSPRC pipeline. ✅ DONE (built & CI-checked).** `Ssprc.lean` (executable, `Float`)
  realizes systematic sampling (`Pⱼ = (j−0.5)/Nᵢ` via the shared inverse-CDF), separated propagation
  (`aᵢⱼ = f(…,xᵢⱼ,…) − R`), the empirical per-input deviation distributions, and their **discrete
  convolution** (the FFT of the paper is the O(n log n) optimization of this same operation, deferred).
  `Convolution.lean` (over `ℝ`) proves the three rigor rungs sorry-free: **T5** (`kappa2_conv`/
  `kappa4_conv`/`cumulantsOf_conv` — convolution *adds* cumulants, proved from the joint-expectation
  factorization, not defined as addition), **T3** (`cumulantsOf_combinedDeviation` — the linearized
  SSPRC's convolved deviation has exactly the Willink combined cumulants, closing
  `GUM ⊂ Willink ⊂ SSPRC`), and **T4** (`combinedDeviation_isCentered`/`mean_combinedDeviation` —
  affine ⇒ `E(Y) = R`; the gap is `Σcᵢ·E(Zᵢ)`). *Exit met:* on the fictive example SSPRC recovers
  `E(Y) = 11.5875` (incl. the non-linear `+0.3375` GUM misses) and `u(Y) ≈ 1.686` from **300**
  evaluations vs the reference Monte Carlo's 20 000 (**~67×** fewer), and T3 links it to Willink as a
  theorem (`#print axioms` → `[propext, Classical.choice, Quot.sound]`). Examples `DegenhardtSsprc`
  (numeric) and `SsprcNesting` (T3/T4/T5 proof terms). Deferred (optional, not on the exit path): the
  full `UncertaintyMethod` structure, the continuous DDE reconstruction for the *shape*, an FFT
  convolution, and the `hvp` Taylor-surrogate nonlinearity gauge (§3.2 item 2).

* **Stage 3 — Numerical adequacy. ✅ DONE (built & CI-checked).** The executable `Adequacy` carrier
  (`Adequacy.lean`, `Float`, Mathlib/Torch-free) is a `NumCarrier`, so any WO1 `[NumCarrier α]` model
  instantiates at it and emits an adequacy report with **no rewrite** (P1). Its `add` runs a swamping
  check (the smaller-magnitude operand's uncertainty against half the sum's `ulp₃₂`) and its `sub` a
  catastrophic-cancellation check (relative uncertainty ≥ 100%). The `ℝ` rigor sits in `Adequacy/*`:
  **A1** (`absorb`, with converse `resolve`) proves a sub-½-ulp perturbation of a grid value is
  absorbed — and half a ulp is the *exact* threshold; **A2** (`flx_sterbenz`, self-contained over an
  explicit FLX mantissa/exponent model, the analogue of TorchLean's `neural_generic_format_FLX_sterbenz`)
  proves near-equal subtraction is exact, plus `relUnc_amplifies` for the relative-uncertainty dual;
  **A3** (`verdict_sound`) proves the biconditional *carrier-flag ⟺ contribution numerically lost* —
  sound *and* complete. `Adequacy/Fp32Grounding.lean` re-exports the genuine (but `noncomputable`)
  TorchLean binary32 `round₃₂`/`ulp₃₂`/per-op and sound `RInterval` lemmas the grid model localizes.
  *Exit met:* A3 is a theorem (`#print axioms` → `[propext, Classical.choice, Quot.sound]`, no `sorryAx`,
  verified in `AdequacyLadder`); the flagged/clean pair is a reflection test — `AdequacySwamping`
  flags `10⁸ ⊕ (1±1)` swamped (½·ulp₃₂(10⁸)=4 > 1) and certifies `100 ⊕ (1±1)` clean, and flags a
  near-equal subtraction while certifying `3−1` separated — both indexed in `UncertaintyExamples.lean`.
  Stage 0 stays 18 jobs (toolchain-only).

  Deferred to the sub-stages below (honest scoping, driven by the verified TorchLean API surface in
  §4.6): the *universal* soundness capstone over an arbitrary model/box, the lift of A2 to the FLT
  format binary32 actually uses, and an executable↔spec bridge for the `noncomputable` FP32 layer.

* **Stage 3.1 — Universal adequacy soundness (the capstone A3′). ✅ DONE (built & CI-checked).**
  `Adequacy/DagBound.lean` abstracts a WO1 model as a binary32 evaluation DAG (`Expr` over `+`/`−`) and
  interprets it two ways over TorchLean's *real* `FP32`: `evalFP32` (every node rounds) and `evalExact`
  (the exact `ℝ` reference). Composing the per-op half-ulp bounds
  (`Fp32Grounding.{add32,sub32}_within_half_ulp`, the genuine `FP32.{add,sub}_abs_error`) along the DAG:
  **`dag_fp32_error_bound`** is the forward-error accumulation (`|evalFP32 − evalExact| ≤ errBound`, the
  tree-sum of per-node `eps₃₂`); **A3′ = `dag_fp32_box_faithful`** proves that for *any* two inputs `ρ`,
  `σ` — every input in a box around `ρ` — the FP32 output *variation* reproduces the exact `ℝ` variation
  up to `errBound σ + errBound ρ`; and **`dag_fp32_box_exact_of_flagFree`** collapses that bound to
  *equality* when no site rounds anywhere (`FlagFree` — the whole-evaluation *no flagged site*: no
  absorption at any `+`, every `−` in the Sterbenz A2 regime), so rounding is the *sole* source of the
  FP32/`ℝ` measurand gap. *Exit met:* A3′ is a theorem over nontrivial model DAGs (a 3-input accumulator,
  an add/sub variant, a 5-input tree in the `AdequacyDag` example), `#print axioms` →
  `[propext, Classical.choice, Quot.sound]` (no `sorryAx`). No TorchLean PR needed (the levers all
  existed, §4.6 B6/E13). Honest scope carried to 3.2/3.3: the DAG covers `+`/`−` (what A1/A2/A3 cover);
  `×`/`÷` (their per-op bounds `FP32.{mul,div}_abs_error` exist) remain, and so does the no-absorption
  regime — which the Stage-3.8 row records as two separate things, only the first of them done.

* **Stage 3.2 — FLT/FP32 Sterbenz (lift A2 to the real binary32 format). ✅ DONE (built & CI-checked).**
  A2 was proved over a self-contained FLX (fixed-precision, unbounded-exponent) model; binary32 is
  `fexp32 = FLTExp (−149) 24` (gradual underflow), and TorchLean had **only** FLX Sterbenz. **TorchLean PR
  (branch `flt-fp32-sterbenz` off `upstream/main`, merged into the fork's `combined`):**
  `NN/Floats/NeuralFloat/Analysis/SterbenzFLT.lean` adds `neural_generic_format_FLT_sterbenz` — a regime
  split on the underflow boundary `β^(prec+emin)`: the **subnormal** side subtracts exactly on the fixed
  `emin` grid (`FLT_to_FIX` → `FIX_sub` → `FIX_to_FLT_of_abs_le`, no ratio hypothesis), the **normal**
  side transports through the unbounded FLX family (`FLT_to_FLX` → `FLX_sterbenz` → the new
  `neural_generic_format_FLX_to_FLT_of_normal` helper, where the factor-of-two ratio is used). `FP32/Sterbenz.lean`
  adds `round32_sub_exact_of_sterbenz` (Sterbenz as a theorem about `round₃₂`) and `FP32.sub_exact_of_sterbenz`
  (`(a−b).val = a.val−b.val`), composing FLT Sterbenz with `neural_round_preserves_generic`. PKC grounds
  these in `Adequacy.Fp32Grounding.round32_sterbenz_exact` / `sub32_exact_of_sterbenz`, re-stating
  `Adequacy.Sterbenz32` over `round₃₂`/`neuralGenericFormat fexp32`. All sorry-free
  (`#print axioms` → `[propext, Classical.choice, Quot.sound]`). *Exit met:* `flx_sterbenz`'s binary32
  instance is a theorem about `round₃₂` — exercised by the `AdequacySterbenz32` example. (No co-author
  trailer on the TorchLean commit — upstream-facing.)

* **Stage 3.3 — Executable↔spec bridge for FP32. ✅ DONE (built & CI-checked).** The entire TorchLean
  FP32/Flocq layer is `noncomputable` (§4.6 F): `round₃₂ : ℝ → ℝ` is a spec, not a float. The host-`Float`
  `Adequacy` carrier is inherently uncertifiable (opaque FFI — no theorem relates `Float.log2`/`exp2` to
  `ulp₃₂`), so the certified executable check runs instead on TorchLean's **computable** `IEEE32Exec`,
  whose ops are provably `round₃₂` of the exact real result. **Exploration finding:** the op-level
  `IEEE32Exec ↔ round₃₂` refinement (`toReal_{add,sub,…}_eq_fp32Round`) already existed; what was missing
  is an executable ULP (existed only as the `noncomputable` `neuralUlp`/`ulp₃₂`) and a certified
  absorption verdict. A second **TorchLean PR** (`NN/Floats/IEEEExec/Bridge/FP32/Ulp.lean`, branch
  `ieee32exec-ulp` off `upstream/main`, no co-author trailer, merged into `combined`) adds
  `IEEE32Exec.ulpExp?` (bit-level ULP query via `Nat.log2` + `fexp32`; `none` on NaN/∞), proved: an
  answer `some k` has `2^k = ulp₃₂ (toReal x)` (`neuralBpow_eq_ulp32_of_ulpExp?_eq_some`, via `neural_magnitude_dyadic`
  + `neuralUlp.of_ne_zero`), and the executable test `absorbs a b := decide (add a b = a)`, proved sound
  against `round₃₂` (`round32_add_eq_left_of_absorbs`, a 3-line corollary of `toReal_add_eq_fp32Round`
  since `fp32Round` *is* `round₃₂`). PKC re-exposes these as `Adequacy.ExecBridge.{exec_ulp_grounds,
  exec_half_ulp_grounds,exec_verdict_sound}`: the kernel's absorption verdict *certifies* the spec
  absorption `round₃₂ (toReal s + toReal δ) = toReal s`. All sorry-free (`[propext, Classical.choice,
  Quot.sound]`). The residual `Float32 ↔ IEEE32Exec` step is an upstream *assumption typeclass*
  (`RuntimeFloat32MatchesIEEE32Exec`), not an axiom — the irreducible hardware trust boundary. *Exit met:*
  the executable check (`ulpExp?`/`absorbs`, which actually `#eval`s, unlike the noncomputable `FP32`) is
  certified equal to the A1/A3 spec on the finite fragment — exercised by the `AdequacyExecBridge` example
  (`#guard`s at `2²⁵`/`10⁸` + `exec_verdict` proof term). *(2026-07-27 API modernization: upstream
  evolved the PR's total `ulpExp : IEEE32Exec → Int` into the partial `ulpExp? : … → Option Int` —
  `none` on NaN/∞ rather than an artificial spacing — with the direct soundness form
  `neuralBpow_eq_ulp32_of_ulpExp?_eq_some` and the finiteness-only
  `round32_add_eq_left_of_absorbs_of_isFinite`. `ExecBridge`/`AdequacyExecBridge` re-grounded on that
  API: `exec_ulp_grounds`/`exec_half_ulp_grounds` now take `ulpExp? x = some k`, and the new
  `exec_verdict_sound_of_isFinite` re-export needs only the three executable finiteness checks.)*

* **Stage 3.4 — Wire the Axis-U significance yardstick. ✅ DONE (built & CI-checked).** Until here the
  two areas ran from *separate* inputs (Stage 1 fed autograd `cᵢ` to GUM/Willink; `AdequacySwamping`
  handed the carrier hand-picked absolute uncertainties). Stage 3.4 makes both read the *same*
  `InputDist` descriptor (§4.4). `Adequacy/Significance.lean` (UncertaintyRigor): `ofInputDist` seeds
  the `Adequacy` carrier from the descriptor (value = mean, `unc = √variance = uᵢ`); `significanceOf`
  pairs the autograd `cᵢ` with each `uᵢ` into the significance scale `cᵢ·uᵢ` (the propagated
  contribution of input `i` to the output); `supportMagnitude` reads `InputDist.support`'s box
  magnitude (the unbounded normal is `none`). The driver **`analyze`** takes one carrier-polymorphic
  write-once kernel (`ListModel := {α} → [NumCarrier α] → List α → α`) and instantiates it *twice* from
  one source — at `TapeBuilder .scalar` (reverse pass → `cᵢ`, via `Sensitivity`) and at `Adequacy`
  (verdict, seeded from the same descriptors) — returning `⟨coefficients, significance, verdict⟩`. The
  seeding is definitionally faithful (`ofInputDist_{value,unc,report}` `rfl` lemmas). **Honest scope:**
  Stage 3.4 adds *no new rigor* — the flag's soundness is the Stage-3 A3 verdict (`verdict_sound`), here
  merely *fed* the autograd-propagated `cᵢ·uᵢ`; the carrier runs over host `Float` (uncertifiable FFI,
  §4.6 F), and sound magnitude-range propagation over the support box remains the `RInterval` grounding
  already re-exposed by `Fp32Grounding.interval_add_sound` (referenced, not re-run). *Exit met:* the
  `AdequacyCoupling` example runs *one* `analyze` on the Degenhardt fictive descriptors — reproducing
  the autograd `cᵢ = [5, 5, 2.25]`, deriving `cᵢ·uᵢ = [1.0, 1.30, 0.28]` from the *same* descriptors'
  moments, and certifying the model **adequate** at that scale — and a deliberately ill-scaled
  accumulator `bias + gain·x` (`bias = 10⁸`, `gain = 5`, `x = 0.6 ± 0.5`) whose `x`-contribution
  `cₓ·uₓ = 5·0.5 = 2.5` the carrier propagates *exactly* and flags **swamped** below `½ ulp₃₂(10⁸) = 4`
  (one absorption); the closing theorem `contribution_absorbed_at_scale` applies `verdict_sound` at
  `s = cₓ·uₓ`, sorry-free (`[propext, Classical.choice, Quot.sound]`). No TorchLean PR needed.

  **Metrological kinding (revision).** The GUM budget has three roles a naked `Float` conflates —
  input standard uncertainty `u(xᵢ) : Quantity kᵢ`, sensitivity `cᵢ = ∂y/∂xᵢ : Quantity (kₒ/kᵢ)`,
  contribution `uᵢ(y) = |cᵢ|·u(xᵢ) : Quantity kₒ` — and `Uncertainty.Budget` gives each its kind:
  `stdUncQ`, `sensitivityQ` (the boundary stamp that re-dresses the kind-blind autograd magnitude with
  its *static* kind `kₒ/kᵢ`), `contributionQ` (gated by `ProductKind kₛ kᵢ kₒ` — the GUM units
  cancellation `(kₒ/kᵢ)·kᵢ = kₒ` as a typechecking obligation, built through the named `Quantity.mul`),
  `combinedQ` (quadrature of the homogeneous-at-`kₒ` contributions). `analyzeQ` returns a kind-typed
  `CouplingResultQ kₒ`; its two former swappable `List Float` fields are now a `List (Quantity kₒ)` and
  a `Quantity kₒ`. The model stays *carrier-raw* (kinds are the caller-declared overlay on the budget,
  not on the tape — the key move that needs no kinded autograd). The `AdequacyCoupling` example shows
  the kinded contributions' quadrature reproduces the GUM `u_c = 1.662359` **exactly**, and
  `#check_failure` probes make the three conflations (sensitivity↔uncertainty, heterogeneous
  quadrature, `CouplingResultQ` field swap) type errors. Honest limit (§4.4): `ProductKind.ofRatio` is
  *liberal* (signs any ratio triple), so the gate enforces the GUM *shape* and forbids un-sanctioned
  mixing, but the author still asserts `kₛ = kₒ/kᵢ` (the curated-edge discipline); and `analyzeQ`
  itself covers the *homogeneous-input* case (all `kᵢ` equal) — the genuinely heterogeneous ×/÷ case
  is served by the kinded budget DAG (`BudgetDag.lean`/`BudgetDagLaws.lean`, residual 2 below, closed
  2026-08-03), which threads the `ProductKind`/`QuotientKind` witnesses node by node and provably
  collapses to this same flat quadrature.

  **Carrier-generic (two-axis).** `Budget` is a write-once model over `[NumCarrier R]`, not a
  `Float`-only computation — the second axis (carrier) is orthogonal to the kind. So the *same*
  `stdUncQ`/`contributionQ`/`combinedQ` run at `ℝ` (to prove budget laws), `Float`/`FP32` (execution),
  or the `Adequacy` carrier — where `combinedQ`'s quadrature `√(Σ uᵢ²)` adequacy-checks *itself*: the
  `AdequacyCoupling` example runs the identical `combinedQ` at `R := Adequacy` and shows comparable
  contributions combine clean (0 absorptions) while a `10⁻³` contribution beside a `10⁸` one is swamped
  in the sum of squares (1 absorption). `analyzeQ`'s autograd source stays `Float` (that specialization
  is the driver's, not the budget's).

* **Autograd soundness (backward = fderiv) — feasibility assessed, not a Stage-3.4 gate. ✅ COMPLETE
  — the deferred workstream this bullet scoped was carried out and closed by Stages 3.5–3.6 + the
  eager-provenance addendum below; the sensitivities are now *proved* the adjoint of the Fréchet
  derivative at the ℝ carrier, on the very tape the bridge builds. The assessment below is retained
  as the design record that chose the A→P route.** The
  sensitivities `cᵢ` are *computed* by TorchLean's reverse-mode tape but not *proven* to equal
  `∂f/∂xᵢ` (the tape is "an execution facility… not connected to the fderiv proof layer",
  `Autograd/TorchLean/Dual.lean:24`). A 2026-07-31 read-only sweep found the hard mathematics **already
  exists** in TorchLean `NN/Proofs/Autograd/`: `backpropVec_eq_adjoint_fderiv`
  (`Tape/Core/FDeriv.lean:1129` — reverse-mode = adjoint of Mathlib `fderiv`) plus per-op `HasFDerivAt`
  for PKC's *entire* op class (`add/sub/mul/div/scale/min/max/relu/abs/sqrt/exp/log`,
  `Tape/Nodes/{Arithmetic,Piecewise,Elementwise}.lean`). But it lives on a **clean abstract graph over
  `ℝ`** that PKC's runtime call (`TapeM.backwardScalar` — an eager, `Float`, shape-erased,
  `HashMap`/`Except`, reachability-pruned interpreter) never touches. So a soundness PR is *model
  reconciliation, not new calculus*. Verdict: certifying the current *eager* path is a multi-week
  interpreter-reflection slog (five stacked gaps: two disjoint proof models; sparse vs total reverse
  pass; a `compileAux` provenance/reflection obligation; `Float` vs `ℝ`; `Except` partiality). The
  tractable PR is to **retarget `Sensitivity.gradient` onto the compiled/`backwardDenseFrom` entry
  point** (which TorchLean's `Runtime/Link` theorem already bridges to the `Algebra` graph model) and
  prove **one bridge lemma** `backpropAllCtx ⟹ ℝ-`fderiv``; the honest statement is `= fderiv` only at
  the `ℝ` instantiation (the `Float` gradient is a separate adequacy claim this workstream already
  owns). Deferred as its own workstream (since delivered — Stages 3.5–3.6 below); not required for
  the kinded budget.

  *Spike result (2026-07-31, direct P↔R simulation attempted in Lean).* A compiling scaffold
  (`uncertainty/…/Uncertainty/Experiments/PRSimulation.lean` — at the time deliberately
  **unindexed**, a spike artifact with 5 precisely-typed `sorry` obligations; since **closed,
  sorry-free, and indexed** by Stage 3.6 below) settled the design question
  empirically. **Proven sorry-free** (axiom-checked `[propext, Classical.choice, Quot.sound]`): the
  per-node backward/adjoint correspondence for `add`/`mul` at `ℝ` — R's runtime backward closures
  evaluate to exactly P's node VJP (`p_{mul,add}_vjpVec` via `Node.vjpVec_ofVec`, feeding
  `TapeNodes.{mul,add}Fderiv` → `backpropVec_eq_adjoint_fderiv`), and `AnyTensor`/`Except` do **not**
  obstruct the node-level statement. What blocks the direct route is the *fold*: the scatter/accumulate
  `addGradAll` (`Engine/Core/Backward.lean:113`, four nested shape checks/casts per contribution),
  exactly the ~800 lines of fold-commutation the existing A-bridge (`Runtime/Link/BackwardGraph.lean`)
  already spent on the same plumbing — plus two structural findings: the sparse `backwardScalar` path
  forces you onto the total `backwardDenseFrom` anyway, and P's `backpropVec` returns input-gradients
  only (`CtxVec Γ`) so the comparison must project R's all-nodes output onto the `Γ`-prefix (A's
  `backpropAllCtx` matches R's shape directly; P does not). Partiality resolves cleanly: `.ok` follows
  from shape-alignment alone, and the `log`/`sqrt` domain conditions live entirely on the P side
  (`NodeFDerivCorrectAt`) — R totalises and never inspects values. **Refined verdict:** keep the
  spike's per-node lemmas (the reusable, honest core), but land soundness by a thin **A→P upgrade**
  (ℝ-instantiated `backpropAllCtx` = P's all-node backprop) composed with the existing Link theorem —
  reusing the 800 lines of `AnyTensor` fold work instead of re-deriving it against P.

* **Stage 3.5 — Autograd soundness via the A→P upgrade (a TorchLean PR). ✅ DONE (landed on the
  fork's `combined`; PKC re-pinned & retargeted).** Deliverable delivered: *the compiled runtime
  reverse pass is the adjoint of the Fréchet derivative, at the `ℝ` carrier.* Exploration
  confirmed the two proof models were entirely unconnected — different graph types (the
  carrier-generic `Algebra.Graph α Δ Γ ss` vs the `ℝ`-monomorphic `Proofs.Autograd.Graph Γ ss`),
  no translation function, no lemma either way — so the PR supplies the bridge itself, as one
  self-contained module `NN/Proofs/Autograd/Runtime/Link/FDeriv.lean` (+ its `Link.lean`
  aggregator line; TorchLean branch `autograd-link-fderiv` = commit `92ab40f` based exactly on
  `upstream/main` `14bc499`, merged `--no-ff` into `combined` = `d689b0e`; scrubbed: no
  co-author trailer, no project-specific terms; PR lean-dojo#25; amended once after upstream CI
  lint rejected `omega` — the five `flattenCtx_snoc` guard facts now close with core `Nat`
  lemmas `Nat.lt_of_lt_of_le`/`Nat.add_lt_add_left`/`Nat.lt_of_add_lt_add_left`/
  `Nat.add_sub_add_left`, axiom profiles unchanged):
  1. *The slice isomorphism.* `Algebra.{Node,Graph}.toReal` specialize the algebra model at
     `α := ℝ` and a fixed environment `d : Δ` onto the analytic model; `{Node,Graph}.toAlgebra`
     embed back as the `Δ := Unit` slice; the round trip is the identity (`toAlgebra_toReal`),
     and `toReal_{eval,jvpCtx,backpropCtx}` show the specialization preserves all three
     semantics. The analytic model is therefore *exactly* the environment-free `ℝ` slice of the
     algebraic one. This is the "reduce the model gap" answer: the gap was missing *lemmas*, not
     duplicated *types* (contexts were already shared — `TList Γ` *is* `Algebra.TList ℝ Γ` — and
     the two `backpropCtx` recursions mirror node for node), so the bridge is purely additive;
     re-founding the analytic model as an abbreviation of the algebraic one is offered upstream
     as follow-up, with the round-trip lemmas as its ready-made migration spec.
  2. *Input-prefix extraction.* `TList.takeLeft` + `takeLeft_backpropAllCtx` (`Graph` and
     `GraphData` forms) identify the `Γ`-prefix of the runtime-facing full backpropagation with
     the proof-facing inputs-only `backpropCtx` — the missing lemma relating the two
     backpropagation forms upstream kept side by side.
  3. *Vectorization transport + composed endpoints.* `flattenCtx_{cast,snoc,add}` /
     `unsnocCtx_flattenCtx` commute context vectorization with the tape operations, giving
     `{evalVec,jvpVec,backpropVec}_flattenCtx`; composing with the existing Link theorem and
     `backpropVec_eq_adjoint_fderiv` yields `backpropCtx_eq_adjoint_fderiv` and the headline
     **`backwardDenseFrom_compileAux_adjoint_fderiv`**: the executable dense reverse pass on a
     compiled graph succeeds with the full backpropagation context, whose input prefix is
     exactly `(fderiv ℝ eval x)† seed` — plus `_at` variants under `GraphFDerivCorrectAt` for
     non-smooth primitives (`relu`/`abs`/`min`/`max`, `log`/`sqrt` domains). Axiom profile of
     every new declaration: `[propext, Classical.choice, Quot.sound]` (the `takeLeft` layer
     needs only `propext`).
  4. *(PKC-side.)* Both manifests (root + `blueprint/`) re-pinned at `combined = d689b0e`;
     `Sensitivity.gradient` retargeted onto the total dense entry `Tape.backwardDenseFrom`
     (zero seed everywhere, `1` at the scalar output) with its public signature unchanged — the
     theorem now covers the very entry point PKC invokes, and all numeric guards pass unchanged
     (on a topologically ordered tape the total pass performs the same accumulation as the
     previous reachability-pruned path; a dead subexpression now contributes an exact `0`
     instead of being skipped). The two honest residual gaps, unchanged in kind: *provenance*
     (PKC's tape is built eagerly by `TapeM`, not by `compileAux` — scoped by 3.6 step 2's
     shape-alignment argument) and *carrier* (the theorem speaks at `ℝ`, the run is `Float` —
     that deviation is precisely this workstream's own Adequacy claim, Stages 3–3.3).

* **Stage 3.6 — Direct-route completion (the spike's remaining obligations). ✅ DONE (pure PKC,
  no TorchLean change).** `Experiments/PRSimulation.lean` is now a sorry-free module indexed in
  `UncertaintyRigor`, with the paired probe `AutogradDirectSim.lean` in `UncertaintyExamples`
  (every closed statement instantiated concretely + axiom pins = the classical trio). The three
  planned steps landed exactly in order, with one honest statement refinement:
  1. *Vectorization homomorphisms — PROVEN.* `mulSpec_ofVecT`/`addSpec_ofVecT` via the pointwise
     `toVecT_map2Spec_apply` (`Shape` induction through the upstream coordinate characterization
     `toVecT_dim_apply`; the zero-size branch is vacuous, the base case reuses the
     `euclideanEquiv_symm_ofLp` scalar read). `addSpec` additionally short-cuts through the
     Stage-3.5 `toVecT_addSpec` + the `toVecT`/`ofVecT` roundtrips. `mul_contrib_agree` is
     thereby closed too.
  2. *Partiality (`backwardDenseFrom_ok`) — PROVEN, with a refinement the original statement
     needed:* `ForwardSim` pins the tape's stored **values** but not the opaque `backward`
     **closures** the reverse pass runs — a value-correct tape with a `fun _ => .error` closure
     refutes the unrefined claim. The honest hypothesis is `BackwardShapeWF` (every closure is
     *shape-total*: on a node-shaped cotangent it succeeds and emits contributions targeting
     existing nodes at their shapes). Under it, the "every slot carries its node's shape"
     invariant `AccShapeAligned` threads through `addGradAll` → `backwardDenseFromStep` →
     `backwardDenseFromLoop` value-free, and `ForwardSim` + `ArrCorr` seed it. Crucially the
     hypothesis is *dischargeable*: `backwardShapeWF_{empty,addNode,leaf,add,mul}` prove the
     eager runtime constructors provide it, constructor by constructor (`requireValue_shape`
     pins the parents' stored shapes) — so `.ok` holds on eagerly built `leaf`/`add`/`mul`
     tapes, not just compiled ones. `log`/`sqrt` domains stay P-side, as predicted.
  3. *The fold pair — closed without re-deriving the `addGradAll` commutation.*
     `sim_backward_step` is retired to documentation: its `.ok`-and-invariant half survives as
     `backwardDenseFromStep_ok`; its per-step *value* half is exactly the A-bridge's ~800-line
     `haddGradAllPush` argument and was not duplicated. `direct_PR_soundness` is closed as
     **`direct_PR_soundness_compiled`** (+ `_at` variant): the `Γ`-prefix projection of the
     Stage-3.5 endpoint transported into the spike's own `ArrCorr` phrasing by two new erasure
     lemmas — `getRaw_flattenCtx` (block-reads invert `flattenCtx`, giving also
     `arrCorr_flattenCtx`) and `toAnyArray_extract_takeLeft` (`Array.extract` is the erased
     `TList.takeLeft`). `forwardSim_compileAux` additionally shows compiled tapes *inhabit*
     `ForwardSim`, so the simulation relation is realized, not hypothetical. For an *arbitrary*
     `ForwardSim` tape the value statement stays unprovable for the same reason as (2) — the
     closures are unpinned — which at this point left one residual: identifying the eager
     tape's closures with a compiled tape's, an accounting question, not adjoint mathematics.
  *Exit met:* all five scaffold sorries are gone (three as proofs, one as a refined proof, one as
  a compiled-tape corollary + documentation). Gate: `lake build Uncertainty UncertaintyRigor
  UncertaintyExamples` = 3167 jobs green, 0 warnings; all named endpoints axiom-pinned
  `[propext, Classical.choice, Quot.sound]`.

  **Addendum — the eager-provenance residual, CLOSED (`Experiments/EagerProvenance.lean`,
  sorry-free, indexed; probe additions in `AutogradDirectSim`).** The accounting question above
  is now a theorem, for the `leaf`/`add`/`sub`/`mul` fragment: **`EagerBuilds g x t`** is the
  provenance relation (the base tape is `addLeaves`, which *is* the `Tape.leaf` fold — literally
  the compiled tape of the empty graph — and each graph node corresponds to one successful eager
  `Tape.add`/`Tape.sub`/`Tape.mul` call), and **`backwardDenseFrom_eager_eq_compiled`** proves the total
  dense reverse pass on the eager tape returns *exactly* what it returns on
  `compileAux g.toAlgebra x ()` — same `Result`, same array — from any erased-context seed.
  Consequently **`direct_PR_soundness_eager`** (+ `_at`): the fderiv endpoint holds on the
  eagerly built tape itself, with no compilation anywhere; and `forwardSim_eager` shows those
  tapes inhabit `ForwardSim`. The proof discipline held: no reverse-pass fold is re-derived —
  the compiled node's *dense* contribution list is folded by the upstream accumulation bridge
  (`foldlM_addGradAll_toIndexedAnyList_eq_add`), the eager node's *sparse* two-element list by
  the new single-slot lemma `addGradAll_toAnyArray_single` (one `addGradAll` call = one one-hot
  `TList.add`, via `toAnyList_add_single` + `addSpec_fill_zero`), and the two context updates
  coincide by flatten-injectivity: `flattenCtx_single`/`getIdx_flattenCtx` (new erasure lemmas
  for one-hot contexts and block reads) turn both into vector sums where the Stage-3.6
  homomorphism `toVecT_mulSpec` identifies the eager `mulSpec` payloads with the `ofVec`-authored
  node's Hadamard vjp (`mul_vjp_add_eq`/`add_vjp_add_eq`, and `mul_forward_eq`/`add_forward_eq`
  for the stored values). Push-invariance lemmas (`addGradAll_push` → `backwardDenseFromLoop_push`,
  under the bounded-contribution-ids fact both tape families satisfy) restrict the extended
  tape's loop to the prefix so the `EagerBuilds` induction consumes its hypothesis directly.
  `sub` (2026-08-02) followed as the second binary crank — the same machine as `add`, save that the
  runtime `Tape.sub` feeds the negated cotangent `subSpec (fill 0) δ` to the right parent
  (`sub_vjp_add_eq`, via the two extra facts `toVecT_subSpec` and `single_neg`), which the compiled
  side already accepts (op-generic `direct_PR_soundness_compiled`); a concrete `subGraph = x₀ − x₁`
  probe in `AutogradDirectSim` exercises `EagerBuilds.sub`. What remains, honestly: `div` (reuses the
  two-parent machine under a nonzero-denominator `…At`), `scale`/`neg` and the elementwise unaries
  (the simpler *one-parent* variant of the machine — one contribution, not two), the `TapeM` `StateT`
  sugar (identifying a `TapeM.run` trace with an `EagerBuilds` derivation, wrapper bookkeeping over
  `Engine/TapeM.lean`), and the `Float`-vs-`ℝ` carrier deviation, which is this workstream's own
  Adequacy claim. Gate: `lake build Uncertainty UncertaintyRigor UncertaintyExamples` green, 0
  warnings (the `sub` addition rebuilds the `UncertaintyExamples` library green, 3166 jobs);
  `backwardDenseFrom_eager_eq_compiled`/`direct_PR_soundness_eager{,_at}`/`forwardSim_eager`
  all axiom-pinned `[propext, Classical.choice, Quot.sound]` in the probe (those pins transitively
  cover the `sub` case of `loop_eager_eq_compiled`, so `sub` introduced no axioms).

* **Stage 4 — Scale. ◐ IN PROGRESS.** GPU-batched SSPRC/MCM on `CudaT`; sensitivity-driven `Nᵢ`
  allocation; a real downstream science model (soil-moisture retrieval) as the capstone example.
  **Independent of Stages 3.5–3.6**: SSPRC/MCM are derivative-free, and the `Nᵢ` allocation consumes
  the same *computed* `cᵢ` Stage 1 already relies on — the soundness sub-stages upgrade the *trust* in
  those coefficients, not the pipeline's function, and the capstone model at `CudaT` never touches the
  proof layer. The only soft coupling is that 3.5's retarget must keep `Sensitivity.gradient`'s
  public signature (it does, by construction). Stage 4 can proceed in parallel with, before, or
  after the soundness work.

  * **Batched SSPRC propagator — ✅ DONE (built & verified).** `Uncertainty/SsprcBatched.lean` (`run`)
    runs the *same* write-once `[NumCarrier α]` kernel at `α := CudaT (Shape.dim Nᵢ .scalar)`: input
    `i`'s `Nᵢ` systematic samples become **one batch tensor**, the other inputs broadcast constants,
    and each input's deviation distribution is **one batched launch** (a GPU kernel per elementwise op
    under `-K cuda`, the portable CPU float32 stub otherwise), its moments read with
    `Buffer.reduceMean`; `E(Y)`/`u(Y)` combine exactly as the scalar `Ssprc.run`. **Verification is by
    executable, not `#guard`.** `CudaT`'s device ops are `@[extern]` FFI with no interpreter fallback,
    and the TorchLean dependency graph **cannot** be `precompileModules`-loaded into the elaborator —
    Lake shared-links whole *libraries*, and the upstream `ProofWidgets.Demos` / `QuantumInfo`
    `:shared` facets do not build — so a build-time `#eval`/`#guard` of a `CudaT` value is impossible
    here (a narrow, Mathlib-free precompiled lib does not help; the granularity is the library, not the
    import closure). Instead the `apps/ssprc_batched_parity` executable links the native `CudaT` code
    directly and asserts parity with `Ssprc.run`: on the fictive `Y=(X₁+X₂²)X₃` the float32 stub
    reproduces `E(Y)=11.5875` / `u(Y)=1.6876` within `|ΔE|≈2·10⁻⁶`, `|Δu|≈5·10⁻⁵` of the float64
    reference (`lake exe ssprc_batched_parity`, exits `0` on parity, `1` on mismatch; run on the CPU
    stub here, on the device in the `-K cuda` container). The engine sits in its own
    `precompileModules`-free lib `UncertaintyBatch`; the harness is the one executable the package
    produces. *Exit met:* the batched device propagator agrees with the Stage-2 scalar SSPRC to float32.
  * **Sensitivity-driven `Nᵢ` allocation — ✅ DONE (built & `#guard`-checked).**
    `Uncertainty/Allocation.lean` (`allocate`, `allocateFromTerms`) turns the per-input uncertainty
    contributions `wᵢ = |cᵢ|·uᵢ` — the same `cᵢ` Stage 1's `Sensitivity.coefficients` computes and the
    same `uᵢ = √varianceᵢ` from `MomentData` — into per-input sample counts: it **drops** any input
    with `wᵢ ≤ dropRatio·maxⱼ wⱼ` (`Nᵢ = 0`; its deviation distribution is a point mass) and
    **largest-remainder-splits** the whole budget across the survivors in proportion to `wᵢ`, so
    `Σ Nᵢ = total` exactly and a larger contribution never gets fewer samples. A pure `List Nat` that
    drops into `Ssprc.run`/`SsprcBatched.run`'s `ns` — Mathlib/Torch-free, so (unlike the `CudaT`
    propagator) it is checked at build time. `examples/…/DegenhardtAllocation.lean` verifies, all
    `#guard`: on the fictive model `w=[1.00,1.30,0.28]` ⇒ `allocate 300 = [117,151,32]` (X₂ dominant,
    X₃ ~4.7× fewer, `Σ=300`), the drop mechanic, the degenerate-fallback equal split, and — the payoff
    — that SSPRC on the *allocated* `ns` reproduces the ground-truth `E(Y)=11.5875`/`u(Y)≈1.686` even
    at a 120-eval budget (a 60 % cut vs the flat `[100,100,100]`), because the samples it drops are
    X₃'s over-sampling, not signal. Axiom profile `[propext, Classical.choice, Quot.sound]`.
    *Exit met:* a budget-conserving, ranking-respecting allocation that preserves SSPRC accuracy under
    a cut, checked in CI.
  * **Science-model capstone — ✅ DONE (built & `#guard`-checked; kinded end-to-end).**
    `examples/…/WaterCloudModel.lean` drives **one write-once kernel** — the Water Cloud Model
    soil-moisture forward `σ⁰ = a·ndvi·(1−τ) + τ·(c·mv + d)`, `τ = exp(−2·b·ndvi)` (Attema & Ulaby
    1978, the standard radar vegetation-scattering forward), over `[NumCarrier α]` — written in the
    **rigorous quantity discipline** (the soil-moisture-model's `ConfigKinds`/`AvsKinds` pattern):
    nine role-named kinds-of-property (`backscatter`, `vegetationIndex`, `soilMoisture`, `pureNumber`,
    `attenExponent`, `attenuation`, `vegGain`/`attenRate`/`soilGain`) with the product/`exp` algebra
    witnessed (`wcm_kind_algebra`, axiom-free) and the three dimension-1 roles proved distinct (what a
    dimension checker cannot separate); every numeric constant (`a,c,d` and the two-way `2`) a kinded
    quantity in a carrier-generic `WcmConfig` structure (the *sole* numerals in the module); every
    variable a `Quantity k`/`UncertainQuantity k`; a naked `Float` *only* at the emission boundary,
    where `.magnitude` (definitionally the scalar forward) meets the propagators — no naked twin; and
    `#check_failure` probes certifying the kind confusions. Through the entire pipeline: (1) the `Float`
    forward `σ⁰(E(X)) = 0.047089`; (2) the TorchLean-autograd
    Jacobian `∂σ⁰/∂(mv,ndvi,B) = [0.0861, 0.0206, 0.0129]`, matched to the **hand-derived closed-form
    columns** to 6 dp (this is the first uncertainty example to differentiate an `exp`-nonlinear
    model — it exercises the tape's `exp` VJP, not just `+`/`·`); (3) the GUM/Willink combine
    `u_c ≈ 0.002847`; (4) SSPRC on `[100,100,100]` recovering the mean **including** the small
    `exp`-curvature offset `E(σ⁰) − R ≈ +0.000100` that the linearized rungs (mean = `R = f(E(X))`)
    structurally miss; and (5) the Stage-4 allocation, which ranks **soil moisture** (the retrieval
    target) the dominant input (`allocate 300 = [197,91,12]`), **drops** the canopy coefficient at
    `dropRatio 0.1`, and — at *half* the flat budget (`[99,45,6]`, 151 evals) — still reproduces the
    SSPRC mean/uncertainty, because the samples it cuts are `B`/`ndvi` over-sampling, not signal.
    Self-contained by necessity: PKC cannot import the downstream `soil-moisture-model` (that package
    already requires PKC — a cycle), so the kernel is written fresh. Axiom profile — classical trio.
    *Exit met:* a real downstream science model carried write-once across evaluation, autograd,
    combine, SSPRC, and allocation, every number a checked fact.
  * **Remaining (Stage 4):** batched **MCM** (the same batched-moments primitive, one launch for the
    joint sample block, seed-matched to `Mcm.run` so its parity is checkable, verified by an
    executable like `ssprc_batched_parity` since it uses `CudaT`).

Reflection/CI note: each new proof file gets a paired, *indexed* reflection probe (per the
project's convention that an un-indexed probe is never built and silently rots).

**Remaining work (as of 2026-08-04).** Stages 0–3.6 are built and CI-checked, and autograd
soundness is complete (Stages 3.5–3.6 + the eager-provenance addendum: the reverse pass is proved
the adjoint of the Fréchet derivative at the ℝ carrier, on the eagerly built tape). One stage
(Stage 4) is in progress; of the four honest residuals identified, items 1–2 are closed (2026-08-03)
and items 3–4 remain, each scoped small.

* **Stage 4 — Scale** ([`§6`](#6-staged-plan-each-stage-is-shippable-testable-rigor-first) above) —
  **in progress.** Three slices landed: the batched SSPRC propagator on `CudaT` (`SsprcBatched.run`,
  verified by the `ssprc_batched_parity` executable — build-time `#guard` of a `CudaT` value is
  impossible here, so the harness runs the native kernels and asserts parity with the scalar
  `Ssprc.run`), the sensitivity-driven `Nᵢ` allocation (`Allocation.allocate` — a pure `List Nat`,
  `#guard`-checked in `DegenhardtAllocation`), and the soil-moisture **science-model capstone**
  (`WaterCloudModel` — one write-once Water-Cloud-Model forward through the Float forward, the
  autograd Jacobian matched to closed forms, GUM/Willink, SSPRC, and the allocation; `#guard`-checked,
  self-contained since PKC cannot import the downstream soil-moisture-model). Remaining: batched MCM.
  Independent of Stages 3.5–3.6 (SSPRC/MCM are derivative-free, and the `Nᵢ` allocation consumes the
  same *computed* `cᵢ` Stage 1 already relies on), so it can proceed before, in parallel with, or
  after the soundness work.

The four residuals — all "one more crank of the same machine," none a new workstream:

1. **Autograd ops beyond the arithmetic core, and the `TapeM`/`StateT` sugar — CLOSED (2026-08-03).**
   The eager-provenance closure (`Experiments/EagerProvenance.lean`) now covers the **entire
   elementwise runtime surface of the tape**, plus the monadic sugar:
     * **Both machines, plus the generic unary abstraction** (2026-08-02): binary two-parent
       (`leaf`/`add`/`sub`/`mul`), unary one-parent (`scale`), and the generic `EagerBuilds.unary`
       constructor keyed on the shared `Tape.unary` node shape, with generic §B bridges — adding an
       elementwise op is two pointwise facts, no §E/§F reasoning.
     * **`div` — the binary crank landed** (2026-08-03): the upstream PR
       ([lean-dojo/TorchLean#26](https://github.com/lean-dojo/TorchLean/pull/26), `TapeNodes.div` +
       `divFderivAt`) is **merged** (`0c9a8b8`) and the pin bumped; `EagerBuilds.div` mirrors `sub`
       end-to-end (quotient-rule accounting: `divSpec δ b` to the left parent, negated
       `subSpec (fill 0) (mulSpec δ (divSpec a (mulSpec b b)))` to the right, unconditional under
       the totalized `0⁻¹ = 0`), with the probe `divGraph`/`eagerBuilds_div` and the endpoint
       through the pointwise `direct_PR_soundness_eager_at` (denominator-nonzero at the input).
     * **The elementwise/activation family — instantiated** (2026-08-03): `exp`, `sigmoid`, `tanh`,
       `softplus` (global witnesses, universal endpoint) and `relu`, `log`, `abs`, `sqrt`
       (pointwise `…At` witnesses and endpoint, with the input-nonzero condition threaded through
       the binders) are all literal `EagerBuilds.unary` instances in `AutogradDirectSim`,
       axiom-pinned to the classical trio. Genuine per-op facts were only the pointwise scalar
       bridges the drafts predicted: `signSpec` vs the `SignType.sign` coercion (trichotomy),
       `sqrtSpec`'s clamp (`√(max v 0) = √v` over `ℝ`) and its `if`-guarded backward vs the
       totalized `1/(2·√v)`, and `invSpec = mapSpec (1/·)` vs `(·)⁻¹` (`one_div`). Elaboration
       gotcha worth keeping: the `sigmoid`/`tanh` instance unifications **diverge** (>25M
       heartbeats) unless the scalar specs are made `attribute [local irreducible]` for the block —
       the unifier otherwise substitutes their bodies through the elemwise node machinery; the
       other ops fit the usual 6.4M budget as-is.
     * **The `TapeM`/`StateT` sugar — bridged** (`UncertaintyExamples/TapeMBridge.lean`,
       2026-08-03): the uniform builder reshuffle is reduced once (`opM_run_ok`/`opM_run_error`/
       `opM_run_inv`), per-op corollaries are definitional instantiations
       (`run_{add,sub,mul,div,scale,exp,tanh,sigmoid,softplus,log,relu,abs,sqrt}_ok` + `run_leaf`),
       `run_bind_inv`/`exec_inv` peel `do`-blocks, and the demo `progMulScale_exec_eagerBuilds`
       proves a user-style monadic program's successful `exec` is `EagerBuilds`-covered — composed
       with `direct_PR_soundness_eager`, the reverse pass of the tape a `do`-block built realises
       `(fderiv ℝ eval x)† seed`. Axiom-pinned.
     * **Planned upstream TorchLean PR — the `TapeM` reduction layer.** Everything above the demo
       is TorchLean-generic, not PKC-specific: `opM` and its three run lemmas, `run_bind_inv`/
       `exec_inv`, `run_leaf`, and the per-op `run_<op>_ok` family are all statable over an
       arbitrary carrier `{α}` (each with exactly the typeclass row of its `TapeM.<op>` wrapper) —
       the `α := ℝ` pinning in `TapeMBridge.lean` is an artifact of where they were first needed.
       The PR: a new additive proofs module (e.g. `NN/Proofs/Autograd/Runtime/TapeM.lean`)
       carrying the generalized layer, extended from our 14 ops toward the full `TapeM` wrapper
       surface (every wrapper is the same reshuffle, so each op is a one-line `opM_run_ok`
       instantiation); optionally the per-op "returned id = pre-append size" facts in the
       `tape_mul_id` style (the `addNode` invariant read back through each op's `do`-block).
       Discipline: purely additive, classical-trio axiom profile, and — per the standing TorchLean
       policy — no project-specific terms in code, commits, or the PR body. After it merges and
       the pin bumps, `TapeMBridge.lean` here shrinks to the demo + endpoint, importing the
       upstream lemmas. Proof recipe to reuse: the curated `simp only` set must include
       `TapeM.run`; `cases h : g t` rewrites `g t` *in the goal* (the leftovers are `rfl`s);
       destructure pairs before projecting (`obtain ⟨t1, i1⟩ := p`); ctor-clash hypotheses close
       by `cases h`.
   Out of frame, unchanged in kind: `inv`'s runtime backward is `scaleSpec (mulSpec δ (inv x)²) (-1)`
   — not the `mulSpec (bwd x) δ` shape the generic machine keys on (a dedicated constructor or an
   upstream backward-form alignment would admit it); `safeLog` is machine-shaped but uninstantiated;
   structural/higher-arity nodes (affine/matmul, reductions, softmax, conv) have a non-sparse vjp and
   sit outside the "one crank" framing, and the tape has no trig VJP nodes at all. The science models
   this workstream targets are polynomial/affine in the sensitivity inputs, so nothing outstanding
   gates them. (Minor parity item, unchanged: `sub`/`scale`/`div` and the activation instances are
   proved on the soundness route; only `add`/`mul` carry the independent shape-total totality route.)
2. **The kinded budget's ×/÷ DAG extension — CLOSED (2026-08-03).** `analyzeQ`
   (`Adequacy/Significance.lean`, composing `Budget.lean`'s primitives) covers the
   *homogeneous-input* case (all `kᵢ` equal); the genuinely heterogeneous multiply/divide
   case is now served by the kinded budget DAG (`BudgetDag.lean` + `BudgetDagLaws.lean` + the
   `BudgetDagDensity` example):
     * **The machine** (`BudgetDag.lean`, Mathlib/Torch-free, carrier-generic): `BudgetExpr R k` is
       a ×/÷ expression whose every node carries its `ProductKind`/`QuotientKind` witness as a
       constructor field — the residual's "edges threaded through a multi-node graph" made literal;
       an ill-kinded tree is unwritable. `propagateQ` folds `(value, standard uncertainty)` pairs
       (`EstimateQ`, descriptor-seeded) bottom-up with the per-node GUM two-term quadrature; the
       division's `(|y|·u_b)/|b|` term is built through the *transposed* witness
       `QuotientKind.toProductKind` (new, core spine: `k = k₁/k₂` re-read as `k·k₂ = k₁`), so no
       intermediate is a naked magnitude. `contribsQ` flattens the same tree to per-leaf-occurrence
       contributions at the root kind.
     * **The law that keeps one authority** (`BudgetDagLaws.lean`, `ℝ`, scoped `instNumCarrierReal`):
       the node-wise propagation collapses *exactly* to the flat `Budget.combinedQ` quadrature of
       `contribsQ` (`propagateQ_unc_eq_combinedQ`) — relative to the flat Stage-3.4 budget baseline
       the DAG adds threading only, never a second combination rule. Leaf nonnegativity is the only
       hypothesis; `ℝ`'s totalized `x/0 = 0` makes both sides degenerate identically at a zero
       divisor, so there is no divisor side condition. Plus the textbook relative-quadrature
       corollaries for single `mul`/`div` nodes. Axiom profile: classical trio.
     * **The closure probe** (`BudgetDagDensity`): block density `ρ = m/((l·w)·h)` — five distinct
       kinds (mass, length, area, volume, mass density) through one budget, untypeable under
       `analyzeQ`'s single shared input kind; `#guard`s reproduce the hand-computed GUM numbers and
       the `Float` shadow of the collapse; `#check_failure` probes make the operand swap, the
       heterogeneous quadrature, and the kind-permuted builder type errors; the ℝ collapse is
       applied and the capstone axiom-pinned.
   Honest limits, unchanged in kind: the tree treats every leaf *occurrence* as independent
   (correlation — including a shared subterm written twice — is out of frame exactly as in the flat
   `combinedQ`), and the witnesses stay `ofRatio`-liberal (the calculus' curated-edge trust model).
3. **The `Float`-vs-`ℝ` carrier deviation.** The soundness theorems speak at `ℝ`; the run is `Float`.
   That gap is precisely this workstream's own Adequacy claim, and is discharged in kind by Stages
   3–3.3 (the executable `Adequacy` carrier, A3 verdict soundness, the FP32 Sterbenz lift, and the
   executable↔spec bridge); no separate deliverable is outstanding, only its per-model application.
4. **Optional / decision items.** The `hᵢ`/HVP Taylor surrogate (off the Stage-2 exit path, §5 table)
   and the trig VJP nodes (`sin/cos/tanh/sinh/cosh`, §7 risks: TorchLean's tape has no VJP for these,
   so trig models can be *evaluated* but not *differentiated* on the tape). Fund only if a model needs
   second-order surrogates or transcendental differentiation.

---

## 7. Risks & open decisions

* **Autograd op coverage.** TorchLean's tape/CUDA elementwise surface is
  `add/sub/mul/div/scale/min/max/relu` + `abs/sqrt/exp/log` — **no `sin/cos/tanh/sinh/cosh`** with
  VJP. Models using trig can be *evaluated* (Float/CudaT have the transcendentals as values) but not
  *differentiated* on the tape until `_fwd/_bwd` nodes are added. Decision: accept the exp/log/sqrt
  model class for Stages 1–2, or fund the trig VJP nodes early.
* **Toolchain / build coupling.** PKC is pinned `v4.33.0` (Mathlib v4.33.0, TorchLean `combined`).
  Stage 0 avoids the issue entirely (Mathlib/TorchLean-free). Stage 1+ pull in much more of
  TorchLean (autograd + interval + FFT), enlarging build surface and tightening the PKC↔TorchLean
  coupling (cf. the FGM↔DVB single-toolchain constraint). TorchLean's autograd functional API is
  `func`, so the `Sensitivity` bridge targets `func.grad`/`func.hessian`. Budget a bump-in-lockstep
  workflow; `scripts/check-doc-pins.py` is the gate that keeps the version claims in this file, the
  README and the blueprint README equal to `lean-toolchain`.
* **`Adequacy` carrier laws.** It is a `NumCarrier` that *also* accumulates a report; the monoid/branchless
  discipline of `NumCarrier` must not be violated by the check (the check is a side-record, the numeric
  `value`/`range` stay branchless). Verify the instance is lawful.
* **Pearson percentile fidelity — DECIDED: refuse outside the fit's range, do not clamp.**
  Willink eqs. (6)/(7) are rational fits to the Pearson percentage points, stated on
  `−1.2 ≤ γ ≤ 6`. Both denominators have negative discriminant, so outside that range nothing
  divides by zero and nothing signals: the expression returns a number that is no longer a
  coverage factor. `Combine.lean` now names the range (`pearsonFitLo`/`pearsonFitHi`,
  `inPearsonFitDomain`) and carries it in the return type of every function that *reports* a
  factor or a half-width — `willinkK95?`/`willinkK99?`, `willinkHalfWidth95?`/`willinkHalfWidth99?`
  return `none` outside it. `Ladder.PearsonFitDomain` is the same two bounds over `ℝ`, with
  `zero_mem_pearsonFitDomain` recording that T2's collapse point is interior, so the capstone
  never reads the fit outside where it is stated.

  Clamping was the other option on the table and was rejected: returning `k(6)` for `γ = 10` and
  labelling it the coverage factor for an excess of 10 is the same silent substitution one level
  further in, and it would be invisible in exactly the regime where the method is least
  trustworthy. A caller that wants a clamped value can clamp its own `γ` and say so. The fits
  themselves (`willinkK95`, `willinkK99`, `willinkHalfWidth95/99`) stay total, because
  `k95_zero` is a statement about the fit and T2 needs it unconditionally.

  The two worked examples report the verdict beside the number — the gauge block at
  `γ_Y ≈ 0.124` and the all-Gaussian ladder at `γ_Y = 0` both print `in fit range? true`, and
  `#guard`s pin both the membership and the refusal at `γ = 10`. Implementing the exact Pearson
  quantile remains available and is not scheduled; it would widen the domain rather than change
  what happens outside it.
* **`CarrierRefinement` consolidation — DECIDED: keep both routes, with a division of labour.**
  The question was whether A3's soundness should go through PKC's `CarrierRefinement`
  (`QuantityRefinement.lean:72`, with `MulRefinement`/`DivRefinement` beside it, all three
  instantiated for `FP32↔ℝ` in the `Torch` lib) or directly through TorchLean's `*_abs_error`
  lemmas. It goes through both, because they answer different questions:

  * **An equation is not a bound.** `CarrierRefinement` says what the executable operation *is* in
    the specification carrier — one equation per operator. The `*_abs_error` family says how far it
    is — one bound per operator. The first implies the second given a bound on `round`; the second
    implies nothing about the first.
  * **Their side conditions are about different things, and merging them would conflate a
    definedness question with a magnitude one.** `DivRefinement` is unconditional at the
    specification rung only because `ℝ` totalizes `x / 0`, which is why the executable rung instead
    carries the divisor's nonzero decoded mantissa — *definedness*. `DagBound`'s `Regular` is not
    the companion of that: the per-operation bound `Fp32Grounding.div32_within_half_ulp` has **no**
    hypothesis at all, and `Regular` guards the *propagation* factors `1/|b|` and `|a|/|b|²` —
    *magnitude*. `Adequacy/MeanBound.lean` is where the cost of conflating them shows: at the
    weighted mean's single `div` node the two rungs' licenses are genuinely independent in both
    directions (weights `2²⁴`, `1`, `−2²⁴` sum exactly to `1` and total exactly `+0`; weights `2²⁴`,
    `1`, `1`, `−(2²⁴+2)` sum exactly to `0` and total exactly `−2`), and the two repairs
    (`Aggregation.licenses_agree_of_exact` for a non-rounding denominator,
    `Adequacy.licenses_agree_of_nonneg` for a nonnegative one) are what a consumer reaches for.
  * **They meet, and the meeting point is now machine-checked.** `Adequacy/RefinementBridge.lean`
    records the decision and proves the identification it rests on: the refinement's rounding *is*
    the format's (`CarrierRefinement.round (E := FP32) = round32`, by `rfl`), so
    `DagBound.ExactRepresentable` — the condition under which the metric bound collapses to equality
    — is exactly the statement that the refinement rounds nothing along the evaluation
    (`refinementFixes_iff_exactRepresentable`), and `toSpec_box_exact` states A3′'s exact case in
    the bridge's own vocabulary.

  **So: the forward-error accumulation and box faithfulness are metric and stay on `*_abs_error`;
  the exactness regime is algebraic and is a `CarrierRefinement` statement.** No code moves; what
  changed is that the split is stated and checked rather than incidental.
* **`AdequacyReport`'s counts are path multiplicities, not site counts — OPEN.**
  `merge` adds its operands' counts and `Adequacy` is a plain value carrier with no node identity,
  so a `let`-bound sub-expression used twice contributes its report twice: a flagged site is
  counted once per *evaluation path* that reaches it. One absorption site reused by squaring
  reports `1, 2, 4, 8, 16` (`UncertaintyExamples.AdequacyLimits`). On the first real model scored
  at this carrier the count grew by a factor of exactly 98 per iteration of an 8-sweep fixed point,
  reaching `2.95 × 10¹⁷` for a graph of a few thousand nodes.

  Not a soundness bug: zero is preserved exactly in both directions — a count is non-zero iff some
  path reaches a flagged site iff some site is flagged — so `isAdequate` is sound and is the only
  part of a report that may be read today. `AdequacySwamping` and `AdequacyCoupling` do read
  `.absorptions`/`.cancellations` directly; their pins are correct because their expressions are
  straight-line, which is exactly the shape in which the problem is invisible.

  Three options, cheapest repair first. **(1) Say it in the type:** replace the two `Nat` fields
  with `Bool`s (`absorbed`, `cancelled`) and `merge` with `||`. That is precisely the sound
  content, it cannot be misread, and it costs four `#guard`s in `AdequacySwamping.lean` and two
  reads in `AdequacyCoupling.lean`; `isAdequate` keeps its signature and meaning and nothing else
  moves. **(2) Make the counts true:** hash-cons the evaluation so each node is visited once —
  a different carrier, closer to `TapeBuilder`, for a number nobody has yet asked for.
  **(3) Document only:** leaves a public field whose obvious reading is wrong. Recommendation: (1).
* **A 0th-order `sqrt` turns a contraction into an expansion — OPEN, and it decides where the
  carrier may be used.** `Adequacy`'s `MathCarrier` maps the value through `exp`/`log`/`sqrt` and
  carries the uncertainty through **unchanged**; §4.3 defers first-order sensitivities to Stage 3.x.
  The cost of that deferral is larger than "the sensitivity is approximate": inside a fixed-point
  iteration it replaces the loop's damping factor with `1`, and the multiplications then compound
  unopposed.

  The arithmetic is *not* implicated, which is what makes the diagnosis specific and is the part
  a first reading got wrong. At this carrier `v ↦ ½·v + c` reaches the correct `u(v*) = 2·u(c)`,
  and so does a loop with the uncertain value in a divisor — both pinned in `AdequacyLimits`.
  The `sqrt` loop does not: `f(v) = C·√v` has fixed point `C²` and `f'(C²) = ½` for **every** `C`,
  so the value contracts at one half always, while a carrier modelling `u(√x) = u(x)` multiplies
  the uncertainty by `C` per step. At `C = 93` the value converges on `8649` while `u` runs
  `10⁻³ → 5.6 × 10¹²` in eight steps.

  Consequence for users: **the cancellation half of the carrier is unusable wherever a
  transcendental supplies the damping**, because the flag fires when a subtraction's result falls
  below the uncertainty reaching it, and under a propagation many decades too large it fires on
  everything. Observed on the first real model scored: every node of a 2000-node domain flagged at
  every input uncertainty from `10⁻²` to `10⁻⁹`, against a finite-difference first-order figure of
  `1.3 × 10⁻²` where the carrier modelled more than `10¹⁸`. The swamping half is unaffected — it
  compares an operand's *own* uncertainty against half a ulp before the accumulation reaches it —
  and stayed informative, locating the representation's resolution floor.

  The repair is one derivative per transcendental, with no new dependency:
  `u(√x) = u(x)/(2√x)` (guarding `x = 0`), `u(exp x) = u(x)·exp x`, `u(log x) = u(x)/|x|`, `abs`
  staying 0th order because it is exact, and the trigonometric family following the same rule.
  These are the same first-order coefficients `Budget.contributionQ` already uses on the GUM side,
  so the carrier would become consistent with the ladder rather than a separate story. Until it is
  done, §4.3's warning should name the *shape* of model it excludes and not only that the treatment
  is 0th order: a reader who sees "0th order" reasonably expects a loose bound, not a sign flip on
  the loop's contraction.

  Both limits are pinned in `examples/PropertyKindCalculus/UncertaintyExamples/AdequacyLimits.lean`
  — every claim a `#guard`, importing the carrier and nothing else, so it reruns in under a second
  before anyone touches `Adequacy`. Whether the frequency and magnitude seen on one retrieval are
  representative is a separate question that more models would settle; each limit is a statement
  about the carrier's arithmetic and is worth pinning either way.

---

## 8. Value proposition — the crisp restatement

Parametrizing **both** the numeric carrier **and** the uncertainty descriptor over one WO1 model
buys a *product* of guarantees that no single-representation tool can offer:

* **Proof** (`ℝ`): the three UQ methods are provably one nested ladder; adequacy is a theorem.
* **Sensitivity** (`TapeBuilder`): exact `∂f/∂Xᵢ` for GUM/Willink and for SSPRC surrogates.
* **Noise** (`InputDist`): measurement uncertainty is a first-class, composable property of a quantity.
* **No information loss** (`FP32`/`RInterval`): certify the science model doesn't silently drop a
  small-but-significant input uncertainty — *at the scale that the same descriptor defines*.
* **Fast execution** (`CudaT`/`Float`): the identical model runs batched on GPU and on CPU.

One model. One uncertainty descriptor. Proof, sensitivity, numerical adequacy, and speed — as
*composable interpretations*, not four separate reimplementations.
