# UNCERTAINTY.md — A rigor-first plan for uncertainty & numerical adequacy in PKC

> Status: **design/plan** (no code yet). Audience: PKC maintainers.
> Scope: augment PropertyKindCalculus in two coupled areas —
> (1) **uncertainty quantification** (UQ) of model outputs from input uncertainties, and
> (2) **numerical adequacy** of the floating-point representation of a science model.
> Both are realized *through PKC's existing carrier-parametric quantity design*, and both
> are driven by **one shared uncertainty descriptor** attached to quantities.
>
> Expanding the dependency on TorchLean is in-scope and expected (autograd functional API,
> the `NeuralFloat`/`FP32` error lemmas, the sound `RInterval` carrier, FFT kernels).

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
| `TapeBuilder` | `cᵢ=∂f/∂Xᵢ`, `hᵢ=∂²f/∂Xᵢ²`, HVP, Jacobian ([`TapeCarrier.lean`](PropertyKindCalculus/torch/PropertyKindCalculus/Torch/Paradigm/TapeCarrier.lean)) | **Sensitivity** — GUM/Willink coefficients, contribution ranking, nonlinearity gauge, Taylor surrogates for SSPRC | ✅ `cᵢ` wired (`Sensitivity.lean`, Stage 1); `hᵢ`/HVP Stage 2 |
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
| **Exact cancellation, amplified uncertainty** | `a ⊖ b`, `a≈b`: subtraction is *exact* (no rounding) but *relative* uncertainty blows up | FLX Sterbenz `neural_generic_format_FLX_sterbenz` (`Analysis/Sterbenz.lean:146`) + FLT↔FLX transport (`Error/Multiplication.lean:157`) | FP32/FLT Sterbenz instance; the relative-amplification bound (UQ-level, from `cᵢ`) |
| **Bounded accumulated rounding error** | total FP noise over the whole evaluation ≤ a fraction of the output uncertainty | `(1+δ)` model `neural_round_relative_error_ulp` (`Error/Bounds.lean:139`); FP32 `u=2⁻²⁴` `round_relative_error_of_normal` (`FP32/Error.lean:79`); per-op `add/sub/mul/div_abs_error` (`FP32/Error.lean:99–148`) | DAG-composition of per-op bounds; comparison to `u_Y` |
| **Adequate dynamic range** | no overflow/underflow on the input box | `RInterval` sound enclosures (`Interval/Quantized.lean`), `minNormal=2⁻¹²⁶`, `ieeeMaxFinite` (`FP32/Core.lean:150,160`) | range check vs. `InputDist.support` |

Half-ULP workhorse already available: `FP32.round_abs_error : |round₃₂ x − x| ≤ eps₃₂ x`
(`FP32/Error.lean:73`), `eps₃₂ x = ulp₃₂ x / 2`. Error-free transforms
(`FP32.add_residual_isRepresentable`, `FP32/Error.lean:111`) give exact residuals for
compensated-summation reasoning if we want tighter accumulation bounds.

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
  theorem that makes "no information loss" a *proof*, not a heuristic.

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
  Method.lean           ▫ UncertaintyMethod structure + monoid laws               [Area 1 core]
  Method/Ssprc.lean     ▫ def ssprc (systematic sampling, DDE, FFT convolution)   [Stage 2]
  Sensitivity.lean      ✅ autograd bridge: cᵢ via TapeBuilder reverse tape        [Axis N, Stage 1]
  Ladder.lean           ✅ T1 (cumulant additivity), T2 (gum = willink|κ₄=0) / ℝ  [rigor, Stage 1]
                           (T3–T5 arrive with SSPRC in Stage 2)
  Adequacy.lean         ▫ Adequacy carrier + NumCarrier instance                  [Area 2, Stage 3]
  Adequacy/Absorption.lean ▫ A1 absorption theorem
  Adequacy/Sterbenz32.lean ▫ A2 FP32 Sterbenz (transport from FLX)
  Adequacy/Soundness.lean  ▫ A3 capstone
```

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
  DegenhardtSsprc.lean    ▫ Degenhardt SSPRC systematic-sampling run (Stage 2)
  DegenhardtAfm.lean      ▫ Degenhardt §3.2 AFM indenter PAF, ~70× efficiency (Stage 2)
  WillinkAsymmetric.lean  ▫ Willink §5 asymmetric input (κ₃) + Type-A t-cases (Stage 1)
  AdequacySwamping.lean   ▫ a deliberately-inadequate model the Adequacy carrier flags (Stage 3)
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

* **Stage 2 — SSPRC pipeline.** Systematic sampling (inverse-CDF), separated propagation, DDE
  reconstruction, FFT convolution; T3, T4, T5. Optional autograd Taylor surrogate (§3.2 item 2)
  gated by the `hvp` nonlinearity gauge.
  *Exit:* SSPRC agrees with MCM on the fictive example at ~70× fewer evals; T3 links it to Willink.

* **Stage 3 — Numerical adequacy.** `Adequacy` carrier (runtime certificate) over `RInterval`+FP32;
  A1 absorption theorem; A2 FP32 Sterbenz; A3 soundness. Demonstrate a *deliberately inadequate*
  model (small-uncertainty input swamped by a large accumulator) that the carrier flags, and an
  adequate variant that certifies clean.
  *Exit:* A3 is a theorem; the flagged/clean pair is a reflection test (indexed per the project's
  reflection-tests convention).

* **Stage 4 — Scale.** GPU-batched SSPRC/MCM on `CudaT`; sensitivity-driven `Nᵢ` allocation; a
  real downstream science model (soil-moisture retrieval) as the capstone example.

Reflection/CI note: each new proof file gets a paired, *indexed* reflection probe (per the
project's convention that an un-indexed probe is never built and silently rots).

---

## 7. Risks & open decisions

* **Autograd op coverage.** TorchLean's tape/CUDA elementwise surface is
  `add/sub/mul/div/scale/min/max/relu` + `abs/sqrt/exp/log` — **no `sin/cos/tanh/sinh/cosh`** with
  VJP. Models using trig can be *evaluated* (Float/CudaT have the transcendentals as values) but not
  *differentiated* on the tape until `_fwd/_bwd` nodes are added. Decision: accept the exp/log/sqrt
  model class for Stages 1–2, or fund the trig VJP nodes early.
* **Toolchain / build coupling.** PKC is pinned `v4.32.0` (Mathlib v4.32.0, TorchLean `combined`).
  Stage 0 avoids the issue entirely (Mathlib/TorchLean-free). Stage 1+ pull in much more of
  TorchLean (autograd + interval + FFT), enlarging build surface and tightening the PKC↔TorchLean
  coupling (cf. the FGM↔DVB single-toolchain constraint). Note TorchLean 4.32 renamed the autograd
  functional API (`fn1`→`func`); the `Sensitivity` bridge must target `func.grad`/`func.hessian`.
  Budget a bump-in-lockstep workflow.
* **`Adequacy` carrier laws.** It is a `NumCarrier` that *also* accumulates a report; the monoid/branchless
  discipline of `NumCarrier` must not be violated by the check (the check is a side-record, the numeric
  `value`/`range` stay branchless). Verify the instance is lawful.
* **Pearson percentile fidelity.** Willink eqs. (6)/(7) are rational fits valid for `−1.2 ≤ γ ≤ 6`;
  outside that range the closure degrades. Decision: clamp + warn, or implement the exact Pearson
  quantile.
* **`CarrierRefinement` consolidation.** It is PKC's class (`QuantityRefinement.lean:47`), instantiated
  for `FP32↔ℝ` in the `Torch` lib; TorchLean itself has no such class (it uses `Context` + `toReal` +
  per-op error bridges). Decide whether A3's soundness routes through `CarrierRefinement` or directly
  through the TorchLean `*_abs_error` lemmas.

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
