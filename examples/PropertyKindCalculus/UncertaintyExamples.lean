/-
# `PropertyKindCalculus.UncertaintyExamples` — worked, paper-grounded uncertainty examples

Checked facts exercising the Stage-0 uncertainty layer against the two source papers of
`UNCERTAINTY.md`. Each example reproduces a headline number from its paper, so the library
building under CI is what makes the claims true rather than asserted.

  * `DegenhardtFictive` — Degenhardt et al. (2025) §3.1, the non-linear fictive model
    `Y = (X₁ + X₂²)·X₃`: Monte Carlo reference `E(Y)/u(Y)` + the GUM linearized cross-check,
    exhibiting the non-linearity gap.
  * `WillinkGaugeBlock` — Willink (2005) Table 4, the gauge-block calibration: the cumulants
    method reproducing `u_Y = 33.4 nm`, `γ_Y = 0.124`, `h₀.₉₉ = 87.6 nm`.

Stage-1 additions (these two pull in Mathlib and TorchLean respectively):
  * `DegenhardtSensitivity` — the fictive model's GUM sensitivities `cᵢ` sourced from TorchLean
    autograd over the write-once kernel, reproducing the hand-supplied `[5, 5, 2.25]` and the GUM
    `u_c ≈ 1.662`.
  * `LadderNesting` — the T1/T2 nesting theorems (`gum = willink|κ₄=0`) applied to a concrete
    term list over `ℝ`, plus the executable `Float` shadow of the collapse.

Stage-2 additions (the derivative-free SSPRC method):
  * `DegenhardtSsprc` — the SSPRC pipeline on the same fictive model, recovering the ground-truth
    `E(Y) = 11.5875` (incl. its non-linear offset) and `u(Y) ≈ 1.69` at ~67× fewer model
    evaluations than the Monte Carlo reference; the convolution engine cross-checks against the
    moment read-off.
  * `SsprcNesting` — the T3/T4/T5 ladder theorems (`convolution adds cumulants`, `willink is the
    projection of the linearized SSPRC`, `affine ⇒ E(Y)=R`) applied to concrete distributions over
    `ℝ`, plus the sorry-free axiom profile.

Stage-4 additions (Scale — allocation + the science-model capstone):
  * `DegenhardtAllocation` — the sensitivity-driven `Nᵢ` allocation on the fictive model: rank the
    inputs by `wᵢ = |cᵢ|·uᵢ`, largest-remainder-split a 300-sample SSPRC budget (`[117, 151, 32]`,
    X₂ dominant), drop negligible inputs, and reproduce `E(Y)/u(Y)` even at a 60 %-cut budget.
  * `WaterCloudModel` — **the capstone.** One write-once Water Cloud Model soil-moisture forward
    `σ⁰ = A·ndvi·(1−τ) + τ·(C·mv + D)`, `τ = exp(−2B·ndvi)`, driven through the whole pipeline: the
    `Float` forward, the TorchLean-autograd Jacobian (matched to the hand-derived closed forms), the
    GUM/Willink combine, the derivative-free SSPRC (recovering the `exp`-curvature mean offset), and
    the Stage-4 allocation — which ranks soil moisture (the retrieval target) dominant and drops the
    canopy coefficient. Self-contained (PKC cannot import the downstream soil-moisture-model — that
    package already requires PKC); depends on TorchLean for the autograd column.

Stage-3 additions (numerical adequacy):
  * `AdequacySwamping` — the executable `Adequacy` carrier: one WO1 kernel flags floating-point
    swamping under a large accumulator (and certifies clean under a small one), a second flags
    catastrophic cancellation (and certifies clean when the operands are well separated).
  * `AdequacyLadder` — the `ℝ`-level adequacy theorems A1 (absorption), A2 (Sterbenz), A3 (verdict
    soundness) applied to concrete values, with the sorry-free axiom profile.

Stage-3.1 addition (the universal, whole-evaluation lift of A3):
  * `AdequacyDag` — the capstone A3′ (`Adequacy.DagBound`) instantiated on concrete model DAGs (a
    three-input accumulator, an add/sub variant, a deeper five-input tree): the FP32 measurand's
    variation over an input box equals the `ℝ` one up to the DAG-additive rounding budget, and
    *exactly* when no site rounds (flag-free). Sorry-free axiom profile confirmed.

Stage-3.2 addition (A2 at the real binary32 format):
  * `AdequacySterbenz32` — A2 (Sterbenz) lifted from the `FLX` model to TorchLean's genuine
    `fexp32 = FLTExp (−149) 24` (gradual underflow): `round₃₂ (u − v) = u − v` and `(a − b).val =
    a.val − b.val` for near-equal representable binary32 values, so the `sub32_within_half_ulp` bound
    collapses to zero. Grounded in the Stage-3.2 TorchLean PR (`neural_generic_format_FLT_sterbenz`).

Stage-3.3 addition (the executable↔spec bridge):
  * `AdequacyExecBridge` — the runtime adequacy verdict certified against the specification. The
    executable ULP `ulpExp` and absorption test `absorbs` run over TorchLean's computable
    `IEEE32Exec` (concrete `#guard`s at `2²⁵` and `10⁸`), while `exec_verdict` proves that whenever
    the kernel reports absorption, the exact real sum rounds back under the binary32 `round₃₂` spec —
    the computed verdict is provably the specified one. Sorry-free axiom profile confirmed.

Stage-3.6 addition (the direct P↔R simulation, closed; + the eager-provenance addendum):
  * `AutogradDirectSim` — the closed `PRSim` obligations instantiated concretely: the
    vectorization homomorphisms at a 3-vector shape; the compiled product graph `x₀ * x₁` with
    the `direct_PR_soundness_compiled` endpoint (runtime dense reverse pass = `(fderiv eval)†`
    on the input prefix) and its inhabited `ForwardSim`; an eager two-leaf/`mul` tape whose
    `BackwardShapeWF` is discharged constructor by constructor; and `EagerBuilds` witnessing
    that runtime tape with `direct_PR_soundness_eager` giving the endpoint on it — no
    compilation involved. Axiom pins confirm the classical trio only.

Residual-2 addition (the kinded ×/÷ budget DAG):
  * `BudgetDagDensity` — a genuinely *heterogeneous* ×/÷ budget: block density `ρ = m/((l·w)·h)`
    threads five distinct kinds (mass, length, area, volume, mass density) through one
    `BudgetExpr`, every edge carrying its `ProductKind`/`QuotientKind` witness — a model the
    homogeneous-input `analyzeQ` cannot type at all. `#guard`s pin ρ = 2500, the four per-leaf
    contributions [1.0, 2.5, 5.0, 25.0] and u_c = √657.25 ≈ 25.637, plus the executable `Float`
    shadow of the ℝ collapse law (`propagateQ` agrees with `combinedQ ∘ contribsQ`);
    `#check_failure` probes make the operand swap, the heterogeneous quadrature, and the
    kind-misplaced leaf type errors; the capstone's axiom pin is the classical trio only.

Further paper examples (the AFM indenter model; Willink's asymmetric and Type-A cases) arrive with
later sub-stages.
-/
import PropertyKindCalculus.UncertaintyExamples.DegenhardtFictive
import PropertyKindCalculus.UncertaintyExamples.WillinkGaugeBlock
import PropertyKindCalculus.UncertaintyExamples.DegenhardtSensitivity
import PropertyKindCalculus.UncertaintyExamples.LadderNesting
import PropertyKindCalculus.UncertaintyExamples.DegenhardtSsprc
import PropertyKindCalculus.UncertaintyExamples.SsprcNesting
import PropertyKindCalculus.UncertaintyExamples.DegenhardtAllocation
import PropertyKindCalculus.UncertaintyExamples.WaterCloudModel
import PropertyKindCalculus.UncertaintyExamples.AdequacySwamping
import PropertyKindCalculus.UncertaintyExamples.AdequacyLadder
import PropertyKindCalculus.UncertaintyExamples.AdequacyDag
import PropertyKindCalculus.UncertaintyExamples.AdequacySterbenz32
import PropertyKindCalculus.UncertaintyExamples.AdequacyExecBridge
import PropertyKindCalculus.UncertaintyExamples.AdequacyCoupling
import PropertyKindCalculus.UncertaintyExamples.AutogradDirectSim
import PropertyKindCalculus.UncertaintyExamples.BudgetDagDensity
import PropertyKindCalculus.UncertaintyExamples.Coverage
