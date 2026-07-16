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

Further paper examples (the AFM indenter model; Willink's asymmetric and Type-A cases) arrive with
later sub-stages.
-/
import PropertyKindCalculus.UncertaintyExamples.DegenhardtFictive
import PropertyKindCalculus.UncertaintyExamples.WillinkGaugeBlock
import PropertyKindCalculus.UncertaintyExamples.DegenhardtSensitivity
import PropertyKindCalculus.UncertaintyExamples.LadderNesting
import PropertyKindCalculus.UncertaintyExamples.DegenhardtSsprc
import PropertyKindCalculus.UncertaintyExamples.SsprcNesting
import PropertyKindCalculus.UncertaintyExamples.AdequacySwamping
import PropertyKindCalculus.UncertaintyExamples.AdequacyLadder
import PropertyKindCalculus.UncertaintyExamples.AdequacyDag
import PropertyKindCalculus.UncertaintyExamples.AdequacySterbenz32
