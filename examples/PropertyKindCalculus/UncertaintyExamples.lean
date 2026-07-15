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

Further paper examples (Degenhardt's SSPRC systematic-sampling run and the AFM indenter model;
Willink's asymmetric and Type-A cases) arrive with Stages 2–3.
-/
import PropertyKindCalculus.UncertaintyExamples.DegenhardtFictive
import PropertyKindCalculus.UncertaintyExamples.WillinkGaugeBlock
import PropertyKindCalculus.UncertaintyExamples.DegenhardtSensitivity
import PropertyKindCalculus.UncertaintyExamples.LadderNesting
