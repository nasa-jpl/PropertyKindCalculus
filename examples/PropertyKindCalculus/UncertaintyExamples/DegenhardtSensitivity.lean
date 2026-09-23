/-
# Worked example — Stage 1 autograd sensitivities for the Degenhardt fictive model

The Stage-0 `DegenhardtFictive` example supplied the GUM sensitivity coefficients
`c₁ = ∂Y/∂X₁ = X₃ = 5`, `c₂ = ∂Y/∂X₂ = 2·X₂·X₃ = 5`, `c₃ = ∂Y/∂X₃ = X₁ + X₂² = 2.25`
*by hand*. Stage 1 sources them from **TorchLean autograd** instead — a single reverse pass over
the *same write-once kernel* `fictiveModel` (`UNCERTAINTY.md` §3.2 item 1).

This is the WO1 payoff made concrete: `fictiveModel {α} [NumCarrier α] (a b c : α)` is the very
definition Monte Carlo runs at `α := Float`; here the identical source is instantiated at
`α := TapeBuilder .scalar` and differentiated. No second model. The autograd `cᵢ` reproduce the
hand-computed values to machine precision, and feeding them through `gumStdUnc` reproduces the
Stage-0 GUM combined uncertainty `u_c ≈ 1.662` exactly.

Everything here is a **checked fact** (the module builds under CI). It exercises the Stage-1
`Sensitivity` bridge end to end. Depends on TorchLean (the tape carrier); it is the first
uncertainty example that does.
-/

module

public import PropertyKindCalculus.Uncertainty.Sensitivity
meta import PropertyKindCalculus.Uncertainty.Sensitivity
public import PropertyKindCalculus.UncertaintyExamples.DegenhardtFictive
meta import PropertyKindCalculus.UncertaintyExamples.DegenhardtFictive

@[expose] public section Blanket

namespace PropertyKindCalculus.UncertaintyExamples.DegenhardtSensitivity

open PropertyKindCalculus.Paradigm (TapeBuilder)
open PropertyKindCalculus.Uncertainty
open PropertyKindCalculus.UncertaintyExamples.DegenhardtFictive

/-- The write-once fictive kernel `Y = (X₁ + X₂²)·X₃` presented to the autograd bridge as an
arity-3 `ScalarModel`. The body is exactly `fictiveModel a b c` — the same source run at `Float`
for Monte Carlo — now interpreted at `α := TapeBuilder .scalar`; only the list adapter is new. -/
def modelTape : Sensitivity.ScalarModel
  | [a, b, c] => fictiveModel a b c
  | _ => 0

/-! ## Autograd sensitivities at the input means -/

/-- The sensitivity coefficients `cᵢ = ∂Y/∂Xᵢ` at `E(X) = (2, 0.5, 5)`, from one reverse pass. -/
def cs : List Float := (Sensitivity.gradient modelTape [2.0, 0.5, 5.0]).toOption.getD []

#eval s!"autograd c = {cs}   (expect [5, 5, 2.25])"

-- ∂Y/∂X₁ = X₃ = 5 ;  ∂Y/∂X₂ = 2·X₂·X₃ = 5 ;  ∂Y/∂X₃ = X₁ + X₂² = 2.25.
#guard cs.length == 3
#guard Float.abs (cs[0]! - 5.0) < 1e-6
#guard Float.abs (cs[1]! - 5.0) < 1e-6
#guard Float.abs (cs[2]! - 2.25) < 1e-6

/-! ## GUM with autograd-sourced sensitivities reproduces the Stage-0 number -/

/-- GUM combined standard uncertainty with **autograd-sourced** sensitivities — the Stage-1
`extract` feeding the Stage-0 `combine`. A `0.0` sentinel on autograd failure makes the guard
fail loudly rather than silently pass. -/
def gumAuto : Float :=
  match Sensitivity.coefficients modelTape [x1, x2, x3] with
  | .ok terms => gumStdUnc terms
  | .error _ => 0.0

#eval s!"GUM (autograd cᵢ) u_c ≈ {gumAuto}   (Stage-0 hand-supplied: 1.662)"
#guard Float.abs (gumAuto - 1.662) < 0.01

end PropertyKindCalculus.UncertaintyExamples.DegenhardtSensitivity

end Blanket
