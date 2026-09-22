/-
# Worked example — Stage 2 SSPRC on the Degenhardt fictive model

Reproduces the SSPRC run of *Degenhardt et al., Metrologia 62 (2025) 025004* §3.1 on the fictive,
intentionally non-linear model `Y = (X₁ + X₂²)·X₃` (paper eq. 12) — the same model, inputs, and
write-once kernel the Stage-0 `DegenhardtFictive` example runs under Monte Carlo. This is the
executable payoff of Stage 2: the derivative-free SSPRC pipeline (systematic sampling → separated
propagation → empirical deviation distributions → convolution) recovers the *full non-linear*
`E(Y)`/`u(Y)` — including the `E(Y) − R = 0.3375` curvature the linearized GUM rung cannot see — at a
fraction of the model evaluations.

Everything here is a **checked fact** (the module builds under CI). Mathlib- and TorchLean-free.
-/

module

public import PropertyKindCalculus.Uncertainty
meta import PropertyKindCalculus.Uncertainty
public import PropertyKindCalculus.UncertaintyExamples.DegenhardtFictive
meta import PropertyKindCalculus.UncertaintyExamples.DegenhardtFictive

public section -- pkc-blanket
@[expose] section -- pkc-blanket-expose

namespace PropertyKindCalculus.UncertaintyExamples.DegenhardtSsprc

open PropertyKindCalculus.Uncertainty
open PropertyKindCalculus.UncertaintyExamples.DegenhardtFictive

/-! ## The SSPRC run — 100 systematic samples per input -/

/-- Per-input systematic sample counts `Nᵢ`. `N_s = Σ Nᵢ = 300` model evaluations (plus the one
reference `R`), against the Monte Carlo reference's 20 000 joint draws. -/
def ns : List Nat := [100, 100, 100]

/-- The SSPRC combined result `(E(Y), u(Y))`, read from the per-input deviation distributions. -/
def ssprc : Float × Float := Ssprc.run modelF [x1, x2, x3] ns

/-- The reference value `R = f(E(X)) = 11.25`. -/
def R : Float := Ssprc.reference modelF [x1, x2, x3]

#eval s!"SSPRC  E(Y) ≈ {ssprc.1}   u(Y) ≈ {ssprc.2}   (R = {R};  evals = {Ssprc.evalCount ns})"
#eval s!"MCM    E(Y) ≈ {mcm.1}   u(Y) ≈ {mcm.2}   (evals = 20000)"
#eval s!"GUM    u_c ≈ {gum}   (linearized; misses the curvature)"
#eval s!"non-linearity signature  E(Y) − R ≈ {ssprc.1 - R}   (expect 0.3375)"

/-! ## SSPRC reproduces the ground truth at ~67× fewer evaluations

Ground truth (high-`N` Monte Carlo): `E(Y) = 11.5875`, `u(Y) ≈ 1.691`. SSPRC recovers *both* — the
mean including its non-linear `+0.3375` offset, and the standard uncertainty — from 300 evaluations,
where the Stage-0 Monte Carlo reference used 20 000 (a factor of `20000/300 ≈ 67`). -/

-- E(Y): SSPRC recovers the non-linear mean 11.5875 (GUM/Willink, linearized, only ever give R = 11.25).
#guard Float.abs (ssprc.1 - 11.5875) < 0.02
-- u(Y): SSPRC matches the ground-truth 1.691 — closer than GUM's 1.662, because it keeps the curvature.
#guard Float.abs (ssprc.2 - 1.691) < 0.05
-- The reference value is exactly 11.25.
#guard Float.abs (R - 11.25) < 1e-9
-- The non-linearity signature E(Y) − R ≈ 0.3375 (the X₂² curvature the linearized rungs drop).
#guard Float.abs ((ssprc.1 - R) - 0.3375) < 0.02
-- SSPRC's u(Y) is closer to the Monte Carlo truth than the linearized GUM value is.
#guard Float.abs (ssprc.2 - 1.691) < Float.abs (gum - 1.691)
-- Additive evaluation budget: N_s = 300 (+1 reference), vs the reference Monte Carlo's 20 000.
#guard Ssprc.evalCount ns == 301

/-! ## The convolution engine agrees with the moment-addition read-off

`run` reads `E(Y)`/`u(Y)` from the per-input distributions (means and variances add under
convolution, so it never materializes the convolution). `runConv` performs the actual discrete
convolution and reads the moments off the combined distribution. They must agree — a cross-check of
the convolution engine — shown here at a modest `Nᵢ = 20` (so the convolution is `20³ = 8000`
points). -/

/-- Small per-input counts so the full convolution is cheap to materialize. -/
def nsSmall : List Nat := [20, 20, 20]

/-- Moment-addition read-off at the small sample count. -/
def ssprcSmall : Float × Float := Ssprc.run modelF [x1, x2, x3] nsSmall
/-- The actual-convolution read-off at the same sample count. -/
def ssprcConv : Float × Float := Ssprc.runConv modelF [x1, x2, x3] nsSmall

#eval s!"run     (moment add) E(Y)={ssprcSmall.1}  u(Y)={ssprcSmall.2}"
#eval s!"runConv (convolution) E(Y)={ssprcConv.1}  u(Y)={ssprcConv.2}"

-- The convolution reproduces the moment-addition read-off to machine precision.
#guard Float.abs (ssprcConv.1 - ssprcSmall.1) < 1e-6
#guard Float.abs (ssprcConv.2 - ssprcSmall.2) < 1e-6

end PropertyKindCalculus.UncertaintyExamples.DegenhardtSsprc

end -- pkc-blanket-expose
end -- pkc-blanket
