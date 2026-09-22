/-
# Worked example — Stage 4 sensitivity-driven sample allocation for SSPRC

SSPRC's cost is *additive*: `N_s = Σ Nᵢ`, one budget per input, propagated separately
(`DegenhardtSsprc` spent a flat `[100, 100, 100]`). Stage 4 spends that budget where it changes the
answer. `Allocation.allocate` ranks the inputs by their **contribution to the combined uncertainty**
`wᵢ = |cᵢ|·uᵢ` — the per-input GUM variance summand — and apportions the whole budget in proportion,
by largest remainder, dropping negligible inputs (Degenhardt §4; `UNCERTAINTY.md` §3.2 item 3).

On the fictive model `Y = (X₁ + X₂²)·X₃` the sensitivities at the means are `c = (5, 5, 2.25)` (the
same coefficients `DegenhardtFictive.gum` uses and `DegenhardtSensitivity` derives from autograd),
and the input standard uncertainties are `u = (0.2, 0.45/√3, 0.3/√6)`. So the contributions are

    w₁ = 5·0.2      = 1.000     (X₁, normal)
    w₂ = 5·0.45/√3  ≈ 1.299     (X₂, uniform — the widest input, and it ties X₁'s sensitivity)
    w₃ = 2.25·0.3/√6 ≈ 0.276    (X₃, triangular — the least influential)

X₂ dominates the uncertainty budget and X₃ is minor, so a flat split over-samples X₃. This example is
entirely **checked facts** (`#guard`): the allocation arithmetic exactly, and — the payoff — that
running SSPRC on the allocated `ns` reproduces the ground-truth `E(Y)`/`u(Y)`, even at a budget cut
that a flat split could not afford. Mathlib- and TorchLean-free.
-/

module

public import PropertyKindCalculus.Uncertainty
meta import PropertyKindCalculus.Uncertainty
public import PropertyKindCalculus.UncertaintyExamples.DegenhardtFictive
meta import PropertyKindCalculus.UncertaintyExamples.DegenhardtFictive

public section -- pkc-blanket
@[expose] section -- pkc-blanket-expose

namespace PropertyKindCalculus.UncertaintyExamples.DegenhardtAllocation

open PropertyKindCalculus.Uncertainty
open PropertyKindCalculus.Uncertainty.Allocation
open PropertyKindCalculus.UncertaintyExamples.DegenhardtFictive

/-! ## The contribution ranking `wᵢ = |cᵢ|·uᵢ`

The `(cᵢ, momentsᵢ)` terms are exactly `DegenhardtFictive.gum`'s: hand-supplied sensitivities
`(5, 5, 2.25)` paired with the three inputs' moments. (`DegenhardtSensitivity` shows one autograd
reverse pass over the *same* write-once kernel reproduces these `cᵢ` — so the whole pipeline, from
`cᵢ` to allocation, consumes only quantities it already computes.) -/

/-- Sensitivity coefficient paired with input moments — the shape `Combine`/`Sensitivity` use. -/
def terms : List (Float × MomentData Float) :=
  [(5.0, x1.moments), (5.0, x2.moments), (2.25, x3.moments)]

/-- The per-input contributions to the combined standard uncertainty. -/
def ws : List Float := contributions terms

#eval s!"contributions  w = {ws}   (expect ≈ [1.000, 1.299, 0.276])"

-- w₁ = 5·√(0.2²) = 1 ;  w₂ = 5·√(0.45²/3) ≈ 1.299 ;  w₃ = 2.25·√(0.3²/6) ≈ 0.2756.
#guard Float.abs (ws[0]! - 1.0)      < 1e-6
#guard Float.abs (ws[1]! - 1.299038) < 1e-6
#guard Float.abs (ws[2]! - 0.275568) < 1e-6
-- X₂ contributes most, X₃ least — the ranking the allocation must respect.
#guard ws[1]! > ws[0]! && ws[0]! > ws[2]!

/-! ## The allocation — proportion the budget, exactly

A total budget of 300 systematic samples (matching `DegenhardtSsprc`'s flat `[100,100,100]`) split
by contribution: X₂ gets the most, X₃ the fewest, and the counts sum to the budget exactly. -/

/-- The sensitivity-driven per-input counts at a 300-sample budget. -/
def ns300 : List Nat := allocateFromTerms 300 terms

#eval s!"allocate 300   ns = {ns300}   (Σ = {ns300.foldl (·+·) 0})"

-- Proportional to w = [1.000, 1.299, 0.276]: X₂ dominant, X₃ minor.
#guard ns300 == [117, 151, 32]
-- The whole budget is spent (largest-remainder apportionment is exact).
#guard ns300.foldl (· + ·) 0 == 300
-- Sample count follows the contribution ranking: N₂ ≥ N₁ ≥ N₃.
#guard ns300[1]! ≥ ns300[0]! && ns300[0]! ≥ ns300[2]!
-- X₃ (least influential) draws ~4.7× fewer samples than X₂ — the flat split's wasted effort.
#guard ns300[1]! ≥ 4 * ns300[2]!
-- Budget conservation holds at other totals, too.
#guard (allocateFromTerms 120 terms).foldl (· + ·) 0 == 120
#guard (allocateFromTerms 30  terms).foldl (· + ·) 0 == 30

/-! ## Dropping a negligible input

`dropRatio` zeroes any input whose contribution is below that fraction of the largest — its deviation
distribution is a point mass, so it neither moves `E(Y)`/`Var(Y)` nor costs evaluations. Here a third
input at `0.05` (5 % of the leading `1.0`) is dropped at `dropRatio = 0.2`, and its share is
reapportioned to the survivors (the budget stays whole). -/

/-- Two clear contributors and one negligible tail input. -/
def wsDrop : List Float := [1.0, 0.5, 0.05]

#eval s!"drop 0.2 : {allocate 300 wsDrop 0.2}     keep 0.0 : {allocate 300 wsDrop 0.0}"

-- At dropRatio 0.2 the 0.05 input (< 0.2·1.0) is dropped; its budget goes to the 2:1 survivors.
#guard allocate 300 wsDrop 0.2 == [200, 100, 0]
-- Kept (dropRatio 0), all three are sampled and the budget is still exactly 300.
#guard (allocate 300 wsDrop 0.0).foldl (· + ·) 0 == 300
#guard (allocate 300 wsDrop 0.0)[2]! > 0
-- Degenerate model (no input has any uncertainty) ⇒ equal split, budget still conserved.
#guard allocate 300 [0.0, 0.0, 0.0] == [100, 100, 100]

/-! ## The payoff — the allocated run reproduces the ground truth

Ground truth (high-`N` Monte Carlo): `E(Y) = 11.5875`, `u(Y) ≈ 1.691`. Running SSPRC on the
**allocated** `ns` recovers both — the mean including its non-linear `+0.3375` offset — just as the
flat `[100,100,100]` did. The point of the allocation is the *next* line: a 120-sample budget (a 60 %
cut) still lands the mean, because the samples it keeps are on the inputs that matter. -/

/-- SSPRC at the 300-sample sensitivity allocation. -/
def ssprc300 : Float × Float := Ssprc.run modelF [x1, x2, x3] ns300
/-- SSPRC at a 120-sample sensitivity allocation (`[47, 60, 13]`). -/
def ssprc120 : Float × Float := Ssprc.run modelF [x1, x2, x3] (allocateFromTerms 120 terms)

#eval s!"SSPRC @300 alloc  E(Y)={ssprc300.1}  u(Y)={ssprc300.2}   (evals {Ssprc.evalCount ns300})"
#eval s!"SSPRC @120 alloc  E(Y)={ssprc120.1}  u(Y)={ssprc120.2}   (evals {Ssprc.evalCount (allocateFromTerms 120 terms)})"

-- The allocated 300-sample run reproduces the non-linear mean and the standard uncertainty.
#guard Float.abs (ssprc300.1 - 11.5875) < 0.02
#guard Float.abs (ssprc300.2 - 1.691)   < 0.05
-- And a 60 %-smaller budget still lands the mean (to the same tolerance) and u to within 0.05 —
-- because the 60 % it dropped was mostly X₃'s over-sampling, not signal.
#guard Float.abs (ssprc120.1 - 11.5875) < 0.02
#guard Float.abs (ssprc120.2 - 1.691)   < 0.05
-- Additive budgets: 301 and 121 model evaluations (+1 reference each), vs Monte Carlo's 20 000.
#guard Ssprc.evalCount ns300 == 301
#guard Ssprc.evalCount (allocateFromTerms 120 terms) == 121

end PropertyKindCalculus.UncertaintyExamples.DegenhardtAllocation

end -- pkc-blanket-expose
end -- pkc-blanket
