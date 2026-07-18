/-
# Validation probes — uncertainty and numerical adequacy (R14, R15, R18)

Inhabitation and axiom-profile probes for the uncertainty workstream's verifiable requirements,
whose theorems live in the Mathlib/Torch-backed `Uncertainty` / `UncertaintyRigor` libraries — the
last of the sixteen that CI did not build before the `Tests` library existed.

Inhabitation reuses the concrete worked witnesses that already apply each theorem at real numbers
(a uniform distribution's central half, a grid-absorption verdict, two Gaussian ladder terms), so
these are exercised non-vacuously; importing them here also brings them under CI. The
Mathlib-backed proofs use `[propext, Classical.choice, Quot.sound]` — the gate confirms no
`sorryAx`, with `whitespace := lax` for robustness to line-wrapping.
-/

import PropertyKindCalculus.Uncertainty.Ladder
import PropertyKindCalculus.Uncertainty.Coverage
import PropertyKindCalculus.Uncertainty.Adequacy.Soundness
import PropertyKindCalculus.Uncertainty.Adequacy.Sterbenz32
import PropertyKindCalculus.UncertaintyExamples.LadderNesting
import PropertyKindCalculus.UncertaintyExamples.AdequacyLadder
import PropertyKindCalculus.UncertaintyExamples.Coverage

namespace PropertyKindCalculus.Tests.UncertaintyLadder

open PropertyKindCalculus

/-! ## R14 — output uncertainty by a provably nested ladder (GUM ⊂ Willink) -/

-- Inhabitation: the Willink-combine's second cumulant *is* the GUM variance, applied to the
-- concrete two-Gaussian term list `normalTerms` — a real instance of the nesting law.
example := Uncertainty.willinkCumulants_kappa2 UncertaintyExamples.LadderNesting.normalTerms

/-- info: 'PropertyKindCalculus.Uncertainty.willinkCumulants_cons' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Uncertainty.willinkCumulants_cons
/-- info: 'PropertyKindCalculus.Uncertainty.willinkCumulants_kappa2' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Uncertainty.willinkCumulants_kappa2
/-- info: 'PropertyKindCalculus.Uncertainty.gum_eq_willink_of_normal' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Uncertainty.gum_eq_willink_of_normal

/-! ## R15 — numerical adequacy: no information loss at the scale of the input uncertainties -/

-- Inhabitation (fresh, self-contained): at a cancellation site the relative uncertainty reaches
-- ≥ 100% — `relUnc_amplifies` applied to concrete `d = 1`, `ũ = 2`.
example : (1 : ℝ) ≤ 2 / 1 := Uncertainty.Adequacy.relUnc_amplifies (by norm_num) (by norm_num)

-- Inhabitation (worked): the absorption verdict is exactly right on a concrete grid value.
example := UncertaintyExamples.AdequacyLadder.a3_verdict_sound

/-- info: 'PropertyKindCalculus.Uncertainty.Adequacy.verdict_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Uncertainty.Adequacy.verdict_sound
/-- info: 'PropertyKindCalculus.Uncertainty.Adequacy.relUnc_amplifies' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Uncertainty.Adequacy.relUnc_amplifies

/-! ## R18 — the recorded variance certifies a coverage interval -/

-- Inhabitation: the central half `[-1,1]` of a uniform on `[-2,2]` has coverage *exactly* 1/2 —
-- `uniform_coverage_exact` applied at a concrete distribution.
example := UncertaintyExamples.Coverage.central_half_coverage

/-- info: 'PropertyKindCalculus.Uncertainty.Coverage.coverageBound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Uncertainty.Coverage.coverageBound
/-- info: 'PropertyKindCalculus.Uncertainty.Coverage.coverageBound_stdUnc' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Uncertainty.Coverage.coverageBound_stdUnc
/-- info: 'PropertyKindCalculus.Uncertainty.Coverage.uniform_coverage_exact' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Uncertainty.Coverage.uniform_coverage_exact

end PropertyKindCalculus.Tests.UncertaintyLadder
