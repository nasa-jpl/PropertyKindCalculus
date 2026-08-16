/-
# Validation probes — evidence across repeated measurements (`Uncertainty.Evidence`)

Executable probes for the Type A evaluation, the `t`-based coverage factor, Welch–Satterthwaite,
and the accumulation rules. `Evidence` is Mathlib-free and computes, so these are `#guard`s over
real arithmetic rather than axiom-profile gates: each one fails the build if the number moves.

Floats are compared to a relative tolerance, never with `==` — a probe that pins a float bit
pattern tests the platform's libm as much as it tests the module.

The claims worth a probe are the ones that are easy to get wrong, and each is a metrological
statement rather than an implementation detail:
  * the Type A evaluation gives the standard deviation *of the mean*, `s/√n`, not `s`;
  * `n < 2` yields no evaluation at all, rather than a `u` of zero;
  * the coverage factor is `t_p(ν)` while `ν` is small, and reaches `1.96` only at `ν = ∞`;
  * pooling drops `u` and *raises* `ν`, so a guard band built on it tightens on both counts;
  * a Type B prior is **displaced** by data, never averaged with it.
-/

import PropertyKindCalculus.Uncertainty.Evidence

namespace PropertyKindCalculus.Tests.Evidence

open PropertyKindCalculus.Uncertainty

/-- Relative closeness, for probes that pin a computed number rather than a bit pattern. -/
private def close (a b : Float) : Bool :=
  let scale := if b.abs > 1e-9 then b.abs else 1e-9
  (a - b).abs ≤ 1e-6 * scale

/-! ## GUM 4.2 — the Type A evaluation -/

/-- Five indications with mean exactly `10` and `s² = 0.025`, so `s = 0.1581…` and the standard
uncertainty of the *mean* is `s/√5 = 0.070711`. -/
private def five : List Float := [10.0, 10.2, 9.8, 10.1, 9.9]

-- The estimate is the mean, `u` is `s/√n` (**not** `s`), and `ν = n − 1`.
#guard (typeA five).any fun e =>
  close e.estimate 10.0 && close e.stdUnc 0.0707106781186547 && close e.dof 4.0

-- One indication supports an estimate and no dispersion: the honest result is *no evaluation*.
-- A `u` of zero here would claim the opposite of what one reading knows.
#guard (typeA [10.0]).isNone
#guard (typeA []).isNone

/-! ## GUM 4.3.7 — the rectangular prior, and its `ν = ∞` -/

/-- The deployment's own Type B prior: two bracketing observations, nothing about where between
them the truth lies. `u = a/√3`. -/
private def prior : Evidence := typeBRectangular 985.5 1763.6

#guard close prior.estimate 1374.55 && close prior.stdUnc 224.61812246
#guard !prior.dofIsFinite
-- An asserted bound has no sampling variability, so its coverage factor is the Gaussian one.
#guard prior.coverageFactor95 = some 1.960

/-! ## GUM Table G.2 — the coverage factor while `n` is small -/

-- At `ν = 4` the 95 % factor is `2.776` — **42 % wider** than the asymptotic `1.96` a Gaussian
-- assumption would have used on the same five readings.
#guard (typeA five).bind (·.coverageFactor95) = some 2.776
#guard (typeA five).bind (·.coverageFactor99) = some 4.604

-- Non-integer `ν` truncates downwards (G.4.1), and a gap in the table reads at its lower entry:
-- both roundings give the *larger* factor, so an interval is never narrower than the table.
#guard ({ estimate := 0.0, stdUnc := 1.0, dof := 4.9, evalKind := .typeA } : Evidence).coverageFactor95
  = some 2.776
#guard ({ estimate := 0.0, stdUnc := 1.0, dof := 13.0, evalKind := .typeA } : Evidence).coverageFactor95
  = some 2.179

-- Below the table there is no factor to state, and inventing one is how a coverage statement
-- becomes a fiction.
#guard ({ estimate := 0.0, stdUnc := 1.0, dof := 0.5, evalKind := .typeA } : Evidence).coverageFactor95
  = none

-- The expanded uncertainty is `t·u`.
#guard ((typeA five).bind (·.expanded95)).any (close · (2.776 * 0.0707106781186547))

/-! ## The `t` moments — and where they stop existing -/

-- `ν = 4`: a `t` with four degrees of freedom has no fourth moment, so there is no cumulant to
-- state. `none`, not `0` — `0` would claim normality of the least normal case.
#guard ((typeA five).bind (·.momentsT)).isNone
-- `ν = ∞`: the `t` reading collapses to the Gaussian one, which is the same statement.
#guard prior.momentsT.any fun m =>
  close m.variance (prior.stdUnc * prior.stdUnc) && close m.fourthCumulant 0.0

/-! ## GUM G.4.1 — effective degrees of freedom -/

-- A well-observed contributor (`ν = 4`) and a thin one (`ν = 2`) of comparable weight: the
-- combination is entitled to neither's `ν`, but to something between them.
#guard
  let thin : Evidence := { estimate := 0.0, stdUnc := 0.5, dof := 2.0, evalKind := .typeA }
  (welchSatterthwaite [(1.0, (typeA five).get!), (1.0, thin)]).any fun nu =>
    2.0 ≤ nu && nu ≤ 4.0

-- Every contributor unqualified ⇒ the combination is too. No sampling variability entered, so
-- the Gaussian factor is the right one, and it falls out of `x/∞ = 0` rather than out of a case.
#guard (welchSatterthwaite [(1.0, prior), (2.0, prior)]).any fun nu => !(nu < dofUnbounded)

-- Nothing to qualify: a zero `u_c` has no degrees of freedom, not infinitely many.
#guard (welchSatterthwaite []).isNone

/-! ## Accumulation — the four rules -/

private def a5 : Evidence := (typeA five).get!
private def b5 : Evidence := (typeA [10.05, 9.95, 10.15, 9.85, 10.0]).get!

-- **Pooled.** Two data-derived evaluations: `u` falls and `ν` rises. Both directions matter — a
-- guard band `k·u` tightens because `u` shrinks *and* because the `k` that qualifies it does.
#guard match a5.accumulate b5 with
  | .pooled e => e.stdUnc < a5.stdUnc && e.stdUnc < b5.stdUnc && e.dof > a5.dof
      && e.coverageFactor95.any (· < 2.776)
  | _ => false

-- **Displaced.** A statement of ignorance meets data: the data replaces it outright. The pooled
-- alternative is what this rule exists to forbid — inverse-variance weighting would leave the
-- prior's estimate visible forever, since an asserted half-width never shrinks.
#guard match prior.accumulate a5 with
  | .displaced e => close e.estimate a5.estimate && close e.stdUnc a5.stdUnc
  | _ => false

-- **Retained.** A fresh assertion is not an observation; evidence in hand outranks it.
#guard match a5.accumulate prior with
  | .retained e => close e.estimate a5.estimate
  | _ => false
#guard match prior.accumulate prior with | .retained _ => true | _ => false

-- **Refused.** A `u` of exactly zero is a legitimate record — a deterministic instrument has no
-- dispersion to evaluate — and carries infinite weight, so pooling it would silently *replace*
-- the other evaluation while looking like a combination.
#guard match
    ({ estimate := 100.0, stdUnc := 0.0, dof := dofUnbounded, evalKind := .typeA } : Evidence).accumulate a5 with
  | .refused e _ => close e.estimate 100.0
  | _ => false

-- Every case carries the evidence to hold afterwards, so a caller always has a number.
#guard close (a5.accumulate b5).evidence.estimate 10.0

/-! ## The combined evidence a conformity assessment consumes -/

-- `u_c` from the contributors' moments, `ν_eff` from the same terms, and the tag that says it is
-- an evaluation of neither type.
#guard (combinedEvidence 42.0 [(1.0, a5), (2.0, prior)]).any fun e =>
  close e.estimate 42.0 && e.evalKind = .combined
  && close e.stdUnc (Float.sqrt (a5.stdUnc * a5.stdUnc + 4.0 * prior.stdUnc * prior.stdUnc))

end PropertyKindCalculus.Tests.Evidence
