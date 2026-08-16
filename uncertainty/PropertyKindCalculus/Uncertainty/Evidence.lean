/-
`PropertyKindCalculus.Uncertainty.Evidence` — evidence *across* repeated measurements of one
measurand: the GUM 4.2 Type A evaluation, effective degrees of freedom, the `t`-based coverage
factor, and the two ways a record's uncertainty may be updated by new readings.

`Combine.lean` combines **contributions within one budget** — several inputs, one measurement,
`u_c = √(Σ cᵢ²uᵢ²)`. This module combines the orthogonal thing: several *measurements* of the
**same** measurand, which the GUM treats separately (4.2 for the evaluation, G.4 for the degrees
of freedom, G.6.4 for the coverage factor) and which this library had nowhere. The distinction
is not bookkeeping. Combining contributions is a statement about a *model*; combining evidence is
a statement about how much has been *observed*, and only the second one gets better with time.

Four things, in the order a measurand acquires them.

  * **The evaluation.** `Evidence` is an estimate, its standard uncertainty, the degrees of
    freedom that qualify it, and *how it was evaluated* — the GUM's Type A / Type B, which is a
    fact about provenance and not a quality ranking. `typeA` performs the 4.2 evaluation from `n`
    indications (mean, experimental standard deviation of the mean `s/√n`, `ν = n − 1`) and
    refuses `n < 2`: one indication supports an estimate and no dispersion at all.

  * **The coverage factor.** While `n` is small the mean is `t`-distributed, so the factor that
    turns `u` into an interval is `t_p(ν)` and not the Gaussian `1.96` that is only right
    asymptotically. The difference is largest in exactly the early regime a calibration loop
    starts in — at `ν = 3`, `t₀.₉₅ = 3.182`, **62 % wider** than `1.96` — and it decays as
    evidence accumulates, which is the mechanism by which a guard band earns the right to tighten.
    GUM Table G.2 is the source; `ν` is truncated downwards (G.4.1) and a gap in the table is
    read at its lower entry, so both roundings err towards a *larger* factor.

  * **Effective degrees of freedom.** `welchSatterthwaite` gives `u_c` the `ν_eff` its
    contributors' own `νᵢ` support (GUM G.4.1), so a `u_c` dominated by one three-reading term
    does not get to claim the coverage of a well-observed one. A contributor with `ν = ∞`
    contributes nothing to the denominator, which falls out of the float arithmetic rather than
    needing a case.

  * **Accumulation.** `accumulate` folds new evidence into a record's current evidence, and the
    *reason* is part of the result rather than a comment: `pooled` (two data-derived evaluations,
    inverse-variance weighted), `displaced` (a Type B prior replaced by data), `retained`
    (the incoming claim adds no evidence), `refused` (with the reason). Every case carries the
    evidence to hold afterwards, so a caller always has a number and never silently drops one.

**The modelling subtlety this module exists to enforce.** The Type B → Type A transition is a
*displacement*, not an average. A rectangular prior is GUM 4.3.7's statement of **ignorance** —
"the truth is somewhere in this interval and nothing is known about where". Pooling ignorance
with data as though it were an independent measurement would let a made-up half-width
permanently anchor the estimate: no amount of subsequent data can fully outvote a `u` that was
never observed. So `accumulate` displaces a Type B prior on the first Type A evidence and never
inverse-variance-weights one. Cold start stays safe on the prior and merely inefficient — never
the reverse.

`Float`-only and Mathlib-free, like `Combine.lean`: the table lookup needs `floor` and a total
order on the carrier, which `MathCarrier` does not offer. The kinded overlay at the end mirrors
`Budget.lean` — an estimate's uncertainty is a quantity of the estimate's own kind, and the
coverage factor is dimensionless, so the expanded uncertainty is at that kind too.
-/
import PropertyKindCalculus.Uncertainty.Budget
import PropertyKindCalculus.Uncertainty.Combine

namespace PropertyKindCalculus.Uncertainty

open PropertyKindCalculus (Quantity KindOfProperty)

/-! ## The evaluation kind -/

/-- **How an uncertainty was evaluated** (GUM 3.3.4). Type A is "by the statistical analysis of a
series of observations", Type B is "by means other than" that. The GUM is explicit that this is
*not* a quality ranking and that neither type is more reliable — it is a fact about provenance,
and it is load-bearing here for one reason: only Type A evidence accumulates. A `combined`
uncertainty is neither, and saying so is the point of having a third constructor rather than
picking whichever of the two the biggest contributor happened to be. -/
inductive EvalKind where
  /-- GUM 4.2: from the dispersion of repeated indications. -/
  | typeA
  /-- GUM 4.3: from anything else — a bound, a certificate, a handbook value, an assumed
  distribution over an interval nobody sampled. -/
  | typeB
  /-- GUM 5: a combined standard uncertainty `u_c`, which is a property of a *model* over
  contributors of both types and is therefore neither. -/
  | combined
  deriving DecidableEq, Repr, Inhabited

/-- **Degrees of freedom for an uncertainty that is not qualified by a finite number of them**
(GUM G.4.3: a Type B `u` whose bound is reliably known is taken as `ν = ∞`). Written as a float
infinity deliberately: it is the value at which Welch–Satterthwaite's `uᵢ⁴/νᵢ` term vanishes and
the coverage factor falls back to the Gaussian one, so both behaviours come out of the arithmetic
instead of out of a case analysis that could disagree with it. -/
def dofUnbounded : Float := 1.0 / 0.0

/-- **An estimate together with the evidence behind it** — the object a calibration loop updates.
`stdUnc` is the GUM's `u`: a *dispersion*, in the same quantity as the estimate (not a tolerance,
not an error, not a percentage). `dof` is what licenses a coverage factor; it is a `Float` because
Welch–Satterthwaite does not return an integer and because `dofUnbounded` has to be expressible. -/
structure Evidence where
  /-- The estimate of the measurand. -/
  estimate : Float
  /-- The standard uncertainty `u` of that estimate, at the estimate's own kind. -/
  stdUnc : Float
  /-- The degrees of freedom `ν` qualifying `stdUnc`; `dofUnbounded` when unqualified. -/
  dof : Float
  /-- How `stdUnc` was arrived at. -/
  evalKind : EvalKind
  deriving Repr, Inhabited

/-- Whether `ν` is a *finite* number of degrees of freedom. Also false for a `NaN`, which is the
wanted reading: an unusable `ν` is not a large one. -/
def Evidence.dofIsFinite (e : Evidence) : Bool := e.dof < dofUnbounded

/-- Whether this evidence is usable at all: a positive dispersion and no `NaN` anywhere. A `u` of
exactly zero is a *claim* (a deterministic instrument has no dispersion to evaluate) and a
perfectly good record, but it carries infinite weight, so it is not usable in anything that
weights by `1/u²`. -/
def Evidence.isWeightable (e : Evidence) : Bool :=
  e.stdUnc > 0.0 && !e.stdUnc.isNaN && !e.estimate.isNaN

/-! ## GUM 4.2 — the Type A evaluation -/

/-- **GUM 4.2 Type A evaluation from `n` indications.** The estimate is the arithmetic mean
(4.2.1); the experimental variance of the observations is `s² = Σ(xⱼ − x̄)²/(n−1)` (4.2.2); and the
standard uncertainty of the *mean* — which is what qualifies the estimate — is the experimental
standard deviation of the mean, `u = s/√n` (4.2.3), with `ν = n − 1`.

`none` for `n < 2`, and that is the whole reason this returns an `Option`: a single indication
gives an estimate and supports no statement about its dispersion, so the honest result is the
absence of one rather than a `u` of zero, which would claim the opposite. -/
def typeA (xs : List Float) : Option Evidence :=
  if xs.length < 2 then none
  else
    let n := xs.length.toFloat
    let mean := xs.foldl (· + ·) 0.0 / n
    let ss := xs.foldl (fun acc x => acc + (x - mean) * (x - mean)) 0.0
    let s2 := ss / (n - 1.0)
    some { estimate := mean, stdUnc := Float.sqrt (s2 / n), dof := n - 1.0, evalKind := .typeA }

/-- **GUM 4.3.7 — the rectangular prior.** Given only that the value lies in `[lo, hi]` and
nothing about where, the estimate is the midpoint and `u = a/√3` for half-width `a`. This is the
purest Type B evaluation there is, it is a statement of *ignorance*, and it is exactly what
`accumulate` will displace rather than pool the moment real indications arrive. Its `ν` is
`dofUnbounded`: the interval is asserted, not estimated, so there is no sampling variability in
the half-width itself (GUM G.4.3). -/
def typeBRectangular (lo hi : Float) : Evidence :=
  let a := (hi - lo) / 2.0
  { estimate := (lo + hi) / 2.0, stdUnc := a / Float.sqrt 3.0, dof := dofUnbounded,
    evalKind := .typeB }

/-! ## The bridge to the moment-combine methods -/

/-- The moments `Combine.lean` consumes, under the **asymptotic (Gaussian) reading** of this
evidence: `κ₂ = u²` and no fourth cumulant. Correct as `ν → ∞`, and named for what it assumes so
that a caller who has three readings cannot reach for it believing it is free. -/
def Evidence.momentsAsymptotic (e : Evidence) : MomentData Float :=
  { mean := e.estimate, variance := e.stdUnc * e.stdUnc, fourthCumulant := 0.0,
    thirdCumulant := 0.0 }

/-- The moments under the **`t` reading**: with `ν` degrees of freedom the estimate's sampling
distribution is a scaled `t`, whose variance is `u²·ν/(ν−2)` and whose coefficient of excess is
`6/(ν−4)` — the same fat tail the `t` coverage factor prices, handed to `willinkCombine` in the
form it consumes. `none` for `ν ≤ 4`, because a `t` with four or fewer degrees of freedom has no
fourth moment: there is no cumulant to state, and stating `0` would claim normality of the very
distribution that is least normal. `dofUnbounded` collapses to `momentsAsymptotic`, which is the
same statement at the other end of the range. -/
def Evidence.momentsT (e : Evidence) : Option (MomentData Float) :=
  if !e.dofIsFinite then some e.momentsAsymptotic
  else if e.dof > 4.0 then
    let v := e.stdUnc * e.stdUnc * (e.dof / (e.dof - 2.0))
    some { mean := e.estimate, variance := v, fourthCumulant := 6.0 / (e.dof - 4.0) * (v * v),
           thirdCumulant := 0.0 }
  else none

/-! ## GUM Table G.2 — the `t`-based coverage factor -/

/-- Student's `t₉₅(ν)` — GUM Table G.2, the 95 % column, `ν` ascending and ending at `∞`
(where it is the Gaussian `1.960`). -/
private def tTable95 : List (Float × Float) :=
  [(1.0, 12.71), (2.0, 4.303), (3.0, 3.182), (4.0, 2.776), (5.0, 2.571), (6.0, 2.447),
   (7.0, 2.365), (8.0, 2.306), (9.0, 2.262), (10.0, 2.228), (12.0, 2.179), (14.0, 2.145),
   (16.0, 2.120), (18.0, 2.101), (20.0, 2.086), (25.0, 2.060), (30.0, 2.042), (35.0, 2.030),
   (40.0, 2.021), (45.0, 2.014), (50.0, 2.009), (100.0, 1.984), (dofUnbounded, 1.960)]

/-- Student's `t₉₉(ν)` — GUM Table G.2, the 99 % column, ending at the Gaussian `2.576`. -/
private def tTable99 : List (Float × Float) :=
  [(1.0, 63.66), (2.0, 9.925), (3.0, 5.841), (4.0, 4.604), (5.0, 4.032), (6.0, 3.707),
   (7.0, 3.500), (8.0, 3.355), (9.0, 3.250), (10.0, 3.169), (12.0, 3.055), (14.0, 2.977),
   (16.0, 2.921), (18.0, 2.878), (20.0, 2.845), (25.0, 2.787), (30.0, 2.750), (35.0, 2.724),
   (40.0, 2.704), (45.0, 2.690), (50.0, 2.678), (100.0, 2.626), (dofUnbounded, 2.576)]

/-- Read a coverage factor off a Table G.2 column at `ν`. Two roundings, both deliberately in the
conservative direction: a non-integer `ν_eff` is **truncated downwards** (GUM G.4.1), and a `ν`
that falls in a gap between tabulated entries is read at the **lower** entry. Both give a larger
factor, so an interval built from this is never narrower than the table supports.

`none` below `ν = 1` (and for a `NaN`), because the table starts there and inventing a factor for
evidence too thin to have one is how a coverage statement becomes a fiction. -/
private def tCoverage (table : List (Float × Float)) (dof : Float) : Option Float :=
  let target := Float.floor dof
  if !(target ≥ 1.0) then none
  else some (table.foldl (fun best (nu, t) => if nu ≤ target then t else best) 0.0)

/-- The 95 % coverage factor `t₉₅(ν)` for this evidence. -/
def Evidence.coverageFactor95 (e : Evidence) : Option Float := tCoverage tTable95 e.dof

/-- The 99 % coverage factor `t₉₉(ν)` for this evidence. -/
def Evidence.coverageFactor99 (e : Evidence) : Option Float := tCoverage tTable99 e.dof

/-- The 95 % **expanded uncertainty** `U₉₅ = t₉₅(ν)·u` — the half-width of an interval expected
to contain 95 % of the values attributable to the measurand (GUM 6.2.1). -/
def Evidence.expanded95 (e : Evidence) : Option Float :=
  e.coverageFactor95.map (· * e.stdUnc)

/-- The 99 % expanded uncertainty `U₉₉ = t₉₉(ν)·u`. -/
def Evidence.expanded99 (e : Evidence) : Option Float :=
  e.coverageFactor99.map (· * e.stdUnc)

/-! ## GUM G.4.1 — effective degrees of freedom -/

/-- **Welch–Satterthwaite** (GUM G.4.1): the effective degrees of freedom of a combined standard
uncertainty, `ν_eff = u_c⁴ / Σ (cᵢ⁴uᵢ⁴/νᵢ)`, over the same `(cᵢ, evidence)` terms
`Combine.lean` takes. A contributor at `dofUnbounded` adds `x/∞ = 0` to the denominator and so
does not constrain `ν_eff` — no case for it, because the arithmetic already says it.

`none` when `u_c` is zero: there is nothing to qualify. `dofUnbounded` when every contributor is,
which is the right reading of a budget assembled entirely from asserted bounds — the coverage
factor is then the Gaussian one, and correctly so, since no sampling variability entered. -/
def welchSatterthwaite (terms : List (Float × Evidence)) : Option Float :=
  let uc2 := terms.foldl (fun acc t => acc + t.1 * t.1 * t.2.stdUnc * t.2.stdUnc) 0.0
  let denom := terms.foldl (fun acc t =>
    let ui2 := t.1 * t.1 * t.2.stdUnc * t.2.stdUnc
    acc + ui2 * ui2 / t.2.dof) 0.0
  if !(uc2 > 0.0) then none
  else if !(denom > 0.0) then some dofUnbounded
  else some (uc2 * uc2 / denom)

/-- **A combined standard uncertainty with the degrees of freedom it is entitled to.** Pairs a
model's output `estimate` with `u_c = √(Σ cᵢ²uᵢ²)` (`gumStdUnc`, over the contributors' moments)
and `ν_eff` (Welch–Satterthwaite over the same terms), tagged `combined` because it is a property
of the model rather than an evaluation of either type.

This is the shape a conformity assessment consumes: it needs `u_c` *and* the `ν_eff` that fixes
the coverage factor, and a `u_c` handed over without its `ν_eff` silently gets the asymptotic
factor it has not earned. -/
def combinedEvidence (estimate : Float) (terms : List (Float × Evidence)) : Option Evidence :=
  (welchSatterthwaite terms).map fun nu =>
    { estimate := estimate,
      stdUnc := gumStdUnc (terms.map fun t => (t.1, t.2.momentsAsymptotic)),
      dof := nu, evalKind := .combined }

/-! ## Accumulating evidence across measurements -/

/-- **What happened when new evidence met a record's current evidence** — carried in the result
rather than left to a comment, because "the uncertainty went down" and "the prior was thrown
away" are different events and a calibration series that cannot tell them apart is not auditable.
Every case carries the evidence to hold afterwards, so nothing is dropped for want of a branch. -/
inductive Accumulation where
  /-- Two data-derived evaluations of one measurand, inverse-variance weighted. -/
  | pooled (e : Evidence)
  /-- A Type B prior *displaced* by data — not averaged with it. -/
  | displaced (e : Evidence)
  /-- The incoming claim carries no evidence the record does not already have; the current
  evidence stands. -/
  | retained (e : Evidence)
  /-- Refused, with the reason; the current evidence stands. -/
  | refused (e : Evidence) (why : String)
  deriving Repr

/-- The evidence to hold after an accumulation, in every case. -/
def Accumulation.evidence : Accumulation → Evidence
  | .pooled e | .displaced e | .retained e | .refused e _ => e

/-- Inverse-variance pooling of two data-derived evaluations of the same measurand: weights
`wᵢ = 1/uᵢ²`, estimate `Σwᵢxᵢ/Σwᵢ`, and `u² = 1/Σwᵢ` — the minimum-variance combination. Its
degrees of freedom are Welch–Satterthwaite's over the very coefficients the weighting uses
(`cᵢ = wᵢ/Σw`), so pooling three readings with three readings yields the coverage of six and not
of infinitely many. -/
private def poolTwo (a b : Evidence) : Evidence :=
  let wa := 1.0 / (a.stdUnc * a.stdUnc)
  let wb := 1.0 / (b.stdUnc * b.stdUnc)
  let w := wa + wb
  { estimate := (a.estimate * wa + b.estimate * wb) / w,
    stdUnc := Float.sqrt (1.0 / w),
    dof := (welchSatterthwaite [(wa / w, a), (wb / w, b)]).getD dofUnbounded,
    evalKind := if a.evalKind = .typeA && b.evalKind = .typeA then .typeA else .combined }

/-- **Fold new evidence into a record's current evidence.** The rules, and each one is a
metrological claim rather than a convenience:

  * *Type B, then data* → **displaced**. A rectangular prior is ignorance; the first real
    indications replace it outright. Pooling would let an asserted half-width anchor the estimate
    forever, which is the failure this module exists to prevent.
  * *data, then data* → **pooled** by inverse variance, with Welch–Satterthwaite degrees of
    freedom. This is the case that makes a guard band tighten as the fleet runs.
  * *anything, then Type B* → **retained**. A fresh assertion is not an observation, and evidence
    in hand outranks it.
  * *Type B, then Type B* → **retained**, reported rather than chosen: which of two priors to
    hold is a modelling decision and there is no arithmetic that makes it.
  * *either side unweightable* → **refused**, with the reason. A `u` of zero is a legitimate
    record (a deterministic instrument has no dispersion) and carries infinite weight, so pooling
    it would silently *replace* the other evaluation while looking like a combination. -/
def Evidence.accumulate (current new : Evidence) : Accumulation :=
  match current.evalKind, new.evalKind with
  | .typeB, .typeB => .retained current
  | _, .typeB => .retained current
  | .typeB, _ =>
    if new.isWeightable then .displaced new
    else .refused current "the incoming evidence has no usable dispersion to displace the prior with"
  | _, _ =>
    if !current.isWeightable then
      .refused current "the current evidence states no dispersion, so it carries infinite weight \
and pooling would replace it rather than combine with it"
    else if !new.isWeightable then
      .refused current "the incoming evidence states no dispersion, so it carries infinite weight \
and pooling would replace the record rather than add to it"
    else .pooled (poolTwo current new)

/-! ## The kinded overlay -/

/-- The estimate at the measurand's kind. -/
def Evidence.estimateQ {k : KindOfProperty} (e : Evidence) : Quantity k Float := ⟨e.estimate⟩

/-- The standard uncertainty at the measurand's kind — the uncertainty of a quantity is a
quantity of that same kind (`Budget.stdUncQ`'s rule, at an evidence record instead of at raw
moments). -/
def Evidence.stdUncQ {k : KindOfProperty} (e : Evidence) : Quantity k Float := ⟨e.stdUnc⟩

/-- The 95 % expanded uncertainty at the measurand's kind. The coverage factor is a pure number,
so `U = t·u` lands at the kind `u` already had; the multiplication is done on the carrier and the
kind re-stamped, exactly as `Budget.combinedQ` does with its quadrature. -/
def Evidence.expanded95Q {k : KindOfProperty} (e : Evidence) : Option (Quantity k Float) :=
  e.expanded95.map (⟨·⟩)

/-- The 99 % expanded uncertainty at the measurand's kind. -/
def Evidence.expanded99Q {k : KindOfProperty} (e : Evidence) : Option (Quantity k Float) :=
  e.expanded99.map (⟨·⟩)

end PropertyKindCalculus.Uncertainty
