/-
`PropertyKindCalculus.Uncertainty.Evidence` — evidence *across* repeated measurements of one
measurand: the GUM 4.2 Type A evaluation, effective degrees of freedom, the `t`-based coverage
factor, and the two ways a record's uncertainty may be updated by new readings.

`Combine.lean` combines **contributions within one budget** — several inputs, one measurement,
`u_c = √(Σ cᵢ²uᵢ²)`. This module combines the orthogonal thing: several *measurements* of the
**same** measurand, which the GUM treats separately (4.2 for the evaluation, G.4 for the degrees
of freedom, G.6.4 for the coverage factor) and which this library had nowhere. The distinction is
not bookkeeping. Combining contributions is a statement about a *model*; combining evidence is a
statement about how much has been *observed*, and only the second one gets better with time.

Four things, in the order a measurand acquires them.

  * **The evaluation.** `Evidence k` is an estimate of a `k`-measurand, its standard uncertainty
    (a dispersion *of* that estimate, hence a quantity of the same kind — `Budget.lean`'s rule),
    the degrees of freedom qualifying it, and *how it was evaluated* — the GUM's Type A / Type B,
    which is a fact about provenance and not a quality ranking. `typeA` performs the 4.2
    evaluation from `n` indications (mean, experimental standard deviation of the mean `s/√n`,
    `ν = n − 1` through `dofOfMean`) and refuses `n < 2`: one indication supports an estimate and
    no dispersion at all.

  * **The coverage factor.** While `n` is small the mean is `t`-distributed, so the factor that
    turns `u` into an interval is `t_p(ν)` and not the Gaussian `1.96` that is only right
    asymptotically. The difference is largest in exactly the early regime a calibration loop
    starts in — at `ν = 3`, `t₀.₉₅ = 3.182`, **62 % wider** than `1.96` — and it decays as
    evidence accumulates, which is the mechanism by which a guard band earns the right to
    tighten. The factor is *computed* (a `t` quantile at any `ν` and any probability), with GUM
    Table G.2 as the oracle it is validated against rather than as the mechanism, so a conformity
    assessment can ask for the one-sided factor at the risk it actually runs instead of at the two
    probabilities a table happens to print.

  * **Effective degrees of freedom.** `welchSatterthwaite` gives `u_c` the `ν_eff` its
    contributors' own `νᵢ` support (GUM G.4.1), so a `u_c` dominated by one three-reading term
    does not get to claim the coverage of a well-observed one. It takes `Contribution`s — an
    output-kind `uᵢ(y)` beside its degrees of freedom — which is what `Budget.contributionQ`
    already produces, so the sensitivity coefficients and their kind-cancellation stay where they
    belong and never appear here. A contributor with `ν = ∞` contributes nothing to the
    denominator, which falls out of the float arithmetic rather than needing a case.

  * **Accumulation.** `accumulate` folds new evidence into a record's current evidence, and the
    *reason* is part of the result rather than a comment: `pooled` (two data-derived evaluations,
    inverse-variance weighted), `displaced` (a Type B prior replaced by data), `retained` (the
    incoming claim adds no evidence), `refused` (with the reason). Every case carries the evidence
    to hold afterwards, so a caller always has a number and never silently drops one.

**The modelling subtlety this module exists to enforce.** The Type B → Type A transition is a
*displacement*, not an average. A rectangular prior is GUM 4.3.7's statement of **ignorance** —
"the truth is somewhere in this interval and nothing is known about where". Pooling ignorance with
data as though it were an independent measurement would let a made-up half-width permanently
anchor the estimate: no amount of subsequent data can fully outvote a `u` that was never observed.
So `accumulate` displaces a Type B prior on the first Type A evidence and never
inverse-variance-weights one. Cold start stays safe on the prior and merely inefficient — never
the reverse.

**Kinds on every signature.** The measurand's quantities ride its own kind; the probabilities,
coverage factors, indication counts and degrees of freedom ride the four kinds of
`EvidenceKinds.lean`, so no argument of this module is a naked number. The carrier is visible only
*inside* a definition, at a re-stamp documented where it happens — `Budget.combinedQ`'s discipline
(it computes the quadrature on the carrier and re-stamps the output kind, leaving the transient
squared kind an erasure detail), which a variance and an inverse-variance weight need for exactly
the same reason.

`Float`-carried and Mathlib-free, like `Combine.lean`: the `t` quantile needs a concrete
approximation, and a coverage factor read off one is a concrete number.
-/

module

public import PropertyKindCalculus.Uncertainty.EvidenceKinds
public import PropertyKindCalculus.Uncertainty.Roles
public import PropertyKindCalculus.Uncertainty.Budget
public import PropertyKindCalculus.Uncertainty.Carriers

public section -- pkc-blanket
@[expose] section -- pkc-blanket-expose

namespace PropertyKindCalculus.Uncertainty

open PropertyKindCalculus (Quantity KindOfProperty ProductKind QuotientKind)

variable {k : KindOfProperty}

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

/-! ## The evidence record -/

/-- **An estimate together with the evidence behind it** — the object a calibration loop updates.
`stdUnc` is the GUM's `u`: a *dispersion*, and therefore a quantity of the measurand's own kind
(the uncertainty of a length is a length), not a tolerance, not an error, not a percentage.

The `rational` field is the metrological precondition carried once so every downstream expansion
is licensed by it: a standard uncertainty presupposes a ratio-scale measurand, and it is what
`EvidenceKinds.expansionLaw` needs to make `k·u` a construction rather than a re-stamp. It is an
autoParam, so a record built at a concrete kind never mentions it. -/
structure Evidence (k : KindOfProperty) where
  /-- The estimate of the measurand. -/
  estimate : Estimate k Float
  /-- The standard uncertainty `u` of that estimate, at the measurand's own kind.

  `Dispersion` and not `Quantity`, which is the point of `Roles`: this field and the one above
  it are the same kind, sit adjacent, and are passed positionally at every construction site, so
  nothing but a type distinction stops them being exchanged — and exchanging them turns a band
  reading of `42 u` into one of `1/42`, in the safe-looking direction. -/
  stdUnc : Dispersion k Float
  /-- The degrees of freedom `ν` qualifying `stdUnc`; `dofUnbounded` when unqualified. -/
  dof : Quantity degreesOfFreedom Float
  /-- How `stdUnc` was arrived at. -/
  evalKind : EvalKind
  /-- The measurand's scale admits ratios — the precondition for a standard uncertainty, and the
  licence for a coverage factor to expand one. -/
  rational : k.IsRational := by rfl

instance : Repr (Evidence k) where
  reprPrec e _ := Std.Format.text
    s!"⟨estimate := {e.estimate.magnitude}, u := {e.stdUnc.magnitude}, ν := {e.dof.magnitude}⟩"

/-- Whether `ν` is a *finite* number of degrees of freedom. Also false for a `NaN`, which is the
wanted reading: an unusable `ν` is not a large one. -/
def Evidence.dofIsFinite (e : Evidence k) : Bool := e.dof.magnitude < dofUnbounded.magnitude

/-- Whether this evidence is usable in anything that weights by `1/u²`: a positive dispersion and
no `NaN` anywhere. A `u` of exactly zero is a *claim* (a deterministic instrument has no dispersion
to evaluate) and a perfectly good record, but it carries infinite weight. -/
def Evidence.isWeightable (e : Evidence k) : Bool :=
  e.stdUnc.magnitude > 0.0 && !e.stdUnc.magnitude.isNaN && !e.estimate.magnitude.isNaN

/-! ## GUM 4.2 — the Type A evaluation -/

/-- **GUM 4.2 Type A evaluation from `n` indications.** The estimate is the arithmetic mean
(4.2.1); the experimental variance of the observations is `s² = Σ(xⱼ − x̄)²/(n−1)` (4.2.2); and the
standard uncertainty of the *mean* — which is what qualifies the estimate — is the experimental
standard deviation of the mean, `u = s/√n` (4.2.3), with `ν` from `dofOfMean`.

`none` for `n < 2`, and that is the whole reason this returns an `Option`: a single indication
gives an estimate and supports no statement about its dispersion, so the honest result is the
absence of one rather than a `u` of zero, which would claim the opposite.

The sum of squared deviations passes through the measurand's *squared* kind, which is the
transient `Budget.combinedQ` documents: computed on the carrier, and the result re-stamped at `k`
where the square root brings it back. -/
def typeA (xs : List (Quantity k Float)) (hk : k.IsRational := by rfl) : Option (Evidence k) :=
  if xs.length < 2 then none
  else
    let n : Quantity indicationCount Float := ⟨xs.length.toFloat⟩
    let mean := (xs.foldl (fun acc x => acc + x.magnitude) 0.0) / n.magnitude
    let ss := xs.foldl (fun acc x => acc + (x.magnitude - mean) * (x.magnitude - mean)) 0.0
    let variance := ss / (n.magnitude - 1.0)
    some { estimate := ⟨⟨mean⟩⟩, stdUnc := ⟨⟨Float.sqrt (variance / n.magnitude)⟩⟩,
           dof := dofOfMean n, evalKind := .typeA, rational := hk }

/-- **GUM 4.3.7 — the rectangular prior.** Given only that the value lies in `[lo, hi]` and
nothing about where, the estimate is the midpoint and `u = a/√3` for half-width `a`. This is the
purest Type B evaluation there is, it is a statement of *ignorance*, and it is exactly what
`accumulate` will displace rather than pool the moment real indications arrive. Its `ν` is
`dofUnbounded`: the interval is asserted, not estimated, so there is no sampling variability in
the half-width itself (GUM G.4.3). -/
def typeBRectangular (lo hi : Quantity k Float) (hk : k.IsRational := by rfl) : Evidence k :=
  let a := (hi.magnitude - lo.magnitude) / 2.0
  { estimate := ⟨⟨(lo.magnitude + hi.magnitude) / 2.0⟩⟩, stdUnc := ⟨⟨a / Float.sqrt 3.0⟩⟩,
    dof := dofUnbounded, evalKind := .typeB, rational := hk }

/-! ## The crossing into the moment-combine methods

`Combine.lean` works over `MomentData`, which is carrier-parametric but kind-blind — its
`variance` is at the measurand's *squared* kind and its fourth cumulant at the fourth power, and
no `MomentData` says which measurand it belongs to. The two functions below are the sanctioned
crossing into that world, named rather than hidden, in the sense of `Budget.sensitivityQ`. -/

/-- The moments `Combine.lean` consumes, under the **asymptotic (Gaussian) reading** of this
evidence: `κ₂ = u²` and no fourth cumulant. Correct as `ν → ∞`, and named for what it assumes so
that a caller who has three readings cannot reach for it believing it is free. -/
def Evidence.momentsAsymptotic (e : Evidence k) : MomentData Float :=
  { mean := e.estimate.magnitude, variance := e.stdUnc.magnitude * e.stdUnc.magnitude,
    fourthCumulant := 0.0, thirdCumulant := 0.0 }

/-- The moments under the **`t` reading**: with `ν` degrees of freedom the estimate's sampling
distribution is a scaled `t`, whose variance is `u²·ν/(ν−2)` and whose coefficient of excess is
`6/(ν−4)` — the same fat tail the `t` coverage factor prices, handed to `willinkCombine` in the
form it consumes. `none` for `ν ≤ 4`, because a `t` with four or fewer degrees of freedom has no
fourth moment: there is no cumulant to state, and stating `0` would claim normality of the very
distribution that is least normal. `dofUnbounded` collapses to `momentsAsymptotic`, which is the
same statement at the other end of the range. -/
def Evidence.momentsT (e : Evidence k) : Option (MomentData Float) :=
  let ν := e.dof.magnitude
  if !e.dofIsFinite then some e.momentsAsymptotic
  else if ν > 4.0 then
    let u := e.stdUnc.magnitude
    let v := u * u * (ν / (ν - 2.0))
    some { mean := e.estimate.magnitude, variance := v,
           fourthCumulant := 6.0 / (ν - 4.0) * (v * v), thirdCumulant := 0.0 }
  else none

/-! ## The `t`-based coverage factor (GUM G.6.4, Table G.2) -/

/-- **The one-sided coverage factor** for this evidence at tail probability `p`: the `1 − p`
quantile of Student's `t` with `ν` degrees of freedom. This is the factor a *one-sided* limit
needs — the probability of exceeding the estimate by `k·u` in the direction that matters — and it
is the one a conformity assessment against a budget consumes. At `ν = ∞` it is the Gaussian
quantile, exactly.

`none` below `ν = 1` (and for a `NaN` `ν`): with less than one degree of freedom there is no `t`
to take a quantile of, and inventing a factor for evidence that thin is how a coverage statement
becomes a fiction. -/
def Evidence.coverageFactorOneSided (e : Evidence k) (p : Quantity probability Float) :
    Option (Quantity coverageFactor Float) :=
  let pv := p.magnitude
  if !(e.dof.magnitude ≥ 1.0) || !(0.0 < pv && pv < 1.0) then none
  else some ⟨Sampling.studentTQuantile (1.0 - pv) e.dof.magnitude⟩

/-- **The two-sided coverage factor** `t_P(ν)` at coverage probability `P` — GUM Table G.2's own
reading, where `±t_P(ν)·u` is expected to contain the fraction `P` of the values attributable to
the measurand. Its tail is `(1 − P)/2` in each direction, which is the conversion that is easy to
get wrong: `t₉₅` is the `0.975` quantile, not the `0.95` one. -/
def Evidence.coverageFactorTwoSided (e : Evidence k) (coverage : Quantity probability Float) :
    Option (Quantity coverageFactor Float) :=
  e.coverageFactorOneSided ⟨(certainty.magnitude - coverage.magnitude) / 2.0⟩

/-- The 95 % coverage factor `t₉₅(ν)` — GUM Table G.2's 95 % column. -/
def Evidence.coverageFactor95 (e : Evidence k) : Option (Quantity coverageFactor Float) :=
  e.coverageFactorTwoSided p95

/-- The 99 % coverage factor `t₉₉(ν)` — GUM Table G.2's 99 % column. -/
def Evidence.coverageFactor99 (e : Evidence k) : Option (Quantity coverageFactor Float) :=
  e.coverageFactorTwoSided p99

/-- The **expanded uncertainty** `U = t_P(ν)·u` at coverage probability `P` (GUM 6.2.1) — the
half-width of an interval expected to contain that fraction of the values attributable to the
measurand, at the measurand's own kind. Built through `Quantity.mul` on `expansionLaw`, so the
kind of the product is derived from a stated law rather than asserted; the licence comes from the
record's own `rational` field. -/
def Evidence.expanded (e : Evidence k) (coverage : Quantity probability Float) :
    Option (Quantity k Float) :=
  (e.coverageFactorTwoSided coverage).map fun f =>
    Quantity.mul (expansionLaw k e.rational) f e.stdUnc.q

/-- The 95 % expanded uncertainty `U₉₅`. -/
def Evidence.expanded95 (e : Evidence k) : Option (Quantity k Float) := e.expanded p95

/-- The 99 % expanded uncertainty `U₉₉`. -/
def Evidence.expanded99 (e : Evidence k) : Option (Quantity k Float) := e.expanded p99

/-! ## GUM G.4.1 — effective degrees of freedom -/

/-- **One contributor to a combined standard uncertainty**: its contribution `uᵢ(y) = |cᵢ|·u(xᵢ)`
at the *output* kind — which is exactly what `Budget.contributionQ` produces, gated by the GUM's
units-cancellation law — beside the degrees of freedom that qualify it.

Taking the contribution rather than the `(cᵢ, uᵢ)` pair is what keeps the sensitivity kinds out of
this module: their cancellation is `Budget.lean`'s business and is already checked there, and
Welch–Satterthwaite never needs to see it. -/
structure Contribution (kO : KindOfProperty) where
  /-- The contribution `uᵢ(y)` to the output's uncertainty, at the output kind. -/
  value : Quantity kO Float
  /-- The degrees of freedom qualifying it. -/
  dof : Quantity degreesOfFreedom Float

/-- **Welch–Satterthwaite** (GUM G.4.1): the effective degrees of freedom of a combined standard
uncertainty, `ν_eff = u_c⁴ / Σ (uᵢ(y)⁴/νᵢ)`. A contributor at `dofUnbounded` adds `x/∞ = 0` to the
denominator and so does not constrain `ν_eff` — no case for it, because the arithmetic already
says it.

`none` when `u_c` is zero: there is nothing to qualify. `dofUnbounded` when every contributor is,
which is the right reading of a budget assembled entirely from asserted bounds — the coverage
factor is then the Gaussian one, and correctly so, since no sampling variability entered.

The fourth powers pass through the output kind's fourth power and come back at
`degreesOfFreedom` — a ratio of two quantities of that transient kind, hence dimension one, which
is `Budget.combinedQ`'s re-stamp applied to a quotient instead of a square root. -/
def welchSatterthwaite {kO : KindOfProperty} (cs : List (Contribution kO)) :
    Option (Quantity degreesOfFreedom Float) :=
  let uc2 := cs.foldl (fun acc c => acc + c.value.magnitude * c.value.magnitude) 0.0
  let denom := cs.foldl (fun acc c =>
    let ui2 := c.value.magnitude * c.value.magnitude
    acc + ui2 * ui2 / c.dof.magnitude) 0.0
  if !(uc2 > 0.0) then none
  else if !(denom > 0.0) then some dofUnbounded
  else some ⟨uc2 * uc2 / denom⟩

/-- **A combined standard uncertainty with the degrees of freedom it is entitled to.** Pairs a
model's output `estimate` with `u_c = √(Σ uᵢ(y)²)` — `Budget.combinedQ`, the quadrature this
library already had — and `ν_eff` (Welch–Satterthwaite over the same contributions), tagged
`combined` because it is a property of the model rather than an evaluation of either type.

This is the shape a conformity assessment consumes: it needs `u_c` *and* the `ν_eff` that fixes
the coverage factor, and a `u_c` handed over without its `ν_eff` silently gets the asymptotic
factor it has not earned. -/
def combinedEvidence {kO : KindOfProperty} (estimate : Quantity kO Float)
    (cs : List (Contribution kO)) (hk : kO.IsRational := by rfl) : Option (Evidence kO) :=
  (welchSatterthwaite cs).map fun nu =>
    { estimate := ⟨estimate⟩, stdUnc := ⟨combinedQ (cs.map (·.value))⟩, dof := nu,
      evalKind := .combined, rational := hk }

/-! ## Accumulating evidence across measurements -/

/-- **What happened when new evidence met a record's current evidence** — carried in the result
rather than left to a comment, because "the uncertainty went down" and "the prior was thrown away"
are different events and a calibration series that cannot tell them apart is not auditable. Every
case carries the evidence to hold afterwards, so nothing is dropped for want of a branch. -/
inductive Accumulation (k : KindOfProperty) where
  /-- Two data-derived evaluations of one measurand, inverse-variance weighted. -/
  | pooled (e : Evidence k)
  /-- A Type B prior *displaced* by data — not averaged with it. -/
  | displaced (e : Evidence k)
  /-- The incoming claim carries no evidence the record does not already have; the current
  evidence stands. -/
  | retained (e : Evidence k)
  /-- Refused, with the reason; the current evidence stands. -/
  | refused (e : Evidence k) (why : String)
  deriving Repr

/-- The evidence to hold after an accumulation, in every case. -/
def Accumulation.evidence : Accumulation k → Evidence k
  | .pooled e | .displaced e | .retained e | .refused e _ => e

/-- Inverse-variance pooling of two data-derived evaluations of the same measurand: weights
`wᵢ = 1/uᵢ²`, estimate `Σwᵢxᵢ/Σwᵢ`, and `u² = 1/Σwᵢ` — the minimum-variance combination. Its
degrees of freedom are Welch–Satterthwaite's over the very coefficients the weighting uses
(`cᵢ = wᵢ/Σw`), so pooling three readings with three readings yields the coverage of six and not
of infinitely many.

The weights are reciprocals of the measurand's squared kind and the weighted mean divides them
back out, so the whole expression passes through transient kinds and returns at `k` — computed on
the carrier and re-stamped, `Budget.combinedQ`'s discipline again. -/
def poolTwo (a b : Evidence k) : Evidence k :=
  let ua := a.stdUnc.magnitude
  let ub := b.stdUnc.magnitude
  let wa := 1.0 / (ua * ua)
  let wb := 1.0 / (ub * ub)
  let w := wa + wb
  let uPooled := Float.sqrt (1.0 / w)
  { estimate := ⟨⟨(a.estimate.magnitude * wa + b.estimate.magnitude * wb) / w⟩⟩,
    stdUnc := ⟨⟨uPooled⟩⟩,
    dof := (welchSatterthwaite
      [ { value := (⟨wa / w * ua⟩ : Quantity k Float), dof := a.dof },
        { value := (⟨wb / w * ub⟩ : Quantity k Float), dof := b.dof } ]).getD dofUnbounded,
    evalKind := if a.evalKind = .typeA && b.evalKind = .typeA then .typeA else .combined,
    rational := a.rational }

/-- **Fold new evidence into a record's current evidence.** The rules, and each one is a
metrological claim rather than a convenience:

  * *Type B, then data* → **displaced**. A rectangular prior is ignorance; the first real
    indications replace it outright. Pooling would let an asserted half-width anchor the estimate
    forever, which is the failure this module exists to prevent.
  * *data, then data* → **pooled** by inverse variance, with Welch–Satterthwaite degrees of
    freedom. This is the case that makes a guard band tighten as the fleet runs.
  * *anything, then Type B* → **retained**. A fresh assertion is not an observation, and evidence
    in hand outranks it.
  * *Type B, then Type B* → **retained**, reported rather than chosen: which of two priors to hold
    is a modelling decision and there is no arithmetic that makes it.
  * *either side unweightable* → **refused**, with the reason. A `u` of zero is a legitimate
    record (a deterministic instrument has no dispersion) and carries infinite weight, so pooling
    it would silently *replace* the other evaluation while looking like a combination. -/
def Evidence.accumulate (current new : Evidence k) : Accumulation k :=
  match current.evalKind, new.evalKind with
  | .typeB, .typeB => .retained current
  | _, .typeB => .retained current
  | .typeB, _ =>
    if new.isWeightable then .displaced new
    else .refused current
      "the incoming evidence has no usable dispersion to displace the prior with"
  | _, _ =>
    if !current.isWeightable then
      .refused current "the current evidence states no dispersion, so it carries infinite weight \
and pooling would replace it rather than combine with it"
    else if !new.isWeightable then
      .refused current "the incoming evidence states no dispersion, so it carries infinite weight \
and pooling would replace the record rather than add to it"
    else .pooled (poolTwo current new)

end PropertyKindCalculus.Uncertainty

end -- pkc-blanket-expose
end -- pkc-blanket
