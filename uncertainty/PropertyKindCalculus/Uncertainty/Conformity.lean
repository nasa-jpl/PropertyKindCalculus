/-
`PropertyKindCalculus.Uncertainty.Conformity` — conformity assessment: deciding whether a quantity
*with uncertainty* conforms to a limit (ISO/IEC Guide 98-4, JCGM 106:2012).

The GUM says what an uncertainty *is* and how it combines. It does not say what to **do** with one
at a limit, and that gap is where guard bands come from. A decision rule of the form "accept iff
the estimate is below the limit" ignores the uncertainty entirely and runs a consumer's risk of
essentially 50 % at the limit; every practitioner therefore applies a margin, and — this is the
failure mode this module exists to end — the margin is almost always a *chosen factor* rather than
a derived one. A chosen factor cannot be checked, cannot be shown to be too tight or too loose,
and above all cannot **shrink as evidence accumulates**, so it charges the first measurement's
ignorance forever.

JCGM 106's vocabulary, and the four things this module computes.

  * **Tolerance limit** `T` (§3.3.4) — the specified bound on permissible values of the measurand.
    Given, not computed: it is what the decision is *about*.
  * **Acceptance limit** `A` (§3.3.8) — the bound the decision actually compares against.
  * **Guard band** `g = |T − A|` (§3.3.10). Applied inward it is *guarded acceptance*: the
    acceptance interval sits inside the tolerance interval and the consumer's risk falls. Applied
    outward it is *guarded rejection*.
  * **Specific consumer's risk** `R_C(y)` (§9.5.2) — given a measured value `y` with standard
    uncertainty `u`, the probability that the measurand is past `T` anyway. Its counterpart, the
    **specific producer's risk**, is the probability that a value rejected at `A` would in fact
    have conformed.

**Nothing here is a naked number.** The limits are values of the measurand, so they are
`Quantity k`; their *direction* is what a guard band is applied against, so they are carried as
`Bounds.lean`'s `LowerBound`/`UpperBound` roles rather than as bare endpoints; and the four
dimension-one quantities in the arithmetic — a probability, a coverage factor, a count of
indications, a number of degrees of freedom — ride the distinct kinds of `EvidenceKinds.lean`.
Three failure modes close as a result. Comparing an estimate against a limit of a *different kind*
is a type error. Reading a coverage factor as a probability, in an expression that contains both
and where `1.96` and `0.95` are equally plausible, is a type error. And guarding is
`Tolerance.guardedBy`, which subtracts the band from an upper limit and adds it to a lower one —
so the sign of a guard band is fixed by the endpoint's *role* and cannot be written backwards,
which is precisely the mistake that turns guarded acceptance into guarded rejection while still
typechecking.

Three things this module can do that a chosen factor cannot.

**It derives the guard band from a stated risk.** `factorForRisk` inverts §9.5.2: to hold the
consumer's risk at the acceptance limit to `p`, the band is `k·u` with `k = Φ⁻¹(1 − p)`. The
factor stops being an input and becomes a *consequence* of a risk the operator names.

**It derives the risk from the costs, when the risk is asymmetric.** The usual reason a margin is
picked rather than derived is that no one knows what risk to ask for — but the *costs* are often
known, and they fix it. Accepting a non-conforming value costs `C_a`; rejecting a conforming one
costs `C_r`; at a measured value the expected costs are `R_C·C_a` and `(1 − R_C)·C_r`, so the
break-even risk is `p* = C_r/(C_a + C_r)` (`riskFromCosts`, licensed by `costRatioIsRisk` — the
authored crossing that turns a ratio of two same-kind costs into a probability). Strongly
asymmetric costs then *produce* the conclusion that is usually asserted: when a wrong acceptance
costs a hundred times a wrong rejection, `p* ≈ 1 %` and the band is a one-sided `2.33 u`. That is
a derivation, and it is auditable in a way "we used 0.9" is not.

**It reads an existing band and says what kind of thing it is.** `readBand` divides a deployed
margin by the measurand's own `u` — a quotient of two `k`-quantities, which `bandReadingLaw`
declares to be a coverage factor. A band that comes out at a few `u` is a coverage statement and
`riskForFactor` prices it. A band at tens of `u` is *not* — no risk target produces it, and reading
it as coverage puts a coverage factor on what is actually a **systematic the model does not
carry**. The distinction matters because the two have opposite repairs: dispersion shrinks with
evidence, a missing term does not, and a conformity assessment that cannot tell them apart will
tighten a band that was never covering dispersion in the first place.

**Scope, stated.** The risk arithmetic is §9.5.2's: a Gaussian posterior for the measurand given
the measured value. That is exact when `u` is known (`ν = ∞`) and optimistic when `u` was itself
estimated from few readings, since the posterior is then a `t` with heavier tails — so
`factorForEvidence` takes the `t` factor at the evidence's own `ν`, which agrees with the Gaussian
one at `ν = ∞` and exceeds it everywhere else. Global (as opposed to specific) risks, which
integrate over a prior for the measurand across a production run, are deliberately out of scope:
they need a prior this library has no business inventing.

Mathlib-free, like `Combine` and `Evidence`. Carrier-generic wherever the structure allows it; the
risk arithmetic is `Float`-carried, because a probability read off a normal tail is a concrete
number.
-/
import PropertyKindCalculus.Bounds
import PropertyKindCalculus.Uncertainty.Evidence

namespace PropertyKindCalculus.Uncertainty.Conformity

open PropertyKindCalculus (Quantity KindOfProperty OrderKind DifferenceKind ProductKind
  QuotientKind LowerBound UpperBound IccQ)
open PropertyKindCalculus.Uncertainty

variable {k : KindOfProperty} {R : Type}

/-! ## The tolerance limits -/

/-- **The tolerance limits** (JCGM 106 §3.3.4) — the specified bounds on permissible values of the
measurand, carried as `Bounds.lean` *roles* so that each endpoint can only ever be used from its
own side. Either bound may be absent: a one-sided requirement is the common case (a memory budget
bounds from above and not from below), and an absent bound is `none` rather than an infinity, so
"unbounded below" cannot be confused with a bound whose value was lost. -/
structure Tolerance (k : KindOfProperty) (R : Type) where
  /-- The lower tolerance limit `T_L`, if there is one. -/
  lower : Option (LowerBound k R) := none
  /-- The upper tolerance limit `T_U`, if there is one. -/
  upper : Option (UpperBound k R) := none

/-- A one-sided upper tolerance limit — a budget, a ceiling, a maximum rating. Scale-gated by
`OrderKind`, since a limit presupposes an order to be on one side of. -/
def Tolerance.atMost (t : Quantity k R) (_ord : OrderKind k := by exact OrderKind.ofScale) :
    Tolerance k R :=
  { upper := some ⟨t⟩ }

/-- A one-sided lower tolerance limit — a minimum strength, a floor. -/
def Tolerance.atLeast (t : Quantity k R) (_ord : OrderKind k := by exact OrderKind.ofScale) :
    Tolerance k R :=
  { lower := some ⟨t⟩ }

/-- A two-sided tolerance interval, from the kind-indexed closed interval itself. Taking an `IccQ`
rather than two quantities means the endpoints arrive already role-typed, so a swapped tolerance
is not expressible here either. -/
def Tolerance.ofIcc (I : IccQ k R) : Tolerance k R := { lower := some I.lo, upper := some I.hi }

/-- Whether a *value* conforms — the question asked of the measurand itself, with no uncertainty
in sight. Everything else in this module exists because this is not the question a measurement can
answer. Each endpoint is queried through its own directional decider, so the comparison cannot be
written backwards. -/
def Tolerance.admits [LE R] [∀ x y : R, Decidable (x ≤ y)] (t : Tolerance k R)
    (x : Quantity k R) : Bool :=
  (t.lower.all (·.leb x)) && (t.upper.all (·.geb x))

/-! ## The coverage factor, from a risk the operator names -/

/-- **The coverage factor that holds the specific consumer's risk to `p`** at a one-sided
acceptance limit: `k = Φ⁻¹(1 − p)`, the inverse of JCGM 106 §9.5.2 read at the limit. Naming a
risk therefore *determines* the guard band; nothing is left to be chosen.

`none` unless `0 < p < 1`: a risk of zero demands an infinite band, and a risk of one is not a
decision rule. -/
def factorForRisk (p : Quantity probability Float) : Option (Quantity coverageFactor Float) :=
  let pv := p.magnitude
  if 0.0 < pv && pv < 1.0 then
    some ⟨Sampling.normalQuantile (certainty.magnitude - pv)⟩
  else none

/-- **The specific consumer's risk at an acceptance limit `k` standard uncertainties inside the
tolerance limit** — the exact inverse of `factorForRisk`, and the function that prices a band
somebody else chose. `1 − Φ(k)`. -/
def riskForFactor (f : Quantity coverageFactor Float) : Quantity probability Float :=
  ⟨certainty.magnitude - Sampling.normalCDF f.magnitude⟩

/-- **The coverage factor for a target risk, at the degrees of freedom the evidence has.** The
Gaussian `Φ⁻¹(1 − p)` of `factorForRisk` is §9.5.2's own assumption and is exact only when `u` is
known; with `ν` finite the posterior is a `t`, whose heavier tails make the Gaussian factor
under-cover. This uses the evidence's own `t` quantile, which *is* the Gaussian one at `ν = ∞`, so
the correction appears and disappears on its own rather than being applied by hand.

The effect is not small in the regime a calibration loop starts in: at `ν = 4` a 1 % consumer's
risk needs `3.75 u`, not the `2.33 u` a Gaussian assumption would have taken from the same five
readings. -/
def factorForEvidence (e : Evidence k) (p : Quantity probability Float) :
    Option (Quantity coverageFactor Float) :=
  e.coverageFactorOneSided p

/-- **The break-even risk implied by the two costs of being wrong.** Accepting a non-conforming
value costs `costOfWrongAccept`; rejecting a conforming one costs `costOfWrongReject`. At a
measured value the two expected costs are `R_C·C_a` and `(1 − R_C)·C_r`, so accepting is the
cheaper action exactly while `R_C ≤ C_r/(C_a + C_r)` — which is the risk target to hand
`factorForRisk`.

This is how an asymmetric risk becomes a number instead of an adjective. The two costs are usually
*known* even when the acceptable risk is not: a wrong acceptance that loses a whole run against a
wrong rejection that adds one more unit of work is a ratio the operator can state, and it produces
the one-sided high-coverage band that would otherwise be asserted.

The costs are quantities of one kind `kc`, and the step from their ratio to a probability is
`costRatioIsRisk` — an authored crossing, written here because nothing about a ratio of two
durations makes it a probability except the decision-theoretic argument above. Requiring both
costs to share `kc` is the other half: a wall-clock cost divided by a monetary one is a number
with no meaning, and exactly the kind that looks fine in a spreadsheet. -/
def riskFromCosts {kc : KindOfProperty} (costOfWrongAccept costOfWrongReject : Quantity kc Float)
    (hc : kc.IsRational := by rfl) : Option (Quantity probability Float) :=
  let a := costOfWrongAccept.magnitude
  let r := costOfWrongReject.magnitude
  if a > 0.0 && r > 0.0 && !(a + r).isNaN then
    some (Quantity.div (costRatioIsRisk kc hc) costOfWrongReject ⟨a + r⟩)
  else none

/-! ## Guard bands and acceptance limits -/

/-- **The guard band** `g = k·u` — a quantity of the measurand's own kind, since it is an offset
applied to a limit on that measurand. Built through `Quantity.mul` on `expansionLaw`, so the kind
of the product is derived from a stated law rather than asserted: a coverage factor is dimension
one *in the specific role of expanding an uncertainty*, and that role is what the law records. -/
def guardBand (u : Quantity k Float) (factor : Quantity coverageFactor Float)
    (hk : k.IsRational := by rfl) : Quantity k Float :=
  Quantity.mul (expansionLaw k hk) factor u

/-- **Guarded acceptance limits** (JCGM 106 §8.2): the band is subtracted from an upper tolerance
limit and added to a lower one, so a two-sided tolerance narrows from both ends.

The direction is not a convention here — it is forced by the endpoint's *role*. An `UpperBound`
can only be moved to a stricter upper bound by subtraction and a `LowerBound` by addition, so
"applied the guard band the wrong way and turned guarded acceptance into guarded rejection" is not
a mistake this function's caller is in a position to make. Gated by `DifferenceKind`, which is the
metrological licence to form the difference at all. -/
def Tolerance.guardedBy [Add R] [Sub R] (t : Tolerance k R) (band : Quantity k R)
    (_diff : DifferenceKind k := by exact DifferenceKind.ofScale) : Tolerance k R :=
  { lower := t.lower.map (fun b => ⟨⟨b.q.magnitude + band.magnitude⟩⟩),
    upper := t.upper.map (fun b => ⟨⟨b.q.magnitude - band.magnitude⟩⟩) }

/-- **The decision.** Accept iff the estimate lies within the *acceptance* limits — equivalently
`y + k·u ≤ T_U` and `y − k·u ≥ T_L`, which is the form the rule is usually written in. -/
def accepts (t : Tolerance k Float) (y u : Quantity k Float)
    (factor : Quantity coverageFactor Float) (hk : k.IsRational := by rfl) : Bool :=
  (t.guardedBy (guardBand u factor hk) (differenceOfRational hk)).admits y

/-! ## The risks actually run -/

/-- **The specific consumer's risk** `R_C(y)` (JCGM 106 §9.5.2): given the estimate `y` and its
standard uncertainty `u`, the probability that the measurand lies outside the *tolerance* limits —
the risk run by accepting this particular value. A two-sided tolerance sums the two tails, which
is exact under the Gaussian posterior since the events are disjoint. The kinds cancel on the way
in: each tail is a quotient of two `k`-quantities before `Φ` sees it, and the result is stamped
`probability` because that is what a normal tail is.

`u ≤ 0` is not a degenerate case to be smoothed over: with no dispersion the measurand *is* the
estimate, so the risk is certainty or its complement and the conformity question has a definite
answer. -/
def consumerRisk (t : Tolerance k Float) (y u : Quantity k Float) : Quantity probability Float :=
  if u.magnitude > 0.0 then
    let above := (t.upper.map fun b =>
      certainty.magnitude
        - Sampling.normalCDF ((b.q.magnitude - y.magnitude) / u.magnitude)).getD 0.0
    let below := (t.lower.map fun b =>
      Sampling.normalCDF ((b.q.magnitude - y.magnitude) / u.magnitude)).getD 0.0
    ⟨above + below⟩
  else if t.admits y then ⟨0.0⟩ else certainty

/-- **The specific producer's risk** at a rejected estimate: the probability that a value the rule
rejected would in fact have conformed. It is `1 − R_C(y)` by construction, and it is named
separately because the two are charged to different parties and, in an asymmetric application,
priced very differently. -/
def producerRisk (t : Tolerance k Float) (y u : Quantity k Float) : Quantity probability Float :=
  ⟨certainty.magnitude - (consumerRisk t y u).magnitude⟩

/-- The specific consumer's risk a rule runs **at its own acceptance limit** — the number a stated
guard band actually buys, obtained by evaluating `consumerRisk` exactly where the rule stops
accepting. For a one-sided tolerance this is `riskForFactor factor`; the general form is here so a
two-sided rule, whose far tail is not zero, is priced with both tails. -/
def riskAtLimit (t : Tolerance k Float) (u : Quantity k Float)
    (factor : Quantity coverageFactor Float) (hk : k.IsRational := by rfl) :
    Option (Quantity probability Float) :=
  let a := t.guardedBy (guardBand u factor hk) (differenceOfRational hk)
  match a.upper, a.lower with
  | some b, _ => some (consumerRisk t b.q u)
  | none, some b => some (consumerRisk t b.q u)
  | none, none => none

/-! ## Reading a guard band that already exists -/

/-- **What a deployed margin turns out to be**, once divided by the measurand's own standard
uncertainty. The two readings have opposite repairs, which is why the distinction is a constructor
and not a comment. -/
inductive BandReading where
  /-- A coverage statement: `g = k·u` for a plausible `k`, buying the stated specific consumer's
  risk. This band is *dispersion*, so it shrinks as evidence accumulates. -/
  | coverage (factor : Quantity coverageFactor Float) (risk : Quantity probability Float)
  /-- Not a coverage statement. No risk target produces a factor this large, so the margin is
  standing in for a **systematic the model does not carry** — a term that is missing, not a
  measurement that is imprecise. It does not shrink with evidence, and tightening it as though it
  did is how a fleet walks into a correlated failure. -/
  | systematic (factor : Quantity coverageFactor Float)
  /-- No uncertainty to divide by, so the band cannot be read at all. Not the same as a band of
  zero: it is a band whose meaning is unavailable. -/
  | unstated
  deriving Repr

/-- **The factor beyond which a margin is no longer a coverage statement.** `6` is where the
specific consumer's risk reaches `1e-9`, and where — in practice — nobody has ever *chosen* a band
from a risk target. A judgement, which is why `readBand` takes it as an argument; but a judgement
that then applies uniformly, which is the improvement over judging each band on its own. -/
def systematicThreshold : Quantity coverageFactor Float := ⟨6.0⟩

/-- Read a deployed guard band `g` against the standard uncertainty `u` of the quantity it
qualifies — both quantities of the measurand's kind, so their quotient is the coverage factor
`bandReadingLaw` says it is, and a band accidentally compared against the uncertainty of something
else is a type error. -/
def readBand (g u : Quantity k Float)
    (systematicAt : Quantity coverageFactor Float := systematicThreshold)
    (hk : k.IsRational := by rfl) : BandReading :=
  if !(u.magnitude > 0.0) || u.magnitude.isNaN || g.magnitude.isNaN then .unstated
  else
    let factor := Quantity.div (bandReadingLaw k hk) g u
    if factor.magnitude ≤ systematicAt.magnitude then .coverage factor (riskForFactor factor)
    else .systematic factor

/-! ## The evidence-driven entry point -/

/-- **The whole assessment**: an evidence record, a tolerance, and a target consumer's risk in,
and the decision plus everything that justifies it out.

This is the shape that makes the guard band an *output*. The factor comes from the risk at the
evidence's own degrees of freedom, the band comes from the factor and the evidence's own `u`, and
both fall as evidence accumulates — which is the mechanism by which an acceptance limit rises
towards the tolerance limit without anyone re-tuning anything. -/
structure Assessment (k : KindOfProperty) where
  /-- The coverage factor used. -/
  factor : Quantity coverageFactor Float
  /-- The guard band `k·u`, at the measurand's kind. -/
  band : Quantity k Float
  /-- The acceptance limits after guarding. -/
  acceptance : Tolerance k Float
  /-- Whether the estimate is accepted. -/
  accepted : Bool
  /-- The specific consumer's risk at *this* estimate — usually far below the target, which is the
  risk only at the acceptance limit itself. -/
  risk : Quantity probability Float

/-- Assess an evidence record against a tolerance at a target consumer's risk. `none` when the
evidence cannot support a coverage factor at that risk — fewer than one degree of freedom, or a
target that is not a probability. A refusal, rather than a factor nothing justifies. -/
def assess (t : Tolerance k Float) (e : Evidence k) (targetRisk : Quantity probability Float) :
    Option (Assessment k) :=
  (factorForEvidence e targetRisk).map fun factor =>
    let band := guardBand e.stdUnc factor e.rational
    { factor := factor, band := band,
      acceptance := t.guardedBy band (differenceOfRational e.rational),
      accepted := accepts t e.estimate e.stdUnc factor e.rational,
      risk := consumerRisk t e.estimate e.stdUnc }

end PropertyKindCalculus.Uncertainty.Conformity
