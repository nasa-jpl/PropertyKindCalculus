/-
# Validation probes — evidence and conformity (`Uncertainty.Evidence`, `Uncertainty.Conformity`)

Executable probes for the Type A evaluation, the `t`-based coverage factor, Welch–Satterthwaite,
the accumulation rules, and the JCGM 106 conformity assessment built on them. These modules are
Mathlib-free and compute, so these are `#guard`s over real arithmetic rather than axiom-profile
gates: each one fails the build if a number moves.

**The strongest probe here is the Table G.2 oracle.** The coverage factor is *computed* — a
Student `t` quantile through a Lanczos log-gamma, a Lentz continued fraction and a bisection — so
the GUM's own printed table is available as an independent check rather than as the mechanism. All
23 rows and both columns are reproduced to the precision the table prints, including the `ν = ∞`
row where the `t` collapses to the Gaussian quantile through an entirely different code path.

Everything is exercised at a **concrete kind** (`Platform.storageCapacity` — the deployment's own
case, a memory budget), because a kinded API that is only ever instantiated at a variable proves
nothing about whether its laws discharge.

Floats are compared to a relative tolerance, never with `==`: a probe that pins a float bit
pattern tests the platform's libm as much as it tests the module.
-/

import PropertyKindCalculus.Agreement
import PropertyKindCalculus.Uncertainty.Conformity
import PropertyKindCalculus.Paradigm.PlatformKinds

namespace PropertyKindCalculus.Tests.Evidence

open PropertyKindCalculus
open PropertyKindCalculus.Uncertainty
open PropertyKindCalculus.Uncertainty.Conformity

/-- The kind everything below is measured at: a storage capacity, which is what a memory budget,
a residency estimate and the guard band between them all are. -/
private abbrev K := Paradigm.Platform.storageCapacity

/-- A `K`-quantity, for the probes' literals. -/
private def q (x : Float) : Quantity K Float := ⟨x⟩

/-- A coverage factor, for the probes that price one directly. Distinct from `q` because that is
the distinction the vocabulary exists to make: `4.50` the band and `4.50` the factor are the same
`Float` and different quantities, and only one of them can be handed to `riskForFactorAt`. -/
private def q' (x : Float) : Quantity coverageFactor Float := ⟨x⟩

/-! ### Agreement, as a kinded interval

`Quantity.closeTo` is the comparison, at whatever kind the values carry: a probe cannot compare a
coverage factor against a probability, and the tolerance cannot be handed a reading's slot. Each
of the three tolerances below is a *value* of `relativeTolerance` and is named for what licenses
it, so a probe that needs a looser one has to say which and why. -/

/-- Agreement to the four significant figures GUM Table G.2 prints. -/
private def tableTol : Quantity relativeTolerance Float := ⟨1e-3⟩

/-- Agreement to double precision, for everything this library computes itself. -/
private def exactTol : Quantity relativeTolerance Float := ⟨1e-6⟩

/-- The absolute floor a comparison against zero needs, at the measurand's kind: a purely relative
tolerance demands exact equality at a reference of zero. Stated rather than hidden. -/
private def floorK : Quantity K Float := ⟨1e-9⟩

/-- Agreement between two `K`-quantities, to the double-precision tolerance. -/
private def closeK (a b : Quantity K Float) : Bool := a.closeTo b exactTol floorK

/-! ## GUM 4.2 — the Type A evaluation -/

/-- Five indications with mean exactly `10` and `s² = 0.025`, so `s = 0.1581…` and the standard
uncertainty of the *mean* is `s/√5 = 0.070711`. -/
private def five : List (Quantity K Float) := [q 10.0, q 10.2, q 9.8, q 10.1, q 9.9]

-- The estimate is the mean, `u` is `s/√n` (**not** `s`), and `ν = n − 1` through `dofOfMean`.
#guard (typeA five).any fun e =>
  closeK e.estimate.q (q 10.0)
  && closeK e.stdUnc.q (q 0.0707106781186547)
  && e.dof.closeTo ⟨4.0⟩ exactTol ⟨1e-9⟩

-- One indication supports an estimate and no dispersion: the honest result is *no evaluation*.
-- A `u` of zero here would claim the opposite of what one reading knows.
#guard (typeA [q 10.0]).isNone
#guard (typeA ([] : List (Quantity K Float))).isNone

/-! ## GUM 4.3.7 — the rectangular prior, and its `ν = ∞` -/

/-- The deployment's own Type B prior: two bracketing observations, nothing about where between
them the truth lies. `u = a/√3`. -/
private def prior : Evidence K := typeBRectangular (q 985.5) (q 1763.6)

#guard closeK prior.estimate.q (q 1374.55) && closeK prior.stdUnc.q (q 224.61812246)
#guard !prior.dofIsFinite
-- An asserted bound has no sampling variability, so its coverage factor is the Gaussian one.
#guard prior.coverageFactor95.any fun f => f.closeTo ⟨1.960⟩ tableTol

/-! ## The oracle — GUM Table G.2, all 23 rows, both columns

`(ν, t₉₅(ν), t₉₉(ν))` as the GUM prints them. The library computes these from a `t` quantile; the
table is the independent check. -/

private def tableG2 : List (Float × Float × Float) :=
  [(1.0, 12.71, 63.66), (2.0, 4.303, 9.925), (3.0, 3.182, 5.841), (4.0, 2.776, 4.604),
   (5.0, 2.571, 4.032), (6.0, 2.447, 3.707), (7.0, 2.365, 3.500), (8.0, 2.306, 3.355),
   (9.0, 2.262, 3.250), (10.0, 2.228, 3.169), (12.0, 2.179, 3.055), (14.0, 2.145, 2.977),
   (16.0, 2.120, 2.921), (18.0, 2.101, 2.878), (20.0, 2.086, 2.845), (25.0, 2.060, 2.787),
   (30.0, 2.042, 2.750), (35.0, 2.030, 2.724), (40.0, 2.021, 2.704), (45.0, 2.014, 2.690),
   (50.0, 2.009, 2.678), (100.0, 1.984, 2.626)]

/-- Evidence at a stated `ν` and a unit uncertainty — the shape the table is indexed by. -/
private def atDof (nu : Float) : Evidence K :=
  { estimate := ⟨q 0.0⟩, stdUnc := ⟨q 1.0⟩, dof := ⟨nu⟩, evalKind := .typeA }

#guard tableG2.all fun row =>
  let (nu, t95, t99) := row
  (atDof nu).coverageFactor95.any (fun f => f.closeTo ⟨t95⟩ tableTol)
  && (atDof nu).coverageFactor99.any (fun f => f.closeTo ⟨t99⟩ tableTol)

-- The `ν = ∞` row, which reaches the Gaussian quantile by a different branch entirely.
#guard (atDof dofUnbounded.magnitude).coverageFactor95.any (fun f => f.closeTo ⟨1.960⟩ tableTol)
#guard (atDof dofUnbounded.magnitude).coverageFactor99.any (fun f => f.closeTo ⟨2.576⟩ tableTol)

-- Below the table there is no factor to state, and inventing one is how a coverage statement
-- becomes a fiction.
#guard (atDof 0.5).coverageFactor95.isNone

-- The one-sided factor is *not* the two-sided one: `t₉₅` is the 0.975 quantile, so the one-sided
-- factor at a 5 % tail is smaller. Getting this backwards is the classic doubling error.
#guard (atDof 4.0).coverageFactorOneSided ⟨0.05⟩ |>.any fun f => f.closeTo ⟨2.131847⟩ tableTol

-- The expanded uncertainty is `t·u`, at the measurand's own kind, through the expansion law.
#guard (typeA five).any fun e =>
  e.expanded95.any fun U => closeK U ⟨2.776445 * e.stdUnc.q.magnitude⟩

/-! ## The `t` moments — and where they stop existing -/

-- `ν = 4`: a `t` with four degrees of freedom has no fourth moment, so there is no cumulant to
-- state. `none`, not `0` — `0` would claim normality of the least normal case.
#guard ((typeA five).bind (·.momentsT)).isNone
-- `ν = ∞`: the `t` reading collapses to the Gaussian one, which is the same statement.
#guard prior.momentsT.any fun m =>
  (⟨m.variance⟩ : Quantity K Float).closeTo ⟨prior.stdUnc.q.magnitude * prior.stdUnc.q.magnitude⟩
      exactTol floorK
  && (⟨m.fourthCumulant⟩ : Quantity K Float).closeTo (q 0.0) exactTol floorK

/-! ## GUM G.4.1 — effective degrees of freedom -/

-- **A `u_c` dominated by one thin term does not get to claim the coverage of a well-observed
-- one.** A contribution ten times the size, from two readings, beside a well-observed one at
-- `ν = 100`: the combination is entitled to barely more than the thin term's own `ν = 2`.
#guard
  (welchSatterthwaite
    [ { value := q 1.0, dof := (⟨2.0⟩ : Quantity degreesOfFreedom Float) },
      { value := q 0.1, dof := ⟨100.0⟩ } ]).any fun nu =>
    2.0 ≤ nu.magnitude && nu.magnitude ≤ 2.1

-- Comparable contributions pool their degrees of freedom, but never beyond their sum — the bound
-- Welch–Satterthwaite always respects, and the reason it cannot manufacture coverage.
#guard
  (welchSatterthwaite
    [ { value := q 0.07, dof := (⟨4.0⟩ : Quantity degreesOfFreedom Float) },
      { value := q 0.05, dof := ⟨2.0⟩ } ]).any fun nu =>
    4.0 ≤ nu.magnitude && nu.magnitude ≤ 6.0

-- Every contributor unqualified ⇒ the combination is too. No sampling variability entered, so
-- the Gaussian factor is the right one, and it falls out of `x/∞ = 0` rather than out of a case.
#guard (welchSatterthwaite
  [ { value := q 1.0, dof := dofUnbounded }, { value := q 2.0, dof := dofUnbounded } ]).any
    fun nu => !(nu.magnitude < dofUnbounded.magnitude)

-- Nothing to qualify: a zero `u_c` has no degrees of freedom, not infinitely many.
#guard (welchSatterthwaite ([] : List (Contribution K))).isNone

-- The combined evidence is `u_c = √(Σ uᵢ²)` — `Budget.combinedQ`'s quadrature — tagged as an
-- evaluation of neither type.
#guard (combinedEvidence (q 42.0)
  [ { value := q 3.0, dof := (⟨10.0⟩ : Quantity degreesOfFreedom Float) },
    { value := q 4.0, dof := ⟨10.0⟩ } ]).any fun e =>
  closeK e.stdUnc.q (q 5.0) && e.evalKind = .combined

/-! ## Accumulation — the four rules -/

private def a5 : Evidence K := (typeA five).getD prior
private def b5 : Evidence K :=
  (typeA [q 10.05, q 9.95, q 10.15, q 9.85, q 10.0]).getD prior

-- **Pooled.** Two data-derived evaluations: `u` falls and `ν` rises. Both directions matter — a
-- guard band `k·u` tightens because `u` shrinks *and* because the `k` that qualifies it does.
#guard match a5.accumulate b5 with
  | .pooled e =>
    e.stdUnc.q.magnitude < a5.stdUnc.q.magnitude && e.stdUnc.q.magnitude < b5.stdUnc.q.magnitude
      && e.dof.magnitude > a5.dof.magnitude
      && e.coverageFactor95.any (·.magnitude < 2.776)
  | _ => false

-- **Displaced.** A statement of ignorance meets data: the data replaces it outright. The pooled
-- alternative is what this rule exists to forbid — inverse-variance weighting would leave the
-- prior's estimate visible forever, since an asserted half-width never shrinks.
#guard match prior.accumulate a5 with
  | .displaced e => closeK e.estimate.q a5.estimate.q && closeK e.stdUnc.q a5.stdUnc.q
  | _ => false

-- **Retained.** A fresh assertion is not an observation; evidence in hand outranks it.
#guard match a5.accumulate prior with
  | .retained e => closeK e.estimate.q a5.estimate.q
  | _ => false
#guard match prior.accumulate prior with | .retained _ => true | _ => false

-- **Refused.** A `u` of exactly zero is a legitimate record — a deterministic instrument has no
-- dispersion to evaluate — and carries infinite weight, so pooling it would silently *replace*
-- the other evaluation while looking like a combination.
#guard match
    ({ estimate := ⟨q 100.0⟩, stdUnc := ⟨q 0.0⟩, dof := dofUnbounded,
       evalKind := .typeA } : Evidence K).accumulate a5 with
  | .refused e _ => closeK e.estimate.q (q 100.0)
  | _ => false

-- Every case carries the evidence to hold afterwards, so a caller always has a number.
#guard closeK (a5.accumulate b5).evidence.estimate.q (q 10.0)

/-! ## JCGM 106 — the conformity assessment -/

-- The factor and the risk are exact inverses of each other.
#guard (factorForRisk ⟨0.05⟩).any fun f => f.closeTo ⟨1.6448536269514722⟩ exactTol
#guard (factorForRisk ⟨0.01⟩).any fun f => f.closeTo ⟨2.3263478740408408⟩ exactTol
#guard (factorForRisk ⟨0.05⟩).any fun f => (riskForFactor f).closeTo ⟨0.05⟩ exactTol
#guard (factorForRisk ⟨0.001⟩).any fun f => (riskForFactor f).closeTo ⟨0.001⟩ exactTol

-- Not a probability ⇒ no factor. A risk of zero demands an infinite band.
#guard (factorForRisk ⟨0.0⟩).isNone && (factorForRisk ⟨1.0⟩).isNone

/-- Two costs of being wrong, at one kind — here wall-clock, as a storage-capacity stand-in is not
what a duration is. A wrong acceptance loses an eight-hour attempt; a wrong rejection adds one
more six-minute block. -/
private abbrev Kc := Paradigm.Platform.storageCapacity

-- **The asymmetry produces the band.** 480 against 6 gives a 1.23 % break-even risk, hence a
-- one-sided `2.25 u` — derived, where "we used 0.9" was chosen.
#guard (riskFromCosts (⟨480.0⟩ : Quantity Kc Float) ⟨6.0⟩).any fun p =>
  p.closeTo ⟨6.0 / 486.0⟩ exactTol
#guard ((riskFromCosts (⟨480.0⟩ : Quantity Kc Float) ⟨6.0⟩).bind factorForRisk).any fun f =>
  f.closeTo ⟨2.246198⟩ tableTol

-- **Reading the three deployed guard bands.** Two are coverage statements at a few `u`; the third
-- is not a coverage statement at all, and saying so is this function's whole purpose.
#guard match readBand (q 4.50) ⟨q 1.0⟩ with
  | .coverage f r => f.closeTo ⟨4.50⟩ exactTol && r.closeTo ⟨3.3977e-6⟩ tableTol
  | _ => false
#guard match readBand (q 4.39) ⟨q 1.0⟩ with | .coverage _ _ => true | _ => false
#guard match readBand (q 41.0) ⟨q 1.0⟩ with
  | .systematic f => f.closeTo ⟨41.0⟩ exactTol
  | _ => false
-- No uncertainty to divide by ⇒ the band's meaning is unavailable, which is not a band of zero.
#guard match readBand (q 4.50) ⟨q 0.0⟩ with | .unstated => true | _ => false

-- The deployed `1700` sits `1.45 u` above its own rectangular estimate, and that band was never
-- named: it buys a 7.4 % consumer's risk.
#guard match readBand (q (1700.0 - prior.estimate.q.magnitude)) prior.stdUnc with
  | .coverage f r => f.closeTo ⟨1.4489⟩ tableTol && r.closeTo ⟨0.07368⟩ tableTol
  | _ => false

/-! ### Pricing a chosen band at the `ν` that qualifies its `u`

The forward direction is safe by construction; this is the direction a chosen band is read in, and
the direction in which a Gaussian reading is optimistic by orders of magnitude. -/

-- **Three orders of magnitude, in the optimistic direction.** The same `4.5 u` band: `3.4e-6` read
-- against a Gaussian, `5.4e-3` against the `t` that the five readings behind its `u` actually give.
#guard (riskForFactorAt (q' 4.50) ⟨4.0⟩).any fun r => r.closeTo ⟨0.0054113⟩ tableTol
#guard (riskForFactor (q' 4.50)).closeTo ⟨3.3977e-6⟩ tableTol
#guard (riskForFactorAt (q' 4.39) ⟨4.0⟩).any fun r => r.closeTo ⟨0.0058913⟩ tableTol

-- At `ν = 1` — three points and two parameters, the worker-RSS record's own case — the same band
-- buys **7 %**. That record's note says a Gaussian factor "would be badly wrong" at `ν = 1`; this
-- is the number it was describing.
#guard (riskForFactorAt (q' 4.50) ⟨1.0⟩).any fun r => r.closeTo ⟨0.0696045⟩ tableTol

-- Unbounded `ν` **is** the Gaussian reading — the correction disappears on its own rather than
-- being switched off, which is what makes it safe to apply everywhere.
#guard (riskForFactorAt (q' 2.3263478740408408) dofUnbounded).any fun r =>
  r.closeTo ⟨0.01⟩ exactTol
-- Exact inverses at a finite `ν`, in both directions.
#guard ((atDof 4.0).coverageFactorOneSided ⟨0.01⟩).any fun f =>
  (riskForFactorAt f ⟨4.0⟩).any fun r => r.closeTo ⟨0.01⟩ exactTol
-- Fewer than two indications qualify no tail: a refusal, not a Gaussian fallback.
#guard (riskForFactorAt (q' 4.50) ⟨0.5⟩).isNone

-- `Evidence.readBand` is the same reading taken against a record's own evidence, so the `ν` cannot
-- be forgotten at the call site — which is the whole failure mode, since `u` and `ν` arrive
-- together and only `u` has a slot in the arithmetic.
#guard match (atDof 4.0).readBand (q 4.50) with
  | .coverage f r => f.closeTo ⟨4.50⟩ exactTol && r.closeTo ⟨0.0054113⟩ tableTol
  | _ => false
-- A factor of tens is a systematic at every `ν`: no posterior produces it from a risk target.
#guard match (atDof 4.0).readBand (q 41.0) with | .systematic _ => true | _ => false
-- A `u` nothing qualifies reads no band, for the same reason no `u` does: the meaning is
-- unavailable either way.
#guard match (atDof 0.5).readBand (q 4.50) with | .unstated => true | _ => false

/-! ### GUM 4.3.7's posterior is bounded, and the Gaussian prices a tail it does not have -/

-- `√3 u` **is** the bracket's own endpoint, where the risk is exactly zero — so no larger band
-- buys anything, and a Gaussian rule that asks for one is pricing a tail the evaluation denies.
#guard (riskForFactorRectangular rectangularFactorLimit).closeTo ⟨0.0⟩ exactTol ⟨1e-12⟩
#guard (riskForFactorRectangular (q' 3.0)).closeTo ⟨0.0⟩ exactTol ⟨1e-12⟩
#guard (riskForFactor (q' 3.0)).closeTo ⟨1.3499e-3⟩ tableTol
-- At the estimate itself the measurand is as likely to be past the limit as not.
#guard (riskForFactorRectangular (q' 0.0)).closeTo ⟨0.5⟩ exactTol

-- Exact inverses, in closed form, in both directions — so a disagreement with the Gaussian figure
-- is a disagreement about the posterior and cannot be blamed on numerics.
#guard (factorForRiskRectangular ⟨0.05⟩).any fun f =>
  (riskForFactorRectangular f).closeTo ⟨0.05⟩ exactTol
#guard (factorForRiskRectangular ⟨0.0⟩).any fun f => f.closeTo rectangularFactorLimit exactTol

-- **The deployment's own case.** The T4 prior is rectangular by its own evaluation, so the `1700`
-- in force buys `8.2 %`, not the `7.4 %` a Gaussian reads — and the cost-derived 1.23 % target
-- asks for `1.69 u`, which is *inside* the bracket, where the Gaussian's `2.25 u` is not.
#guard match prior.readBand (q (1700.0 - prior.estimate.q.magnitude)) with
  | .coverage f _ => (riskForFactorRectangular f).closeTo ⟨0.081785⟩ tableTol
  | _ => false
#guard ((riskFromCosts (⟨480.0⟩ : Quantity Kc Float) ⟨6.0⟩).bind factorForRiskRectangular).any
  fun f => f.magnitude < rectangularFactorLimit.magnitude && f.closeTo ⟨1.6892841⟩ tableTol
#guard ((riskFromCosts (⟨480.0⟩ : Quantity Kc Float) ⟨6.0⟩).bind factorForRisk).any
  fun f => f.magnitude > rectangularFactorLimit.magnitude

-- **The whole assessment.** A 28 497 MiB budget, a need estimated at 26 000 with `u = 900` from
-- five readings, at a 1 % target consumer's risk. The small-sample factor is 3.75 against the
-- Gaussian 2.33 — a **61 % wider** band from the same five readings — and on this evidence that
-- is exactly the difference between accepting and refusing.
#guard
  let need : Evidence K := { estimate := ⟨q 26000.0⟩, stdUnc := ⟨q 900.0⟩, dof := ⟨4.0⟩,
                             evalKind := .typeA }
  (assess (Tolerance.atMost (q 28497.0)) need ⟨0.01⟩).any fun a =>
    a.factor.closeTo ⟨3.746947⟩ tableTol
    && a.band.closeTo (q (3.746947 * 900.0)) tableTol floorK
    && a.accepted = false
    && a.acceptance.upper.any
        (fun b => b.q.closeTo (q (28497.0 - 3.746947 * 900.0)) tableTol floorK)

-- The same estimate with `u` *known* (`ν = ∞`) is accepted. The finite-`ν` correction is the whole
-- difference, and it disappears on its own as evidence accumulates — which is the mechanism, not
-- a special case: the acceptance limit rises from 25 125 to 26 403 with nothing re-tuned.
#guard
  let known : Evidence K := { estimate := ⟨q 26000.0⟩, stdUnc := ⟨q 900.0⟩, dof := dofUnbounded,
                              evalKind := .typeB }
  (assess (Tolerance.atMost (q 28497.0)) known ⟨0.01⟩).any fun a =>
    a.factor.closeTo ⟨2.3263478740408408⟩ exactTol && a.accepted = true

-- The risk a rule runs **at its own acceptance limit** is exactly the target it was built from.
#guard ((factorForRisk ⟨0.01⟩).bind fun f =>
    riskAtLimit (Tolerance.atMost (q 28497.0)) ⟨q 900.0⟩ f).any fun r =>
  r.closeTo ⟨0.01⟩ exactTol

/-! ### The invariance the ratchet rests on, at `Float`

`ConformityLadder.riskAt_acceptanceLimit` proves over `ℝ` that the risk at the acceptance limit
does not depend on `u`: the band and the uncertainty shrink together, so the standardized deviate
the tail is read at is `k` whatever they shrink to. These are its executable witnesses — the same
arithmetic on the rounding carrier, which is the only place a deployment ever evaluates it. -/

/-- The risk this rule runs at its own acceptance limit, at a stated `u`. The quantity the theorem
says is constant in `u`. -/
private def riskAtLimitFor (uv : Float) : Option (Quantity probability Float) :=
  let limit := Tolerance.atMost (q 28497.0)
  (factorForRisk ⟨0.01⟩).bind fun f => riskAtLimit limit ⟨q uv⟩ f

-- **Four uncertainties spanning two orders of magnitude, one risk.** The acceptance limit moves
-- from 26 403 to 28 474 as `u` falls from 900 to 10 — a 2 071-unit gain in what the deployment
-- may accept — and the consumer's risk at it is 1 % throughout. That is the fleet's speedup and
-- the risk bound being the same statement, which is what makes automatic tightening defensible.
#guard [900.0, 300.0, 100.0, 10.0].all fun uv =>
  (riskAtLimitFor uv).any fun r => r.closeTo ⟨0.01⟩ exactTol

-- The limit itself really does move, so the probe above is not constant for the trivial reason.
#guard ((factorForRisk ⟨0.01⟩).map fun f =>
    (28497.0 - f.magnitude * 900.0, 28497.0 - f.magnitude * 10.0)).any fun (lo, hi) =>
  (⟨lo⟩ : Quantity K Float).closeTo (q 26403.28) tableTol && (⟨hi⟩ : Quantity K Float).closeTo (q 28473.74) tableTol

-- And it never rises past the tolerance limit, however small `u` gets — the ceiling of
-- `ConformityLadder.acceptanceLimit_le`, checked at a `u` far below anything this deployment
-- will ever pool to.
#guard ((factorForRisk ⟨0.01⟩).map fun f => 28497.0 - f.magnitude * 1e-6).any fun a =>
  a < 28497.0

-- **The scope boundary, as a checked fact rather than a caveat.** `riskAtLimit` is §9.5.2's own
-- Gaussian, so pricing a `t`-derived factor with it disagrees with the target that factor was
-- built for — 8.9e-5 where the rule asked for 1 %. Not a defect: it is why `riskForFactorAt`
-- exists and why a consumer must price a band under the posterior it was derived from.
#guard (((atDof 4.0).coverageFactorOneSided ⟨0.01⟩).map riskForFactor).any fun r =>
  r.closeTo ⟨8.9455e-5⟩ tableTol
#guard (((atDof 4.0).coverageFactorOneSided ⟨0.01⟩).bind (riskForFactorAt · ⟨4.0⟩)).any fun r =>
  r.closeTo ⟨0.01⟩ exactTol

end PropertyKindCalculus.Tests.Evidence
