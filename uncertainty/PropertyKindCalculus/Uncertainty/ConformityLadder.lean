/-
`PropertyKindCalculus.Uncertainty.ConformityLadder` — why an acceptance limit may be allowed to
tighten itself, stated and proved over Mathlib's `ℝ`.

`Conformity.lean` computes a guard band from a stated consumer's risk, and `Evidence.lean` pools
indications so that `u` falls as evidence accumulates. Putting the two together gives a deployment
that gets *less* conservative the longer it runs — which is the point of the whole exercise and
also, stated that baldly, exactly the kind of automatic loosening that should not be allowed near
anything that can be killed for using too much memory.

This module is the argument that it is safe, and the argument turns out to be sharper than
"the risk stays bounded". Three facts, of which the middle one is the whole content:

  * **The limit rises as `u` falls** (`acceptanceLimit_antitone`), and never past the tolerance
    limit itself (`acceptanceLimit_le`). So the mechanism is a ratchet with a ceiling, not an
    extrapolation.
  * **The risk at the acceptance limit does not depend on `u` at all**
    (`riskAt_acceptanceLimit`). It is `Q k` — the tail beyond the coverage factor — for every
    `u ≠ 0`. The band and the uncertainty shrink *together*, and the standardized deviate they
    are read at is exactly `k` whatever they shrink to.
  * Therefore a rule built for a target risk **runs that target at every stage of evidence**
    (`riskAt_acceptanceLimit_le`), including the first — which is the cold-start property stated
    as a corollary rather than assumed as an invariant: with one Type B prior the loop is *safe*
    and merely inefficient, and it cannot be otherwise.

**What is not being claimed.** That the risk is *unchanged by accumulating evidence* is a
statement about the decision rule, not about the world. If the pooled `u` is wrong — a systematic
the model does not carry, an extrapolation outside the calibration range, a device that is not the
device the record was keyed to — then `Q k` was never the operating risk and shrinking `u`
compounds the error rather than causing it. That is precisely why `Conformity.readBand`
distinguishes a coverage band from a systematic, and why a `systematic` reading is the one thing
the loop must never tighten: this theorem says the rule is sound, and says nothing about whether
its input is.

**The tail function is abstract on purpose.** `Q` is any map from a standardized deviate to a
probability; the invariance is algebraic and holds for all of them. Both families
`Conformity.lean` computes with satisfy the extra `Antitone` hypothesis the target-risk corollary
needs — the Gaussian and `t` tails because they are complements of CDFs, the rectangular
`(√3 − k)/(2√3)` because it is affine with a negative slope — so nothing here has to choose one,
and a fourth posterior added later inherits the result rather than needing a new one.

Mathlib's `ℝ`, like `Ladder.lean` and for the same reason: monotonicity is not a statement `Float`
can carry, and the executable counterparts in `Conformity.lean` are the same arithmetic on the
rounding carrier.
-/
import Mathlib.Basic.Real.Basic
import Mathlib.Order.Monotone.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

namespace PropertyKindCalculus.Uncertainty.ConformityLadder

/-! ## The two quantities the ratchet moves -/

/-- **The acceptance limit** (JCGM 106 §3.3.8) at a tolerance limit `L`, a coverage factor `k` and
a standard uncertainty `u`: `A = L − k·u`, the guarded-acceptance form for an *upper* limit.

Written as a function of `u` with `L` and `k` fixed, because `u` is the argument that moves: the
tolerance limit is a property of the device and the coverage factor is a property of the stated
risk, while `u` is what a calibration loop changes underneath both. -/
def acceptanceLimit (L k u : ℝ) : ℝ := L - k * u

/-- **The specific consumer's risk at a measured value** `y` with standard uncertainty `u`,
against an upper tolerance limit `L`: the tail of the posterior beyond `(L − y)/u` standard
uncertainties.

`Q` is left abstract — any map from a standardized deviate to a probability. The theorems below
that are about the *rule* need nothing of it; only the one about hitting a stated target needs it
to be antitone, which every tail is. -/
noncomputable def riskAt (Q : ℝ → ℝ) (L y u : ℝ) : ℝ := Q ((L - y) / u)

/-! ## The ratchet: it rises, and it has a ceiling -/

/-- **Shrinking the uncertainty raises the acceptance limit.** The mechanism by which a deployment
gets less conservative as indications accumulate, and the reason nobody has to re-tune a factor
for that to happen: `A` is antitone in `u` for any non-negative coverage factor.

`k = 0` is the degenerate rule that ignores uncertainty entirely; it is admitted here (the limit is
then constant, not decreasing) because excluding it would make the statement about a class of rules
this one is not a member of. -/
theorem acceptanceLimit_antitone (L : ℝ) {k : ℝ} (hk : 0 ≤ k) :
    Antitone (acceptanceLimit L k) := by
  intro u₁ u₂ h
  have : k * u₁ ≤ k * u₂ := by exact mul_le_mul_of_nonneg_left h hk
  simp only [acceptanceLimit]
  linarith

/-- **And it never rises past the tolerance limit.** The ceiling of the ratchet: no amount of
accumulated evidence turns guarded acceptance into acceptance *beyond* the specification. Together
with `acceptanceLimit_antitone` this is what makes "the margin tightens itself" a bounded process
rather than an extrapolation — the limit approaches `L` and stops. -/
theorem acceptanceLimit_le (L : ℝ) {k u : ℝ} (hk : 0 ≤ k) (hu : 0 ≤ u) :
    acceptanceLimit L k u ≤ L := by
  have : 0 ≤ k * u := mul_nonneg hk hu
  simp only [acceptanceLimit]
  linarith

/-- The ceiling is reached only in the degenerate cases — no coverage factor, or no uncertainty
to cover. Stated so that "approaches `L`" cannot be misread as "reaches `L`": on any real evidence
the acceptance limit is strictly inside the tolerance limit, however much evidence there is. -/
theorem acceptanceLimit_lt (L : ℝ) {k u : ℝ} (hk : 0 < k) (hu : 0 < u) :
    acceptanceLimit L k u < L := by
  have : 0 < k * u := mul_pos hk hu
  simp only [acceptanceLimit]
  linarith

/-- **A shrinking `u` only ever adds acceptable values.** The operational form of the ratchet: a
need the rule accepted under the old evidence is still accepted under the new, so tightening can
never reject a block that used to fit. Without this, "the loop tightens" would be compatible with
a fleet that refuses work it did yesterday. -/
theorem accepts_mono (L : ℝ) {k u₁ u₂ y : ℝ} (hk : 0 ≤ k) (h : u₁ ≤ u₂)
    (hy : y ≤ acceptanceLimit L k u₂) : y ≤ acceptanceLimit L k u₁ :=
  le_trans hy (acceptanceLimit_antitone L hk h)

/-! ## The invariance — the fact that makes the ratchet free

The two theorems above would hold of any rule that subtracts *something* proportional to `u`. What
distinguishes a conformity assessment from a scaled-margin heuristic is that the something is
`k·u` for a `k` fixed by a stated risk, and the consequence is this: the risk at the acceptance
limit is **the same number at every `u`**. The band shrinks exactly as fast as the uncertainty it
covers, so the standardized deviate the tail is read at never moves. -/

/-- **The risk at the acceptance limit does not depend on the uncertainty.** `(L − A)/u = k` for
every `u ≠ 0`, so the specific consumer's risk there is `Q k` whatever the evidence has done to `u`.

This is the theorem the compounding layer rests on. "The guard band tightens as calibration
accumulates" is, without it, a smaller number with no argument behind it; with it, the fleet's
speedup is a *corollary of a risk bound* — the deployment buys back wall clock and keeps the same
consumer's risk, because those are the same statement.

`u ≠ 0` rather than `0 < u`: a negative `u` is not meaningful but the algebra does not care, and
requiring positivity here would be a hypothesis the result does not use. What the algebra does care
about is that `u` is not zero — with no dispersion there is no standardized deviate, and the
conformity question has a definite answer that this expression is not the way to compute. -/
theorem riskAt_acceptanceLimit (Q : ℝ → ℝ) (L k : ℝ) {u : ℝ} (hu : u ≠ 0) :
    riskAt Q L (acceptanceLimit L k u) u = Q k := by
  simp only [riskAt, acceptanceLimit]
  congr 1
  have : L - (L - k * u) = k * u := by ring
  rw [this, mul_div_assoc, div_self hu, mul_one]

/-- **So a rule built for a target risk runs that target at every stage of evidence** — the first
included. `Q k ≤ p` is what `factorForRisk` establishes when it chooses `k`; this says the choice
survives every subsequent update of `u` without being revisited.

The cold-start property falls out rather than being assumed: with one Type B prior `u` is large,
the acceptance limit is low, and the risk is *still* `Q k`. The loop is therefore safe on day one
and merely inefficient, which is the correct direction and the one that has to be true by
construction rather than by care. -/
theorem riskAt_acceptanceLimit_le (Q : ℝ → ℝ) (L k p : ℝ) {u : ℝ} (hu : u ≠ 0)
    (hQ : Q k ≤ p) : riskAt Q L (acceptanceLimit L k u) u ≤ p := by
  rw [riskAt_acceptanceLimit Q L k hu]; exact hQ

/-- **The risk at a value strictly inside the acceptance limit is no worse**, for any antitone
tail. The complement of the invariance: `Q k` is the risk at the *limit*, and every accepted value
runs at most it — usually far less, which is why `Assessment.risk` and the target are different
numbers and why confusing them understates how much margin an ordinary decision has.

This is the one statement that needs `Q` to be a tail rather than an arbitrary function, and the
hypothesis is met by every posterior in `Conformity.lean`: the Gaussian and `t` tails are
complements of CDFs, and the rectangular `(√3 − k)/(2√3)` is affine with a negative slope. -/
theorem riskAt_le_of_accepted (Q : ℝ → ℝ) (hQ : Antitone Q) (L k : ℝ) {u y : ℝ} (hu : 0 < u)
    (hy : y ≤ acceptanceLimit L k u) : riskAt Q L y u ≤ Q k := by
  have hk : k ≤ (L - y) / u := by
    rw [le_div_iff₀ hu]
    simp only [acceptanceLimit] at hy
    linarith
  simpa [riskAt] using hQ hk

/-- **A larger coverage factor buys a smaller risk**, for an antitone tail — the sanity property
that makes `factorForRisk` and `riskForFactor` an inverse pair rather than two unrelated maps, and
the direction an operator relies on when widening a band by hand. -/
theorem riskAt_acceptanceLimit_antitone_in_factor (Q : ℝ → ℝ) (hQ : Antitone Q) (L : ℝ) {u : ℝ}
    (hu : u ≠ 0) {k₁ k₂ : ℝ} (h : k₁ ≤ k₂) :
    riskAt Q L (acceptanceLimit L k₂ u) u ≤ riskAt Q L (acceptanceLimit L k₁ u) u := by
  rw [riskAt_acceptanceLimit Q L k₁ hu, riskAt_acceptanceLimit Q L k₂ hu]
  exact hQ h

/-! ## The floor the operational ratchet still needs

Nothing above bounds how *fast* `u` may fall, and nothing above should: the theorems are about a
rule at a given `u`, and they hold at every one. What they therefore do not supply — and what the
deployment-side ratchet has to — is a floor on the evidence that produces `u`. A run of small
peaks can shrink a pooled `u` faster than the underlying dispersion warrants, and the invariance
above will faithfully report the target risk for a `u` that is wrong. The theorem is that the rule
is sound; the floor is what keeps its input honest, and it is an operational parameter rather than
a mathematical one. -/

/-- **A floor on `u` is a floor on the acceptance limit** — the shape of the operational guard,
stated here so that the deployment-side parameter has a proposition to be an instance of rather
than being a number in a config file with a comment. Given `uFloor ≤ u`, no update can raise the
limit above `L − k·uFloor`, whatever the evidence claims. -/
theorem acceptanceLimit_le_of_floor (L : ℝ) {k uFloor u : ℝ} (hk : 0 ≤ k) (h : uFloor ≤ u) :
    acceptanceLimit L k u ≤ acceptanceLimit L k uFloor :=
  acceptanceLimit_antitone L hk h

end PropertyKindCalculus.Uncertainty.ConformityLadder
