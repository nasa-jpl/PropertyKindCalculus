/-
`PropertyKindCalculus.Uncertainty.Adequacy.Soundness` — **A3, the adequacy soundness theorem**
over `ℝ` (Stage 3, `UNCERTAINTY.md` §4.5).

The `Adequacy` carrier (`Adequacy.lean`) flags an addition site as *absorbing* an operand when that
operand's carried uncertainty falls below half the accumulated value's ulp. This module proves that
verdict is exactly right: on the local grid, flagging is *sound and complete* for the question "does
any information about this contribution survive into the floating-point result?".

  * `AbsorptionFlag u unc` — the `ℝ`-level specification of the carrier's swamping check
    (`unc < ½ ulp`), of which the executable `Float` carrier computes the numeric image.
  * **A3 — `verdict_sound`.** For a representable accumulator (ulp `u`) and a nonnegative uncertainty
    within one ulp, `AbsorptionFlag u unc ↔ gridRound u (s + unc) = s`: the flag fires *iff* the
    contribution is genuinely lost (the rounded sum is unchanged). Sound (flag ⟹ lost, from A1
    `absorb`) and complete (lost ⟹ flag, from A1-converse `resolve`).

This is the local, per-site soundness that makes the carrier's report trustworthy. The universal
capstone of `UNCERTAINTY.md` §4.5 — *for every input in a box, the `FP32` measurand's uncertainty
equals the `ℝ` one up to a proven bound over an arbitrary model* — composes this per-site fact with
interval-carrier soundness across a whole evaluation, and is the subject of the follow-up sub-stages
(§6, Stage 3.x). Proved over `ℝ`, sorry-free.
-/
import PropertyKindCalculus.Uncertainty.Adequacy.Absorption

namespace PropertyKindCalculus.Uncertainty.Adequacy

/-- The **absorption verdict** the adequacy carrier raises at an addition site: given the accumulated
value's ulp `u` and an operand's carried uncertainty `unc`, flag the operand as *absorbed* exactly
when its uncertainty is below half a ulp. This is the `ℝ` specification of the executable carrier's
swamping check (`Adequacy.absorbs`). -/
def AbsorptionFlag (u unc : ℝ) : Prop := unc < u / 2

/-- **A3 — soundness of the absorption verdict.** For a representable accumulated value `s` (grid
spacing `u = ulp`) and a nonnegative uncertainty within one ulp, the carrier flags absorption *iff*
the contribution is genuinely lost: perturbing the accumulator by `unc` leaves the rounded result
unchanged. So the flag `unc < ½ ulp` is *exactly* the condition "no information about this
contribution survives into the floating-point result" — **sound** (flag ⟹ lost) and **complete**
(lost ⟹ flag). This is the theorem that makes the `Adequacy` carrier's report trustworthy. -/
theorem verdict_sound {u s unc : ℝ} (hu : 0 < u) (hs : OnGrid u s)
    (h0 : 0 ≤ unc) (h1 : unc < u) :
    AbsorptionFlag u unc ↔ gridRound u (s + unc) = s := by
  constructor
  · intro hflag
    exact absorb hu hs (by rw [abs_of_nonneg h0]; exact hflag)
  · intro hkept
    by_contra hflag
    have hge : u / 2 ≤ unc := by
      unfold AbsorptionFlag at hflag
      exact not_lt.mp hflag
    have hres := resolve hu hs hge (by linarith)
    rw [hres] at hkept
    have : u = 0 := by linarith
    exact (ne_of_gt hu) this

/-- **A3, swamping corollary.** A small input uncertainty added to a large accumulator is
numerically invisible: when the operand's uncertainty is below half the accumulator's ulp, the flag
fires and the rounded sum is exactly the accumulator — the input contributes nothing. This is the
site the `Adequacy` carrier reports in the deliberately-inadequate `AdequacySwamping` example. -/
theorem swamped {u s unc : ℝ} (hu : 0 < u) (hs : OnGrid u s) (h0 : 0 ≤ unc)
    (hflag : AbsorptionFlag u unc) : gridRound u (s + unc) = s :=
  absorb hu hs (by rw [abs_of_nonneg h0]; exact hflag)

end PropertyKindCalculus.Uncertainty.Adequacy
