/-
# Worked example — Stage 3 numerical-adequacy theorems as checked proof terms

The `ℝ`-level rigor of the adequacy layer (`UNCERTAINTY.md` §4.5), applied to concrete values and
verified sorry-free by `#print axioms`. This is the proof-carrier companion of the executable
`AdequacySwamping` example: the numbers that example *computes* over `Float`, this one *proves* over
`ℝ`.

  * **A1 — absorption / resolution.** On the grid of spacing `8` (a binary32 ulp), a value `80`
    perturbed by `1 < ½·8` rounds back to `80` (`absorb`); perturbed by `5 ≥ ½·8` it moves to the
    next grid point `88` (`resolve`). Half a ulp is the exact threshold.
  * **A3 — soundness of the verdict.** The carrier's flag `unc < ½ ulp` holds *iff* the contribution
    is lost (`verdict_sound`): the biconditional that makes the runtime check trustworthy.
  * **A2 — Sterbenz.** `3 − 2` of two `FLX 24` numbers within a factor of two is itself `FLX 24`
    (`flx_sterbenz`) and exact on their common grid (`sub_exact_on_grid`); cancellation nonetheless
    amplifies relative uncertainty to ≥ 100% (`relUnc_amplifies`).

Everything is a **checked fact** (the module builds under CI); the axiom prints confirm no `sorryAx`.
Mathlib-backed.
-/

module

public import PropertyKindCalculus.Uncertainty.Adequacy.Absorption
meta import PropertyKindCalculus.Uncertainty.Adequacy.Absorption
public import PropertyKindCalculus.Uncertainty.Adequacy.Soundness
meta import PropertyKindCalculus.Uncertainty.Adequacy.Soundness
public import PropertyKindCalculus.Uncertainty.Adequacy.Sterbenz32
meta import PropertyKindCalculus.Uncertainty.Adequacy.Sterbenz32

@[expose] public section Blanket

namespace PropertyKindCalculus.UncertaintyExamples.AdequacyLadder

open PropertyKindCalculus.Uncertainty.Adequacy

/-! ## A1 — absorption and its sharp threshold at half a ulp -/

/-- A `1`-perturbation of the grid value `80` (spacing `8`) is absorbed: `fl(80 + 1) = 80`. -/
theorem a1_absorb : gridRound 8 (80 + 1) = 80 :=
  absorb (by norm_num) ⟨10, by norm_num⟩ (by rw [abs_one]; norm_num)

/-- A `5`-perturbation (≥ half a ulp) resolves: it moves `80` to the next grid point `88`. -/
theorem a1_resolve : gridRound 8 (80 + 5) = 80 + 8 :=
  resolve (by norm_num) ⟨10, by norm_num⟩ (by norm_num) (by norm_num)

/-! ## A3 — the absorption verdict is sound and complete -/

/-- The flag `1 < ½·8` holds iff the contribution is numerically lost — the verdict is exactly right. -/
theorem a3_verdict_sound : AbsorptionFlag 8 1 ↔ gridRound 8 (80 + 1) = 80 :=
  verdict_sound (by norm_num) ⟨10, by norm_num⟩ (by norm_num) (by norm_num)

/-- The flag fires here (`1 < 4`), and A3 turns it into the concrete loss `fl(80 + 1) = 80`. -/
theorem a3_flag_fires : AbsorptionFlag 8 1 := by unfold AbsorptionFlag; norm_num

/-! ## A2 — Sterbenz exactness and the cancellation hazard -/

/-- `3` and `2` are representable at precision 24 (binary32). -/
theorem three_flx : FLX 24 3 := ⟨3, 0, by norm_num, by norm_num⟩
theorem two_flx : FLX 24 2 := ⟨2, 0, by norm_num, by norm_num⟩

/-- **Sterbenz:** the difference `3 − 2` of two near-equal `FLX 24` numbers is itself `FLX 24`. -/
theorem a2_sterbenz : FLX 24 (3 - 2) :=
  flx_sterbenz (by norm_num) (by norm_num) (by norm_num) three_flx two_flx

/-- The subtraction is exact on the common grid of spacing `1`: `fl(3 − 2) = 3 − 2`. -/
theorem a2_sub_exact : gridRound 1 (3 - 2) = 3 - 2 :=
  sub_exact_on_grid (by norm_num) ⟨3, by norm_num⟩ ⟨2, by norm_num⟩

/-- Cancellation to a difference `1` with operands each carrying uncertainty `100` amplifies the
relative uncertainty to `100 ≥ 1` (100%). -/
theorem a2_relunc : (1 : ℝ) ≤ 100 / 1 :=
  relUnc_amplifies (by norm_num) (by norm_num)

/-! ## Sorry-free — the axiom profile of the adequacy theorems -/

/-- info: 'PropertyKindCalculus.UncertaintyExamples.AdequacyLadder.a1_absorb' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms a1_absorb
/-- info: 'PropertyKindCalculus.UncertaintyExamples.AdequacyLadder.a3_verdict_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms a3_verdict_sound
/-- info: 'PropertyKindCalculus.UncertaintyExamples.AdequacyLadder.a2_sterbenz' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms a2_sterbenz

end PropertyKindCalculus.UncertaintyExamples.AdequacyLadder

end Blanket
