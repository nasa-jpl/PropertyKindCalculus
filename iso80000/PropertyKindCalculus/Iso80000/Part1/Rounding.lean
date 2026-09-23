/-
# ISO 80000-1 Annex B (normative) — Rounding of numbers

Annex B fixes what rounding *is* in the series: replacing a number by an integral multiple
of a chosen **rounding range** (B.1), taking the nearest such multiple (B.2), and — when
two are equally near — resolving the tie by one of two named rules (B.3):

  * **Rule A** selects the even multiple;
  * **Rule B** selects the multiple greater in magnitude.

The annex records that both are in use, prefers Rule A for series of measurements because
it minimizes the accumulated rounding error, and notes that Rule B is sometimes used in
computers. B.4 adds that rounding shall be done in one step, never in stages.

This work already has the grid the annex describes: `Uncertainty.Adequacy.OnGrid u x` is
"an integral multiple of the rounding range `u`", and `gridRound u x = u · round (x / u)`
is the rounding operation, the specification carrier for numerical adequacy (`UNCERTAINTY.md`
§4). So the annex is not re-implemented here; what this module supplies is the **conformance
statement**, and it is worth stating because it is not a clean fit:

  * B.1 and B.2 hold — `gridRound` lands on the grid and within half a rounding range.
  * B.3 does **not** name the rule `gridRound` uses. Mathlib's `round` breaks a tie toward
    `+∞`, so `gridRound` agrees with Rule B on a nonnegative tie and with neither rule on a
    negative one. The two worked ties below are the annex's own, and they are what settles
    it: nothing here rests on reading the definition.

The consequence for a reader of this library is small but specific: the two rounding
carriers in this work resolve ties differently. The specification grid rounds ties toward
`+∞`, while genuine binary32 (`round32`, ISO/IEC 60559 round-to-nearest-even) is Annex B's
Rule A. Every bound proved over the grid is a *half-range* bound
(`abs_sub_gridRound_le`), which both rules satisfy, so no result transfers incorrectly —
but a claim about *which* multiple is selected at a tie does not transfer, and that is what
this module records.

No normative text from the licensed standard is reproduced; the annex is restated in this
work's own formalism.
-/

module

public import PropertyKindCalculus.Iso80000.References
public import PropertyKindCalculus.Uncertainty.Adequacy.Grid

@[expose] public section Blanket

namespace PropertyKindCalculus.Iso80000.Part1.AnnexB

open PropertyKindCalculus.Uncertainty.Adequacy

/-- The source: ISO 80000-1, whose Annex B is normative. -/
def source : StandardRef := iso80000_1

/-! ## B.1 and B.2 — the grid, and the nearest multiple -/

/-- **B.1 — the rounded number is on the grid.** A rounded value is an integral multiple
of the rounding range, which is what `OnGrid` says. -/
theorem rounded_onGrid (u x : ℝ) : OnGrid u (gridRound u x) :=
  ⟨round (x / u), by rw [gridRound]; ring⟩

/-- **B.2 — the nearest multiple.** `gridRound` never moves a number by more than half a
rounding range, so when one multiple is strictly nearest it is the one selected. -/
theorem rounded_within_half_range {u : ℝ} (x : ℝ) (hu : 0 < u) :
    |gridRound u x - x| ≤ u / 2 :=
  abs_sub_gridRound_le x hu

/-- **B.4 — one step, not two.** A value already on the grid is left alone, so re-rounding
a rounded number at the same range changes nothing; the annex's warning is about rounding
at a *finer* range first, which is a different operation and not this identity. -/
theorem round_idempotent {u : ℝ} (hu : u ≠ 0) (x : ℝ) :
    gridRound u (gridRound u x) = gridRound u x :=
  gridRound_onGrid hu (rounded_onGrid u x)

/-! ## B.3 — which tie rule this grid uses

The annex's own worked ties, at rounding range `1/10`. Rule A selects the even multiple
and Rule B the multiple greater in magnitude, so the two rules disagree at `12,25`
(`12,2` against `12,3`) and again at `−12,25` (`−12,2` against `−12,3`). -/

/-- **The positive tie.** `gridRound` selects the greater multiple — Rule B's answer, and
not Rule A's. -/
theorem gridRound_tie_pos : gridRound (1 / 10) (49 / 4) = 123 / 10 := by
  rw [gridRound, round_eq]
  norm_num

/-- **The negative tie.** `gridRound` selects the multiple *smaller* in magnitude, because
Mathlib's `round` breaks ties toward `+∞`. This is Rule A's answer here and not Rule B's —
so, with `gridRound_tie_pos`, the grid follows neither rule of B.3 consistently. -/
theorem gridRound_tie_neg : gridRound (1 / 10) (-(49 / 4)) = -(61 / 5) := by
  rw [gridRound, round_eq]
  norm_num

/-- **Neither rule, stated as one fact.** Rule A would have given `123/10 ≠ 61/5` at the
positive tie and Rule B `-(123/10) ≠ -(61/5)` at the negative one, so no single rule of
B.3 describes this grid. The half-range bound (`rounded_within_half_range`) is what both
rules share and what every result in this work actually uses. -/
theorem gridRound_follows_neither_rule :
    gridRound (1 / 10) (49 / 4) ≠ 61 / 5 ∧
      gridRound (1 / 10) (-(49 / 4)) ≠ -(123 / 10) := by
  refine ⟨?_, ?_⟩
  · rw [gridRound_tie_pos]; norm_num
  · rw [gridRound_tie_neg]; norm_num

end PropertyKindCalculus.Iso80000.Part1.AnnexB

end Blanket
