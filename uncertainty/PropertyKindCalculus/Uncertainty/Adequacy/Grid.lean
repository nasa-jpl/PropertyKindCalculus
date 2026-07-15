/-
`PropertyKindCalculus.Uncertainty.Adequacy.Grid` — the local floating-point rounding grid over `ℝ`
(Stage 3, `UNCERTAINTY.md` §4). The specification carrier for numerical adequacy.

A binary floating-point format is, *near any fixed magnitude*, a uniform grid of representable reals
spaced one unit in the last place (`ulp`) apart. TorchLean's `FP32` layer realizes exactly this grid
over `ℝ`: `TorchLean.Floats.ulp₃₂` is the spacing and
`FP32.round_abs_error : |round₃₂ x − x| ≤ ulp₃₂ x / 2` its half-ulp bound (both `noncomputable` ℝ
specs — see `Adequacy.Fp32Grounding`). This module abstracts that grid to a *uniform spacing*
`u = ulp > 0`, which is all the absorption/soundness arguments (`Absorption`, `Soundness`) and the
cancellation argument (`Sterbenz32`) need: they are local statements at one magnitude, where the
binary32 grid *is* uniform. Nothing here is `noncomputable`-dependent; it is pure Mathlib `ℝ`.

  * `gridRound u x` — round `x` to the nearest point of the grid `u·ℤ` (round-to-nearest, ties up),
    the local model of a floating-point round.
  * `OnGrid u x` — `x` is exactly representable (an integer multiple of the spacing).
  * `gridRound_onGrid` — rounding is the identity on representable values.
  * `abs_sub_gridRound_le` — the half-ulp bound, the local mirror of `FP32.round_abs_error`.

All sorry-free.
-/
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Algebra.Order.Round
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp

namespace PropertyKindCalculus.Uncertainty.Adequacy

/-- **A representable value** on the local grid of spacing `u`: an exact integer multiple of `u`.
These are the floating-point numbers at one magnitude. -/
def OnGrid (u x : ℝ) : Prop := ∃ k : ℤ, x = (k : ℝ) * u

/-- **Round to the nearest grid point** of spacing `u` (round-to-nearest, ties toward `+∞`, matching
Mathlib's `round`): the local model of a binary floating-point round at ulp `u`. -/
noncomputable def gridRound (u x : ℝ) : ℝ := u * (round (x / u) : ℤ)

/-- `0` is on every grid. -/
@[simp] theorem onGrid_zero (u : ℝ) : OnGrid u 0 := ⟨0, by simp⟩

/-- The spacing itself is on the grid (`u = 1·u`). -/
theorem onGrid_self (u : ℝ) : OnGrid u u := ⟨1, by simp⟩

/-- The grid is closed under subtraction — the algebraic root of the exactness of near-equal
subtraction (`Sterbenz32.sub_exact_on_grid`). -/
theorem OnGrid.sub {u x y : ℝ} (hx : OnGrid u x) (hy : OnGrid u y) : OnGrid u (x - y) := by
  obtain ⟨j, rfl⟩ := hx
  obtain ⟨k, rfl⟩ := hy
  exact ⟨j - k, by push_cast; ring⟩

/-- The grid is closed under addition. -/
theorem OnGrid.add {u x y : ℝ} (hx : OnGrid u x) (hy : OnGrid u y) : OnGrid u (x + y) := by
  obtain ⟨j, rfl⟩ := hx
  obtain ⟨k, rfl⟩ := hy
  exact ⟨j + k, by push_cast; ring⟩

/-- **Rounding is the identity on representable values.** A grid point rounds to itself — the
fixed-point law every rounding satisfies on its own format. -/
theorem gridRound_onGrid {u x : ℝ} (hu : u ≠ 0) (h : OnGrid u x) : gridRound u x = x := by
  obtain ⟨k, rfl⟩ := h
  unfold gridRound
  rw [mul_div_assoc, div_self hu, mul_one, round_intCast]
  ring

/-- **The half-ulp bound** `|gridRound u x − x| ≤ u/2` — the local mirror of TorchLean's
`FP32.round_abs_error : |round₃₂ x − x| ≤ ulp₃₂ x / 2`. -/
theorem abs_sub_gridRound_le {u : ℝ} (x : ℝ) (hu : 0 < u) : |gridRound u x - x| ≤ u / 2 := by
  have hune : u ≠ 0 := ne_of_gt hu
  have h : gridRound u x - x = u * ((round (x / u) : ℝ) - x / u) := by
    unfold gridRound
    field_simp
  rw [h, abs_mul, abs_of_pos hu]
  have hr : |(round (x / u) : ℝ) - x / u| ≤ 1 / 2 := by
    rw [abs_sub_comm]; exact abs_sub_round (x / u)
  calc u * |(round (x / u) : ℝ) - x / u| ≤ u * (1 / 2) :=
        mul_le_mul_of_nonneg_left hr (le_of_lt hu)
    _ = u / 2 := by ring

end PropertyKindCalculus.Uncertainty.Adequacy
