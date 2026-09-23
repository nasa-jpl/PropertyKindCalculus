/-
`PropertyKindCalculus.Uncertainty.Adequacy.Sterbenz32` — **A2, the exact-cancellation (Sterbenz)
theorem** over `ℝ` (Stage 3, `UNCERTAINTY.md` §4.2/§4.5).

Absorption's dual: subtracting two *near-equal* floating-point numbers is **exact** — no rounding
error is introduced — yet the *relative* uncertainty of the result is amplified without bound. Both
halves matter for adequacy, and both are theorems here:

  * **`sub_exact_on_grid`.** Subtraction of two values on a common grid is exact (rounds to itself) —
    the local "no new rounding error" fact, immediate from grid closure (`Grid.OnGrid.sub`).

  * **A2 — `flx_sterbenz`.** The *reason* near-equal operands share a grid: for two positive numbers
    representable at precision `p` (Flocq's `FLX p`) with `y ≤ x ≤ 2y`, the difference `x − y` is
    itself representable at precision `p`. This is the self-contained real-number analogue of
    FloatLib's `generic_format_FLX_sterbenz` (`Flocq/Theory/Format`), stated over the
    explicit mantissa/exponent model. Binary32 is `FLX 24` with a bounded exponent; **Stage 3.2 now
    carries this to TorchLean's `fexp32`/`FP32` (the FLT format with gradual underflow)** —
    `Fp32Grounding.round32_sterbenz_exact` / `sub32_exact_of_sterbenz` state near-equal binary32
    subtraction as a theorem about `round32`, grounded in the TorchLean PR's
    `generic_format_FLT_sterbenz`.

  * **`relUnc_amplifies`.** The uncertainty-side hazard: when the difference shrinks to at or below
    the absolute uncertainty the operands carry, the *relative* uncertainty of the difference is at
    least `1` (100%). This is the cancellation warning the carrier raises, dual to swamping.

Proved over `ℝ`, sorry-free.
-/

module

public import PropertyKindCalculus.Uncertainty.Adequacy.Grid
public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.Tactic.Positivity

@[expose] public section Blanket

namespace PropertyKindCalculus.Uncertainty.Adequacy

/-! ## Exactness on a shared grid, and the relative-uncertainty hazard -/

/-- **Subtraction of two co-representable values is exact.** When `x` and `y` lie on a common grid
of spacing `u`, their difference rounds to itself — no rounding error is introduced. This is the
"no new noise" half of the cancellation story (its magnitude may still be tiny — see
`relUnc_amplifies`). -/
theorem sub_exact_on_grid {u x y : ℝ} (hu : u ≠ 0) (hx : OnGrid u x) (hy : OnGrid u y) :
    gridRound u (x - y) = x - y :=
  gridRound_onGrid hu (hx.sub hy)

/-- **Cancellation amplifies relative uncertainty.** Sterbenz makes near-equal subtraction *exact*
(`sub_exact_on_grid`) — but the *relative* uncertainty of the result blows up: once the difference
`d = x − y` shrinks to at or below the absolute uncertainty `ũ` carried by the operands, the relative
uncertainty `ũ/d` of the difference is at least `1` (100%). This is the adequacy hazard the carrier
warns about at a cancellation site — dual to absorption, and invisible to the exactness of the
subtraction itself. -/
theorem relUnc_amplifies {d ũ : ℝ} (hd : 0 < d) (hsmall : d ≤ ũ) : 1 ≤ ũ / d :=
  one_le_div_iff.mpr (Or.inl ⟨hd, hsmall⟩)

/-! ## The FLX floating-point format and Sterbenz's theorem -/

/-- **Representable at precision `p`** (Flocq's `FLX p`): a `p`-bit signed mantissa `m` (`|m| < 2^p`)
scaled by an integer power of two. Fixed precision, unbounded exponent — the set of exact
floating-point numbers ignoring overflow/underflow. Binary32 is `FLX 24` with a bounded exponent. -/
def FLX (p : ℕ) (x : ℝ) : Prop := ∃ m e : ℤ, x = (m : ℝ) * (2 : ℝ) ^ e ∧ |m| < 2 ^ p

/-- Align a mantissa `m` at exponent `eHi` down to a lower exponent `eLo`: the value is unchanged and
the new mantissa `m · 2^(eHi−eLo)` is an integer. The arithmetic core of exponent alignment. -/
private theorem align (m : ℤ) {eHi eLo : ℤ} (he : eLo ≤ eHi) :
    (m : ℝ) * (2 : ℝ) ^ eHi = ((m * 2 ^ ((eHi - eLo).toNat) : ℤ) : ℝ) * (2 : ℝ) ^ eLo := by
  have hd : ((eHi - eLo).toNat : ℤ) = eHi - eLo := Int.toNat_of_nonneg (by linarith)
  push_cast
  rw [← zpow_natCast (2 : ℝ) ((eHi - eLo).toNat), hd, mul_assoc,
    ← zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0), show eHi - eLo + eLo = eHi from by ring]

/-- Cancel a positive common factor `2^e` from a mantissa inequality. -/
private theorem mantissa_le {a b e : ℤ} (h : (a : ℝ) * (2 : ℝ) ^ e ≤ (b : ℝ) * (2 : ℝ) ^ e) :
    a ≤ b := by
  by_contra hcon
  have hR : (b : ℝ) < (a : ℝ) := by exact_mod_cast not_le.mp hcon
  have hp : (0 : ℝ) < (2 : ℝ) ^ e := zpow_pos (by norm_num) e
  have := mul_lt_mul_of_pos_right hR hp
  linarith

/-- A positive value with a positive power-of-two factor has a positive mantissa. -/
private theorem mantissa_pos {a e : ℤ} (h : 0 < (a : ℝ) * (2 : ℝ) ^ e) : 0 < a := by
  by_contra hcon
  have hR : (a : ℝ) ≤ 0 := by exact_mod_cast not_lt.mp hcon
  have hp : (0 : ℝ) < (2 : ℝ) ^ e := zpow_pos (by norm_num) e
  have := mul_nonpos_of_nonpos_of_nonneg hR (le_of_lt hp)
  linarith

/-- **A2 — Sterbenz's theorem.** The difference of two positive numbers representable at precision
`p`, when they lie within a factor of two of each other (`y ≤ x ≤ 2y`), is itself representable at
precision `p` — so the subtraction is *exact*. This is why near-equal floating-point subtraction
introduces no rounding error. The real-number analogue of TorchLean's
`generic_format_FLX_sterbenz`. -/
theorem flx_sterbenz {p : ℕ} {x y : ℝ} (hy : 0 < y) (hyx : y ≤ x) (hx2y : x ≤ 2 * y)
    (hxr : FLX p x) (hyr : FLX p y) : FLX p (x - y) := by
  obtain ⟨mx, ex, hxe, hmx⟩ := hxr
  obtain ⟨my, ey, hye, hmy⟩ := hyr
  rcases le_total ey ex with hle | hle
  · -- align x down to y's (smaller) exponent ey
    have hxal : x = ((mx * 2 ^ ((ex - ey).toNat) : ℤ) : ℝ) * (2 : ℝ) ^ ey := by
      rw [hxe]; exact align mx hle
    have hMxle : my ≤ mx * 2 ^ ((ex - ey).toNat) :=
      mantissa_le (e := ey) (by rw [← hxal, ← hye]; exact hyx)
    have hMx2 : mx * 2 ^ ((ex - ey).toNat) ≤ 2 * my := by
      apply mantissa_le (e := ey)
      have hrhs : (((2 * my : ℤ)) : ℝ) * (2 : ℝ) ^ ey = 2 * y := by rw [hye]; push_cast; ring
      rw [← hxal, hrhs]; exact hx2y
    have hmylt : my < 2 ^ p := lt_of_le_of_lt (le_abs_self my) hmy
    refine ⟨mx * 2 ^ ((ex - ey).toNat) - my, ey, ?_, ?_⟩
    · rw [hxal, hye]; push_cast; ring
    · rw [abs_of_nonneg (by linarith : (0 : ℤ) ≤ mx * 2 ^ ((ex - ey).toNat) - my)]
      linarith
  · -- align y down to x's (smaller) exponent ex
    have hyal : y = ((my * 2 ^ ((ey - ex).toNat) : ℤ) : ℝ) * (2 : ℝ) ^ ex := by
      rw [hye]; exact align my hle
    have hMyle : my * 2 ^ ((ey - ex).toNat) ≤ mx :=
      mantissa_le (e := ex) (by rw [← hyal, ← hxe]; exact hyx)
    have hMypos : 0 < my * 2 ^ ((ey - ex).toNat) :=
      mantissa_pos (e := ex) (by rw [← hyal]; exact hy)
    have hmxlt : mx < 2 ^ p := lt_of_le_of_lt (le_abs_self mx) hmx
    refine ⟨mx - my * 2 ^ ((ey - ex).toNat), ex, ?_, ?_⟩
    · rw [hxe, hyal]; push_cast; ring
    · rw [abs_of_nonneg (by linarith : (0 : ℤ) ≤ mx - my * 2 ^ ((ey - ex).toNat))]
      linarith

end PropertyKindCalculus.Uncertainty.Adequacy

end Blanket
