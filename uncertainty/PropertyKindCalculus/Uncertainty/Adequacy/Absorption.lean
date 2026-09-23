/-
`PropertyKindCalculus.Uncertainty.Adequacy.Absorption` — **A1, the absorption (swamping) theorem**
over `ℝ` (Stage 3, `UNCERTAINTY.md` §4.2/§4.5).

Numerical adequacy hinges on one fact: adding a small number to a large one can lose the small one.
On the local rounding grid (spacing `u = ulp`, `Grid.lean`) it is precise and has a sharp threshold
at *half a ulp*:

  * **A1 — absorption.** A representable value `x` perturbed by strictly less than half a ulp rounds
    back to `x` (`absorb`): `|y| < u/2 → gridRound u (x + y) = x`. The perturbation carries *no*
    information into the result — this is floating-point swamping, `x ⊕ y = x` when `|y| < ½ ulp(x)`.

  * **A1-converse — resolution.** A perturbation of at least half a ulp (up to one and a half) *does*
    move the result to the next grid point (`resolve`): `u/2 ≤ y < 3u/2 → gridRound u (x + y) = x + u`.

Together they say half a ulp is the *exact* absorption boundary — below it a contribution is lost,
at or above it it survives. That threshold is the datum the `Adequacy` carrier flags a contribution
`cᵢ·uᵢ` against, and the fact that makes the flag sound (`Adequacy.Soundness`, A3). The binary32
realization is FloatLib's `round_nearestEven_point` (the rounded value is the globally nearest
representable) and `ulp` (see `Adequacy.Fp32Grounding`); the grid statement here is that fact
localized to one magnitude. Proved over `ℝ`, sorry-free.
-/

module

public import PropertyKindCalculus.Uncertainty.Adequacy.Grid

@[expose] public section Blanket

namespace PropertyKindCalculus.Uncertainty.Adequacy

/-- **A1 — absorption.** A representable value `x` perturbed by strictly less than half a ulp rounds
back to `x`: the perturbation is *absorbed*, contributing nothing to the floating-point result. This
is the mathematical content of swamping — `fl(x + y) = x` whenever `|y| < ½ ulp(x)`. -/
theorem absorb {u x y : ℝ} (hu : 0 < u) (hx : OnGrid u x) (hy : |y| < u / 2) :
    gridRound u (x + y) = x := by
  obtain ⟨k, rfl⟩ := hx
  have hune : u ≠ 0 := ne_of_gt hu
  have hdiv : ((k : ℝ) * u + y) / u = (k : ℝ) + y / u := by field_simp
  have hyu : |y / u| < 1 / 2 := by
    rw [abs_div, abs_of_pos hu]
    have h : 1 / 2 - |y| / u = (u / 2 - |y|) / u := by field_simp
    have hpos : 0 < (u / 2 - |y|) / u := div_pos (by linarith) hu
    have : 0 < 1 / 2 - |y| / u := by rw [h]; exact hpos
    linarith
  have hround0 : round (y / u) = 0 := by
    rw [round_eq_zero_iff, Set.mem_Ico]
    have := abs_lt.mp hyu
    exact ⟨le_of_lt this.1, this.2⟩
  unfold gridRound
  rw [hdiv, round_intCast_add, hround0]
  push_cast
  ring

/-- **A1-converse — resolution.** A perturbation of at least half a ulp (up to one and a half) moves
`x` to the next grid point, so it *does* change the rounded result. Thus half a ulp is the exact
absorption threshold: below it the contribution is lost (`absorb`), at or above it it survives. -/
theorem resolve {u x y : ℝ} (hu : 0 < u) (hx : OnGrid u x)
    (hy0 : u / 2 ≤ y) (hy1 : y < 3 * u / 2) :
    gridRound u (x + y) = x + u := by
  obtain ⟨k, rfl⟩ := hx
  have hune : u ≠ 0 := ne_of_gt hu
  have hdiv : ((k : ℝ) * u + y) / u = (k : ℝ) + y / u := by field_simp
  have hlo : (1 : ℝ) / 2 ≤ y / u := by
    have h : y / u - 1 / 2 = (y - u / 2) / u := by field_simp
    have hpos : 0 ≤ (y - u / 2) / u := div_nonneg (by linarith) (le_of_lt hu)
    have : 0 ≤ y / u - 1 / 2 := by rw [h]; exact hpos
    linarith
  have hhi : y / u < 3 / 2 := by
    have h : 3 / 2 - y / u = (3 * u / 2 - y) / u := by field_simp
    have hpos : 0 < (3 * u / 2 - y) / u := div_pos (by linarith) hu
    have : 0 < 3 / 2 - y / u := by rw [h]; exact hpos
    linarith
  have hround1 : round (y / u) = 1 := by
    rw [round_eq_iff, Set.mem_Ico]
    refine ⟨?_, ?_⟩
    · push_cast; linarith
    · push_cast; linarith
  unfold gridRound
  rw [hdiv, round_intCast_add, hround1]
  push_cast
  ring

end PropertyKindCalculus.Uncertainty.Adequacy

end Blanket
