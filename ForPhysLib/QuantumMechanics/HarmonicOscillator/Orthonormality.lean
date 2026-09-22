/-
# The upstream `sorryful` lemma, discharged — `eigenstates_orthonormal`

`Physlib/QuantumMechanics/HarmonicOscillator/Eigenstates.lean` states the orthonormality
of the oscillator's eigenstates with `@[sorryful]`, and its TODO list opens with it. This
module proves it, against the mirrored directory's own imports — no new hypotheses, the
statement verbatim.

**The shape of the proof is the sorry's own hint.** The upstream comment asks for a
product-splitting of the `Space d` integral; `integral_prod_coord` below is that lemma —
`Space.basis` is an orthonormal basis, its `repr` is measure-preserving
(`OrthonormalBasis.measurePreserving_repr`), `EuclideanSpace`'s volume matches the pi
volume, and Mathlib's n-variable Fubini (`integral_fin_nat_prod_volume_eq_prod`,
unconditional at `ℂ`) finishes. The 1D content is PhysLib's own:
`physHermite_orthogonal_cons` and `physHermite_norm_cons` at scale `ξᵢ⁻¹`, with
`eigenCoeff`'s normalization cancelling the `ξᵢ · nᵢ! · 2^nᵢ · √π` exactly.

**Why it sits in the campaign directory.** This is not kind-layer content — it is pure
analysis at magnitudes, PhysLib-facing. It is here because the campaign's rules ask for a
patch rather than a finding: the mirror directory that re-authors the oscillator kinded
also discharges the first item of its upstream TODO list. Offered upstream as a PR, the
transfer is: drop the `ForPhysLib` namespace, inline `integral_prod_coord` where the
sorry's hint asks for it (`Space` API), and replace the `sorryful` proof. Per
`AI-POLICY.md` §3.1 the offer itself is a human's to make.

Axiom profile: `propext, Classical.choice, Quot.sound` — checked at authoring; no
`sorryAx`.
-/

module

public import Physlib.QuantumMechanics.HarmonicOscillator.Eigenstates
public import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

public section -- pkc-blanket
@[expose] section -- pkc-blanket-expose

open MeasureTheory QuantumMechanics HarmonicOscillator Polynomial Real Complex
open SpaceDHilbertSpace SchwartzSubmodule InnerProductSpace
open scoped Nat ComplexConjugate

namespace ForPhysLib.QuantumMechanics.HarmonicOscillator.Orthonormality

noncomputable section

variable {d : ℕ}


/-- The coordinates of `Space.basis.repr` are the point's own coordinates. -/
lemma repr_coord (p : Space d) (i : Fin d) : Space.basis.repr p i = p i := by
  rw [OrthonormalBasis.repr_apply_apply]
  simp

/-- The splitting lemma the upstream sorry's hint asks for. -/
theorem integral_prod_coord (f : Fin d → ℝ → ℂ) :
    ∫ x : Space d, ∏ i, f i (x i) = ∏ i, ∫ t : ℝ, f i t := by
  rw [← (Space.basis.measurePreserving_measurableEquiv.symm
      (μb := volume)).integral_comp']
  have h1 : ∀ (z : EuclideanSpace ℝ (Fin d)) (i : Fin d),
      ((Space.basis.measurableEquiv.symm z : Space d)) i = z i := by
    intro z i
    have he : (Space.basis.measurableEquiv.symm z : Space d)
        = Space.basis.repr.symm z := rfl
    rw [he, ← repr_coord (Space.basis.repr.symm z) i,
      Space.basis.repr.apply_symm_apply]
  simp_rw [h1]
  rw [← ((EuclideanSpace.volume_preserving_symm_measurableEquiv_toLp
      (Fin d)).symm).integral_comp']
  have h2 : ∀ (w : Fin d → ℝ) (i : Fin d),
      (((MeasurableEquiv.toLp 2 (Fin d → ℝ)).symm.symm w :
        EuclideanSpace ℝ (Fin d))) i = w i := fun _ _ => rfl
  simp_rw [h2]
  exact integral_fin_nat_prod_volume_eq_prod f

/-- The scaled 1D Hermite pair integral, if-collapsed. -/
lemma integral_hermite_pair {ξ : ℝ} (hξ : 0 < ξ) (a b : ℕ) :
    ∫ t : ℝ, (physHermite a (t / ξ) * physHermite b (t / ξ)) * Real.exp (-(t / ξ) ^ 2) =
    if a = b then ξ * (a ! * 2 ^ a * √π) else 0 := by
  have h2 : ∀ t : ℝ, -(t / ξ) ^ 2 = -ξ⁻¹ ^ 2 * t ^ 2 := by
    intro t; rw [div_eq_inv_mul]; ring
  simp_rw [h2, div_eq_inv_mul]
  split_ifs with h
  · subst h
    rw [physHermite_norm_cons a ξ⁻¹, inv_inv, abs_of_pos hξ, smul_eq_mul]
  · exact physHermite_orthogonal_cons h ξ⁻¹

/-- One coordinate's slice of `conj (eigenfunction n) * eigenfunction n'`. -/
noncomputable def pairIntegrand (Q : HarmonicOscillator d) (n n' : Fin d → ℕ)
    (i : Fin d) (t : ℝ) : ℂ :=
  (starRingEnd ℂ) (↑(Q.eigenCoeff n i) *
      ↑(physHermite (n i) (t / Q.ξ i)) * cexp (-2⁻¹ * (↑t / ↑(Q.ξ i)) ^ 2)) *
    (↑(Q.eigenCoeff n' i) * ↑(physHermite (n' i) (t / Q.ξ i)) *
      cexp (-2⁻¹ * (↑t / ↑(Q.ξ i)) ^ 2))

/-- One coordinate's factor integral: the normalized pair integrates to the delta. -/
lemma integral_factor (Q : HarmonicOscillator d) (n n' : Fin d → ℕ) (i : Fin d) :
    ∫ t : ℝ, pairIntegrand Q n n' i t = (δ[n i, n' i] : ℂ) := by
  have hξ := Q.ξ_pos i
  simp only [pairIntegrand]
  have hcast : ∀ t : ℝ,
      (starRingEnd ℂ) (↑(Q.eigenCoeff n i) *
          ↑(physHermite (n i) (t / Q.ξ i)) * cexp (-2⁻¹ * (↑t / ↑(Q.ξ i)) ^ 2)) *
        (↑(Q.eigenCoeff n' i) * ↑(physHermite (n' i) (t / Q.ξ i)) *
          cexp (-2⁻¹ * (↑t / ↑(Q.ξ i)) ^ 2)) =
      ↑((Q.eigenCoeff n i * Q.eigenCoeff n' i) *
        ((physHermite (n i) (t / Q.ξ i) * physHermite (n' i) (t / Q.ξ i)) *
          Real.exp (-(t / Q.ξ i) ^ 2))) := by
    intro t
    have hw : (-2⁻¹ * ((t : ℂ) / ((Q.ξ i : ℝ) : ℂ)) ^ 2)
        = ((-2⁻¹ * (t / Q.ξ i) ^ 2 : ℝ) : ℂ) := by push_cast; ring
    rw [hw, ← Complex.ofReal_exp]
    simp only [← Complex.ofReal_mul, conj_ofReal]
    norm_cast
    have harg : (-2⁻¹ * (t / Q.ξ i) ^ 2) + (-2⁻¹ * (t / Q.ξ i) ^ 2)
        = -(t / Q.ξ i) ^ 2 := by ring
    calc Q.eigenCoeff n i * physHermite (n i) (t / Q.ξ i) *
          Real.exp (-2⁻¹ * (t / Q.ξ i) ^ 2) *
        (Q.eigenCoeff n' i * physHermite (n' i) (t / Q.ξ i) *
          Real.exp (-2⁻¹ * (t / Q.ξ i) ^ 2))
        = (Q.eigenCoeff n i * Q.eigenCoeff n' i) *
          ((physHermite (n i) (t / Q.ξ i) * physHermite (n' i) (t / Q.ξ i)) *
            (Real.exp (-2⁻¹ * (t / Q.ξ i) ^ 2) *
              Real.exp (-2⁻¹ * (t / Q.ξ i) ^ 2))) := by ring
      _ = _ := by rw [← Real.exp_add, harg]
  simp_rw [hcast]
  rw [integral_complex_ofReal, integral_const_mul,
    integral_hermite_pair hξ (n i) (n' i)]
  rw [eigenCoeff_eq, eigenCoeff_eq]
  rcases eq_or_ne (n i) (n' i) with h | h
  · rw [ite_eq_left h, ← h]
    have hX : (0 : ℝ) < 2 ^ n i * (n i)! * √π * Q.ξ i := by positivity
    rw [div_mul_div_comm, one_mul, Real.mul_self_sqrt hX.le]
    rw [KroneckerDelta.eq_one_of_same]
    norm_cast
    rw [one_div, inv_mul_eq_div]
    have hB : ((2 ^ n i * (n i)! : ℕ) : ℝ) * √π * Q.ξ i ≠ 0 :=
      ne_of_gt (mul_pos (mul_pos (by positivity) (Real.sqrt_pos.mpr Real.pi_pos)) hξ)
    rw [div_eq_one_iff_eq hB]
    push_cast
    ring
  · rw [ite_eq_right h]
    simp [KroneckerDelta.eq_zero_of_ne h]

set_option maxHeartbeats 1000000 in
/-- The upstream sorry, discharged. -/
theorem eigenstates_orthonormal' (Q : HarmonicOscillator d) (n n' : Fin d → ℕ) :
    ⟪(Q.eigenstate n : Q.HS), Q.eigenstate n'⟫_ℂ = δ[n,n'] := by
  rw [eigenstate_eq, eigenstate_eq, ← Submodule.coe_inner, schwartzEquiv_inner]
  have h1 : ∀ x : Space d,
      (starRingEnd ℂ) (Q.eigenfunction n x) * Q.eigenfunction n' x
        = ∏ i, pairIntegrand Q n n' i (x i) := by
    intro x
    rw [eigenfunction_apply, eigenfunction_apply, map_prod, ← Finset.prod_mul_distrib]
    simp only [pairIntegrand]
  simp_rw [h1]
  rw [integral_prod_coord (pairIntegrand Q n n')]
  have h2 : ∀ i ∈ Finset.univ, (∫ t : ℝ, pairIntegrand Q n n' i t) = (δ[n i, n' i] : ℂ) :=
    fun i _ => integral_factor Q n n' i
  rw [Finset.prod_congr rfl h2]
  rcases eq_or_ne n n' with h | h
  · subst h
    simp [KroneckerDelta.eq_one_of_same]
  · obtain ⟨i, hi⟩ := Function.ne_iff.mp h
    rw [Finset.prod_eq_zero (Finset.mem_univ i)
      (by rw [KroneckerDelta.eq_zero_of_ne hi, Nat.cast_zero])]
    simp [KroneckerDelta.eq_zero_of_ne h]

end

end ForPhysLib.QuantumMechanics.HarmonicOscillator.Orthonormality

end -- pkc-blanket-expose
end -- pkc-blanket
