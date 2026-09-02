/-
# The second patch — Heisenberg for the oscillator's own operators

`σ_x · σ_p ≥ ℏ/2`, assembled from parts PhysLib already owns but has never joined:
`Operators/Uncertainty.lean` proves the abstract Robertson bound, `Commutation.lean`
proves the canonical `[x̂ᵢ, p̂ⱼ] = iℏδᵢⱼ` on Schwartz maps, and the position and
momentum operators are self-adjoint/symmetric partial maps — yet the bound is
instantiated nowhere, and `ℏ/2` appears nowhere else in the library. The first half of
this file joins them: **`heisenberg_uncertainty` — for every normalized Schwartz state,
`ℏ/2 ≤ σ_xᵢ σ_pᵢ`** — sorry-free, in upstream's own vocabulary (`standardDeviation` of
`𝓧 volume i` and `𝓟 i`), so the transfer upstream is dropping the namespace. Per
`AI-POLICY.md` §3.1 the offer is a human's to make.

The second half is the oscillator's: **the ground state's position uncertainty is
`ξᵢ/√2`** — the characteristic-length species in its metrological role, computed by the
same Hermite–Gaussian machinery that discharged orthonormality (`H₁ = 2X` turns the
first and second moments into the `a = 1` rows of `integral_hermite_pair`). With it the
kind layer closes the loop:

* the position operator becomes a PKC `Observable` (self-adjointness is *proved*
  upstream for `𝓧`, unlike the Hamiltonian's, so no hypothesis rides along) and a
  `Measurand` on the Stage-1 `length · length` edge, with every real an indication —
  the continuous spectrum;
* `sigma_position_groundState`: the measurand's σ at the ground state *is* `ξᵢ/√2`,
  kinded at length;
* `heisenberg_kinded`: `(1/2) • ℏ ≤ σ_x * σ_p` with the product landing at action
  through Stage 3's `length · momentum` entry — the comparison is same-kind because
  the table says so, which is the kind-layer content of "uncertainty principle";
* saturation: `σ_x · σ_p = ℏ/2` at the ground state, exactly. The momentum moment
  `σ_p(ψ₀) = ℏ/(√2 ξᵢ)` comes from differentiating the Gaussian: `𝐩` sends the
  ground state to `(iℏ/ξᵢ²) ·` its `𝐱`-image, so both momentum moments are the
  position moments already computed.
-/

import ForPhysLib.QuantumMechanics.HarmonicOscillator.Operators
import Physlib.QuantumMechanics.Operators.Uncertainty
import Physlib.QuantumMechanics.Operators.Commutation

open MeasureTheory QuantumMechanics HarmonicOscillator SpaceDHilbertSpace SchwartzSubmodule
open InnerProductSpace Complex Constants LinearPMap SchwartzMap
open PropertyKindCalculus
open ForPhysLib.QuantumMechanics.HarmonicOscillator
open ForPhysLib.QuantumMechanics.HarmonicOscillator.Kinds
open ForPhysLib.QuantumMechanics.HarmonicOscillator.Orthonormality

namespace ForPhysLib.QuantumMechanics.HarmonicOscillator.Heisenberg

open scoped PropertyKindCalculus.OperatorTable

local notation "PhysHO" => _root_.QuantumMechanics.HarmonicOscillator

noncomputable section

variable {d : ℕ} (i : Fin d)

/-! ## The bound, for any normalized Schwartz state — upstream-facing analysis -/

-- Schwartz classes sit in the position operator's domain.
lemma schwartz_mem_positionOperator_domain (g : 𝓢(Space d, ℂ)) :
    ((schwartzEquiv volume g : SchwartzSubmodule d) : SpaceDHilbertSpace d)
      ∈ (𝓧 volume i).domain :=
  mulOperator_domain_ge_of_hasTemperateGrowth (by fun_prop) volume
    (schwartzEquiv volume g).2

-- The position operator applied to a Schwartz class is the class of the Schwartz-level
-- position CLM.
lemma positionOperator_apply_schwartz (g : 𝓢(Space d, ℂ)) :
    𝓧 volume i ⟨((schwartzEquiv volume g : SchwartzSubmodule d) : SpaceDHilbertSpace d),
        schwartz_mem_positionOperator_domain i g⟩
      = ((schwartzEquiv volume (𝐱 i g) : SchwartzSubmodule d) : SpaceDHilbertSpace d) := by
  rw [SpaceDHilbertSpace.ext_iff]
  refine Filter.EventuallyEq.trans (mulOperator_apply_ae
    (⟨((schwartzEquiv volume g : SchwartzSubmodule d) : SpaceDHilbertSpace d),
      schwartz_mem_positionOperator_domain i g⟩ : (𝓧 volume i).domain)) ?_
  filter_upwards [schwartzEquiv_coe_ae (μ := volume) g,
    schwartzEquiv_coe_ae (μ := volume) (𝐱 i g)] with x h2 h3
  rw [h3, positionCLM_apply]
  simp [Space.coordCLM_apply, h2, Space.coord_apply]

-- The canonical commutator at one Schwartz map, same index: `[x̂ᵢ, p̂ᵢ] g = (iℏ) g`.
lemma commutator_apply_same (g : 𝓢(Space d, ℂ)) :
    𝐱 i (𝐩 i g) - 𝐩 i (𝐱 i g) = (I * (ℏ : ℝ)) • g := by
  have h := position_commutation_momentum (d := d) i i
  have h2 := congrArg (fun T => T g) h
  simpa [Ring.lie_def, _root_.sub_apply, mul_apply_eq_comp,
    KroneckerDelta.eq_one_of_same] using h2

-- The raw commutator expectation of x̂ᵢ, p̂ᵢ in a normalized Schwartz state is `iℏ`.
lemma rawCommutatorExpectation_xp (g : 𝓢(Space d, ℂ))
    (hnorm : ‖((schwartzEquiv volume g : SchwartzSubmodule d) : SpaceDHilbertSpace d)‖ = 1)
    (hBA : 𝓧 volume i ⟨_, schwartz_mem_positionOperator_domain i g⟩ ∈ (𝓟 i).domain)
    (hAB : 𝓟 i ⟨((schwartzEquiv volume g : SchwartzSubmodule d) : SpaceDHilbertSpace d),
        (schwartzEquiv volume g).2⟩ ∈ (𝓧 volume i).domain) :
    rawCommutatorExpectation (𝓧 volume i) (𝓟 i)
      ⟨_, schwartz_mem_positionOperator_domain i g⟩ (schwartzEquiv volume g).2 hBA hAB
      = Complex.I * (ℏ : ℝ) := by
  set ψ := ((schwartzEquiv volume g : SchwartzSubmodule d) : SpaceDHilbertSpace d) with hψ
  have hBapp : 𝓟 i ⟨ψ, (schwartzEquiv volume g).2⟩
      = ((schwartzEquiv volume (𝐩 i g) : SchwartzSubmodule d) : SpaceDHilbertSpace d) := by
    have h := momentumOperator_apply i (schwartzEquiv volume g)
    simp only [LinearEquiv.symm_apply_apply] at h
    exact h
  have hXapp : 𝓧 volume i ⟨ψ, schwartz_mem_positionOperator_domain i g⟩
      = ((schwartzEquiv volume (𝐱 i g) : SchwartzSubmodule d) : SpaceDHilbertSpace d) :=
    positionOperator_apply_schwartz i g
  have hAB' : (⟨𝓟 i ⟨ψ, (schwartzEquiv volume g).2⟩, hAB⟩ : (𝓧 volume i).domain)
      = ⟨((schwartzEquiv volume (𝐩 i g) : SchwartzSubmodule d) : SpaceDHilbertSpace d),
          schwartz_mem_positionOperator_domain i (𝐩 i g)⟩ := Subtype.ext hBapp
  have hBA' : (⟨𝓧 volume i ⟨ψ, schwartz_mem_positionOperator_domain i g⟩, hBA⟩ :
        (𝓟 i).domain)
      = schwartzEquiv volume (𝐱 i g) := Subtype.ext hXapp
  have hXPapp : 𝓧 volume i ⟨𝓟 i ⟨ψ, (schwartzEquiv volume g).2⟩, hAB⟩
      = ((schwartzEquiv volume (𝐱 i (𝐩 i g)) : SchwartzSubmodule d) :
          SpaceDHilbertSpace d) := by
    rw [hAB']; exact positionOperator_apply_schwartz i (𝐩 i g)
  have hPXapp : 𝓟 i ⟨𝓧 volume i ⟨ψ, schwartz_mem_positionOperator_domain i g⟩, hBA⟩
      = ((schwartzEquiv volume (𝐩 i (𝐱 i g)) : SchwartzSubmodule d) :
          SpaceDHilbertSpace d) := by
    rw [hBA']
    have h := momentumOperator_apply i (schwartzEquiv volume (𝐱 i g))
    simpa using h
  have hdiff : 𝓧 volume i ⟨𝓟 i ⟨ψ, (schwartzEquiv volume g).2⟩, hAB⟩
        - 𝓟 i ⟨𝓧 volume i ⟨ψ, schwartz_mem_positionOperator_domain i g⟩, hBA⟩
      = (Complex.I * (ℏ : ℝ)) • ψ := by
    rw [hXPapp, hPXapp, hψ]
    have hsub : 𝐱 i (𝐩 i g) - 𝐩 i (𝐱 i g) = (Complex.I * (ℏ : ℝ)) • g :=
      commutator_apply_same i g
    calc ((schwartzEquiv volume (𝐱 i (𝐩 i g)) : SchwartzSubmodule d) :
            SpaceDHilbertSpace d)
          - ((schwartzEquiv volume (𝐩 i (𝐱 i g)) : SchwartzSubmodule d) :
            SpaceDHilbertSpace d)
        = ((schwartzEquiv volume (𝐱 i (𝐩 i g) - 𝐩 i (𝐱 i g)) : SchwartzSubmodule d) :
            SpaceDHilbertSpace d) := by
          rw [_root_.map_sub]; norm_cast
      _ = ((schwartzEquiv volume ((Complex.I * (ℏ : ℝ)) • g) : SchwartzSubmodule d) :
            SpaceDHilbertSpace d) := by rw [hsub]
      _ = (Complex.I * (ℏ : ℝ)) • ((schwartzEquiv volume g : SchwartzSubmodule d) :
            SpaceDHilbertSpace d) := by
          rw [_root_.map_smul]; norm_cast
  show ⟪ψ, _ - _⟫_ℂ = Complex.I * (ℏ : ℝ)
  rw [hdiff, inner_smul_right, inner_self_eq_norm_sq_to_K, hnorm]
  simp

-- The two second-order domain witnesses, discharged once.
lemma xg_mem_momentum_domain (g : 𝓢(Space d, ℂ)) :
    𝓧 volume i ⟨_, schwartz_mem_positionOperator_domain i g⟩ ∈ (𝓟 i).domain := by
  rw [positionOperator_apply_schwartz i g]
  exact (schwartzEquiv volume (𝐱 i g)).2

lemma pg_mem_position_domain (g : 𝓢(Space d, ℂ)) :
    𝓟 i ⟨((schwartzEquiv volume g : SchwartzSubmodule d) : SpaceDHilbertSpace d),
        (schwartzEquiv volume g).2⟩ ∈ (𝓧 volume i).domain := by
  have h : 𝓟 i ⟨((schwartzEquiv volume g : SchwartzSubmodule d) : SpaceDHilbertSpace d),
        (schwartzEquiv volume g).2⟩
      = ((schwartzEquiv volume (𝐩 i g) : SchwartzSubmodule d) : SpaceDHilbertSpace d) := by
    have h := momentumOperator_apply i (schwartzEquiv volume g)
    simp only [LinearEquiv.symm_apply_apply] at h
    exact h
  rw [h]
  exact schwartz_mem_positionOperator_domain i (𝐩 i g)

-- Heisenberg for position and momentum, any normalized Schwartz state.
theorem heisenberg_uncertainty (g : 𝓢(Space d, ℂ))
    (hnorm : ‖((schwartzEquiv volume g : SchwartzSubmodule d) : SpaceDHilbertSpace d)‖ = 1) :
    (ℏ : ℝ) / 2 ≤
      standardDeviation (𝓧 volume i) ⟨_, schwartz_mem_positionOperator_domain i g⟩
        * standardDeviation (𝓟 i)
            ⟨((schwartzEquiv volume g : SchwartzSubmodule d) : SpaceDHilbertSpace d),
              (schwartzEquiv volume g).2⟩ := by
  have h := state_uncertainty_of_raw_commutator (𝓧 volume i) (𝓟 i)
    (LinearPMap.IsSelfAdjoint.isSymmetric (positionOperator_isSelfAdjoint volume i))
    (momentumOperator_isSymmetric i)
    ⟨_, schwartz_mem_positionOperator_domain i g⟩ (schwartzEquiv volume g).2
    hnorm (xg_mem_momentum_domain i g) (pg_mem_position_domain i g)
    (c := (ℏ : ℝ)) (rawCommutatorExpectation_xp i g hnorm _ _)
  simpa [abs_of_pos ℏ_pos] using h

/-! ## The ground state's coordinate moments — the Gaussian second moment -/

variable (Q : PhysHO d)

/-- The ground state's 1D density factor along coordinate `j`. -/
def groundDensity (j : Fin d) (t : ℝ) : ℝ :=
  Q.eigenCoeff 0 j ^ 2 * Real.exp (-(t / Q.ξ j) ^ 2)

/-- The ground-state Born density factorizes into the coordinate factors. -/
lemma conj_mul_groundState (x : Space d) :
    (starRingEnd ℂ) (Q.eigenfunction 0 x) * Q.eigenfunction 0 x
      = ↑(∏ j, groundDensity Q j (x j)) := by
  rw [eigenfunction_apply, map_prod, ← Finset.prod_mul_distrib]
  push_cast
  refine Finset.prod_congr rfl fun j _ => ?_
  have hw : (-2⁻¹ * ((x j : ℂ) / ((Q.ξ j : ℝ) : ℂ)) ^ 2)
      = ((-2⁻¹ * (x j / Q.ξ j) ^ 2 : ℝ) : ℂ) := by push_cast; ring
  simp only [Pi.zero_apply]
  rw [hw, ← Complex.ofReal_exp]
  simp only [← Complex.ofReal_mul, conj_ofReal]
  norm_cast
  rw [Polynomial.physHermite_zero_coe]
  have harg : (-2⁻¹ * (x j / Q.ξ j) ^ 2) + (-2⁻¹ * (x j / Q.ξ j) ^ 2)
      = -(x j / Q.ξ j) ^ 2 := by ring
  calc Q.eigenCoeff 0 j * 1 * Real.exp (-2⁻¹ * (x j / Q.ξ j) ^ 2) *
        (Q.eigenCoeff 0 j * 1 * Real.exp (-2⁻¹ * (x j / Q.ξ j) ^ 2))
      = Q.eigenCoeff 0 j ^ 2 * (Real.exp (-2⁻¹ * (x j / Q.ξ j) ^ 2) *
          Real.exp (-2⁻¹ * (x j / Q.ξ j) ^ 2)) := by ring
    _ = groundDensity Q j (x j) := by
        rw [← Real.exp_add, harg, groundDensity]

/-- The evaluated `H₁`: the physicists' Hermite polynomial `2X`, as a function. -/
lemma physHermite_one_apply (t : ℝ) : (Polynomial.physHermite 1 : ℝ → ℝ) t = 2 * t := by
  rw [Polynomial.physHermite_succ_coe']
  rw [Polynomial.physHermite_zero_coe]
  simp

/-- The ground coefficient, squared: the Gaussian normalization `1/(√π ξ)`. -/
lemma eigenCoeff_zero_sq (j : Fin d) :
    Q.eigenCoeff 0 j ^ 2 = 1 / (√Real.pi * Q.ξ j) := by
  rw [HarmonicOscillator.eigenCoeff_eq]
  simp only [Pi.zero_apply, pow_zero, Nat.factorial_zero, Nat.cast_one, one_mul]
  rw [div_pow, one_pow, Real.sq_sqrt (mul_nonneg (Real.sqrt_nonneg _) (Q.ξ_nonneg j))]

/-- The zeroth moment: each factor is normalized. -/
lemma integral_groundDensity (j : Fin d) : ∫ t : ℝ, groundDensity Q j t = 1 := by
  have hξ := Q.ξ_pos j
  have h : ∀ t : ℝ, groundDensity Q j t
      = Q.eigenCoeff 0 j ^ 2 *
        ((Polynomial.physHermite 0 (t / Q.ξ j) * Polynomial.physHermite 0 (t / Q.ξ j)) *
          Real.exp (-(t / Q.ξ j) ^ 2)) := by
    intro t
    rw [Polynomial.physHermite_zero_coe, groundDensity]
    ring
  simp_rw [h]
  rw [MeasureTheory.integral_const_mul, integral_hermite_pair hξ 0 0, if_pos rfl,
    eigenCoeff_zero_sq]
  have hπ : √Real.pi ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr Real.pi_pos)
  field_simp
  norm_num

/-- The first moment vanishes — `t·e^{-t²}` is the `(1,0)` Hermite pair, orthogonal. -/
lemma integral_id_mul_groundDensity (j : Fin d) :
    ∫ t : ℝ, t * groundDensity Q j t = 0 := by
  have hξ := Q.ξ_pos j
  have h : ∀ t : ℝ, t * groundDensity Q j t
      = (Q.eigenCoeff 0 j ^ 2 * (Q.ξ j / 2)) *
        ((Polynomial.physHermite 1 (t / Q.ξ j) * Polynomial.physHermite 0 (t / Q.ξ j)) *
          Real.exp (-(t / Q.ξ j) ^ 2)) := by
    intro t
    rw [Polynomial.physHermite_zero_coe, physHermite_one_apply, groundDensity]
    field_simp
  simp_rw [h]
  rw [MeasureTheory.integral_const_mul, integral_hermite_pair hξ 1 0,
    if_neg one_ne_zero]
  exact mul_zero _

/-- The second moment is `ξ²/2` — `t²·e^{-t²}` is the `(1,1)` Hermite pair, normed. -/
lemma integral_sq_mul_groundDensity (j : Fin d) :
    ∫ t : ℝ, t ^ 2 * groundDensity Q j t = Q.ξ j ^ 2 / 2 := by
  have hξ := Q.ξ_pos j
  have h : ∀ t : ℝ, t ^ 2 * groundDensity Q j t
      = (Q.eigenCoeff 0 j ^ 2 * (Q.ξ j ^ 2 / 4)) *
        ((Polynomial.physHermite 1 (t / Q.ξ j) * Polynomial.physHermite 1 (t / Q.ξ j)) *
          Real.exp (-(t / Q.ξ j) ^ 2)) := by
    intro t
    rw [physHermite_one_apply, groundDensity]
    field_simp
    ring
  simp_rw [h]
  rw [MeasureTheory.integral_const_mul, integral_hermite_pair hξ 1 1, if_pos rfl,
    eigenCoeff_zero_sq]
  have hπ : √Real.pi ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr Real.pi_pos)
  have hξ' : Q.ξ j ≠ 0 := ne_of_gt hξ
  field_simp
  ring

/-- The `d`-dimensional coordinate moment, split by Fubini: the `i`-th factor carries
the power, every other factor integrates to one. -/
lemma integral_coord_pow_ground (k : ℕ) :
    ∫ x : Space d, (x i : ℂ) ^ k * ↑(∏ j, groundDensity Q j (x j))
      = ↑(∫ t : ℝ, t ^ k * groundDensity Q i t) := by
  set F : Fin d → ℝ → ℂ := fun j t =>
    if j = i then ((t : ℂ) ^ k * ↑(groundDensity Q j t)) else ↑(groundDensity Q j t)
    with hF
  have hFi : ∀ t : ℝ, F i t = (t : ℂ) ^ k * ↑(groundDensity Q i t) := by
    intro t; rw [hF]; simp
  have hFj : ∀ j, j ≠ i → ∀ t : ℝ, F j t = ↑(groundDensity Q j t) := by
    intro j hj t; rw [hF]; simp [hj]
  have hsplit : ∀ x : Space d, (x i : ℂ) ^ k * ↑(∏ j, groundDensity Q j (x j))
      = ∏ j, F j (x j) := by
    intro x
    rw [← Finset.mul_prod_erase Finset.univ (fun j => F j (x j)) (Finset.mem_univ i)]
    push_cast
    rw [← Finset.mul_prod_erase Finset.univ
      (fun j => ((groundDensity Q j (x j) : ℝ) : ℂ)) (Finset.mem_univ i)]
    rw [hFi, Finset.prod_congr rfl fun j hj =>
      hFj j (Finset.ne_of_mem_erase hj) (x j)]
    ring
  simp_rw [hsplit]
  rw [integral_prod_coord F]
  rw [← Finset.mul_prod_erase Finset.univ (fun j => ∫ t : ℝ, F j t) (Finset.mem_univ i)]
  have hi : (∫ t : ℝ, F i t) = ↑(∫ t : ℝ, t ^ k * groundDensity Q i t) := by
    simp_rw [hFi]
    rw [show (fun t : ℝ => (t : ℂ) ^ k * ↑(groundDensity Q i t))
        = fun t : ℝ => ((t ^ k * groundDensity Q i t : ℝ) : ℂ) by
      funext t; push_cast; ring]
    exact integral_complex_ofReal
  have hrest : ∀ j ∈ Finset.univ.erase i, (∫ t : ℝ, F j t) = 1 := by
    intro j hj
    simp_rw [hFj j (Finset.ne_of_mem_erase hj)]
    rw [integral_complex_ofReal, integral_groundDensity]
    norm_num
  rw [hi, Finset.prod_congr rfl hrest]
  simp

/-- The ground state is normalized — the diagonal of the discharged orthonormality. -/
lemma groundState_norm :
    ‖((Q.eigenstate 0 : SchwartzSubmodule d) : SpaceDHilbertSpace d)‖ = 1 := by
  have h := eigenstates_orthonormal' Q 0 0
  simp only [KroneckerDelta.eq_one_of_same, Nat.cast_one] at h
  have h3 : ‖((Q.eigenstate 0 : SchwartzSubmodule d) : SpaceDHilbertSpace d)‖ ^ 2 = 1 := by
    rw [← inner_self_eq_norm_sq (𝕜 := ℂ), h]
    simp
  rw [← Real.sqrt_sq (norm_nonneg _), h3, Real.sqrt_one]

/-- The ground state sits in the position operator's domain. -/
lemma groundState_mem_position_domain :
    ((Q.eigenstate 0 : SchwartzSubmodule d) : SpaceDHilbertSpace d)
      ∈ (𝓧 volume i).domain :=
  schwartz_mem_positionOperator_domain i (Q.eigenfunction 0)

/-- The position expectation in the ground state vanishes — the first Gaussian moment. -/
lemma inner_groundState_position :
    ⟪((Q.eigenstate 0 : SchwartzSubmodule d) : SpaceDHilbertSpace d),
      𝓧 volume i ⟨_, groundState_mem_position_domain i Q⟩⟫_ℂ = 0 := by
  rw [show (⟨_, groundState_mem_position_domain i Q⟩ : (𝓧 volume i).domain)
      = ⟨((schwartzEquiv volume (Q.eigenfunction 0) : SchwartzSubmodule d) :
          SpaceDHilbertSpace d), schwartz_mem_positionOperator_domain i (Q.eigenfunction 0)⟩
    from rfl, positionOperator_apply_schwartz i (Q.eigenfunction 0)]
  rw [show ((Q.eigenstate 0 : SchwartzSubmodule d) : SpaceDHilbertSpace d)
      = ((schwartzEquiv volume (Q.eigenfunction 0) : SchwartzSubmodule d) :
          SpaceDHilbertSpace d) from rfl]
  rw [← Submodule.coe_inner, schwartzEquiv_inner]
  have h : ∀ x : Space d,
      (starRingEnd ℂ) (Q.eigenfunction 0 x) * 𝐱 i (Q.eigenfunction 0) x
        = (x i : ℂ) ^ 1 * ↑(∏ j, groundDensity Q j (x j)) := by
    intro x
    rw [positionCLM_apply, ← conj_mul_groundState]
    ring
  simp_rw [h]
  rw [integral_coord_pow_ground i Q 1]
  simp_rw [pow_one, integral_id_mul_groundDensity]
  norm_num

/-- The position second moment in the ground state — the Gaussian second moment `ξ²/2`. -/
lemma inner_position_position :
    ⟪𝓧 volume i ⟨_, groundState_mem_position_domain i Q⟩,
      𝓧 volume i ⟨_, groundState_mem_position_domain i Q⟩⟫_ℂ = (Q.ξ i ^ 2 / 2 : ℝ) := by
  rw [show (⟨_, groundState_mem_position_domain i Q⟩ : (𝓧 volume i).domain)
      = ⟨((schwartzEquiv volume (Q.eigenfunction 0) : SchwartzSubmodule d) :
          SpaceDHilbertSpace d), schwartz_mem_positionOperator_domain i (Q.eigenfunction 0)⟩
    from rfl, positionOperator_apply_schwartz i (Q.eigenfunction 0)]
  rw [← Submodule.coe_inner, schwartzEquiv_inner]
  have h : ∀ x : Space d,
      (starRingEnd ℂ) (𝐱 i (Q.eigenfunction 0) x) * 𝐱 i (Q.eigenfunction 0) x
        = (x i : ℂ) ^ 2 * ↑(∏ j, groundDensity Q j (x j)) := by
    intro x
    rw [positionCLM_apply, map_mul, ← conj_mul_groundState, conj_ofReal]
    ring
  simp_rw [h]
  rw [integral_coord_pow_ground i Q 2]
  simp_rw [integral_sq_mul_groundDensity]

/-! ## The momentum moment — the Gaussian's eigen-relation carries the position
moments through `𝐩` -/

/-- The ground state as a single Gaussian: the Hermite factors are `H₀ = 1` and the
per-coordinate exponentials combine. -/
lemma groundState_apply (y : Space d) :
    Q.eigenfunction 0 y = (↑(∏ k, Q.eigenCoeff 0 k) : ℂ) *
      Complex.exp (((∑ k, -2⁻¹ * (Q.ξ k)⁻¹ ^ 2 * (y k) ^ 2 : ℝ)) : ℂ) := by
  rw [eigenfunction_apply]
  have h : ∀ k : Fin d,
      (Q.eigenCoeff 0 k : ℂ) *
          ((Polynomial.physHermite ((0 : Fin d → ℕ) k) : ℝ → ℝ) (y k / Q.ξ k) : ℂ) *
          cexp (-2⁻¹ * ((y k : ℂ) / ((Q.ξ k : ℝ) : ℂ)) ^ 2)
        = ((Q.eigenCoeff 0 k * Real.exp (-2⁻¹ * (Q.ξ k)⁻¹ ^ 2 * (y k) ^ 2) : ℝ) : ℂ) := by
    intro k
    have hw : (-2⁻¹ * ((y k : ℂ) / ((Q.ξ k : ℝ) : ℂ)) ^ 2)
        = ((-2⁻¹ * (Q.ξ k)⁻¹ ^ 2 * (y k) ^ 2 : ℝ) : ℂ) := by
      push_cast
      ring
    rw [hw, ← Complex.ofReal_exp]
    simp only [Pi.zero_apply]
    norm_cast
    rw [Polynomial.physHermite_zero_coe]
    ring
  simp only [h]
  rw [← Complex.ofReal_prod, Finset.prod_mul_distrib, ← Real.exp_sum]
  push_cast
  ring

/-- The coordinate functions have the coordinate CLMs as derivatives. -/
lemma hasFDerivAt_coord (k : Fin d) (x : Space d) :
    HasFDerivAt (fun y : Space d => y k) (Space.coordCLM k) x := by
  have h : ⇑(Space.coordCLM (d := d) k) = fun y : Space d => y k :=
    funext fun y => by rw [Space.coordCLM_apply, Space.coord_apply]
  rw [← h]
  exact (Space.coordCLM k).hasFDerivAt

/-- The directional derivative of the ground state: `∂ᵢ ψ₀ = -(xᵢ/ξᵢ²) ψ₀`. -/
lemma deriv_groundState (x : Space d) :
    Space.deriv i (⇑(Q.eigenfunction 0)) x
      = -((x i : ℂ) / (Q.ξ i : ℂ) ^ 2) * Q.eigenfunction 0 x := by
  have hu := HasFDerivAt.fun_sum (u := Finset.univ)
    (A := fun (k : Fin d) (y : Space d) => -2⁻¹ * (Q.ξ k)⁻¹ ^ 2 * (y k) ^ 2)
    (fun k _ => ((hasFDerivAt_coord k x).pow 2).const_mul (-2⁻¹ * (Q.ξ k)⁻¹ ^ 2))
  have hre := Complex.ofRealCLM.hasFDerivAt.comp x hu
  have hexp := hre.cexp
  have hf := hexp.const_mul (↑(∏ k, Q.eigenCoeff 0 k) : ℂ)
  have hEq : ⇑(Q.eigenfunction 0) =ᶠ[nhds x]
      (fun y => (↑(∏ k, Q.eigenCoeff 0 k) : ℂ) *
        cexp ((⇑Complex.ofRealCLM ∘ fun y : Space d =>
          ∑ k, -2⁻¹ * (Q.ξ k)⁻¹ ^ 2 * (y k) ^ 2) y)) :=
    Filter.Eventually.of_forall fun y => by
      rw [groundState_apply Q y]
      simp
  have hf' := hf.congr_of_eventuallyEq hEq
  rw [Space.deriv_eq, hf'.fderiv, groundState_apply Q x]
  simp only [FunLike.coe_smul, Pi.smul_apply, ContinuousLinearMap.coe_comp,
    Function.comp_apply, FunLike.coe_sum, Finset.sum_apply,
    _root_.smul_apply, Space.coordCLM_apply, Space.coord_apply,
    Space.basis_apply, smul_eq_mul, Complex.ofRealCLM_apply, mul_ite, mul_one, mul_zero,
    Finset.sum_ite_eq, Finset.mem_univ, if_true, nsmul_eq_mul]
  have hξ : ((Q.ξ i : ℝ) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (ne_of_gt (Q.ξ_pos i))
  push_cast
  field_simp

/-- The momentum CLM sends the ground state to `(iℏ/ξᵢ²) ·` the position CLM's image:
the Gaussian's own eigen-relation for the annihilation combination. -/
lemma momentumCLM_groundState :
    𝐩 i (Q.eigenfunction 0)
      = ((Complex.I * (ℏ : ℝ)) / ((Q.ξ i : ℝ) : ℂ) ^ 2) • 𝐱 i (Q.eigenfunction 0) := by
  ext x
  have hξ : ((Q.ξ i : ℝ) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (ne_of_gt (Q.ξ_pos i))
  rw [_root_.smul_apply, momentumCLM_apply, positionCLM_apply, deriv_groundState]
  rw [smul_eq_mul]
  ring

/-- The momentum operator's value on the ground state, as `(iℏ/ξᵢ²) ·` the position
operator's value. -/
lemma momentumOperator_groundState :
    𝓟 i (Q.eigenstate 0)
      = ((Complex.I * (ℏ : ℝ)) / ((Q.ξ i : ℝ) : ℂ) ^ 2) •
          𝓧 volume i ⟨_, groundState_mem_position_domain i Q⟩ := by
  have hBapp : 𝓟 i (Q.eigenstate 0)
      = ((schwartzEquiv volume (𝐩 i (Q.eigenfunction 0)) : SchwartzSubmodule d) :
          SpaceDHilbertSpace d) := by
    have h := momentumOperator_apply i (Q.eigenstate 0)
    rw [eigenstate_eq, LinearEquiv.symm_apply_apply] at h
    rw [eigenstate_eq]
    exact h
  rw [show (⟨_, groundState_mem_position_domain i Q⟩ : (𝓧 volume i).domain)
      = ⟨((schwartzEquiv volume (Q.eigenfunction 0) : SchwartzSubmodule d) :
            SpaceDHilbertSpace d),
          schwartz_mem_positionOperator_domain i (Q.eigenfunction 0)⟩ from rfl,
    hBapp, momentumCLM_groundState, _root_.map_smul,
    positionOperator_apply_schwartz i (Q.eigenfunction 0)]
  norm_cast

/-- The ground state's momentum variance is `ℏ²/(2ξᵢ²)` — the position second moment
carried through the Gaussian's eigen-relation. -/
lemma variance_momentum_groundState :
    variance (𝓟 i) (Q.eigenstate 0) = (ℏ : ℝ) ^ 2 / (2 * Q.ξ i ^ 2) := by
  rw [variance_eq_norm_sq_sub_expectedValue_sq _ (momentumOperator_isSymmetric i) _
    (groundState_norm Q)]
  have hXnorm : ‖𝓧 volume i ⟨_, groundState_mem_position_domain i Q⟩‖ ^ 2
      = Q.ξ i ^ 2 / 2 := by
    rw [← inner_self_eq_norm_sq (𝕜 := ℂ), inner_position_position]
    simp [-Complex.ofReal_pow]
  have hexp0 : expectedValue (𝓟 i) (Q.eigenstate 0) = 0 := by
    rw [expectedValue_eq_re_inner (𝓟 i) (Q.eigenstate 0), momentumOperator_groundState,
      inner_smul_right, inner_groundState_position]
    simp
  have hc : ‖((Complex.I * (ℏ : ℝ)) / ((Q.ξ i : ℝ) : ℂ) ^ 2)‖ = (ℏ : ℝ) / Q.ξ i ^ 2 := by
    simp [Complex.norm_I, Complex.norm_real, Real.norm_eq_abs, norm_pow,
      abs_of_pos ℏ_pos, abs_of_pos (Q.ξ_pos i)]
  rw [momentumOperator_groundState, norm_smul, hexp0, mul_pow, hXnorm, hc]
  have hξ : Q.ξ i ≠ 0 := ne_of_gt (Q.ξ_pos i)
  field_simp
  ring

/-- **`σ_p(ψ₀) = ℏ/(√2 ξᵢ)`** — the momentum moment. -/
theorem sigma_momentum_groundState :
    standardDeviation (𝓟 i) (Q.eigenstate 0) = (ℏ : ℝ) / (√2 * Q.ξ i) := by
  rw [standardDeviation_eq_sqrt_variance (𝓟 i) (Q.eigenstate 0),
    variance_momentum_groundState]
  have h : (ℏ : ℝ) ^ 2 / (2 * Q.ξ i ^ 2) = ((ℏ : ℝ) / (√2 * Q.ξ i)) ^ 2 := by
    rw [div_pow, mul_pow, Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 2)]
  rw [h, Real.sqrt_sq (div_nonneg ℏ_pos.le
    (mul_nonneg (Real.sqrt_nonneg 2) (Q.ξ_pos i).le))]

/-! ## The kinded layer — position as observable and measurand, and the bound -/

/-- The position operator read at its kind — self-adjointness is *proved* upstream
(`positionOperator_isSelfAdjoint`), unlike the Hamiltonian's, so the observable below
needs no hypothesis. -/
@[kindIngest]
def positionOpQ : Quantity length (SpaceDHilbertSpace d →ₗ.[ℂ] SpaceDHilbertSpace d) :=
  .attest "reading of PhysLib's positionOperator" (𝓧 volume i)

/-- Position as a PKC observable at `𝕜 = ℂ`. -/
def positionObservable : Observable ℂ length (SpaceDHilbertSpace d) where
  op := positionOpQ i
  selfAdjoint := positionOperator_isSelfAdjoint volume i

/-- The position measurand on the Stage-1 `length · length` edge; every real is an
indication — the continuous spectrum. -/
def positionMeasurand :
    Measurand length xiSqRadicand
      (𝓧 (volume : MeasureTheory.Measure (Space d)) i).domain ℝ :=
  (positionObservable i).toMeasurand Metrology.length_mul_length (fun _ => True)

/-- **The ground state's position variance is `ξᵢ²/2`** — the Gaussian second moment,
read through the measurand. -/
theorem position_variance_groundState :
    ((positionMeasurand i).variance
        ⟨_, groundState_mem_position_domain i Q⟩).magnitude
      = Q.ξ i ^ 2 / 2 := by
  show ‖𝓧 volume i ⟨_, groundState_mem_position_domain i Q⟩‖ ^ 2
      - (RCLike.re (inner ℂ
          ((Q.eigenstate 0 : SchwartzSubmodule d) : SpaceDHilbertSpace d)
          (𝓧 volume i ⟨_, groundState_mem_position_domain i Q⟩))) ^ 2
      = Q.ξ i ^ 2 / 2
  have h1 : ‖𝓧 volume i ⟨_, groundState_mem_position_domain i Q⟩‖ ^ 2
      = Q.ξ i ^ 2 / 2 := by
    rw [← inner_self_eq_norm_sq (𝕜 := ℂ), inner_position_position]
    simp [-Complex.ofReal_pow]
  rw [h1, inner_groundState_position i Q]
  simp

/-- **`σ_x(ψ₀) = ξᵢ/√2`** — the characteristic-length species in its metrological
role: the ground state's position uncertainty, kinded at length. -/
theorem sigma_position_groundState :
    ((positionMeasurand i).sigma
        ⟨_, groundState_mem_position_domain i Q⟩).magnitude
      = Q.ξ i / √2 := by
  show √(((positionMeasurand i).variance
      ⟨_, groundState_mem_position_domain i Q⟩).magnitude) = _
  rw [position_variance_groundState, Real.sqrt_div (sq_nonneg _),
    Real.sqrt_sq (Q.ξ_nonneg i)]

/-- PKC's measurand σ *is* upstream's `standardDeviation`, on normalized states — the
parity that lets the kinded bound consume the analysis theorem. -/
theorem sigma_position_eq_standardDeviation
    (ψ : (𝓧 (volume : MeasureTheory.Measure (Space d)) i).domain)
    (hnorm : ‖(ψ : SpaceDHilbertSpace d)‖ = 1) :
    ((positionMeasurand i).sigma ψ).magnitude = standardDeviation (𝓧 volume i) ψ := by
  show √(‖𝓧 volume i ψ‖ ^ 2
      - (RCLike.re (inner ℂ (ψ : SpaceDHilbertSpace d) (𝓧 volume i ψ))) ^ 2)
      = standardDeviation (𝓧 volume i) ψ
  rw [standardDeviation_eq_sqrt_variance,
    variance_eq_norm_sq_sub_expectedValue_sq _
      (LinearPMap.IsSelfAdjoint.isSymmetric (positionOperator_isSelfAdjoint volume i))
      ψ hnorm]
  rfl

/-- The momentum uncertainty read at its kind. Momentum's *essential*
self-adjointness is upstream's open analysis, so no `Observable` is minted for it;
the standard deviation needs only the symmetric operator. -/
@[kindIngest]
def momentumSigmaQ (ψ : (𝓟 i).domain) : Quantity momentum ℝ :=
  .attest "standard deviation of PhysLib's momentumOperator"
    (standardDeviation (𝓟 i) ψ)

/-- **Heisenberg, kinded**: the uncertainty product lands at action through Stage 3's
`length · momentum` entry, so the comparison against `(1/2) • ℏ` is same-kind — for
every normalized Schwartz state. -/
theorem heisenberg_kinded (g : 𝓢(Space d, ℂ))
    (hnorm : ‖((schwartzEquiv volume g : SchwartzSubmodule d) :
        SpaceDHilbertSpace d)‖ = 1) :
    ((1 : ℝ) / 2) • hbarQ ≤
      (positionMeasurand i).sigma ⟨_, schwartz_mem_positionOperator_domain i g⟩
        * momentumSigmaQ i (schwartzEquiv volume g) := by
  rw [Quantity.le_iff]
  show (1 : ℝ) / 2 * (ℏ : ℝ) ≤
    ((positionMeasurand i).sigma ⟨_, schwartz_mem_positionOperator_domain i g⟩).magnitude
      * standardDeviation (𝓟 i) (schwartzEquiv volume g)
  rw [sigma_position_eq_standardDeviation i
    ⟨((schwartzEquiv volume g : SchwartzSubmodule d) : SpaceDHilbertSpace d),
      schwartz_mem_positionOperator_domain i g⟩ hnorm]
  have h := heisenberg_uncertainty i g hnorm
  have hσ : standardDeviation (𝓟 i)
      (⟨((schwartzEquiv volume g : SchwartzSubmodule d) : SpaceDHilbertSpace d),
        (schwartzEquiv volume g).2⟩ : (𝓟 i).domain)
      = standardDeviation (𝓟 i) (schwartzEquiv volume g) := rfl
  rw [hσ] at h
  linarith

/-- **Saturation at the ground state.** `σ_x(ψ₀) = ξᵢ/√2` and `σ_p(ψ₀) = ℏ/(√2 ξᵢ)`
multiply to exactly `ℏ/2`: the ground state meets the kinded bound with equality. -/
theorem heisenberg_saturation_groundState :
    ((positionMeasurand i).sigma ⟨_, groundState_mem_position_domain i Q⟩
        * momentumSigmaQ i (Q.eigenstate 0)).magnitude = (ℏ : ℝ) / 2 := by
  show ((positionMeasurand i).sigma ⟨_, groundState_mem_position_domain i Q⟩).magnitude
      * standardDeviation (𝓟 i) (Q.eigenstate 0) = _
  rw [sigma_position_groundState, sigma_momentum_groundState]
  have hξ : Q.ξ i ≠ 0 := Q.ξ_ne_zero i
  have h2 : √2 ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr (by norm_num))
  field_simp
  exact (Real.sq_sqrt (by norm_num)).symm

end

end ForPhysLib.QuantumMechanics.HarmonicOscillator.Heisenberg
