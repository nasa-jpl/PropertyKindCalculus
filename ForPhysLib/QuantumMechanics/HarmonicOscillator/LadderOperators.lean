/-
# The ladder — upstream's green-field stub, co-authored at the Schwartz layer

`Physlib/QuantumMechanics/HarmonicOscillator/LadderOperators.lean` is a stub of eleven
TODOs. This file delivers their content at the layer where the oscillator's analysis
already lives — continuous linear maps on Schwartz space, the home of `𝐱`, `𝐩` and the
CCR — so that every commutation relation is CLM algebra and no domain bookkeeping
intrudes:

* **A. Ladder operators**: `aᵢ = (x̂ᵢ/ξᵢ + i·ξᵢp̂ᵢ/ℏ)/√2` and its conjugate; the
  formal-adjoint pairing `⟪aᵢψ, φ⟫ = ⟪ψ, a†ᵢφ⟫` on Schwartz classes; the CCR
  `[aᵢ, a†ⱼ] = δᵢⱼ𝟙` with `[aᵢ, aⱼ] = [a†ᵢ, a†ⱼ] = 0`.
* **B. Number operators**: `Nᵢ = a†ᵢaᵢ`, symmetric on Schwartz classes;
  `[Nᵢ, Nⱼ] = 0`, `[Nᵢ, aⱼ] = -δᵢⱼaⱼ`, `[Nᵢ, a†ⱼ] = δᵢⱼa†ⱼ`.
* **C. Hamiltonian**: `H_N = ∑ᵢ ℏωᵢ(Nᵢ + ½)` *is* `(2m)⁻¹p̂² + (mωᵢ²/2)x̂ᵢ²` at this
  layer (`numberHamiltonianCLM_eq` — the scalar content is exactly `ξ² = ℏ/(mω)`),
  with `[H_N, aⱼ] = -ℏωⱼaⱼ` and `[H_N, a†ⱼ] = ℏωⱼa†ⱼ`.
* **The ladder ladders**: `aᵢψ₀ = 0`, `a†ᵢψ₀ = ψ_{eᵢ}`, `aᵢψ_{eᵢ} = ψ₀`, so
  `Nᵢψ₀ = 0` and `Nᵢψ_{eᵢ} = ψ_{eᵢ}` — the first two rungs realized against the
  labeled eigenfunctions, off the Gaussian eigen-relation with no new integrals.

What stays upstream's, by name: *essential self-adjointness* of `N` and `H_N` (this
file proves symmetry — the analysis half is the same deficiency-index work the
Hamiltonian's own TODO names), and the LinearPMap-level "same quantum system" relation,
which is a statement about domains this layer deliberately avoids.

Kinded coda: the number operator is the *occupation observable* — it reads at the
quantum-number kind (ISO 80000-10 item 10-13.1), and its first two eigenvalues are
`Kinded.occupationQ`'s magnitudes, label by label.
-/

module

public import ForPhysLib.QuantumMechanics.HarmonicOscillator.AngularMomentum
meta import ForPhysLib.QuantumMechanics.HarmonicOscillator.AngularMomentum

public section -- pkc-blanket
@[expose] section -- pkc-blanket-expose

open MeasureTheory QuantumMechanics HarmonicOscillator SpaceDHilbertSpace SchwartzSubmodule
open InnerProductSpace Complex Constants LinearPMap SchwartzMap
open PropertyKindCalculus
open ForPhysLib.QuantumMechanics.HarmonicOscillator
open ForPhysLib.QuantumMechanics.HarmonicOscillator.Heisenberg
open ForPhysLib.QuantumMechanics.HarmonicOscillator.AngularMomentum

namespace ForPhysLib.QuantumMechanics.HarmonicOscillator.Ladder

local notation "PhysHO" => _root_.QuantumMechanics.HarmonicOscillator

noncomputable section

variable {d : ℕ} (Q : PhysHO d) (i j : Fin d)

/-- The lowering (annihilation) operator of mode `i`:
`aᵢ = (1/√2)·(x̂ᵢ/ξᵢ + i·ξᵢ·p̂ᵢ/ℏ)`. -/
def lowerCLM : 𝓢(Space d, ℂ) →L[ℂ] 𝓢(Space d, ℂ) :=
  ((((√2 * Q.ξ i)⁻¹ : ℝ)) : ℂ) • 𝐱 i
    + (I * (((Q.ξ i / (√2 * (ℏ : ℝ)) : ℝ)) : ℂ)) • 𝐩 i

/-- The raising (creation) operator of mode `i`:
`a†ᵢ = (1/√2)·(x̂ᵢ/ξᵢ - i·ξᵢ·p̂ᵢ/ℏ)`. -/
def raiseCLM : 𝓢(Space d, ℂ) →L[ℂ] 𝓢(Space d, ℂ) :=
  ((((√2 * Q.ξ i)⁻¹ : ℝ)) : ℂ) • 𝐱 i
    - (I * (((Q.ξ i / (√2 * (ℏ : ℝ)) : ℝ)) : ℂ)) • 𝐩 i

/-- Bilinearity of the ring commutator, in the shape the ladder expansion needs. -/
lemma lie_expand (a b c e : 𝓢(Space d, ℂ) →L[ℂ] 𝓢(Space d, ℂ)) :
    ⁅a + b, c - e⁆ = ⁅a, c⁆ - ⁅a, e⁆ + ⁅b, c⁆ - ⁅b, e⁆ := by
  simp only [Ring.lie_def]
  noncomm_ring

lemma smul_lie_smul (c₁ c₂ : ℂ) (A B : 𝓢(Space d, ℂ) →L[ℂ] 𝓢(Space d, ℂ)) :
    ⁅c₁ • A, c₂ • B⁆ = (c₁ * c₂) • ⁅A, B⁆ := by
  simp only [Ring.lie_def]
  rw [smul_mul_smul_comm, smul_mul_smul_comm, mul_comm c₂ c₁, smul_sub]

/-- **The ladder CCR**: `[aᵢ, a†ⱼ] = δᵢⱼ 𝟙`. -/
lemma lower_commutation_raise :
    ⁅lowerCLM Q i, raiseCLM Q j⁆
      = δ[i,j] • ContinuousLinearMap.id ℂ 𝓢(Space d, ℂ) := by
  unfold lowerCLM raiseCLM
  rw [lie_expand, smul_lie_smul, smul_lie_smul, smul_lie_smul, smul_lie_smul,
    position_commutation_position, momentum_commutation_momentum,
    position_commutation_momentum]
  rw [show ⁅𝐩 i, 𝐱 j⁆ = -⁅𝐱 j, 𝐩 i⁆ by rw [Ring.lie_def, Ring.lie_def]; abel,
    position_commutation_momentum]
  by_cases h : i = j
  · subst h
    simp only [KroneckerDelta.eq_one_of_same, one_smul, smul_zero, sub_zero,
      smul_neg, smul_smul, zero_sub, neg_add_eq_sub]
    rw [← neg_smul, ← sub_smul]
    have hξ : ((Q.ξ i : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (Q.ξ_ne_zero i)
    have hℏ : (((ℏ : ℝ)) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (ne_of_gt ℏ_pos)
    have h2 : ((√2 : ℝ) : ℂ) ≠ 0 :=
      Complex.ofReal_ne_zero.mpr (ne_of_gt (Real.sqrt_pos.mpr (by norm_num)))
    have h22 : ((√2 : ℝ) : ℂ) * ((√2 : ℝ) : ℂ) = 2 := by
      exact_mod_cast congrArg Complex.ofReal
        (Real.mul_self_sqrt (by norm_num : (0:ℝ) ≤ 2))
    have hs : (-(I * (((Q.ξ i / (√2 * (ℏ : ℝ)) : ℝ)) : ℂ) * ((((√2 * Q.ξ i)⁻¹ : ℝ)) : ℂ)
          * (I * (((ℏ : ℝ)) : ℂ)))
        - ((((√2 * Q.ξ i)⁻¹ : ℝ)) : ℂ) * (I * (((Q.ξ i / (√2 * (ℏ : ℝ)) : ℝ)) : ℂ))
          * (I * (((ℏ : ℝ)) : ℂ))) = 1 := by
      push_cast
      field_simp
      rw [Complex.I_sq, pow_two, h22]
      norm_num
    rw [hs, one_smul]
  · simp [KroneckerDelta.eq_zero_of_ne h, KroneckerDelta.eq_zero_of_ne (Ne.symm h)]

lemma lie_expand_add (a b c e : 𝓢(Space d, ℂ) →L[ℂ] 𝓢(Space d, ℂ)) :
    ⁅a + b, c + e⁆ = ⁅a, c⁆ + ⁅a, e⁆ + ⁅b, c⁆ + ⁅b, e⁆ := by
  simp only [Ring.lie_def]
  noncomm_ring

/-- Lowering operators commute: `[aᵢ, aⱼ] = 0`. -/
lemma lower_commutation_lower : ⁅lowerCLM Q i, lowerCLM Q j⁆ = 0 := by
  unfold lowerCLM
  rw [lie_expand_add, smul_lie_smul, smul_lie_smul, smul_lie_smul, smul_lie_smul,
    position_commutation_position, momentum_commutation_momentum,
    position_commutation_momentum,
    show ⁅𝐩 i, 𝐱 j⁆ = -⁅𝐱 j, 𝐩 i⁆ by rw [Ring.lie_def, Ring.lie_def]; abel,
    position_commutation_momentum]
  by_cases h : i = j
  · subst h
    simp only [KroneckerDelta.eq_one_of_same, one_smul, smul_zero, smul_neg, smul_smul,
      add_zero, zero_add]
    rw [← neg_smul, ← add_smul]
    convert zero_smul ℂ _
    ring
  · simp [KroneckerDelta.eq_zero_of_ne h, KroneckerDelta.eq_zero_of_ne (Ne.symm h)]

/-- Raising operators commute: `[a†ᵢ, a†ⱼ] = 0`. -/
lemma raise_commutation_raise : ⁅raiseCLM Q i, raiseCLM Q j⁆ = 0 := by
  unfold raiseCLM
  rw [show ((((√2 * Q.ξ i)⁻¹ : ℝ)) : ℂ) • 𝐱 i
        - (I * (((Q.ξ i / (√2 * (ℏ : ℝ)) : ℝ)) : ℂ)) • 𝐩 i
      = ((((√2 * Q.ξ i)⁻¹ : ℝ)) : ℂ) • 𝐱 i
        + (-(I * (((Q.ξ i / (√2 * (ℏ : ℝ)) : ℝ)) : ℂ))) • 𝐩 i by
    rw [neg_smul, sub_eq_add_neg],
    show ((((√2 * Q.ξ j)⁻¹ : ℝ)) : ℂ) • 𝐱 j
        - (I * (((Q.ξ j / (√2 * (ℏ : ℝ)) : ℝ)) : ℂ)) • 𝐩 j
      = ((((√2 * Q.ξ j)⁻¹ : ℝ)) : ℂ) • 𝐱 j
        + (-(I * (((Q.ξ j / (√2 * (ℏ : ℝ)) : ℝ)) : ℂ))) • 𝐩 j by
    rw [neg_smul, sub_eq_add_neg]]
  rw [lie_expand_add, smul_lie_smul, smul_lie_smul, smul_lie_smul, smul_lie_smul,
    position_commutation_position, momentum_commutation_momentum,
    position_commutation_momentum,
    show ⁅𝐩 i, 𝐱 j⁆ = -⁅𝐱 j, 𝐩 i⁆ by rw [Ring.lie_def, Ring.lie_def]; abel,
    position_commutation_momentum]
  by_cases h : i = j
  · subst h
    simp only [KroneckerDelta.eq_one_of_same, one_smul, smul_zero, smul_neg, smul_smul,
      add_zero, zero_add]
    rw [← neg_smul, ← add_smul]
    convert zero_smul ℂ _
    ring
  · simp [KroneckerDelta.eq_zero_of_ne h, KroneckerDelta.eq_zero_of_ne (Ne.symm h)]

/-- **The lowering operator annihilates the ground state**: `aᵢ ψ₀ = 0`. -/
lemma lowerCLM_groundState : lowerCLM Q i (Q.eigenfunction 0) = 0 := by
  rw [lowerCLM]
  simp only [_root_.add_apply, _root_.smul_apply, momentumCLM_groundState]
  rw [smul_smul, ← add_smul]
  convert zero_smul ℂ _
  have hξ : ((Q.ξ i : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (Q.ξ_ne_zero i)
  have hℏ : (((ℏ : ℝ)) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (ne_of_gt ℏ_pos)
  have h2 : ((√2 : ℝ) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (ne_of_gt (Real.sqrt_pos.mpr (by norm_num)))
  push_cast
  field_simp
  rw [Complex.I_sq]
  ring

/-- **The raising operator climbs the first rung**: `a†ᵢ ψ₀ = ψ_{eᵢ}`. -/
lemma raiseCLM_groundState :
    raiseCLM Q i (Q.eigenfunction 0) = Q.eigenfunction (Pi.single i 1) := by
  rw [raiseCLM, eigenfunction_single]
  simp only [_root_.sub_apply, _root_.smul_apply, momentumCLM_groundState]
  rw [smul_smul, ← sub_smul]
  congr 1
  have hξ : ((Q.ξ i : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (Q.ξ_ne_zero i)
  have hℏ : (((ℏ : ℝ)) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (ne_of_gt ℏ_pos)
  have h2 : ((√2 : ℝ) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (ne_of_gt (Real.sqrt_pos.mpr (by norm_num)))
  have h22 : ((√2 : ℝ) : ℂ) * ((√2 : ℝ) : ℂ) = 2 := by
    exact_mod_cast congrArg Complex.ofReal
      (Real.mul_self_sqrt (by norm_num : (0:ℝ) ≤ 2))
  push_cast
  field_simp
  rw [Complex.I_sq]
  linear_combination -h22

/-- The number operator of mode `i`: `Nᵢ = a†ᵢ ∘ aᵢ`. -/
def numberCLM : 𝓢(Space d, ℂ) →L[ℂ] 𝓢(Space d, ℂ) :=
  raiseCLM Q i ∘L lowerCLM Q i

/-- The number operator annihilates the ground state — occupation `0`. -/
lemma numberCLM_groundState : numberCLM Q i (Q.eigenfunction 0) = 0 := by
  rw [numberCLM, ContinuousLinearMap.comp_apply, lowerCLM_groundState, _root_.map_zero]

/-- The lowering operator descends the first rung: `aᵢ ψ_{eᵢ} = ψ₀`. -/
lemma lowerCLM_single :
    lowerCLM Q i (Q.eigenfunction (Pi.single i 1)) = Q.eigenfunction 0 := by
  rw [← raiseCLM_groundState]
  have h := congrArg (fun T => T (Q.eigenfunction 0)) (lower_commutation_raise Q i i)
  simp only [Ring.lie_def, ContinuousLinearMap.mul_def, ContinuousLinearMap.comp_apply,
    _root_.sub_apply, ContinuousLinearMap.id_apply,
    KroneckerDelta.eq_one_of_same, one_smul, lowerCLM_groundState, _root_.map_zero,
    sub_zero] at h
  exact h

/-- The number operator counts the first rung: `Nᵢ ψ_{eᵢ} = 1 · ψ_{eᵢ}`. -/
lemma numberCLM_single :
    numberCLM Q i (Q.eigenfunction (Pi.single i 1))
      = Q.eigenfunction (Pi.single i 1) := by
  rw [numberCLM, ContinuousLinearMap.comp_apply, lowerCLM_single, raiseCLM_groundState]

/-- The skewed CCR: `[a†ᵢ, aⱼ] = -δᵢⱼ 𝟙`. -/
lemma raise_commutation_lower :
    ⁅raiseCLM Q i, lowerCLM Q j⁆
      = -(δ[j,i] • ContinuousLinearMap.id ℂ 𝓢(Space d, ℂ)) := by
  rw [show ⁅raiseCLM Q i, lowerCLM Q j⁆ = -⁅lowerCLM Q j, raiseCLM Q i⁆ by
    rw [Ring.lie_def, Ring.lie_def]; abel]
  rw [lower_commutation_raise]

/-- Number operators commute: `[Nᵢ, Nⱼ] = 0`. -/
lemma number_commutation_number : ⁅numberCLM Q i, numberCLM Q j⁆ = 0 := by
  by_cases h : i = j
  · subst h
    rw [Ring.lie_def, sub_self]
  · unfold numberCLM
    rw [leibniz_lie, lie_leibniz, lie_leibniz, lower_commutation_raise,
      raise_commutation_raise, raise_commutation_lower, lower_commutation_lower]
    simp [KroneckerDelta.eq_zero_of_ne h, KroneckerDelta.eq_zero_of_ne (Ne.symm h)]

/-- `[Nᵢ, aⱼ] = -δᵢⱼ aⱼ` — the number operator counts what lowering removes. -/
lemma number_commutation_lower :
    ⁅numberCLM Q i, lowerCLM Q j⁆ = -(δ[i,j] • lowerCLM Q j) := by
  rw [numberCLM, leibniz_lie, lower_commutation_lower, raise_commutation_lower]
  by_cases h : i = j
  · subst h
    simp [KroneckerDelta.eq_one_of_same]
  · simp [KroneckerDelta.eq_zero_of_ne h, KroneckerDelta.eq_zero_of_ne (Ne.symm h)]

/-- `[Nᵢ, a†ⱼ] = δᵢⱼ a†ⱼ` — and counts what raising adds. -/
lemma number_commutation_raise :
    ⁅numberCLM Q i, raiseCLM Q j⁆ = δ[i,j] • raiseCLM Q j := by
  rw [numberCLM, leibniz_lie, lower_commutation_raise, raise_commutation_raise]
  by_cases h : i = j
  · subst h
    simp [KroneckerDelta.eq_one_of_same]
  · simp [KroneckerDelta.eq_zero_of_ne h]

/-- `𝓟` applied to a Schwartz class is the class of the momentum CLM's image. -/
lemma momentumOperator_apply_schwartz' (g : 𝓢(Space d, ℂ)) :
    𝓟 i (schwartzEquiv volume g)
      = ((schwartzEquiv volume (𝐩 i g) : SchwartzSubmodule d) : SpaceDHilbertSpace d) := by
  have h := momentumOperator_apply i (schwartzEquiv volume g)
  simpa using h

/-- Position moves across the L² pairing of Schwartz classes. -/
lemma inner_position_move (ψ φ : 𝓢(Space d, ℂ)) :
    ⟪((schwartzEquiv volume (𝐱 i ψ) : SchwartzSubmodule d) : SpaceDHilbertSpace d),
        ((schwartzEquiv volume φ : SchwartzSubmodule d) : SpaceDHilbertSpace d)⟫_ℂ
      = ⟪((schwartzEquiv volume ψ : SchwartzSubmodule d) : SpaceDHilbertSpace d),
        ((schwartzEquiv volume (𝐱 i φ) : SchwartzSubmodule d) : SpaceDHilbertSpace d)⟫_ℂ := by
  have h := (LinearPMap.IsSelfAdjoint.isSymmetric (positionOperator_isSelfAdjoint volume i))
    (⟨_, schwartz_mem_positionOperator_domain i ψ⟩ : (𝓧 volume i).domain)
    (⟨_, schwartz_mem_positionOperator_domain i φ⟩ : (𝓧 volume i).domain)
  rwa [positionOperator_apply_schwartz, positionOperator_apply_schwartz] at h

/-- Momentum moves across the L² pairing of Schwartz classes. -/
lemma inner_momentum_move (ψ φ : 𝓢(Space d, ℂ)) :
    ⟪((schwartzEquiv volume (𝐩 i ψ) : SchwartzSubmodule d) : SpaceDHilbertSpace d),
        ((schwartzEquiv volume φ : SchwartzSubmodule d) : SpaceDHilbertSpace d)⟫_ℂ
      = ⟪((schwartzEquiv volume ψ : SchwartzSubmodule d) : SpaceDHilbertSpace d),
        ((schwartzEquiv volume (𝐩 i φ) : SchwartzSubmodule d) : SpaceDHilbertSpace d)⟫_ℂ := by
  have h := (momentumOperator_isSymmetric i)
    (schwartzEquiv volume ψ) (schwartzEquiv volume φ)
  rwa [momentumOperator_apply_schwartz', momentumOperator_apply_schwartz'] at h

/-- **The ladder operators are formal adjoints of one another** on Schwartz classes:
`⟪aᵢψ, φ⟫ = ⟪ψ, a†ᵢφ⟫`. -/
theorem inner_lower_raise (ψ φ : 𝓢(Space d, ℂ)) :
    ⟪((schwartzEquiv volume (lowerCLM Q i ψ) : SchwartzSubmodule d) :
        SpaceDHilbertSpace d),
      ((schwartzEquiv volume φ : SchwartzSubmodule d) : SpaceDHilbertSpace d)⟫_ℂ
      = ⟪((schwartzEquiv volume ψ : SchwartzSubmodule d) : SpaceDHilbertSpace d),
        ((schwartzEquiv volume (raiseCLM Q i φ) : SchwartzSubmodule d) :
          SpaceDHilbertSpace d)⟫_ℂ := by
  rw [lowerCLM, raiseCLM]
  simp only [_root_.add_apply, _root_.sub_apply, _root_.smul_apply, _root_.map_add,
    _root_.map_sub, _root_.map_smul]
  simp only [Submodule.coe_add, Submodule.coe_smul, AddSubgroupClass.coe_sub]
  simp only [inner_add_left, inner_smul_left, inner_sub_right, inner_smul_right,
    map_mul, Complex.conj_I, Complex.conj_ofReal]
  rw [inner_position_move, inner_momentum_move]
  push_cast
  ring

/-- The reversed pairing: `⟪a†ᵢψ, φ⟫ = ⟪ψ, aᵢφ⟫`. -/
theorem inner_raise_lower (ψ φ : 𝓢(Space d, ℂ)) :
    ⟪((schwartzEquiv volume (raiseCLM Q i ψ) : SchwartzSubmodule d) :
        SpaceDHilbertSpace d),
      ((schwartzEquiv volume φ : SchwartzSubmodule d) : SpaceDHilbertSpace d)⟫_ℂ
      = ⟪((schwartzEquiv volume ψ : SchwartzSubmodule d) : SpaceDHilbertSpace d),
        ((schwartzEquiv volume (lowerCLM Q i φ) : SchwartzSubmodule d) :
          SpaceDHilbertSpace d)⟫_ℂ := by
  rw [← inner_conj_symm, ← inner_lower_raise, inner_conj_symm]

/-- **The number operator is symmetric** on Schwartz classes. -/
theorem inner_number_symm (ψ φ : 𝓢(Space d, ℂ)) :
    ⟪((schwartzEquiv volume (numberCLM Q i ψ) : SchwartzSubmodule d) :
        SpaceDHilbertSpace d),
      ((schwartzEquiv volume φ : SchwartzSubmodule d) : SpaceDHilbertSpace d)⟫_ℂ
      = ⟪((schwartzEquiv volume ψ : SchwartzSubmodule d) : SpaceDHilbertSpace d),
        ((schwartzEquiv volume (numberCLM Q i φ) : SchwartzSubmodule d) :
          SpaceDHilbertSpace d)⟫_ℂ := by
  simp only [numberCLM, ContinuousLinearMap.comp_apply]
  rw [inner_raise_lower, inner_lower_raise]

/-- The number operator, expanded over position and momentum:
`Nᵢ = x̂ᵢ²/(2ξᵢ²) + ξᵢ²p̂ᵢ²/(2ℏ²) - ½`. -/
lemma numberCLM_eq :
    numberCLM Q i
      = ((((2 * Q.ξ i ^ 2)⁻¹ : ℝ)) : ℂ) • (𝐱 i ∘L 𝐱 i)
        + (((Q.ξ i ^ 2 / (2 * (ℏ : ℝ) ^ 2) : ℝ)) : ℂ) • (𝐩 i ∘L 𝐩 i)
        - (2⁻¹ : ℂ) • (1 : 𝓢(Space d, ℂ) →L[ℂ] 𝓢(Space d, ℂ)) := by
  rw [numberCLM]
  unfold raiseCLM lowerCLM
  simp only [ContinuousLinearMap.sub_comp, ContinuousLinearMap.comp_add,
    ContinuousLinearMap.smul_comp, ContinuousLinearMap.comp_smul]
  rw [momentum_comp_position_eq, KroneckerDelta.eq_one_of_same, one_smul]
  have hξ : ((Q.ξ i : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (Q.ξ_ne_zero i)
  have hℏ : (((ℏ : ℝ)) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (ne_of_gt ℏ_pos)
  have h22 : ((√2 : ℝ) : ℂ) * ((√2 : ℝ) : ℂ) = 2 := by
    exact_mod_cast congrArg Complex.ofReal
      (Real.mul_self_sqrt (by norm_num : (0:ℝ) ≤ 2))
  have h2 : ((√2 : ℝ) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (ne_of_gt (Real.sqrt_pos.mpr (by norm_num)))
  simp only [smul_sub, smul_smul]
  push_cast
  rw [show (1 : 𝓢(Space d, ℂ) →L[ℂ] 𝓢(Space d, ℂ))
      = ContinuousLinearMap.id ℂ 𝓢(Space d, ℂ) from rfl]
  match_scalars
  all_goals field_simp
  all_goals simp [pow_two, h22, Complex.I_mul_I]

/-- **Per mode, `ℏωᵢ(Nᵢ + ½)` is kinetic-plus-potential** at the Schwartz layer:
`(2m)⁻¹ p̂ᵢ² + (m ωᵢ²/2) x̂ᵢ²`. -/
theorem mode_hamiltonian_eq :
    ((((ℏ : ℝ) * Q.ω i : ℝ)) : ℂ) • (numberCLM Q i
        + (2⁻¹ : ℂ) • (1 : 𝓢(Space d, ℂ) →L[ℂ] 𝓢(Space d, ℂ)))
      = ((((2 * Q.m)⁻¹ : ℝ)) : ℂ) • (𝐩 i ∘L 𝐩 i)
        + (((Q.m * Q.ω i ^ 2 / 2 : ℝ)) : ℂ) • (𝐱 i ∘L 𝐱 i) := by
  rw [numberCLM_eq, sub_add_cancel, smul_add, smul_smul, smul_smul, add_comm]
  have hm : Q.m ≠ 0 := ne_of_gt Q.hm
  have hω : Q.ω i ≠ 0 := ne_of_gt (Q.hω i)
  have hℏ : (ℏ : ℝ) ≠ 0 := ne_of_gt ℏ_pos
  have hξ2 : (Q.ξ i) ^ 2 = (ℏ : ℝ) / (Q.m * Q.ω i) := Q.ξ_sq i
  have hmC : ((Q.m : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hm
  have hωC : ((Q.ω i : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hω
  have hℏC : (((ℏ : ℝ)) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hℏ
  have hξ2' : ((Q.ξ i : ℝ) : ℂ) ^ 2 = (((ℏ : ℝ)) : ℂ) / (((Q.m : ℝ)) : ℂ) / ((Q.ω i : ℝ) : ℂ) := by
    rw [div_div]
    exact_mod_cast congrArg Complex.ofReal hξ2
  congr 1
  · congr 1
    push_cast
    rw [hξ2']
    field_simp
  · congr 1
    push_cast
    rw [hξ2']
    field_simp

/-- The number-operator Hamiltonian: `∑ᵢ ℏωᵢ(Nᵢ + ½)`. -/
def numberHamiltonianCLM : 𝓢(Space d, ℂ) →L[ℂ] 𝓢(Space d, ℂ) :=
  ∑ i, ((((ℏ : ℝ) * Q.ω i : ℝ)) : ℂ) • (numberCLM Q i
    + (2⁻¹ : ℂ) • (1 : 𝓢(Space d, ℂ) →L[ℂ] 𝓢(Space d, ℂ)))

/-- **The number-operator Hamiltonian is `T + V`** at the Schwartz layer. -/
theorem numberHamiltonianCLM_eq :
    numberHamiltonianCLM Q
      = ((((2 * Q.m)⁻¹ : ℝ)) : ℂ) • (∑ i, 𝐩 i ∘L 𝐩 i)
        + ∑ i, (((Q.m * Q.ω i ^ 2 / 2 : ℝ)) : ℂ) • (𝐱 i ∘L 𝐱 i) := by
  rw [numberHamiltonianCLM]
  simp only [mode_hamiltonian_eq]
  rw [Finset.sum_add_distrib, Finset.smul_sum]

/-- **The ground state is the number-Hamiltonian eigenstate at the ground energy.** -/
theorem numberHamiltonianCLM_groundState :
    numberHamiltonianCLM Q (Q.eigenfunction 0)
      = ((Q.eigenEnergy 0 : ℝ) : ℂ) • Q.eigenfunction 0 := by
  rw [numberHamiltonianCLM]
  simp only [_root_.sum_apply, _root_.smul_apply, _root_.add_apply,
    numberCLM_groundState, zero_add, one_apply_eq_self, smul_smul]
  rw [← Finset.sum_smul]
  congr 1
  rw [eigenEnergy_eq]
  push_cast
  simp

lemma lie_sum_left {s : Finset (Fin d)} (f : Fin d → 𝓢(Space d, ℂ) →L[ℂ] 𝓢(Space d, ℂ))
    (B : 𝓢(Space d, ℂ) →L[ℂ] 𝓢(Space d, ℂ)) :
    ⁅∑ i ∈ s, f i, B⁆ = ∑ i ∈ s, ⁅f i, B⁆ := by
  simp only [Ring.lie_def, Finset.sum_mul, Finset.mul_sum, Finset.sum_sub_distrib]

lemma smul_lie' (c : ℂ) (A B : 𝓢(Space d, ℂ) →L[ℂ] 𝓢(Space d, ℂ)) :
    ⁅c • A, B⁆ = c • ⁅A, B⁆ := by
  simp only [Ring.lie_def, smul_mul_assoc, mul_smul_comm, smul_sub]

lemma add_lie' (A B C : 𝓢(Space d, ℂ) →L[ℂ] 𝓢(Space d, ℂ)) :
    ⁅A + B, C⁆ = ⁅A, C⁆ + ⁅B, C⁆ := by
  simp only [Ring.lie_def]
  noncomm_ring

lemma one_lie' (C : 𝓢(Space d, ℂ) →L[ℂ] 𝓢(Space d, ℂ)) :
    ⁅(1 : 𝓢(Space d, ℂ) →L[ℂ] 𝓢(Space d, ℂ)), C⁆ = 0 := by
  simp only [Ring.lie_def, one_mul, mul_one, sub_self]

/-- `[H_N, aⱼ] = -ℏωⱼ aⱼ` — the Hamiltonian ladders down. -/
theorem numberHamiltonian_commutation_lower :
    ⁅numberHamiltonianCLM Q, lowerCLM Q j⁆
      = -(((((ℏ : ℝ) * Q.ω j : ℝ)) : ℂ) • lowerCLM Q j) := by
  rw [numberHamiltonianCLM, lie_sum_left]
  have h : ∀ i : Fin d,
      ⁅((((ℏ : ℝ) * Q.ω i : ℝ)) : ℂ) • (numberCLM Q i
          + (2⁻¹ : ℂ) • (1 : 𝓢(Space d, ℂ) →L[ℂ] 𝓢(Space d, ℂ))), lowerCLM Q j⁆
        = ((((ℏ : ℝ) * Q.ω i : ℝ)) : ℂ) • (-(δ[i,j] • lowerCLM Q j)) := by
    intro i
    rw [smul_lie', add_lie', smul_lie', one_lie', smul_zero, add_zero,
      number_commutation_lower]
  simp only [h]
  rw [Finset.sum_eq_single j
    (fun k _ hk => by simp [KroneckerDelta.eq_zero_of_ne hk])
    (fun hj => absurd (Finset.mem_univ j) hj)]
  simp [KroneckerDelta.eq_one_of_same]

/-- `[H_N, a†ⱼ] = ℏωⱼ a†ⱼ` — and up. -/
theorem numberHamiltonian_commutation_raise :
    ⁅numberHamiltonianCLM Q, raiseCLM Q j⁆
      = ((((ℏ : ℝ) * Q.ω j : ℝ)) : ℂ) • raiseCLM Q j := by
  rw [numberHamiltonianCLM, lie_sum_left]
  have h : ∀ i : Fin d,
      ⁅((((ℏ : ℝ) * Q.ω i : ℝ)) : ℂ) • (numberCLM Q i
          + (2⁻¹ : ℂ) • (1 : 𝓢(Space d, ℂ) →L[ℂ] 𝓢(Space d, ℂ))), raiseCLM Q j⁆
        = ((((ℏ : ℝ) * Q.ω i : ℝ)) : ℂ) • (δ[i,j] • raiseCLM Q j) := by
    intro i
    rw [smul_lie', add_lie', smul_lie', one_lie', smul_zero, add_zero,
      number_commutation_raise]
  simp only [h]
  rw [Finset.sum_eq_single j
    (fun k _ hk => by simp [KroneckerDelta.eq_zero_of_ne hk])
    (fun hj => absurd (Finset.mem_univ j) hj)]
  simp [KroneckerDelta.eq_one_of_same]

/-! ## Kinded — the occupation observable -/

/-- The number operator read at the quantum-number kind (ISO 80000-10 item 10-13.1):
`a†ᵢaᵢ` is the *occupation observable*, whose eigenvalues are the labels
`Kinded.occupationQ` ingests. -/
@[kindIngest]
def numberOpQ : Quantity Kinds.quantumNumber (𝓢(Space d, ℂ) →L[ℂ] 𝓢(Space d, ℂ)) :=
  .attest "a†ᵢaᵢ — the occupation observable at its kind" (numberCLM Q i)

/-- Rung 0, kinded: the occupation observable reads the ground label's magnitude. -/
theorem numberOpQ_ground :
    (numberOpQ Q i).magnitude (Q.eigenfunction 0)
      = (((Kinded.occupationQ (0 : Fin d → ℕ) i).magnitude : ℕ) : ℂ) •
          Q.eigenfunction 0 := by
  show numberCLM Q i (Q.eigenfunction 0) = _
  rw [numberCLM_groundState]
  simp [Kinded.occupationQ]

/-- Rung 1, kinded: the occupation observable reads the first label's magnitude. -/
theorem numberOpQ_single :
    (numberOpQ Q i).magnitude (Q.eigenfunction (Pi.single i 1))
      = (((Kinded.occupationQ (Pi.single i 1) i).magnitude : ℕ) : ℂ) •
          Q.eigenfunction (Pi.single i 1) := by
  show numberCLM Q i (Q.eigenfunction (Pi.single i 1)) = _
  rw [numberCLM_single]
  simp [Kinded.occupationQ]

end

end ForPhysLib.QuantumMechanics.HarmonicOscillator.Ladder

end -- pkc-blanket-expose
end -- pkc-blanket
