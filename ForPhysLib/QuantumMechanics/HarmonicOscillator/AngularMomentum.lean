/-
# `L_z = m·ℏ` — the J·s collision, crossed on purpose

Angular momentum (ISO 80000-4 item 4-11) and action (item 4-32) share the dimension
`M·L²·T⁻¹` and nothing else: one is the eigenvalue scale of a rotation generator, the
other is the quantum of the phase-space area ℏ measures. PhysLib carries both readings
— `𝐋ᵢⱼ = x̂ᵢp̂ⱼ − x̂ⱼp̂ᵢ` in `Operators/AngularMomentum.lean` and `ℏ` in
`PlanckConstant.lean` — and every `L_z = m·ℏ` sentence in a QM text silently re-kinds
the right-hand side. This file makes both halves explicit for the oscillator:

* **The analysis, upstream-facing.** The Gaussian eigen-relation
  `𝐩ᵢψ₀ = (iℏ/ξᵢ²)·x̂ᵢψ₀` (from `Heisenberg.lean`) turns every `𝐋ᵢⱼ` statement about
  low modes into CLM algebra — no new integrals, no new derivatives:
  - `𝐋ᵢⱼ ψ₀ = iℏ(ξⱼ⁻² − ξᵢ⁻²) · x̂ᵢx̂ⱼψ₀` — the ground state is an `m = 0` eigenstate
    *exactly when* the `i,j` pair is isotropic, and the anisotropic obstruction is the
    visible coefficient;
  - the circular combinations `x̂ᵢψ₀ ± i·x̂ⱼψ₀` are `m = ±1` eigenstates of `𝐋ᵢⱼ`,
    and `ψ_{eᵢ} = (√2/ξᵢ)·x̂ᵢψ₀` identifies them as first-excited-level combinations.

* **The crossing, kinded.** `m·ℏ` multiplies a dimensionless integer into the *action*
  constant and reads the result at *angular momentum* — a same-dimension re-kind no
  algebra licenses. `angularMomentumReading` is that step as one `@[kindCrossing]`
  attest; the registry keeps 4-11 ≠ 4-32 decidable; and the eigenvalue theorems close
  the loop: the circular state's eigenvalue *is* the `m = 1` indication's magnitude.
-/

module

public import ForPhysLib.QuantumMechanics.HarmonicOscillator.Heisenberg
meta import ForPhysLib.QuantumMechanics.HarmonicOscillator.Heisenberg
public import Physlib.QuantumMechanics.Operators.AngularMomentum
meta import Physlib.QuantumMechanics.Operators.AngularMomentum

@[expose] public section

open MeasureTheory QuantumMechanics HarmonicOscillator SpaceDHilbertSpace SchwartzSubmodule
open InnerProductSpace Complex Constants LinearPMap SchwartzMap
open PropertyKindCalculus
open ForPhysLib.QuantumMechanics.HarmonicOscillator
open ForPhysLib.QuantumMechanics.HarmonicOscillator.Heisenberg

namespace ForPhysLib.QuantumMechanics.HarmonicOscillator.AngularMomentum

local notation "PhysHO" => _root_.QuantumMechanics.HarmonicOscillator

noncomputable section

variable {d : ℕ} (Q : PhysHO d) (i j : Fin d)

/-! ## The analysis — `𝐋ᵢⱼ` on the low modes, by CLM algebra alone -/

/-- Position components commute. -/
lemma positionCLM_comm (ψ : 𝓢(Space d, ℂ)) : 𝐱 i (𝐱 j ψ) = 𝐱 j (𝐱 i ψ) := by
  ext x
  simp only [positionCLM_apply]
  ring

/-- `𝐩ⱼ` through `𝐱ᵢ` on the ground state: the CCR plus the Gaussian eigen-relation. -/
lemma momentumCLM_position_groundState :
    𝐩 j (𝐱 i (Q.eigenfunction 0))
      = ((I * (ℏ : ℝ)) / ((Q.ξ j : ℝ) : ℂ) ^ 2) • 𝐱 i (𝐱 j (Q.eigenfunction 0))
        - (I * (ℏ : ℝ)) • δ[i,j] • Q.eigenfunction 0 := by
  have h := congrArg (fun T => T (Q.eigenfunction 0))
    (momentum_comp_position_eq (d := d) i j)
  simp only [ContinuousLinearMap.comp_apply, _root_.sub_apply,
    _root_.smul_apply, ContinuousLinearMap.id_apply] at h
  rw [h, momentumCLM_groundState, _root_.map_smul]

/-- `𝐋ᵢⱼ ψ₀` carries the anisotropy: the coefficient vanishes exactly when the two
characteristic lengths agree. -/
lemma angularMomentum_groundState :
    𝐋 i j (Q.eigenfunction 0)
      = ((I * (ℏ : ℝ)) / ((Q.ξ j : ℝ) : ℂ) ^ 2
          - (I * (ℏ : ℝ)) / ((Q.ξ i : ℝ) : ℂ) ^ 2) • 𝐱 i (𝐱 j (Q.eigenfunction 0)) := by
  rw [angularMomentumOperator_apply_fun, momentumCLM_groundState,
    momentumCLM_groundState, _root_.map_smul, _root_.map_smul,
    positionCLM_comm j i, sub_smul]

/-- The isotropic ground state is an `m = 0` eigenstate of every `𝐋ᵢⱼ`. -/
lemma angularMomentum_groundState_isotropic (hξ : Q.ξ i = Q.ξ j) :
    𝐋 i j (Q.eigenfunction 0) = 0 := by
  rw [angularMomentum_groundState, hξ, sub_self, zero_smul]

/-- Isotropy of frequencies transfers to the characteristic lengths. -/
lemma ξ_eq_of_ω_eq (h : Q.ω i = Q.ω j) : Q.ξ i = Q.ξ j := by
  rw [ξ_eq, ξ_eq, h]

/-- The circular combination `x̂ᵢψ₀ + i·x̂ⱼψ₀` — the `m = +1` circulation, unnormalized. -/
def circularState : 𝓢(Space d, ℂ) :=
  𝐱 i (Q.eigenfunction 0) + I • 𝐱 j (Q.eigenfunction 0)

/-- **`L_z ψ₊ = (+1)·ℏ ψ₊`** for an isotropic pair `i ≠ j`. -/
theorem angularMomentum_circularState (hξ : Q.ξ i = Q.ξ j) (hij : i ≠ j) :
    𝐋 i j (circularState Q i j) = ((ℏ : ℝ) : ℂ) • circularState Q i j := by
  rw [angularMomentumOperator_apply_fun]
  simp only [circularState, _root_.map_add, _root_.map_smul]
  rw [momentumCLM_position_groundState Q i j, momentumCLM_position_groundState Q j j,
    momentumCLM_position_groundState Q i i, momentumCLM_position_groundState Q j i, hξ]
  ext x
  simp only [_root_.add_apply, _root_.sub_apply, _root_.smul_apply,
    positionCLM_apply, smul_eq_mul, KroneckerDelta.eq_zero_of_ne hij,
    KroneckerDelta.eq_zero_of_ne (Ne.symm hij), KroneckerDelta.eq_one_of_same,
    zero_smul, one_smul, _root_.zero_apply]
  linear_combination (-(((ℏ : ℝ) : ℂ) * (x i : ℂ) * Q.eigenfunction 0 x)) * Complex.I_sq

/-- The conjugate combination `x̂ᵢψ₀ - i·x̂ⱼψ₀` — the `m = -1` circulation. -/
def circularStateNeg : 𝓢(Space d, ℂ) :=
  𝐱 i (Q.eigenfunction 0) - I • 𝐱 j (Q.eigenfunction 0)

/-- **`L_z ψ₋ = (-1)·ℏ ψ₋`** for an isotropic pair `i ≠ j`. -/
theorem angularMomentum_circularStateNeg (hξ : Q.ξ i = Q.ξ j) (hij : i ≠ j) :
    𝐋 i j (circularStateNeg Q i j) = (-(ℏ : ℝ) : ℂ) • circularStateNeg Q i j := by
  rw [angularMomentumOperator_apply_fun]
  simp only [circularStateNeg, _root_.map_sub, _root_.map_smul]
  rw [momentumCLM_position_groundState Q i j, momentumCLM_position_groundState Q j j,
    momentumCLM_position_groundState Q i i, momentumCLM_position_groundState Q j i, hξ]
  ext x
  simp only [_root_.sub_apply, _root_.smul_apply,
    positionCLM_apply, smul_eq_mul, KroneckerDelta.eq_zero_of_ne hij,
    KroneckerDelta.eq_zero_of_ne (Ne.symm hij), KroneckerDelta.eq_one_of_same,
    zero_smul, one_smul, _root_.zero_apply]
  linear_combination (((ℏ : ℝ) : ℂ) * (x i : ℂ) * Q.eigenfunction 0 x) * Complex.I_sq

/-! ## The circulations are first-excited-level combinations -/

/-- The single-excitation normalization halves through `√2`. -/
lemma eigenCoeff_single_self :
    Q.eigenCoeff (Pi.single i 1) i = Q.eigenCoeff 0 i / √2 := by
  rw [eigenCoeff_eq, eigenCoeff_eq]
  simp only [Pi.single_eq_same, Pi.zero_apply, pow_one, pow_zero, Nat.factorial_one,
    Nat.factorial_zero, Nat.cast_one, one_mul]
  rw [show (2:ℝ) * 1 * √Real.pi * Q.ξ i = 2 * (√Real.pi * Q.ξ i) by ring,
    Real.sqrt_mul (by norm_num : (0:ℝ) ≤ 2), div_div, mul_comm]

/-- Away from its excitation slot, the single-excitation coefficients are the ground
ones. -/
lemma eigenCoeff_single_of_ne {k : Fin d} (hk : k ≠ i) :
    Q.eigenCoeff (Pi.single i 1) k = Q.eigenCoeff 0 k := by
  rw [eigenCoeff_eq, eigenCoeff_eq]
  simp [Pi.single_eq_of_ne hk]

/-- **The first excited eigenfunctions are position readings of the ground state**:
`ψ_{eᵢ} = (√2/ξᵢ) · x̂ᵢ ψ₀`. -/
lemma eigenfunction_single :
    Q.eigenfunction (Pi.single i 1)
      = (((√2 / Q.ξ i : ℝ)) : ℂ) • 𝐱 i (Q.eigenfunction 0) := by
  ext x
  rw [_root_.smul_apply, positionCLM_apply, eigenfunction_apply, eigenfunction_apply,
    ← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ i),
    ← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ i)]
  rw [Finset.prod_congr rfl fun k hk => by
    rw [eigenCoeff_single_of_ne Q i (Finset.ne_of_mem_erase hk),
      Pi.single_eq_of_ne (Finset.ne_of_mem_erase hk)]]
  rw [eigenCoeff_single_self, Pi.single_eq_same, Pi.zero_apply]
  norm_cast
  rw [physHermite_one_apply, Polynomial.physHermite_zero_coe]
  simp only [Pi.zero_apply, mul_one]
  rw [Complex.real_smul]
  have hξ' : ((Q.ξ i : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (Q.ξ_ne_zero i)
  have h2' : ((√2 : ℝ) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (ne_of_gt (Real.sqrt_pos.mpr (by norm_num)))
  have h22 : ((√2 : ℝ) : ℂ) * ((√2 : ℝ) : ℂ) = 2 := by
    exact_mod_cast congrArg (Complex.ofReal) (Real.mul_self_sqrt (by norm_num : (0:ℝ) ≤ 2))
  push_cast
  field_simp
  rw [Polynomial.physHermite_zero_coe]
  simp only [Complex.ofReal_one, mul_one]
  rw [pow_two, h22]

/-- Under isotropy the `m = +1` circulation is the first-excited combination
`ψ_{eᵢ} + i·ψ_{eⱼ}`, up to the common positive scale `√2/ξᵢ`. -/
lemma eigenfunction_combination_eq_circular (hξ : Q.ξ i = Q.ξ j) :
    Q.eigenfunction (Pi.single i 1) + I • Q.eigenfunction (Pi.single j 1)
      = (((√2 / Q.ξ i : ℝ)) : ℂ) • circularState Q i j := by
  rw [eigenfunction_single, eigenfunction_single, ← hξ, circularState, smul_add,
    smul_comm I]

/-! ## The crossing, kinded — 4-11 and 4-32 at one dimension -/

/-- The collision is real and decided: one dimension, two kinds. -/
example : Metrology.angularMomentumDK.dim = Metrology.actionDK.dim := rfl
example : Kinds.angularMomentum ≠ Kinds.action := by decide

-- ℏ is *not* an angular momentum — the registry refuses the silent re-kind.
#check_failure (hbarQ : Quantity Kinds.angularMomentum ℝ)

/-- **The `m·ℏ` crossing**: a dimensionless integer scales the action constant and the
result is *read at angular momentum* — the same-dimension re-kind every
`L_z = m·ℏ` sentence performs, made a single visible attest. -/
@[kindCrossing]
def angularMomentumReading (m : ℤ) (S : Quantity actionK ℝ) :
    Quantity Kinds.angularMomentum ℝ :=
  .attest "m·ℏ read at 4-11 — the J·s collision crossed on purpose" (m * S.magnitude)

/-- The `L_z` indication ladder: `m ↦ m·ℏ` at the angular-momentum kind. -/
def LzIndicationQ (m : ℤ) : Quantity Kinds.angularMomentum ℝ :=
  angularMomentumReading m hbarQ

@[simp]
lemma LzIndicationQ_magnitude (m : ℤ) : (LzIndicationQ m).magnitude = m * (ℏ : ℝ) := rfl

/-- **The circular state realizes the `m = 1` indication**: its `𝐋ᵢⱼ` eigenvalue is
the magnitude of `LzIndicationQ 1`, stated from the isotropy hypothesis the physics
needs (`ωᵢ = ωⱼ`). -/
theorem circularState_realizes_indication (hω : Q.ω i = Q.ω j) (hij : i ≠ j) :
    𝐋 i j (circularState Q i j)
      = (((LzIndicationQ 1).magnitude : ℝ) : ℂ) • circularState Q i j := by
  rw [LzIndicationQ_magnitude]
  push_cast
  simpa using angularMomentum_circularState Q i j (ξ_eq_of_ω_eq Q i j hω) hij

/-- The conjugate circulation realizes the `m = -1` indication. -/
theorem circularStateNeg_realizes_indication (hω : Q.ω i = Q.ω j) (hij : i ≠ j) :
    𝐋 i j (circularStateNeg Q i j)
      = (((LzIndicationQ (-1)).magnitude : ℝ) : ℂ) • circularStateNeg Q i j := by
  rw [LzIndicationQ_magnitude]
  push_cast
  simpa using angularMomentum_circularStateNeg Q i j (ξ_eq_of_ω_eq Q i j hω) hij

end

end ForPhysLib.QuantumMechanics.HarmonicOscillator.AngularMomentum

