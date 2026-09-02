/-
# Degeneracy — how many labels share one energy indication

`Eigenstates.lean` proves `eigenEnergy_strictMono` — the eigenvalues respect the label
order — and its TODO list asks for the ground state's non-degeneracy. This file counts
the collisions the order cannot see:

* **Label-level ground non-degeneracy, for every oscillator.** No label but `0`
  reaches the ground energy (`eigenEnergy_eq_ground_iff`) — anisotropy not required.
  This is the label half of upstream's TODO; the Hilbert-space half (no *other*
  eigenvector) stays named upstream analysis.
* **The isotropic collision, decided.** With all frequencies equal, the eigenvalue
  depends on a label only through its total occupation
  (`eigenEnergy_isotropic`, `eigenEnergy_eq_iff`) — so distinct labels collide, and
  the collision has a count.
* **Stars and bars.** The `N`-th level set is Mathlib's `piAntidiag`, and its card is
  `(d + N - 1).choose N` (`card_levelSet`) — the textbook degeneracy, off
  `Finset.card_finsuppAntidiag_nat_eq_choose` with no new combinatorics.
* **Kinded.** Two kinded eigenvalues agree exactly when the totals do
  (`eigenEnergyQ_eq_iff`): the energy indication does not individuate the label, and
  the degeneracy count is precisely how far it fails to — a same-kind collision that
  is physics, unlike the cross-kind collisions the registry refuses.
-/

import ForPhysLib.QuantumMechanics.HarmonicOscillator.Kinded
import Mathlib.Algebra.Order.Antidiag.FinsuppEquiv

open QuantumMechanics HarmonicOscillator Constants
open PropertyKindCalculus
open ForPhysLib.QuantumMechanics.HarmonicOscillator

namespace ForPhysLib.QuantumMechanics.HarmonicOscillator.Degeneracy

local notation "PhysHO" => _root_.QuantumMechanics.HarmonicOscillator

noncomputable section

variable {d : ℕ} (Q : PhysHO d) (n n' : Fin d → ℕ)

/-! ## The ground level, for every oscillator -/

/-- The excitation energy above the ground level: `∑ ℏωᵢnᵢ`. -/
lemma eigenEnergy_sub_ground :
    Q.eigenEnergy n - Q.eigenEnergy 0 = ∑ i, (ℏ : ℝ) * Q.ω i * n i := by
  rw [eigenEnergy_eq, eigenEnergy_eq, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [Pi.zero_apply, Nat.cast_zero]
  ring

/-- **Label-level non-degeneracy of the ground level** — isotropic or not: no other
label reaches the ground energy. -/
theorem eigenEnergy_eq_ground_iff :
    Q.eigenEnergy n = Q.eigenEnergy 0 ↔ n = 0 := by
  constructor
  · intro h
    have h0 : ∑ i, (ℏ : ℝ) * Q.ω i * n i = 0 := by
      rw [← eigenEnergy_sub_ground, h, sub_self]
    have hterm : ∀ i ∈ Finset.univ, (0 : ℝ) ≤ (ℏ : ℝ) * Q.ω i * n i := fun i _ =>
      mul_nonneg (mul_nonneg ℏ_pos.le (Q.hω i).le) (Nat.cast_nonneg _)
    funext i
    have := (Finset.sum_eq_zero_iff_of_nonneg hterm).mp h0 i (Finset.mem_univ i)
    have hcast : (n i : ℝ) = 0 := by
      have hne : (ℏ : ℝ) * Q.ω i ≠ 0 :=
        ne_of_gt (mul_pos ℏ_pos (Q.hω i))
      rw [mul_assoc] at this
      simpa [hne] using this
    exact_mod_cast hcast
  · rintro rfl
    rfl

/-! ## The isotropic collision -/

section Isotropic

variable {ω₀ : ℝ}

/-- The isotropic eigenvalue depends on the label only through its total. -/
lemma eigenEnergy_isotropic (hω : ∀ k, Q.ω k = ω₀) :
    Q.eigenEnergy n = (ℏ : ℝ) * ω₀ * ((∑ k, n k : ℕ) + (d : ℝ) / 2) := by
  rw [eigenEnergy_eq]
  simp only [hω]
  rw [← Finset.mul_sum, Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul, Nat.cast_sum]
  ring

/-- Under isotropy, two labels share the eigenvalue exactly when their totals agree —
the collision the degeneracy counts. -/
theorem eigenEnergy_eq_iff (hω : ∀ k, Q.ω k = ω₀) (hω₀ : 0 < ω₀) :
    Q.eigenEnergy n = Q.eigenEnergy n' ↔ ∑ k, n k = ∑ k, n' k := by
  rw [eigenEnergy_isotropic Q n hω, eigenEnergy_isotropic Q n' hω]
  constructor
  · intro h
    have hne : (ℏ : ℝ) * ω₀ ≠ 0 := ne_of_gt (mul_pos ℏ_pos hω₀)
    have h2 : ((∑ k, n k : ℕ) : ℝ) = ((∑ k, n' k : ℕ) : ℝ) := by
      have := mul_left_cancel₀ hne h
      linarith [this]
    exact_mod_cast h2
  · intro h
    rw [h]

end Isotropic

/-! ## The count — stars and bars off Mathlib's antidiagonal -/

/-- The `N`-th level set: the labels with total occupation `N`. -/
def levelSet (d N : ℕ) : Finset (Fin d → ℕ) := Finset.univ.piAntidiag N

lemma mem_levelSet {N : ℕ} {n : Fin d → ℕ} : n ∈ levelSet d N ↔ ∑ k, n k = N := by
  simp [levelSet, Finset.mem_piAntidiag]

/-- **Stars and bars**: the `N`-th level holds `(d + N - 1).choose N` labels. -/
theorem card_levelSet (d N : ℕ) :
    (levelSet d N).card = (d + N - 1).choose N := by
  have h := Finset.card_finsuppAntidiag_nat_eq_choose
    (s := (Finset.univ : Finset (Fin d))) N
  rw [Finset.card_univ, Fintype.card_fin] at h
  rw [← h, Finset.finsuppAntidiag, Finset.card_map, Finset.card_attach]
  rfl

/-- The ground level is a singleton — the counting face of
`eigenEnergy_eq_ground_iff`. -/
theorem levelSet_zero (d : ℕ) : levelSet d 0 = {0} := by
  ext n
  simp only [mem_levelSet, Finset.mem_singleton]
  constructor
  · intro h
    funext i
    simpa using (Finset.sum_eq_zero_iff.mp h) i (Finset.mem_univ i)
  · rintro rfl
    simp

/-! ## Kinded — a same-kind collision that is physics -/

section Kinded

variable {ω₀ : ℝ}

/-- Kinded eigenvalues are equal exactly when the magnitudes are — the quantity adds
the kind, not new identity. -/
lemma eigenEnergyQ_eq_iff_magnitude :
    Kinded.eigenEnergyQ Q n = Kinded.eigenEnergyQ Q n'
      ↔ Q.eigenEnergy n = Q.eigenEnergy n' := by
  constructor
  · intro h
    have := congrArg Quantity.magnitude h
    rwa [Kinded.eigenEnergyQ_magnitude, Kinded.eigenEnergyQ_magnitude] at this
  · intro h
    ext
    rw [Kinded.eigenEnergyQ_magnitude, Kinded.eigenEnergyQ_magnitude]
    exact h

/-- **The kinded collision**: under isotropy, the energy indication determines only
the total occupation — the degeneracy count is how far same-kind equality fails to
individuate the label. -/
theorem eigenEnergyQ_eq_iff (hω : ∀ k, Q.ω k = ω₀) (hω₀ : 0 < ω₀) :
    Kinded.eigenEnergyQ Q n = Kinded.eigenEnergyQ Q n' ↔ ∑ k, n k = ∑ k, n' k :=
  (eigenEnergyQ_eq_iff_magnitude Q n n').trans (eigenEnergy_eq_iff Q n n' hω hω₀)

/-- All labels of one level carry one indication. -/
theorem eigenEnergyQ_const_on_levelSet (hω : ∀ k, Q.ω k = ω₀) (hω₀ : 0 < ω₀)
    {N : ℕ} (h : n ∈ levelSet d N) (h' : n' ∈ levelSet d N) :
    Kinded.eigenEnergyQ Q n = Kinded.eigenEnergyQ Q n' :=
  (eigenEnergyQ_eq_iff Q n n' hω hω₀).mpr
    ((mem_levelSet.mp h).trans (mem_levelSet.mp h').symm)

/-- **The kinded ground level is simple, for every oscillator**: only the zero label
carries the ground indication. -/
theorem eigenEnergyQ_eq_ground_iff :
    Kinded.eigenEnergyQ Q n = Kinded.eigenEnergyQ Q 0 ↔ n = 0 :=
  (eigenEnergyQ_eq_iff_magnitude Q n 0).trans (eigenEnergy_eq_ground_iff Q n)

end Kinded

end

end ForPhysLib.QuantumMechanics.HarmonicOscillator.Degeneracy
