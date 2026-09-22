/-
# The solid sphere's inertia tensor — the subtree's one `sorry`, discharged

`Physlib/ClassicalMechanics/RigidBody/SolidSphere.lean` states, `@[sorryful]`:

> The moment of inertia tensor of a solid sphere through its center of mass is
> `2/5 m R^2 * I`.

This file proves it, sorry-free — the directory's patch candidate, in the pilot's
orthonormality pattern (the offer upstream is a human's to make, AI-POLICY §3.1).

The proof is the textbook computation, carried by three facts:

* **the off-diagonal moments vanish by reflection** — negating one coordinate is a
  linear isometry of `Space 3`, hence measure-preserving and ball-preserving, and it
  flips the sign of `x i · x j` for `i ≠ j`;
* **the diagonal moments agree by permutation** — swapping two coordinates is likewise
  a measure-preserving isometry, so `∫ x i ^ 2` is independent of `i` and each equals
  a third of `∫ ‖x‖²`;
* **the radial integral** — `∫_{B_R} ‖x‖²` reduces by Mathlib's Haar-to-sphere
  machinery (`integral_fun_norm_addHaar`) to `3 · vol(B₁) · ∫₀^R r⁴ dr`, and the ball
  volume scales as `R³ · vol(B₁)`, so the unit-ball volume cancels in the ratio the
  mass distribution takes; only its positivity is used.
-/

module

public import Physlib.ClassicalMechanics.RigidBody.SolidSphere
public import Physlib.SpaceAndTime.Space.Integrals.Basic
public import Mathlib.MeasureTheory.Constructions.HaarToSphere
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

public section -- pkc-blanket
@[expose] section -- pkc-blanket-expose

namespace ForPhysLib.ClassicalMechanics.SolidSphereInertia

open MeasureTheory Metric InnerProductSpace RigidBody NNReal

/-! ## Coordinate isometries of `Space d`, and what they preserve -/

/-- A coordinate isometry of `Space d`, conjugated from one of its Euclidean model
through the standard orthonormal basis. -/
noncomputable def conjIso {d : ℕ}
    (e : EuclideanSpace ℝ (Fin d) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin d)) :
    Space d ≃ₗᵢ[ℝ] Space d :=
  (Space.basis.repr.trans e).trans Space.basis.repr.symm

lemma conjIso_apply {d : ℕ}
    (e : EuclideanSpace ℝ (Fin d) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin d))
    (x : Space d) (i : Fin d) :
    conjIso e x i = e (Space.basis.repr x) i := by
  simp [conjIso]

/-- Negation of the `i`-th coordinate, as a Euclidean isometry. -/
noncomputable def reflectE {d : ℕ} (i : Fin d) :
    EuclideanSpace ℝ (Fin d) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin d) :=
  LinearIsometryEquiv.piLpCongrRight 2
    (fun k => if k = i then LinearIsometryEquiv.neg ℝ else LinearIsometryEquiv.refl ℝ ℝ)

lemma reflectE_apply {d : ℕ} (i : Fin d) (v : EuclideanSpace ℝ (Fin d)) (k : Fin d) :
    reflectE i v k = if k = i then -v k else v k := by
  by_cases h : k = i <;>
    simp [reflectE, LinearIsometryEquiv.piLpCongrRight_apply, h]

/-- Permutation of two coordinates, as a Euclidean isometry. -/
noncomputable def swapE {d : ℕ} (i j : Fin d) :
    EuclideanSpace ℝ (Fin d) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin d) :=
  LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ (Equiv.swap i j)

/-- Any linear isometry of `Space d` preserves the volume measure. -/
lemma conjIso_measurePreserving {d : ℕ}
    (e : EuclideanSpace ℝ (Fin d) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin d)) :
    MeasurePreserving (conjIso e) volume volume :=
  (conjIso e).measurePreserving

/-- A linear isometry of `Space d` maps the centred closed ball onto itself
(as a preimage). -/
lemma conjIso_preimage_closedBall {d : ℕ}
    (e : EuclideanSpace ℝ (Fin d) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin d)) (r : ℝ) :
    (conjIso e) ⁻¹' (closedBall (0 : Space d) r) = closedBall (0 : Space d) r := by
  ext x
  simp [mem_closedBall, dist_zero_right]

/-- **Substitution along a coordinate isometry**: an integral over the centred ball
is unchanged by composing the integrand with `conjIso e`. -/
lemma setIntegral_closedBall_comp_conjIso {d : ℕ}
    (e : EuclideanSpace ℝ (Fin d) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin d)) (r : ℝ)
    (f : Space d → ℝ) :
    ∫ x in closedBall (0 : Space d) r, f (conjIso e x) =
      ∫ x in closedBall (0 : Space d) r, f x := by
  have h := (conjIso_measurePreserving e).setIntegral_preimage_emb
    (conjIso e).toHomeomorph.measurableEmbedding f (closedBall (0 : Space d) r)
  rwa [conjIso_preimage_closedBall] at h

/-! ## The moment integrals -/

/-- **Off-diagonal moments vanish**: for `i ≠ j`, the second moment `∫ x i · x j`
over the centred ball is killed by reflecting coordinate `i`. -/
lemma setIntegral_mul_coord_eq_zero {d : ℕ} {i j : Fin d} (hij : i ≠ j) (r : ℝ) :
    ∫ x in closedBall (0 : Space d) r, x i * x j = 0 := by
  have h := setIntegral_closedBall_comp_conjIso (reflectE i) r (fun x => x i * x j)
  have hcomp : ∀ x : Space d,
      (conjIso (reflectE i) x) i * (conjIso (reflectE i) x) j = -(x i * x j) := by
    intro x
    rw [conjIso_apply, conjIso_apply, reflectE_apply, reflectE_apply]
    simp [hij.symm]
  rw [show (fun x : Space d => (conjIso (reflectE i) x) i * (conjIso (reflectE i) x) j)
      = fun x : Space d => -(x i * x j) from funext hcomp] at h
  rw [integral_neg] at h
  linarith [h]

/-- **Diagonal moments agree**: swapping coordinates `i` and `j` carries
`∫ (x i)²` to `∫ (x j)²`. -/
lemma setIntegral_sq_coord_eq {d : ℕ} (i j : Fin d) (r : ℝ) :
    ∫ x in closedBall (0 : Space d) r, (x i) ^ 2 =
      ∫ x in closedBall (0 : Space d) r, (x j) ^ 2 := by
  have h := setIntegral_closedBall_comp_conjIso (swapE i j) r (fun x => (x j) ^ 2)
  have hcomp : ∀ x : Space d, (conjIso (swapE i j) x) j = x i := by
    intro x
    rw [conjIso_apply]
    simp [swapE, LinearIsometryEquiv.piLpCongrLeft_apply, Equiv.swap_apply_right]
  rw [show (fun x : Space d => ((conjIso (swapE i j) x) j) ^ 2)
      = fun x : Space d => (x i) ^ 2 from funext fun x => by rw [hcomp]] at h
  exact h

/-! ## The radial integral, and the ball volume -/

/-- The squared norm on `Space d` is the sum of the squared coordinates. -/
lemma norm_sq_eq_sum {d : ℕ} (x : Space d) : ‖x‖ ^ 2 = ∑ k, (x k) ^ 2 := by
  rw [← real_inner_self_eq_norm_sq, Space.inner_eq_sum]
  exact Finset.sum_congr rfl fun k _ => (sq (x k)).symm

/-- `∫_{B_R} ‖x‖²` by the Haar-to-sphere reduction: `3 · vol(B₁) · R⁵/5`. -/
lemma setIntegral_normSq_closedBall (R : ℝ) (hR : 0 ≤ R) :
    ∫ x in closedBall (0 : Space 3) R, ‖x‖ ^ 2 =
      3 * volume.real (Metric.ball (0 : Space 3) 1) * (R ^ 5 / 5) := by
  have hind : ∫ x in closedBall (0 : Space 3) R, ‖x‖ ^ 2 =
      ∫ x : Space 3, (fun r : ℝ => if r ≤ R then r ^ 2 else 0) ‖x‖ := by
    rw [← integral_indicator (measurableSet_closedBall)]
    congr 1
    funext x
    by_cases hx : ‖x‖ ≤ R <;>
      simp [Set.indicator, Metric.mem_closedBall, dist_zero_right, hx]
  rw [hind, MeasureTheory.integral_fun_norm_addHaar
    (volume : Measure (Space 3)) (fun r : ℝ => if r ≤ R then r ^ 2 else 0)]
  have hdim : Module.finrank ℝ (Space 3) = 3 := by simp [Space.finrank_eq_dim]
  rw [hdim]
  have hrad : ∫ y in Set.Ioi (0 : ℝ),
      y ^ (3 - 1) • (fun r : ℝ => if r ≤ R then r ^ 2 else 0) y = R ^ 5 / 5 := by
    have hcong : ∫ y in Set.Ioi (0 : ℝ),
        y ^ (3 - 1) • (fun r : ℝ => if r ≤ R then r ^ 2 else 0) y =
          ∫ y in Set.Ioi (0 : ℝ), (Set.Ioc (0 : ℝ) R).indicator (fun y => y ^ 4) y := by
      refine setIntegral_congr_fun measurableSet_Ioi ?_
      intro y hy
      have hy' : (0 : ℝ) < y := hy
      by_cases hyR : y ≤ R
      · simp [Set.indicator, hy', hyR, smul_eq_mul]
        ring
      · simp [Set.indicator, hy', hyR, smul_eq_mul]
    rw [hcong, setIntegral_indicator measurableSet_Ioc,
      show Set.Ioi (0 : ℝ) ∩ Set.Ioc (0 : ℝ) R = Set.Ioc (0 : ℝ) R from
        Set.inter_eq_right.mpr fun y hy => hy.1,
      ← intervalIntegral.integral_of_le hR, integral_pow]
    norm_num
  rw [hrad, nsmul_eq_mul, smul_eq_mul]
  push_cast
  ring

/-- The closed ball's volume scales as `R³` times the unit ball's. -/
lemma volumeReal_closedBall (R : ℝ) (hR : 0 ≤ R) :
    volume.real (closedBall (0 : Space 3) R) =
      R ^ 3 * volume.real (Metric.ball (0 : Space 3) 1) := by
  have h := Measure.addHaar_closedBall (volume : Measure (Space 3)) 0 hR
  have hdim : Module.finrank ℝ (Space 3) = 3 := by simp [Space.finrank_eq_dim]
  rw [hdim] at h
  rw [measureReal_def, h, ENNReal.toReal_mul, ENNReal.toReal_ofReal (by positivity)]
  rfl

/-- Each diagonal second moment is a third of the radial integral. -/
lemma setIntegral_sq_coord (R : ℝ) (i : Fin 3) :
    ∫ x in closedBall (0 : Space 3) R, (x i) ^ 2 =
      (1 / 3) * ∫ x in closedBall (0 : Space 3) R, ‖x‖ ^ 2 := by
  have hint : ∀ k : Fin 3,
      IntegrableOn (fun x : Space 3 => (x k) ^ 2) (closedBall 0 R) volume :=
    fun k => ContinuousOn.integrableOn_compact (isCompact_closedBall 0 R) (by fun_prop)
  have hsum : ∫ x in closedBall (0 : Space 3) R, ‖x‖ ^ 2 =
      ∑ k, ∫ x in closedBall (0 : Space 3) R, (x k) ^ 2 := by
    rw [show (fun x : Space 3 => ‖x‖ ^ 2) = fun x : Space 3 => ∑ k, (x k) ^ 2 from
        funext norm_sq_eq_sum]
    exact integral_finsetSum _ fun k _ => hint k
  have heach : ∀ k : Fin 3,
      ∫ x in closedBall (0 : Space 3) R, (x k) ^ 2 =
        ∫ x in closedBall (0 : Space 3) R, (x i) ^ 2 :=
    fun k => setIntegral_sq_coord_eq k i R
  rw [hsum, Fin.sum_univ_three, heach 0, heach 1, heach 2]
  ring

/-! ## The discharge -/

/-- **The solid sphere's inertia tensor is `(2/5) m R² · 1`** — the statement of
upstream's `@[sorryful]` `solidSphere_inertiaTensor`, proved. -/
theorem solidSphere_inertiaTensor (m R : ℝ≥0) (hr : R ≠ 0) :
    (RigidBody.solidSphere 3 m R).inertiaTensor =
      (2/5 * m.1 * R.1 ^ 2) • (1 : Matrix (Fin 3) (Fin 3) ℝ) := by
  have hR0 : (0 : ℝ) ≤ R.1 := R.2
  have hRne : (R.1 : ℝ) ≠ 0 := by simpa using hr
  have hint_sum : IntegrableOn
      (fun x : Space 3 => ∑ k, (x k) ^ 2) (closedBall 0 R.1) volume :=
    ContinuousOn.integrableOn_compact (isCompact_closedBall 0 R.1) (by fun_prop)
  have hint_sq : ∀ i : Fin 3, IntegrableOn
      (fun x : Space 3 => (x i) ^ 2) (closedBall 0 R.1) volume :=
    fun i => ContinuousOn.integrableOn_compact (isCompact_closedBall 0 R.1)
      (by fun_prop)
  -- The integral of each entry's moment, in both cases of the Kronecker δ.
  have key : ∀ i j : Fin 3,
      (∫ x in closedBall (0 : Space 3) R.1,
        ((if i = j then (1 : ℝ) else 0) * ∑ k, (x k) ^ 2 - x i * x j)) =
      (if i = j then (1 : ℝ) else 0) *
        (2 / 5 * R.1 ^ 2 * (R.1 ^ 3 * volume.real (Metric.ball (0 : Space 3) 1))) := by
    intro i j
    by_cases h : i = j
    · subst h
      have h1 : (fun x : Space 3 =>
            (if i = i then (1 : ℝ) else 0) * ∑ k, (x k) ^ 2 - x i * x i)
          = fun x : Space 3 => (∑ k, (x k) ^ 2) - (x i) ^ 2 := by
        funext x
        simp
        ring
      rw [h1, integral_sub hint_sum (hint_sq i), ite_eq_left rfl,
        show (fun x : Space 3 => ∑ k, (x k) ^ 2)
          = fun x : Space 3 => ‖x‖ ^ 2 from funext fun x => (norm_sq_eq_sum x).symm,
        setIntegral_sq_coord, setIntegral_normSq_closedBall R.1 hR0]
      ring
    · have h1 : (fun x : Space 3 =>
            (if i = j then (1 : ℝ) else 0) * ∑ k, (x k) ^ 2 - x i * x j)
          = fun x : Space 3 => -(x i * x j) := by
        funext x
        simp [h]
      rw [h1, integral_neg, setIntegral_mul_coord_eq_zero h, ite_eq_right h]
      simp
  ext i j
  have hLHS : (RigidBody.solidSphere 3 m R).inertiaTensor i j
      = m.1 / volume.real (closedBall (0 : Space 3) R.1) *
        ∫ x in closedBall (0 : Space 3) R.1,
          ((if i = j then (1 : ℝ) else 0) * ∑ k, (x k) ^ 2 - x i * x j) := rfl
  rw [hLHS, key i j, volumeReal_closedBall R.1 hR0, Matrix.smul_apply,
    Matrix.one_apply, smul_eq_mul]
  have hv₁ : (0 : ℝ) < volume.real (Metric.ball (0 : Space 3) 1) := by
    rw [Space.volume_metricBall_three_real]
    positivity
  by_cases h : i = j
  · field_simp
  · simp [h]

end ForPhysLib.ClassicalMechanics.SolidSphereInertia

end -- pkc-blanket-expose
end -- pkc-blanket
