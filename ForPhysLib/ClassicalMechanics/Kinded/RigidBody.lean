/-
# Stage 2 — kinded re-authoring of `Physlib/ClassicalMechanics/RigidBody`

The third rung of [the adoption ladder](../../PLAN.md#stage-2-kinded-re-authoring-with-definitional-erasure)
for the campaign's third directory, rigid-body half. Every quantity at its kind, the
naked form recovered definitionally or by upstream's own theorem.

**The re-authoring follows the subtree's own derivation order.**

* **The moments of the functional.** `RigidBody.ρ` is a linear functional on test
  functions, and each moment read off it is an ingest whose kind is mass times the
  test function's: the total mass (`ρ(1)`), the centre-of-mass coordinate (the first
  moment over the mass), the inertia entries (the second moments). The
  **parallel-axis theorem** is then consumed at the kinded readings: the inertia
  about `p` is the inertia about the centre of mass plus a point-particle term built
  from the mass reading — a same-kind sum at 4-7, upstream's proof verbatim.
* **The two ω's of one motion.** The angular-velocity tensor `Ω = Ṙ Rᵀ` and its
  body-frame twin `Ω_body = Rᵀ Ṙ` are both read at 3-12 — the *kinds* agree, the
  frames differ, and the kind layer separates kinds, not frames (scope honesty,
  Feasibility F6a). What the layer *does* check: the skew-symmetry is a same-kind
  negation, and the conjugation `Ω_body = Rᵀ Ω R` stays inside the kind because the
  orientation's entries are dimensionless direction cosines — the frame change rides
  the numeral action.
* **The velocity decomposition, through the edge.** Landau–Lifshitz's `v = V + ω × r`:
  the cross product's every component is two table products (`ω·r` through the
  Stage-1 edge grown for it) and one same-kind subtraction — fully table-expressible —
  and upstream's `velocity_eq_angularVelocity` closes the decomposition at the kinded
  readings.
* **The rotational energy, contracted through the table.** `½ ω·(I·ω)` as three
  `I·ω → L` products (Feasibility's contraction), three `ω·L` products, and one
  numeral — erasing to upstream's `rotationalKineticEnergy` by its own
  `T = ½ ω·L` lemma. König itself was Feasibility's second join.
* **The motion preserves the readings.** The pushed-forward distribution's mass
  reading is the body's (`massDistribution_mass`), its centre-of-mass reading tracks
  the trajectory (`massDistribution_centerOfMass`), and the solid sphere's
  centre-of-mass reading is zero — each an upstream theorem consumed at an ingest.
-/

module

public import ForPhysLib.ClassicalMechanics.Feasibility
meta import ForPhysLib.ClassicalMechanics.Feasibility
public import ForPhysLib.ClassicalMechanics.Metrology
meta import ForPhysLib.ClassicalMechanics.Metrology
public import Physlib.ClassicalMechanics.RigidBody.SolidSphere
meta import Physlib.ClassicalMechanics.RigidBody.SolidSphere

public section -- pkc-blanket
@[expose] section -- pkc-blanket-expose

namespace ForPhysLib.ClassicalMechanics.Kinded

open PropertyKindCalculus
open ForPhysLib.ClassicalMechanics
open Time Matrix InnerProductSpace
open scoped PropertyKindCalculus.OperatorTable

variable {d : ℕ}

noncomputable section

/-! ## The moments of the functional -/

/-- A centre-of-mass coordinate — the first moment of the distribution over the
mass, read at the displacement kind. -/
@[kindIngest]
def comQ (R : RigidBody d) (i : Fin d) : Quantity displacementK ℝ :=
  .attest "the first moment over the mass — a centre-of-mass coordinate"
    (R.centerOfMass i)

/-- An inertia entry about an arbitrary point `p` — the second moment with the
displacements taken from `p`. -/
@[kindIngest]
def inertiaAboutAtQ (R : RigidBody d) (p : Space d) (i j : Fin d) :
    Quantity momentOfInertiaK ℝ :=
  .attest "the second moment about p" (R.inertiaTensorAbout p i j)

/-- The point-particle inertia term of the parallel-axis theorem — the whole mass at
the centre of mass, displaced to `p`: a crossing from the mass reading (times the
displacement quadratic) to 4-7. -/
@[kindCrossing]
def pointMassInertiaQ (mq : Quantity massK ℝ) (c p : Space d) (i j : Fin d) :
    Quantity momentOfInertiaK ℝ :=
  .attest "m·(|c−p|²δ − (c−p)⊗(c−p)) — the point-particle inertia"
    ((mq.magnitude • (⟪c - p, c - p⟫_ℝ • (1 : Matrix (Fin d) (Fin d) ℝ)
      - Matrix.vecMulVec ⇑(c - p) ⇑(c - p))) i j)

/-- **The parallel-axis theorem, consumed at the kinded readings**: the inertia about
`p` is the inertia about the centre of mass plus the point-particle term — a
same-kind sum at 4-7, upstream's proof verbatim. -/
theorem inertiaAboutAtQ_parallel_axis (R : RigidBody d) (h : R.mass ≠ 0)
    (p : Space d) (i j : Fin d) :
    (inertiaAboutAtQ R p i j).magnitude =
      (inertiaAboutAtQ R R.centerOfMass i j).magnitude +
        (pointMassInertiaQ (rbMassQ R) R.centerOfMass p i j).magnitude := by
  have h0 := congrFun (congrFun
    (R.inertiaTensorAbout_eq_centerOfMass_add_pointMass h p) i) j
  simp only [Matrix.add_apply] at h0
  exact h0

/-! ## The two ω's of one motion -/

/-- An entry of the (lab-frame) angular-velocity tensor `Ω = Ṙ Rᵀ`, read at 3-12. -/
@[kindIngest]
def omegaTensorAtQ (M : RigidBodyMotion d) (t : Time) (i j : Fin d) :
    Quantity angularVelocityK ℝ :=
  .attest "an entry of Ω = Ṙ Rᵀ — the lab-frame reading"
    (M.angularVelocityTensor t i j)

/-- An entry of the body-frame tensor `Ω_body = Rᵀ Ṙ` — the *same kind*, the other
frame: the kind layer separates kinds, not frames. -/
@[kindIngest]
def bodyOmegaTensorAtQ (M : RigidBodyMotion d) (t : Time) (i j : Fin d) :
    Quantity angularVelocityK ℝ :=
  .attest "an entry of Ω_body = Rᵀ Ṙ — the body-frame reading"
    (M.bodyAngularVelocityTensor t i j)

/-- **Skew-symmetry at the kinded reading**: transposing negates — a same-kind
negation, licensed by the ratio scale, upstream's differentiated orthogonality the
proof. -/
theorem omegaTensorAtQ_skew (M : RigidBodyMotion d) (t : Time)
    (hR : DifferentiableAt ℝ (fun s => (M.orientation s).1) t) (i j : Fin d) :
    (omegaTensorAtQ M t j i).magnitude = -(omegaTensorAtQ M t i j).magnitude := by
  have h0 := congrFun (congrFun (M.angularVelocityTensor_transpose t hR) i) j
  simp only [Matrix.transpose_apply, Matrix.neg_apply] at h0
  exact h0

/-- **The conjugation stays inside the kind**: `Ω_body = Rᵀ Ω R`, and the
orientation's entries are dimensionless direction cosines — the frame change is
numeral work, so both tensors read at one kind. -/
theorem bodyOmegaTensorAtQ_conjugate (M : RigidBodyMotion d) (t : Time) (i j : Fin d) :
    (bodyOmegaTensorAtQ M t i j).magnitude =
      (((M.orientation t).1)ᵀ * M.angularVelocityTensor t * (M.orientation t).1) i j :=
  congrFun (congrFun (M.bodyAngularVelocityTensor_eq_orientation_conj t) i) j

/-! ## The velocity decomposition, through the edge -/

/-- A centre-of-mass velocity component. -/
@[kindIngest]
def comVelocityAtQ (M : RigidBodyMotion d) (t : Time) (i : Fin d) :
    Quantity velocityK ℝ :=
  .attest "a centre-of-mass velocity component" (M.centerOfMassVelocity t i)

/-- A body point's displacement from the moving centre of mass, in the lab frame. -/
@[kindIngest]
def relPositionAtQ (M : RigidBodyMotion d) (t : Time) (y : Space d) (j : Fin d) :
    Quantity displacementK ℝ :=
  .attest "the body point's displacement from the moving centre of mass"
    (M.displacement t y j - M.comTrajectory t j)

/-- An angular-velocity vector component (3-D — the dual of `Ω` under the hat map). -/
@[kindIngest]
def omegaVecAtQ (M : RigidBodyMotion 3) (t : Time) (i : Fin 3) :
    Quantity angularVelocityK ℝ :=
  .attest "an angular-velocity vector component — ω = Ωᵛ" (M.angularVelocity t i)

/-- The cross product, componentwise through the table: each component is two `ω·r`
edge products and one same-kind subtraction — nothing about `×` escapes the kind
algebra. -/
def crossCompQ (aq : Fin 3 → Quantity angularVelocityK ℝ)
    (bq : Fin 3 → Quantity displacementK ℝ) : Fin 3 → Quantity velocityK ℝ
  | 0 => Quantity.mul Metrology.angularVelocity_mul_displacement (aq 1) (bq 2)
      - Quantity.mul Metrology.angularVelocity_mul_displacement (aq 2) (bq 1)
  | 1 => Quantity.mul Metrology.angularVelocity_mul_displacement (aq 2) (bq 0)
      - Quantity.mul Metrology.angularVelocity_mul_displacement (aq 0) (bq 2)
  | 2 => Quantity.mul Metrology.angularVelocity_mul_displacement (aq 0) (bq 1)
      - Quantity.mul Metrology.angularVelocity_mul_displacement (aq 1) (bq 0)

/-- The kinded cross product's magnitude is Mathlib's `⨯₃` of the magnitudes. -/
theorem crossCompQ_magnitude (aq : Fin 3 → Quantity angularVelocityK ℝ)
    (bq : Fin 3 → Quantity displacementK ℝ) (i : Fin 3) :
    (crossCompQ aq bq i).magnitude =
      ((fun j => (aq j).magnitude) ⨯₃ (fun j => (bq j).magnitude)) i := by
  fin_cases i <;> simp [crossCompQ, cross_apply] <;> rfl

/-- **The Landau–Lifshitz decomposition, consumed at the kinded readings**:
`v = V + ω × r` — the sum same-kind, the cross through the edge, upstream's
`velocity_eq_angularVelocity` the proof. -/
theorem velocity_decomposes_through_the_edge (M : RigidBodyMotion 3) (y : Space 3)
    (t : Time) (i : Fin 3)
    (hR : Differentiable ℝ (fun s => (M.orientation s).1))
    (hX : Differentiable ℝ M.comTrajectory) :
    M.velocity y t i =
      (comVelocityAtQ M t i +
        crossCompQ (omegaVecAtQ M t) (relPositionAtQ M t y) i).magnitude := by
  rw [M.velocity_eq_angularVelocity y t i hR hX]
  show _ = (comVelocityAtQ M t i).magnitude +
    (crossCompQ (omegaVecAtQ M t) (relPositionAtQ M t y) i).magnitude
  rw [crossCompQ_magnitude]
  rfl

/-! ## The rotational energy, contracted through the table -/

/-- `½ ω·(I·ω)` — the rotational kinetic energy authored through the table: three
`I·ω → L` products (Feasibility's contraction), three `ω·L → 2T_rot` products, one
numeral. -/
def rotationalFromTableQ (R : RigidBody 3) (ωv : Fin 3 → ℝ) :
    Quantity rotationalKineticEnergyK ℝ :=
  (1 / 2 : ℝ) •
    (Quantity.mul Metrology.angularVelocity_mul_angularMomentum
        (omegaCompQ ωv 0) (angularMomentumFromTableQ R ωv 0)
      + Quantity.mul Metrology.angularVelocity_mul_angularMomentum
          (omegaCompQ ωv 1) (angularMomentumFromTableQ R ωv 1)
      + Quantity.mul Metrology.angularVelocity_mul_angularMomentum
          (omegaCompQ ωv 2) (angularMomentumFromTableQ R ωv 2))

/-- **The erasure**: the table-built contraction is upstream's
`rotationalKineticEnergy`, by its own `T = ½ ω·L` lemma and Feasibility's `L = I·ω`
closure. -/
theorem rotationalFromTableQ_erases (R : RigidBody 3) (ωv : Fin 3 → ℝ) :
    (rotationalFromTableQ R ωv).magnitude = R.rotationalKineticEnergy ωv := by
  rw [R.rotationalKineticEnergy_eq_angularMomentum]
  show 1 / 2 * (ωv 0 * (angularMomentumFromTableQ R ωv 0).magnitude
      + ωv 1 * (angularMomentumFromTableQ R ωv 1).magnitude
      + ωv 2 * (angularMomentumFromTableQ R ωv 2).magnitude) = _
  rw [angularMomentumFromTableQ_erases, angularMomentumFromTableQ_erases,
    angularMomentumFromTableQ_erases]
  simp [dotProduct, Fin.sum_univ_three]

/-! ## The motion preserves the readings -/

/-- The pushed-forward distribution's mass reading is the body's — the motion
preserves the zeroth moment. -/
theorem rbMassQ_motion_invariant (M : RigidBodyMotion d) (t : Time) :
    (rbMassQ (M.massDistribution t)).magnitude = (rbMassQ M.toRigidBody).magnitude :=
  M.massDistribution_mass t

/-- The moving distribution's centre-of-mass reading tracks the prescribed
trajectory — upstream's decisive wiring check, consumed at the ingest. -/
theorem comQ_tracks_the_trajectory (M : RigidBodyMotion d) (t : Time)
    (h : M.mass ≠ 0) (i : Fin d) :
    (comQ (M.massDistribution t) i).magnitude = M.comTrajectory t i :=
  congrArg (fun v : Space d => v i) (M.massDistribution_centerOfMass t h)

/-- The solid sphere's centre-of-mass reading is zero — `SolidSphere.lean`'s computed
moment, at the kinded reading. (Its inertia tensor is the subtree's one `sorry` —
the directory's patch-candidate slot.) -/
theorem comQ_solidSphere (m R : NNReal) (i : Fin d) :
    (comQ (RigidBody.solidSphere d m R) i).magnitude = 0 :=
  congrArg (fun v : Space d => v i) (RigidBody.solidSphere_centerOfMass m R)

end

end ForPhysLib.ClassicalMechanics.Kinded

end -- pkc-blanket-expose
end -- pkc-blanket
