/-
# The scorecard — the ladder and the five exhibits, re-derived

The prose makes claims in three places — `PLAN.md`'s Status lines and Ranking table,
`README.md`'s overview, the exhibits' own headers — and this module is where the part of
them a build can check is collected. Every theorem below is a *restatement*: its proof
term is the source declaration, so a claim that stops being true stops compiling here,
and the tables cannot quietly drift from the files.

The idiom is `CaseStudies/HarmonicOscillator/Scorecard.lean`'s, and so is its scope
rule: verdicts that are `#check_failure`-shaped — a term that should be rejected and is
not, or one that should elaborate and does not — stay in the files that state them,
because a rejection is witnessed by the build succeeding with the probe in place, not by
a term this module could import. What is collected here is the propositions.

## What the checked facts establish

1. **The ladder holds for its first directory.** Stage 0's distinctions are decided,
   Stage 1's laws are the two authored edges, Stage 2's crown theorem closes a kinded
   goal with the library's own metric-is-norm law, Stage 3's operator products erase.
2. **Each exhibit's headline verdict is a theorem.** A's contraction bridges to
   PhysLib's rotational energy; B discharges the API map's requirement 17 with
   PhysLib's own proof term; C proves `ω² = k/m` kinded and the one-definition/two-
   carrier law; D proves the total and refutes the under-count; E proves the Gaussian
   dimension coincidence against decided kind distinctness — the confirmation pair.
3. **The refusals stay where they were made.** Twenty-odd `#check_failure`s across the
   exhibits are cited by the headers, witnessed by their own files building.
-/

module

public import ForPhysLib.Kinds
public import ForPhysLib.Metrology
public import ForPhysLib.Kinded
public import ForPhysLib.Operators
public import ForPhysLib.Exhibits

public section -- pkc-blanket
@[expose] section -- pkc-blanket-expose

namespace ForPhysLib.Scorecard

open PropertyKindCalculus

/-! ## The ladder — `SpaceAndTime/Space`, Stages 0–3 -/

section Ladder
open Kinds.Space

/-- **Stage 0.** The API's own point/translation distinction, decided at the kind
layer: a position vector is not a displacement. -/
theorem stage0_position_ne_displacement : positionVector ≠ displacement :=
  positionVector_ne_displacement

/-- **Stage 0.** Comparability without identity: the pair the torsor relates are
mutually comparable as lengths while staying distinct kinds. -/
theorem stage0_comparable :
    MutuallyComparable Edge positionVector displacement :=
  positionVector_comparable_displacement

/-- **Stage 1.** The directory's two authored edges — the slice/cross-product structure
and the angle-as-ratio — as kind laws. -/
theorem stage1_edges :
    ProductKind length length area ∧ QuotientKind length length planeAngle :=
  ⟨Metrology.Space.length_mul_length, Metrology.Space.angle_is_length_ratio⟩

/-- **Stage 2, the crown.** The metric is the norm of the vsub, stated across two kinds
that stay distinct, closed by the library's own `dist_eq_norm_vsub`. -/
theorem stage2_crown {d : ℕ} (p q : _root_.Space d) :
    (Kinded.Space.distanceQ p q).magnitude
      = (Kinded.Space.lengthOf (Kinded.Space.displacementQ p q)).magnitude :=
  Kinded.Space.distanceQ_eq_lengthOf_displacementQ p q

/-- **Stage 3.** The operator-built area erases to the bare product of norms — the
table changed what elaborates, not what is computed. -/
theorem stage3_erasure {d : ℕ}
    (v w : Quantity Kinds.Space.displacement (EuclideanSpace ℝ (Fin d))) :
    (Operators.Space.spanArea v w).magnitude = ‖v.magnitude‖ * ‖w.magnitude‖ :=
  Operators.Space.spanArea_magnitude v w

end Ladder

/-! ## Exhibit A — RigidBody -/

section ExhibitA
open Exhibits.RigidBody

/-- **A's bridge.** The kinded body-frame contraction *is* PhysLib's rotational kinetic
energy, doubled — the ceremony bought the frame and kind gates and changed nothing
computed. -/
theorem exhibitA_bridge (M : RigidBodyMotion 3) (t : Time) :
    (rotationalContraction inertia_mul_angularVelocity angularVelocity_mul_angularMomentum
        (bodyInertia M) (bodyOmega M t)).components
      = 2 * M.toRigidBody.rotationalKineticEnergy (M.bodyAngularVelocity t) :=
  rotationalContraction_eq_physlib M t

/-- **A's generality.** `sumFin` is `Finset.sum`, the lemma that made the bridge a
two-line computation at any dimension. -/
theorem exhibitA_sumFin {n : ℕ} (v : Fin n → ℝ) : sumFin v = ∑ i, v i :=
  sumFin_eq_sum v

end ExhibitA

/-! ## Exhibit B — ReferenceFrame -/

section ExhibitB
open Exhibits.ReferenceFrame ClassicalMechanics

/-- **B's discharge of requirement 17.** The defining property of an inertial frame's
origin velocity — listed `done: false` in the API map — proved with PhysLib's own proof
term, every erasure a visible `.magnitude`. -/
theorem exhibitB_requirement17 {d : ℕ} (F : ReferenceFrame d) (h : F.IsInertial)
    (t₁ t₂ : Time) :
    (Kinded.Space.displacementQ (F.origin t₂) (F.origin t₁)).magnitude
      = (elapsedQ t₁ t₂).magnitude • (frameVelocityQ h).magnitude :=
  origin_displacement_eq F h t₁ t₂

/-- **B's finding, typed.** The three candidate transformation laws inhabit one type —
the fact that makes requirement 16 unsatisfiable as written. Stated here as the triple
PhysLib's `Vector` cannot refuse. -/
noncomputable def exhibitB_three_laws_one_type (F G : ReferenceFrame 3) (t : Time)
    (u : EuclideanSpace ℝ (Fin 3)) :
    (F.Vector → G.Vector) × (F.Vector → G.Vector) × (F.Vector → G.Vector) :=
  (geometricTransport F G t, boostTransport F G t u, originShiftTransport F G t)

end ExhibitB

/-! ## Exhibit C — HarmonicOscillator -/

section ExhibitC
open Exhibits.HarmonicOscillator
open scoped PropertyKindCalculus.OperatorTable

/-- **C's frequency law.** `ω² = k/m`, kinded, with PhysLib's own proof term — and the
reciprocal `m/k` unwritable in the file that proves it. -/
theorem exhibitC_omega_sq (S : KOscillator) :
    S.ω.magnitude ^ 2 = (S.k / S.m).magnitude :=
  S.ω_sq

/-- **C's carrier law, at the specification carrier.** One definition, and its
magnitude law is a single `rfl` — here instantiated at `ℝ`… -/
theorem exhibitC_magnitude_real (half : ℝ)
    (m : Quantity massK ℝ) (v : Quantity velK ℝ) :
    (kineticE half m v).magnitude
      = half * (m.magnitude * (v.magnitude * v.magnitude)) :=
  kineticE_magnitude half m v

/-- **…and at the executable carrier.** The same theorem at genuine IEEE binary32 —
the MR27 agreement is the quantifier, not a second proof. -/
theorem exhibitC_magnitude_float32 (half : Float32)
    (m : Quantity massK Float32) (v : Quantity velK Float32) :
    (kineticE half m v).magnitude
      = half * (m.magnitude * (v.magnitude * v.magnitude)) :=
  kineticE_magnitude half m v

end ExhibitC

/-! ## Exhibit D — TwoRovers -/

section ExhibitD
open Exhibits.TwoRovers

/-- **D's artifact 1.** The stated total mass of rover 1 is the assembled sum of its
own parts — a theorem, so a changed parts list changes what must be proved. -/
theorem exhibitD_total :
    rover1TotalMass.magnitude = (assemble rover1 rover1Masses).magnitude :=
  rover1_total_is_sum

/-- **D's artifact 3.** The nine-part sum that drops a wheel is provably not the
total: under-counting is caught, not tolerated. -/
theorem exhibitD_undercount :
    ([RoverPart.chassis, .mast, .wheelFL, .wheelFR, .wheelRL,
      .motorFL, .motorFR, .motorRL, .motorRR].foldr
        (fun p acc => (rover1Masses p).magnitude + acc) 0)
      ≠ rover1TotalMass.magnitude :=
  undercount_caught

/-- **D's identity.** One catalogue entry for the fleet — Dybkær §20 dedicates to the
*sort* — while the two chassis remain distinct *objects*, which is what makes rover 1's
chassis mass and rover 2's different quantity types (artifact 2a's `#check_failure`). -/
theorem exhibitD_identity :
    chassisMassDK.systematicTerm = "rover — chassis ; mass"
      ∧ partOf rover1 .chassis ≠ partOf rover2 .chassis :=
  ⟨chassisMassDK_term, chassis_objects_distinct⟩

end ExhibitD

/-! ## Exhibit E — Electromagnetism -/

section ExhibitE
open Exhibits.Electromagnetism

/-- **E's confirmation pair, half one.** Over the Gaussian basis the dimensions of `E`
and `B` provably coincide — the `WithDim` repair of the abbreviation problem is
basis-relative. -/
theorem exhibitE_dimensions_coincide : dimE = dimB :=
  gaussian_dimensions_coincide

/-- **Half two.** The kinds stay apart over the same basis: kind identity is
examination, not exponents. Together the pair is MR4 on a directory that exercises the
parametric bases. -/
theorem exhibitE_kinds_apart : electricFieldK ≠ magneticFieldK :=
  kinds_stay_apart

/-- **E's levels.** dBm and dBW are distinct kinds — the reference is kind identity —
while their gains are one kind, the reference cancelling in every difference. -/
theorem exhibitE_levels : dBm.toKind ≠ dBW.toKind ∧ dBm.gainKind = dBW.gainKind :=
  ⟨dBm_ne_dBW, gain_shared⟩

/-- **E's link budget, re-derived.** 30 dBm, +3 dB, −100 dB, +2 dB → −65 dBm, exact at
`Int`: levels shift by gains, and nothing else was ever writable. -/
theorem exhibitE_link_budget :
    dBm.shift (dBm.shift (dBm.shift (⟨30⟩ : Quantity dBm.toKind Int) ⟨3⟩) ⟨-100⟩) ⟨2⟩
      = ⟨-65⟩ := rfl

/-- **E's curation contrast, the licensed side.** The AC powers are mutually comparable
— which is exactly what does *not* license their sum: `P + Q` stays a `#check_failure`
in the exhibit while this comparability holds. -/
theorem exhibitE_comparable_yet_refused :
    MutuallyComparable PowerEdge activePowerK reactivePowerK :=
  active_comparable_reactive

end ExhibitE

end ForPhysLib.Scorecard

end -- pkc-blanket-expose
end -- pkc-blanket
