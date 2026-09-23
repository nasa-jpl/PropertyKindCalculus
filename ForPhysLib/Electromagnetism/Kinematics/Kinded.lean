/-
# Stage 2 — kinded re-authoring of `Physlib/Electromagnetism/Kinematics`

The third rung of [the adoption ladder](../../PLAN.md#stage-2-kinded-re-authoring-with-definitional-erasure)
for the campaign's second directory: the chain re-authored with every quantity at its
kind and the naked form recovered definitionally (or by upstream's own lemma, where the
source's spelling is the one that needs respelling).

**The re-authoring follows the chain's own derivation order.**

* **The slices.** `vectorPotentialQ` and Feasibility's `scalarPotentialQ` — the two
  time-sliced readings of the one homogeneous four-potential, each a named crossing
  (`timeSlice` re-parameterizes by `c·t ↦ t`, a dimensionful move no table sees; the
  scalar slice additionally multiplies by `c`, the velocity edge).
* **The electric field, built from its parts.** `−∇φ` and `∂ₜ𝐀` as two attested
  derivative crossings — each the Stage-1 edge its formula writes, ridden through
  Mathlib's `fderiv` where no table sees it — and `electricFieldFromPotentialsQ` their
  *same-kind* difference, erasing to upstream's `electricField` definitionally. The
  gradient crossing's docstring carries the scale fact: the derivative of the
  interval-scale potential is a difference quotient, so the field is ratio-scale and
  reference-free.
* **The magnetic field.** The curl crossing (3-D) and the matrix reading (general `d`),
  both `rfl`-erasing.
* **The chart and the extent.** `derivQ` at the gauge-dependent entry kind,
  `fieldStrengthQ`/`fieldStrengthMatrixQ` at the frame-covariant one — the
  antisymmetrization between them is the crossing that *erases the gauge dependence*,
  and `pureGauge_extent_zero` is its witness: a pure translation has zero extent (the
  torsor fact, at the tensor). The frame-bound fields then come off the tensor exactly
  as Stage 1's edges say: `electricReadingQ` is `−c·F⁰ⁱ` through the registered
  velocity edge (erasure by upstream's `electricField_eq_toFieldStrength_eval`), and
  `magneticReadingQ` is the spatial block read in the frame the slicing chose
  (erasure by `toFieldStrength_eval_inr_inr_eq_magneticFieldMatrix`).
* **The boost's other half.** Feasibility delivered the electric law; this stage adds
  the magnetic mirror — `B' = γ(B + (β/c)·E)` through the downward edge — and the
  invariance of the transverse-transverse block, closing MR18's ledger: under a boost
  the tensor's kind is fixed, both frame-bound readings mix through the velocity edge,
  and the block the boost cannot reach does not move.
* **Gauge invariance reaches the fields — two theorems upstream does not state.**
  Upstream proves the *tensor* gauge-invariant; the chain's `electricField` and
  `magneticFieldMatrix` inherit that invariance, but no upstream lemma says so. Proved
  here (`electricField_gaugeTransform`, `magneticFieldMatrix_gaugeTransform`) and then
  consumed at the kinded readings: the gauge shift moves the potential and nothing
  downstream of the extent. A candidate patch, in the pilot's orthonormality pattern —
  the offer upstream is a human's to make (AI-POLICY §3.1).
-/

module

public import ForPhysLib.Electromagnetism.Kinematics.Metrology
meta import ForPhysLib.Electromagnetism.Kinematics.Metrology
public import ForPhysLib.Electromagnetism.Kinematics.Feasibility
meta import ForPhysLib.Electromagnetism.Kinematics.Feasibility

@[expose] public section

open PropertyKindCalculus
open Space Time SpaceTime TensorProduct
open TensorSpecies Tensor Tensorial
open ForPhysLib.Electromagnetism.Kinematics
open ForPhysLib.Electromagnetism.Kinematics.Kinds

namespace ForPhysLib.Electromagnetism.Kinematics.Kinded

open scoped PropertyKindCalculus.OperatorTable

local notation "EMPot " d:max => _root_.Electromagnetism.ElectromagneticPotential d

variable {d : ℕ}

noncomputable section

/-! ## One vocabulary

`Feasibility.lean`'s probe kinds and Stage 0's literals are the *same* kinds,
definitionally — the probe looked them up from the catalogue, Stage 0 copied them from
it, and both routes land on one literal. Stated once, so everything below may freely
compose Feasibility's quantities with the Stage-0 and Stage-1 vocabulary. -/

example : vectorPotentialK = magneticVectorPotential := rfl
example : electricPotentialK = electricPotential := rfl
example : potentialDifferenceK = electricPotentialDifference := rfl
example : electricFieldK = electricFieldStrength := rfl
example : magneticFluxDensityK = magneticFluxDensity := rfl
example : magneticFluxK = magneticFlux := rfl
example : speedOfLightK = speedOfLight := rfl

/-! ## The slices -/

/-- The vector-potential slice — the spatial components at the same kind,
re-parameterized by `timeSlice` (`c·t ↦ t`, a dimensionful move no table sees). The
scalar slice is Feasibility's `scalarPotentialQ`, which additionally multiplies by
`c` — the velocity edge. -/
@[kindCrossing]
def vectorPotentialQ (cq : Quantity speedOfLightK SpeedOfLight)
    (Aq : Quantity vectorPotentialK (EMPot d)) :
    Quantity vectorPotentialK (Time → Space d → EuclideanSpace ℝ (Fin d)) :=
  .attest "the spatial slice — same kind; timeSlice re-parameterizes by c·t ↦ t"
    (Aq.magnitude.vectorPotential cq.magnitude)

theorem vectorPotentialQ_magnitude (cS : SpeedOfLight) (A : EMPot d) :
    (vectorPotentialQ (speedQ cS) (potentialQ A)).magnitude =
      A.vectorPotential cS := rfl

/-! ## The electric field, built from its parts -/

/-- `−∇φ` — the gradient crossing of `E = −∇φ − ∂ₜ𝐀`. The Stage-1 edge is stated at
the potential's *differences*: the derivative of the interval-scale potential is a
difference quotient, so the gradient eats the gauge reference and lands ratio-scale.
The `∇` itself is Mathlib's `fderiv`, which no table sees — attested once. -/
@[kindCrossing]
def negGradScalarQ (cq : Quantity speedOfLightK SpeedOfLight)
    (Aq : Quantity vectorPotentialK (EMPot d)) :
    Quantity electricFieldK (Time → Space d → EuclideanSpace ℝ (Fin d)) :=
  .attest "−∇φ — the difference-quotient edge, ridden through Mathlib's fderiv"
    (fun t x => - ∇ (Aq.magnitude.scalarPotential cq.magnitude t) x)

/-- `∂ₜ𝐀` — the time-derivative crossing of the same equation: a vector potential per
duration is an electric field (the Stage-1 edge), the `∂ₜ` again Mathlib's. -/
@[kindCrossing]
def timeDerivVectorQ (cq : Quantity speedOfLightK SpeedOfLight)
    (Aq : Quantity vectorPotentialK (EMPot d)) :
    Quantity electricFieldK (Time → Space d → EuclideanSpace ℝ (Fin d)) :=
  .attest "∂ₜ𝐀 — the per-duration edge, ridden through Mathlib's fderiv"
    (fun t x => ∂ₜ (fun t => Aq.magnitude.vectorPotential cq.magnitude t x) t)

/-- **The electric field is a same-kind difference** — no join needed anywhere in the
chain (the Stage-0 finding): both derivative routes land at 6-10 and the subtraction
is homogeneous. -/
def electricFieldFromPotentialsQ (cq : Quantity speedOfLightK SpeedOfLight)
    (Aq : Quantity vectorPotentialK (EMPot d)) :
    Quantity electricFieldK (Time → Space d → EuclideanSpace ℝ (Fin d)) :=
  negGradScalarQ cq Aq - timeDerivVectorQ cq Aq

/-- **The erasure** — the built field *is* upstream's `electricField`,
definitionally. -/
theorem electricFieldFromPotentialsQ_magnitude (cS : SpeedOfLight) (A : EMPot d) :
    (electricFieldFromPotentialsQ (speedQ cS) (potentialQ A)).magnitude =
      A.electricField cS := rfl

/-! ## The magnetic field -/

/-- `∇×𝐀` — the curl crossing (3-D): a vector potential per space-length lands at the
flux density (the Stage-1 edge), the curl Mathlib's. -/
@[kindCrossing]
def magneticFieldFromPotentialQ (cq : Quantity speedOfLightK SpeedOfLight)
    (Aq : Quantity vectorPotentialK (EMPot 3)) :
    Quantity magneticFluxDensityK (_root_.Electromagnetism.MagneticField 3) :=
  .attest "∇×𝐀 — the curl edge, ridden through Mathlib's fderiv"
    (Aq.magnitude.magneticField cq.magnitude)

theorem magneticFieldFromPotentialQ_magnitude (cS : SpeedOfLight)
    (A : EMPot 3) :
    (magneticFieldFromPotentialQ (speedQ cS) (potentialQ A)).magnitude =
      A.magneticField cS := rfl

/-- The magnetic-field matrix in general `d` — the tensor's spatial block, sliced. -/
@[kindCrossing]
def magneticFieldMatrixQ (cq : Quantity speedOfLightK SpeedOfLight)
    (Aq : Quantity vectorPotentialK (EMPot d)) :
    Quantity magneticFluxDensityK (Time → Space d → (Fin d × Fin d) → ℝ) :=
  .attest "the spatial block of the tensor, read in the frame the slicing chose"
    (Aq.magnitude.magneticFieldMatrix cq.magnitude)

theorem magneticFieldMatrixQ_magnitude (cS : SpeedOfLight) (A : EMPot d) :
    (magneticFieldMatrixQ (speedQ cS) (potentialQ A)).magnitude =
      A.magneticFieldMatrix cS := rfl

/-! ## The chart and the extent -/

/-- The derivative tensor `∂_μ A^ν` at the **gauge-dependent** chart kind — a vector
potential per spacetime coordinate (a length: `x⁰ = c·t`), before the
antisymmetrization that would erase the gauge dependence. -/
@[kindCrossing]
def derivQ (Aq : Quantity vectorPotentialK (EMPot d)) :
    Quantity potentialGradient
      (SpaceTime d → Lorentz.CoVector d ⊗[ℝ] Lorentz.Vector d) :=
  .attest "∂_μ A^ν — the per-coordinate chart; gauge-dependent until antisymmetrized"
    Aq.magnitude.deriv

theorem derivQ_magnitude (A : EMPot d) :
    (derivQ (potentialQ A)).magnitude = A.deriv := rfl

/-- The field strength `F^{μν}` at the **frame-covariant, gauge-invariant** extent
kind: `η∂A − η∂A` — the antisymmetrization is the chart → extent crossing, and it is
exactly the move that erases the gauge dependence (`pureGauge_extent_zero` below). -/
@[kindCrossing]
def fieldStrengthQ (Aq : Quantity vectorPotentialK (EMPot d)) :
    Quantity fieldStrength (SpaceTime d → Lorentz.Vector d ⊗[ℝ] Lorentz.Vector d) :=
  .attest "η∂A − η∂A — the antisymmetrization erases the gauge dependence"
    Aq.magnitude.toFieldStrength

theorem fieldStrengthQ_magnitude (A : EMPot d) :
    (fieldStrengthQ (potentialQ A)).magnitude = A.toFieldStrength := rfl

/-- The tensor in the standard basis, at the same extent kind. -/
@[kindCrossing]
def fieldStrengthMatrixQ (Aq : Quantity vectorPotentialK (EMPot d)) :
    Quantity fieldStrength
      (SpaceTime d → (Fin 1 ⊕ Fin d) × (Fin 1 ⊕ Fin d) → ℝ) :=
  .attest "the extent in the standard basis"
    (fun x μν => toField {Aq.magnitude.toFieldStrength x | [μν.1] [μν.2]}ᵀ)

/-- **A pure translation has zero extent** — the torsor fact at the tensor: shifting
the zero potential by any gauge function produces a potential whose field strength
vanishes (upstream's `toFieldStrength_ofGradient`, consumed at the kinded reading). -/
theorem pureGauge_extent_zero (χ : SpaceTime d → ℝ) (hχ : ContDiff ℝ 2 χ)
    (x : SpaceTime d) :
    (fieldStrengthQ (gaugeShiftQ (potentialQ 0) (gaugeFnQ χ))).magnitude x = 0 := by
  show (_root_.Electromagnetism.ElectromagneticPotential.gaugeTransform χ 0).toFieldStrength x = 0
  rw [show _root_.Electromagnetism.ElectromagneticPotential.gaugeTransform χ (0 : EMPot d)
      = _root_.Electromagnetism.ElectromagneticPotential.ofGradient χ from zero_add _]
  exact _root_.Electromagnetism.ElectromagneticPotential.toFieldStrength_ofGradient hχ x

/-! ## The frame-bound readings, off the tensor -/

/-- A pointwise extent entry, read at its kind. -/
@[kindIngest]
def fieldStrengthAtQ (A : EMPot d) (x : SpaceTime d)
    (μν : (Fin 1 ⊕ Fin d) × (Fin 1 ⊕ Fin d)) : Quantity fieldStrength ℝ :=
  .attest "pointwise reading of the chain's field-strength components"
    (toField {A.toFieldStrength x | [μν.1] [μν.2]}ᵀ)

/-- **The electric reading** — `E_i = −c·F⁰ⁱ`: the velocity edge one level up, taken
through Stage 1's registered law at the call site; the sign is a numeral. -/
def electricReadingQ (cS : SpeedOfLight) (A : EMPot d) (x : SpaceTime d)
    (i : Fin d) : Quantity electricFieldK ℝ :=
  (-1 : ℝ) • Quantity.mul Metrology.speedOfLight_mul_fieldStrength (speedRQ cS)
    (fieldStrengthAtQ A x (Sum.inl 0, Sum.inr i))

/-- **The erasure** — upstream's own tensor-to-field lemma closes it: at the sliced
point, the reading *is* the chain's `electricField`. -/
theorem electricReadingQ_erases (cS : SpeedOfLight) (A : EMPot d)
    (hA : Differentiable ℝ A) (t : Time) (x : Space d) (i : Fin d) :
    (electricReadingQ cS A ((toTimeAndSpace cS).symm (t, x)) i).magnitude =
      A.electricField cS t x i := by
  rw [_root_.Electromagnetism.ElectromagneticPotential.electricField_eq_toFieldStrength_eval
    A t x i hA]
  show (-1 : ℝ) * (cS.val *
    toField {A.toFieldStrength ((toTimeAndSpace cS).symm (t, x)) | [Sum.inl 0] [Sum.inr i]}ᵀ) = _
  ring

/-- **The magnetic reading** — the spatial block *is* the magnetic field matrix: a
crossing, not an edge, because what changes is only the frame bookkeeping
(`timeSlice`'s re-parameterization), attested once. -/
@[kindCrossing]
def magneticReadingQ (Fq : Quantity fieldStrength ℝ) :
    Quantity magneticFluxDensityK ℝ :=
  .attest "the spatial block read in the frame the slicing chose — same number, framed"
    Fq.magnitude

/-- **The erasure** — upstream's block identification closes it (the frame enters
through the slicing on the right-hand side, not through the crossing). -/
theorem magneticReadingQ_erases (cS : SpeedOfLight) (A : EMPot d)
    (x : SpaceTime d) (i j : Fin d) :
    (magneticReadingQ (fieldStrengthAtQ A x (Sum.inr i, Sum.inr j))).magnitude =
      A.magneticFieldMatrix cS (x.time cS) x.space (i, j) :=
  _root_.Electromagnetism.ElectromagneticPotential.toFieldStrength_eval_inr_inr_eq_magneticFieldMatrix
    A x i j

/-! ## The boost's other half -/

/-- The boosted magnetic entry, kinded: `γ·(B + (β·E)/c)` — the *downward* mixing,
through Stage 1's `electricFieldStrength / speedOfLight` edge at the call site. -/
def boostedBQ (γv β : ℝ) (cq : Quantity speedOfLightK ℝ)
    (B : Quantity magneticFluxDensityK ℝ) (E : Quantity electricFieldK ℝ) :
    Quantity magneticFluxDensityK ℝ :=
  γv • (B + (Quantity.div Metrology.electricFieldStrength_div_speedOfLight (β • E) cq :
    Quantity magneticFluxDensityK ℝ))

/-- The composite's magnitude, spelled out. -/
theorem boostedBQ_magnitude (γv β : ℝ) (cq : Quantity speedOfLightK ℝ)
    (B : Quantity magneticFluxDensityK ℝ) (E : Quantity electricFieldK ℝ) :
    (boostedBQ γv β cq B E).magnitude =
      γv * (B.magnitude + (β * E.magnitude) / cq.magnitude) := rfl

/-- The kinded combination erases to the boost law's right-hand side, at any
evaluation point. -/
theorem boostedBQ_erases (γv β : ℝ) (cS : SpeedOfLight) (A : EMPot d)
    (t : Time) (x : Space d) (ij : Fin d × Fin d) (i : Fin d) :
    (boostedBQ γv β (speedRQ cS)
      (magneticMatrixAtQ cS A t x ij) (electricFieldAtQ cS A t x i)).magnitude =
      γv * (A.magneticFieldMatrix cS t x ij + β / cS.val * A.electricField cS t x i) := by
  rw [boostedBQ_magnitude, magneticMatrixAtQ_magnitude, electricFieldAtQ_magnitude,
    speedRQ_magnitude]
  ring

/-- **The magnetic mirror of Feasibility's F4c** — upstream's boost law for the
magnetic entries closes the kinded combination: the electric term reaches the magnetic
kind only through the downward velocity edge. -/
theorem boost_reads_back_through_the_edge {d : ℕ} (β : ℝ) (hβ : |β| < 1)
    (cS : SpeedOfLight) (A : EMPot d.succ) (hA : Differentiable ℝ A)
    (t : Time) (x : Space d.succ) (i : Fin d) :
    let t' : Time := LorentzGroup.γ β * (t.val + β / cS * x 0)
    let x' : Space d.succ := ⟨fun
      | 0 => LorentzGroup.γ β * (x 0 + cS * β * t.val)
      | ⟨Nat.succ n, ih⟩ => x ⟨Nat.succ n, ih⟩⟩
    (LorentzGroup.boost (d := d.succ) 0 β hβ • A).magneticFieldMatrix cS t x (0, i.succ) =
      (boostedBQ (LorentzGroup.γ β) β (speedRQ cS)
        (magneticMatrixAtQ cS A t' x' (0, i.succ))
        (electricFieldAtQ cS A t' x' i.succ)).magnitude := by
  intro t' x'
  have h := _root_.Electromagnetism.ElectromagneticPotential.magneticFieldMatrix_apply_x_boost_zero_succ
    (c := cS) β hβ A hA t x i
  simp only at h
  rw [h, boostedBQ_erases]
  rfl

/-- **The block the boost cannot reach does not move** — the transverse-transverse
entries are invariant (upstream's third boost law): no mixing, no edge, the same kind
on both sides. MR18's ledger closes: the tensor's kind is fixed, the two frame-bound
readings mix through one velocity edge, and this block is untouched. -/
theorem boost_fixes_transverse_block {d : ℕ} (β : ℝ) (hβ : |β| < 1)
    (cS : SpeedOfLight) (A : EMPot d.succ) (hA : Differentiable ℝ A)
    (t : Time) (x : Space d.succ) (i j : Fin d) :
    let t' : Time := LorentzGroup.γ β * (t.val + β / cS * x 0)
    let x' : Space d.succ := ⟨fun
      | 0 => LorentzGroup.γ β * (x 0 + cS * β * t.val)
      | ⟨Nat.succ n, ih⟩ => x ⟨Nat.succ n, ih⟩⟩
    (LorentzGroup.boost (d := d.succ) 0 β hβ • A).magneticFieldMatrix cS t x (i.succ, j.succ) =
      (magneticMatrixAtQ cS A t' x' (i.succ, j.succ)).magnitude := by
  intro t' x'
  have h := _root_.Electromagnetism.ElectromagneticPotential.magneticFieldMatrix_apply_x_boost_succ_succ
    (c := cS) β hβ A hA t x i j
  simp only at h
  rw [h]
  rfl

/-! ## Gauge invariance reaches the fields

Upstream proves the *tensor* gauge-invariant (`toFieldStrength_eval_gaugeTransform`);
the chain's derived fields inherit the invariance, but no upstream lemma states it.
The two theorems below are that gap closed — a candidate patch, in the pilot's
orthonormality pattern — and the kinded corollary consumes them at the readings. -/

/-- The gauge shift of a differentiable potential is differentiable. -/
theorem gaugeTransform_differentiable (A : EMPot d) (χ : SpaceTime d → ℝ)
    (hA : Differentiable ℝ A) (hχ : ContDiff ℝ 2 χ) :
    Differentiable ℝ (_root_.Electromagnetism.ElectromagneticPotential.gaugeTransform χ A) := by
  have h : ⇑(_root_.Electromagnetism.ElectromagneticPotential.gaugeTransform χ A)
      = fun x => A x + _root_.Electromagnetism.ElectromagneticPotential.ofGradient χ x := rfl
  rw [h]
  exact hA.add
    (_root_.Electromagnetism.ElectromagneticPotential.differentiable_ofGradient hχ)

/-- **The electric field is gauge-invariant** — inherited from the tensor's
invariance through `electricField_eq_toFieldStrength_eval`; not stated upstream. -/
theorem electricField_gaugeTransform (cS : SpeedOfLight) (A : EMPot d)
    (χ : SpaceTime d → ℝ) (hA : Differentiable ℝ A) (hχ : ContDiff ℝ 2 χ)
    (t : Time) (x : Space d) (i : Fin d) :
    (_root_.Electromagnetism.ElectromagneticPotential.gaugeTransform χ A).electricField
      cS t x i = A.electricField cS t x i := by
  rw [_root_.Electromagnetism.ElectromagneticPotential.electricField_eq_toFieldStrength_eval
      _ t x i (gaugeTransform_differentiable A χ hA hχ),
    _root_.Electromagnetism.ElectromagneticPotential.electricField_eq_toFieldStrength_eval
      A t x i hA,
    _root_.Electromagnetism.ElectromagneticPotential.toFieldStrength_eval_gaugeTransform
      A χ hA hχ]

/-- **The magnetic-field matrix is gauge-invariant** — same inheritance; not stated
upstream. -/
theorem magneticFieldMatrix_gaugeTransform (cS : SpeedOfLight) (A : EMPot d)
    (χ : SpaceTime d → ℝ) (hA : Differentiable ℝ A) (hχ : ContDiff ℝ 2 χ)
    (t : Time) (x : Space d) (ij : Fin d × Fin d) :
    (_root_.Electromagnetism.ElectromagneticPotential.gaugeTransform χ A).magneticFieldMatrix
      cS t x ij = A.magneticFieldMatrix cS t x ij := by
  simp only [_root_.Electromagnetism.ElectromagneticPotential.magneticFieldMatrix_eq,
    _root_.Electromagnetism.ElectromagneticPotential.toFieldStrength_eval_gaugeTransform
      A χ hA hχ]

/-- **The kinded corollary**: shifting the potential through the torsor moves nothing
downstream of the extent — the kinded electric reading of the shifted potential is the
original's. -/
theorem electricFieldAtQ_gauge_invariant (cS : SpeedOfLight) (A : EMPot d)
    (χ : SpaceTime d → ℝ) (hA : Differentiable ℝ A) (hχ : ContDiff ℝ 2 χ)
    (t : Time) (x : Space d) (i : Fin d) :
    (electricFieldAtQ cS ((gaugeShiftQ (potentialQ A) (gaugeFnQ χ)).magnitude) t x i).magnitude =
      (electricFieldAtQ cS A t x i).magnitude :=
  electricField_gaugeTransform cS A χ hA hχ t x i

/-! ## The emission boundary -/

/-- The emission boundary, stated once as a `def` so it carries its tier: downstream
code that wants the naked field gets it here. -/
@[kindEmission]
def rawElectricField (cS : SpeedOfLight) (A : EMPot d) :
    Time → Space d → EuclideanSpace ℝ (Fin d) :=
  let eq := electricFieldFromPotentialsQ (speedQ cS) (potentialQ A)
  eq.magnitude

end

end ForPhysLib.Electromagnetism.Kinematics.Kinded

