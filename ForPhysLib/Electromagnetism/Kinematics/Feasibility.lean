/-
# The EM/Kinematics directory — feasibility, before the ladder

**Source.** `Physlib/Electromagnetism/Kinematics/` — the eight-file chain rooted at
`EMPotential.lean`, imported and probed directly. The campaign's second directory — see
`PLAN.md`, "Directory 2: `Electromagnetism/Kinematics`".

Five capability questions, answered as build artifacts before any ladder stage is
climbed. The spine they share: the library's spacetime coordinate is `x⁰ = c·t` — a
*length* — so the `φ/c` in `ofPotentials` is not a convention but the move that makes
the four-vector `A^μ = (φ/c, 𝐀)` a *single kind* (the magnetic vector potential,
item 6-32), and the chain is one homogeneous object being read back into frame-bound
kinds through one velocity edge.

* **F1 — the classical-field carrier.** `Quantity` stands up at
  `Time → Space d → EuclideanSpace ℝ (Fin d)` (one `Carrier` instance serves `E` and
  `B`, because upstream the two are *the same abbreviation*) and at the structure
  `ElectromagneticPotential d` (upstream's own `AddCommGroup`). The chain's own derived
  magnetic field is accepted where an electric field is expected; the kinded readings
  refuse the swap.
* **F2 — one homogeneous tensor, two readings, one velocity edge.** The `/c` pinned at
  `ofPotentials`'s time component; `scalarPotential = c·A⁰` as the attested 6-32 → 6-11
  crossing, with upstream's own round-trip lemma closing the kinded one. The catalogue's
  scales adjudicate the edge's target: electric potential (6-11.1) is *interval*-scale,
  so the ratio table refuses it and the registered edge lands at its ratio-scale sibling
  (6-11.2) — the potential/potential-difference split upstream's `ℝ` cannot see.
* **F3 — the silent numeral, now load-bearing.** `(c : SpeedOfLight := 1)` defaults at
  every definition in the chain; pinned at a bare call site. The kinded chain never
  defaults: `c` is a declared quantity threaded explicitly through every reading.
* **F4 — boosts are the forced joins.** `E'_⊥ = γ(E + cβ·B)` sums an electric-field
  reading with a velocity-scaled magnetic one — kinded, the sum elaborates *only*
  through the registered velocity edge (`E + B` directly is refused), and upstream's own
  boost lemma closes the erasure. MR18 at theorem scale: the mixing is licensed exactly
  where the physics mixes.
* **F5 — gauge freedom is the interval scale, and χ is a flux.** `∂^μχ` lands at 6-32,
  so the gauge function is a *magnetic flux* field (6-22.1 — a lookup, not a mint);
  `gaugeTransform` is the torsor translation, upstream's `toFieldStrength_gaugeTransform`
  the proof that the field strength is the reference-free extent.

The Stage-0 vocabulary here is **lookups only** — every kind this file needs is in
IEC 80000-6. The one expected mint, deferred to `Kinds.lean` with the ladder: the
field-strength tensor's *entry* kind, the frame-covariant carrier the standard does not
list because the standard catalogues frame-bound readings.
-/

module

public import Physlib.Electromagnetism.Kinematics.Boosts
meta import Physlib.Electromagnetism.Kinematics.Boosts
public import Physlib.Electromagnetism.Kinematics.GaugeTransformation
meta import Physlib.Electromagnetism.Kinematics.GaugeTransformation
public import Physlib.Electromagnetism.Basic
meta import Physlib.Electromagnetism.Basic
public import PropertyKindCalculus.BoundaryAudit
meta import PropertyKindCalculus.BoundaryAudit
public import PropertyKindCalculus.KindAlgebra
meta import PropertyKindCalculus.KindAlgebra
public import PropertyKindCalculus.QuantityReal
meta import PropertyKindCalculus.QuantityReal
public import PropertyKindCalculus.Iso80000.Part6
meta import PropertyKindCalculus.Iso80000.Part6

@[expose] public section

namespace ForPhysLib.Electromagnetism.Kinematics

open PropertyKindCalculus
open PropertyKindCalculus.Iso80000

-- PhysLib's potential, qualified past this file's own namespace.
local notation "EMPot " d:max => _root_.Electromagnetism.ElectromagneticPotential d

/-! ## The kind vocabulary — lookups only

Every kind this file needs is a catalogue item; nothing is minted. The contrast with
the pilot (whose radicand chain and momentum-squared kind the standard does not list)
is itself a finding: the kinematics chain's vocabulary *is* IEC 80000-6's. -/

/-- The four-potential's kind — magnetic vector potential, item 6-32 (`A`, Wb/m).
The whole Lorentz vector sits at this one kind: `A⁰ = φ/c` is *made* homogeneous with
the spatial components by the `/c` (F2 pins it). -/
def vectorPotentialK : KindOfProperty := (Part6.magneticVectorPotential).kind

/-- Electric potential, item 6-11.1 — **interval-scale in the catalogue itself**:
fixed only up to gauge freedom. The scale is load-bearing below (the ratio table
refuses to target it). -/
def electricPotentialK : KindOfProperty := (Part6.electricPotential).kind

/-- Electric potential difference, item 6-11.2 — the ratio-scale sibling; the physical
extent, and the only member of the 6-11 family a table edge may land on. -/
def potentialDifferenceK : KindOfProperty := (Part6.electricPotentialDifference).kind

/-- Electric field strength, item 6-10 (`E`, V/m). -/
def electricFieldK : KindOfProperty := (Part6.electricFieldStrength).kind

/-- Magnetic flux density, item 6-21 (`B`, T). -/
def magneticFluxDensityK : KindOfProperty := (Part6.magneticFluxDensity).kind

/-- Magnetic flux, item 6-22.1 (`Φ`, Wb) — the gauge function's kind (F5). -/
def magneticFluxK : KindOfProperty := (Part6.magneticFlux).kind

/-- Speed of light in vacuum, item 6-35.2 (`c₀`, m/s) — the edge's other factor, and
F3's declared alternative to the silent default. -/
def speedOfLightK : KindOfProperty := (Part6.speedOfLight).kind

/-! ### The velocity edge, and its dimensional certificates

One edge, recurring at two levels: speed × vector potential lands in the 6-11 family
(the scalar-potential reading of `A⁰`), and speed × flux density lands at the electric
field (the `E` reading of the tensor, and the boost's mixing term). Each certificate is
a computation in the catalogue's own dimension group. -/

/-- `[V] / [m/s] = [Wb/m]`: dividing the potential's dimension by speed *is* the vector
potential's dimension — the four-vector is homogeneous because of the `/c`. -/
theorem voltage_per_speed_dim :
    Part6.EDim.voltage / Dim.speed = Part6.EDim.magneticVectorPotential := by
  decide

/-- `[Wb/m] / [m] = [T]`: a per-length derivative of the potential lands at flux
density — the field-strength tensor `∂A − ∂A` is dimensionally uniform at the tesla
(the spacetime coordinate is a length). -/
theorem vectorPotential_per_length_dim :
    Part6.EDim.magneticVectorPotential / Dim.length = Part6.EDim.magneticFluxDensity := by
  decide

/-- `[T] · [m/s] = [V/m]`: the electric reading of the tensor is the velocity edge
again — `E_i = −c·F⁰ⁱ`. -/
theorem fluxDensity_times_speed_dim :
    Part6.EDim.magneticFluxDensity * Dim.speed = Part6.EDim.electricFieldStrength := by
  decide

/-- `[Wb/m] · [m] = [Wb]`: since `∂^μχ` sits at the vector potential, the gauge
function `χ` is a magnetic flux field (F5's lookup). -/
theorem gaugeFunction_dim :
    Part6.EDim.magneticVectorPotential * Dim.length = Part6.EDim.magneticFlux := by
  decide

/-- Speed × vector potential — the 6-32 → 6-11 edge, registered at the **ratio-scale**
member of the 6-11 family (see the refusal below). -/
instance : KindMul speedOfLightK vectorPotentialK potentialDifferenceK :=
  ⟨ProductKind.ofRatio _ _ _⟩

/-- Speed × flux density → electric field — the same edge one level up: the `E` reading
of the tensor, and the boost's mixing term (F4). -/
instance : KindMul speedOfLightK magneticFluxDensityK electricFieldK :=
  ⟨ProductKind.ofRatio _ _ _⟩

/- **The catalogue's scale adjudicates the edge's target.** Electric potential
(6-11.1) is interval-scale — `ofRatio`'s obligations are unprovable there, so the
velocity edge *cannot* land on the potential itself; only its ratio-scale sibling
(6-11.2) accepts it. Upstream, both are the same `ℝ`. -/
#check_failure (ProductKind.ofRatio speedOfLightK vectorPotentialK electricPotentialK)

open scoped PropertyKindCalculus.OperatorTable

/-- A dimensionless numeral scales a quantity without changing its kind — `β` and `γ`
below. Same honesty as the pilot's copy of this instance: the action is the
Mathlib-interface tier (MR30) — a dimensioned magnitude smuggled in as a bare numeral
is what the audit measures, not what the type prevents. The mint is attested, not raw,
so the tier survives the mint ratchet. -/
@[carrierVocab]
scoped instance numeralSMul {k : KindOfProperty} {R : Type} [Mul R] :
    SMul R (Quantity k R) :=
  ⟨fun c q => .attest "a dimensionless numeral scales; the kind is unchanged"
    (c * q.magnitude)⟩

/-! ## F1 — the classical-field carrier -/

variable {d : ℕ}

/-- One `Carrier` instance serves the electric *and* the magnetic field, because
upstream the two are the same abbreviation over the same function type — `Zero` and
`Add` are Mathlib's pointwise instances, and that is all `Quantity` asks. -/
noncomputable instance : Carrier (Time → Space d → EuclideanSpace ℝ (Fin d)) :=
  Carrier.ofZeroAdd _

/-- The four-potential joins the carrier vocabulary through its own upstream
`AddCommGroup` — the structure, not a projection of it. -/
noncomputable instance : Carrier (EMPot d) := Carrier.ofZeroAdd _

/-- **F1a — the swap, at the chain's own derived fields.** The magnetic field the chain
*derives* is accepted where an electric field is expected: `ElectricField` and
`MagneticField` are one abbreviation, so nothing upstream can refuse this. -/
noncomputable example (cS : SpeedOfLight) (A : EMPot 3) :
    _root_.Electromagnetism.ElectricField 3 :=
  A.magneticField cS

/-- The declared speed of light — F3's alternative to the silent default: one attested
quantity, threaded explicitly through every kinded reading below. -/
@[kindIngest]
def speedQ (cS : SpeedOfLight) : Quantity speedOfLightK SpeedOfLight :=
  .attest "the unit-system choice, declared once instead of defaulted per call site" cS

/-- `E` read at its kind, at the field carrier — the wrap is of the *whole* field
(MR19); components stay plain indexing beneath it. -/
@[kindIngest]
noncomputable def electricFieldQ (cq : Quantity speedOfLightK SpeedOfLight)
    (A : EMPot d) : Quantity electricFieldK (_root_.Electromagnetism.ElectricField d) :=
  .attest "reading of the chain's electricField" (A.electricField cq.magnitude)

/-- `B` read at its kind, over the *same* naked carrier type as `E`. -/
@[kindIngest]
noncomputable def magneticFieldQ (cq : Quantity speedOfLightK SpeedOfLight)
    (A : EMPot 3) : Quantity magneticFluxDensityK (_root_.Electromagnetism.MagneticField 3) :=
  .attest "reading of the chain's magneticField" (A.magneticField cq.magnitude)

/-- A consumer that wants an electric field, kinded. -/
def expectsE (E : Quantity electricFieldK (_root_.Electromagnetism.ElectricField 3)) :
    Quantity electricFieldK (_root_.Electromagnetism.ElectricField 3) := E

/- **F1b.** The kinded swap is refused — same carrier, distinct kinds. -/
#check_failure fun (cq : Quantity speedOfLightK SpeedOfLight) (A : EMPot 3) =>
  expectsE (magneticFieldQ cq A)

/-! ## F2 — one homogeneous tensor, two readings, one velocity edge -/

/-- The four-potential at its one kind. -/
@[kindIngest]
noncomputable def potentialQ (A : EMPot d) : Quantity vectorPotentialK (EMPot d) :=
  .attest "the four-potential — homogeneous at 6-32 because A⁰ = φ/c" A

/-- **F2a — the `/c`, pinned at the source.** `ofPotentials` stores `φ/c` in the time
slot: the division is what makes the Lorentz vector one kind. -/
example (cS : SpeedOfLight) (φ : Time → Space d → ℝ)
    (Av : Time → Space d → EuclideanSpace ℝ (Fin d)) (x : SpaceTime d) :
    (_root_.Electromagnetism.ElectromagneticPotential.ofPotentials cS φ Av).val x
      (Sum.inl 0) = (SpaceTime.timeSlice cS).symm φ x / cS := rfl

/-- **F2b — the crossing back.** `scalarPotential = c·A⁰`: the 6-32 → 6-11.1 velocity
edge run in reverse, attested. The target is the *interval*-scale potential — the edge
exists in the registry only at the ratio sibling (the refusal above), so the reading is
a named crossing, not a table multiplication. -/
@[kindCrossing]
noncomputable def scalarPotentialQ (cq : Quantity speedOfLightK SpeedOfLight)
    (Aq : Quantity vectorPotentialK (EMPot d)) :
    Quantity electricPotentialK (Time → Space d → ℝ) :=
  .attest "c·A⁰ — the velocity edge, landing on the interval-scale potential"
    (Aq.magnitude.scalarPotential cq.magnitude)

/-- The crossing erases to upstream's `scalarPotential` — definitionally. -/
theorem scalarPotentialQ_eq (cS : SpeedOfLight) (A : EMPot d) :
    (scalarPotentialQ (speedQ cS) (potentialQ A)).magnitude =
      A.scalarPotential cS := rfl

/-- **F2c.** Upstream's own round trip closes the kinded one: building the potential
from `(φ, 𝐀)` and reading the scalar potential back returns `φ`. -/
theorem scalarPotentialQ_roundtrip (cS : SpeedOfLight) (φ : Time → Space d → ℝ)
    (Av : Time → Space d → EuclideanSpace ℝ (Fin d)) :
    (scalarPotentialQ (speedQ cS)
      (potentialQ (_root_.Electromagnetism.ElectromagneticPotential.ofPotentials cS φ Av))).magnitude
      = φ := by
  rw [scalarPotentialQ_eq]
  simp

/-! ## F3 — the silent numeral -/

/- The default, pinned: `electricField` called with no unit system at all — the
`(c : SpeedOfLight := 1)` default decides the physics at this call site, invisibly.
Every definition in the chain (`scalarPotential`, `vectorPotential`, `electricField`,
`magneticField`, `magneticFieldMatrix`) carries the same default. The kinded readings
above have no default to elide: `speedQ` is an argument. -/
noncomputable example (A : EMPot 3) : _root_.Electromagnetism.ElectricField 3 :=
  _root_.Electromagnetism.ElectromagneticPotential.electricField (A := A)

/-! ## F4 — boosts are the forced joins -/

/-- A pointwise electric-field reading — the boost law mixes *values*, so the probe
works at `ℝ`, where the table's edges live. -/
@[kindIngest]
noncomputable def electricFieldAtQ (cS : SpeedOfLight) (A : EMPot d) (t : Time)
    (x : Space d) (i : Fin d) : Quantity electricFieldK ℝ :=
  .attest "pointwise reading of the chain's electricField" (A.electricField cS t x i)

/-- A pointwise magnetic-field-matrix reading — the spatial block of the field
strength, which *is* the magnetic field
(`toFieldStrength_eval_inr_inr_eq_magneticFieldMatrix`). -/
@[kindIngest]
noncomputable def magneticMatrixAtQ (cS : SpeedOfLight) (A : EMPot d) (t : Time)
    (x : Space d) (ij : Fin d × Fin d) : Quantity magneticFluxDensityK ℝ :=
  .attest "pointwise reading of the chain's magneticFieldMatrix"
    (A.magneticFieldMatrix cS t x ij)

/-- The speed of light at the scalar carrier, for the table. -/
@[kindIngest]
def speedRQ (cS : SpeedOfLight) : Quantity speedOfLightK ℝ :=
  .attest "the declared speed, at the table's carrier" cS.val

/- **F4a.** `E + B` directly is refused: distinct kinds, no join — the mixing needs
the edge. -/
#check_failure fun (E : Quantity electricFieldK ℝ) (B : Quantity magneticFluxDensityK ℝ) =>
  E + B

/-- **F4b.** The boosted transverse field, kinded: `γ·(E + c·(β·B))`. The magnetic
term reaches the electric kind *only* through the registered velocity edge; `β` and
`γ` ride the dimensionless numeral action; the outer sum is then same-kind. -/
noncomputable def boostedEQ (γv β : ℝ) (cq : Quantity speedOfLightK ℝ)
    (E : Quantity electricFieldK ℝ) (B : Quantity magneticFluxDensityK ℝ) :
    Quantity electricFieldK ℝ :=
  γv • (E + cq * (β • B))

/-- The composite's magnitude, spelled out — each factor a definitional erasure. -/
theorem boostedEQ_magnitude (γv β : ℝ) (cq : Quantity speedOfLightK ℝ)
    (E : Quantity electricFieldK ℝ) (B : Quantity magneticFluxDensityK ℝ) :
    (boostedEQ γv β cq E B).magnitude =
      γv * (E.magnitude + cq.magnitude * (β * B.magnitude)) := rfl

@[simp] theorem electricFieldAtQ_magnitude (cS : SpeedOfLight) (A : EMPot d)
    (t : Time) (x : Space d) (i : Fin d) :
    (electricFieldAtQ cS A t x i).magnitude = A.electricField cS t x i := rfl

@[simp] theorem magneticMatrixAtQ_magnitude (cS : SpeedOfLight) (A : EMPot d)
    (t : Time) (x : Space d) (ij : Fin d × Fin d) :
    (magneticMatrixAtQ cS A t x ij).magnitude = A.magneticFieldMatrix cS t x ij := rfl

@[simp] theorem speedRQ_magnitude (cS : SpeedOfLight) :
    (speedRQ cS).magnitude = cS.val := rfl

/-- The kinded combination erases to the boost law's right-hand side, at any
evaluation point — the algebraic half of F4c, with the points as free variables. -/
theorem boostedEQ_erases (γv β : ℝ) (cS : SpeedOfLight) (A : EMPot d)
    (t : Time) (x : Space d) (i : Fin d) (ij : Fin d × Fin d) :
    (boostedEQ γv β (speedRQ cS)
      (electricFieldAtQ cS A t x i) (magneticMatrixAtQ cS A t x ij)).magnitude =
      γv * (A.electricField cS t x i + cS.val * β * A.magneticFieldMatrix cS t x ij) := by
  rw [boostedEQ_magnitude, electricFieldAtQ_magnitude, magneticMatrixAtQ_magnitude,
    speedRQ_magnitude]
  ring

/-- **F4c — upstream's boost law closes the kinded one.** The transverse electric
field of the boosted potential *is* the kinded combination's magnitude, term for term:
what survives the boost is the tensor; `E` and `B` are frame-bound readings, licensed
to mix exactly where the physics mixes them (MR18). -/
theorem boost_reads_through_the_edge {d : ℕ} (β : ℝ) (hβ : |β| < 1)
    (cS : SpeedOfLight) (A : EMPot d.succ) (hA : Differentiable ℝ A)
    (t : Time) (x : Space d.succ) (i : Fin d) :
    let t' : Time := LorentzGroup.γ β * (t.val + β / cS * x 0)
    let x' : Space d.succ := ⟨fun
      | 0 => LorentzGroup.γ β * (x 0 + cS * β * t.val)
      | ⟨Nat.succ n, ih⟩ => x ⟨Nat.succ n, ih⟩⟩
    (LorentzGroup.boost (d := d.succ) 0 β hβ • A).electricField cS t x i.succ =
      (boostedEQ (LorentzGroup.γ β) β (speedRQ cS)
        (electricFieldAtQ cS A t' x' i.succ)
        (magneticMatrixAtQ cS A t' x' (0, i.succ))).magnitude := by
  intro t' x'
  have h := _root_.Electromagnetism.ElectromagneticPotential.electricField_apply_x_boost_succ
    (c := cS) β hβ A hA t x i
  simp only at h
  rw [h, boostedEQ_erases]
  rfl

/-! ## F5 — gauge freedom is the interval scale, and χ is a flux -/

/-- A gauge function at its kind: `∂^μχ` sits at 6-32, so `χ` is a magnetic flux
field — a catalogue lookup (6-22.1), not a mint. -/
@[kindIngest]
noncomputable def gaugeFnQ (χ : SpaceTime d → ℝ) :
    Quantity magneticFluxK (SpaceTime d → ℝ) :=
  .attest "a gauge function is a magnetic flux field: ∂^μχ lands at 6-32" χ

/-- **F5a — the torsor translation.** The gauge shift `A ↦ A + ∂^μχ` moves the
potential without leaving its kind: gauge freedom acting, the interval scale's
translation. Upstream's `gaugeTransform_zero` and `gaugeTransform_gaugeTransform` are
the group action. -/
@[kindCrossing]
noncomputable def gaugeShiftQ (Aq : Quantity vectorPotentialK (EMPot d))
    (χq : Quantity magneticFluxK (SpaceTime d → ℝ)) :
    Quantity vectorPotentialK (EMPot d) :=
  .attest "the gauge translation: the potential moves, the kind does not"
    (Aq.magnitude.gaugeTransform χq.magnitude)

/-- **F5b — the field strength is the reference-free extent.** The shifted potential's
field strength is the original's — upstream's own invariance theorem, consumed at the
kinded reading. -/
theorem gaugeShiftQ_extent_invariant (A : EMPot d) (χ : SpaceTime d → ℝ)
    (hA : Differentiable ℝ A) (hχ : ContDiff ℝ 2 χ) (x : SpaceTime d) :
    ((gaugeShiftQ (potentialQ A) (gaugeFnQ χ)).magnitude).toFieldStrength x =
      A.toFieldStrength x :=
  _root_.Electromagnetism.ElectromagneticPotential.toFieldStrength_gaugeTransform
    A χ hA hχ x

/-- The zero shift is the identity — the torsor's `0 +ᵥ`. -/
theorem gaugeShiftQ_zero (A : EMPot d) :
    (gaugeShiftQ (potentialQ A) (gaugeFnQ 0)).magnitude = A :=
  _root_.Electromagnetism.ElectromagneticPotential.gaugeTransform_zero A

/-- Shifts compose additively — the torsor's `+ᵥ` associating over the flux fields'
own sum. -/
theorem gaugeShiftQ_comp (A : EMPot d) (χ₁ χ₂ : SpaceTime d → ℝ)
    (h₁ : Differentiable ℝ χ₁) (h₂ : Differentiable ℝ χ₂) :
    (gaugeShiftQ (gaugeShiftQ (potentialQ A) (gaugeFnQ χ₂)) (gaugeFnQ χ₁)).magnitude =
      (gaugeShiftQ (potentialQ A) (gaugeFnQ (χ₁ + χ₂))).magnitude :=
  _root_.Electromagnetism.ElectromagneticPotential.gaugeTransform_gaugeTransform
    A χ₁ χ₂ h₁ h₂

/- **F5c.** The interval scale refuses the ratio operation: a *ratio* of electric
potentials is meaningless (the gauge convention cannot cancel out of a quotient), and
`ofRatio`'s obligations are unprovable at 6-11.1's scale. -/
#check_failure (QuotientKind.ofRatio electricPotentialK electricPotentialK
  potentialDifferenceK)

/-! ## The substrate, once

The chain rests on bare function types over `ℝ` — the same substrate the exhibits
carry; one probe suffices. -/

/-- An electric field plus a four-potential's scalar reading elaborates at the
source's types (both are bare functions)… -/
noncomputable example (cS : SpeedOfLight) (A : EMPot 3) (t : Time) (x : Space 3) : ℝ :=
  A.electricField cS t x 0 + A.scalarPotential cS t x

/- …and is refused at the kinded ones: `(electric field, electric potential)` joins
nothing. -/
#check_failure fun (cS : SpeedOfLight) (A : EMPot 3) (t : Time) (x : Space 3) =>
  electricFieldAtQ cS A t x 0 + scalarPotentialQ (speedQ cS) (potentialQ A)

end ForPhysLib.Electromagnetism.Kinematics

