/-
# The ClassicalMechanics directory — feasibility, before the ladder

**Source.** `Physlib/ClassicalMechanics/HarmonicOscillator/` (with `Solution.lean`) and
`Physlib/ClassicalMechanics/RigidBody/`, imported and probed directly. The campaign's
third directory — see `PLAN.md`, "Directory 3: `ClassicalMechanics`".

Six capability questions, answered as build artifacts before any ladder stage is
climbed. The spine they share, the inverse of directory 2's: where the EM chain was one
frame-covariant object ranging over many dimensions, classical mechanics is **many
kinds crowded onto few dimensions** — four energies at the joule, two ω's at `T⁻¹` —
and everything upstream types at `ℝ` or `EuclideanSpace ℝ (Fin 1)`, so every one of
those coincidences is invisible there.

* **F1 — the bare-real input data, and the reciprocal that must die before the root.**
  `HarmonicOscillator { m k : ℝ }`: the mass is a lookup, the spring constant a *mint*
  (no ISO 80000 item), and `ω = √(k/m)` the directory's kind-level event — radicand
  through the registered `k/m` edge, root attested, erased to `S.ω` by `rfl` and to the
  radicand by upstream's own `ω_sq`. The reciprocal `m/k` is no edge and dies before
  any root can be taken; upstream, `√(m/k)` typechecks as happily as the right recipe.
* **F2 — four energies, one dimension, and the sum that outruns the difference.**
  `T + V` is a curated `KindJoin` landing at mechanical energy (4-28.3); the
  on-trajectory Hamiltonian erases to the same join by `hamiltonian_eq_energy`. The
  Lagrangian `T − V` is *not* the join sum — the standard's vocabulary has a home for
  the sum of the comparable pair and none for its difference, so the Lagrangian is a
  mint, and `L + E` is refused at the same joule.
* **F3 — the collisions of M6, paid down as refusals.** Upstream, the momentum of a
  momentum, the force fed a momentum, and the Hamiltonian with `p` and `x` swapped all
  typecheck (pinned below); the kinded twins refuse all three.
* **F4 — the tfae is the stress test.** The kinded Newton reading — `m·a` through the
  4-9.1 edge against the ingested force — is equivalent to `EquationOfMotion`, and the
  equivalence is `equationOfMotion_tfae` consumed verbatim (`.out 0 1`), nothing
  re-proved. The full pentad is Stage 2's.
* **F5 — two ω's, the trig boundary, and the complex number that packs two lengths.**
  `ω·t` lands at the phase angle (3-7) through a registered edge — the licence `cos`
  and `sin` consume at the boundary; the period is the crossing `2π/ω`, erased to
  upstream's `period` by `rfl`. The amplitude–phase inverse embeds `(x₀, v₀/ω)` as one
  complex number — licensed exactly because `v₀/ω` is a *length* — and the amplitude
  reading erases to upstream's `fromInitialConditions` by `rfl`. Angular frequency
  (3-18) and angular velocity (3-12) — the two subtrees' shared letter — are separated
  by `decide`.
* **F6 — the functional ingest and the second join.** `RigidBody.ρ` is a linear
  functional on test functions; each moment read off it is an ingest (mass at `1`, the
  second moment at 4-7). `L = I·ω` is the 4-7 × 3-12 edge, contracted as a same-kind
  sum of table products and closed by upstream's `angularMomentum_eq_inertiaTensor_mulVec`.
  König's split is the directory's *second* join — translational and rotational kinetic
  energy as species of 4-28.2, summing at their parent, closed by upstream's own
  body-frame König theorem.

One patch-candidate slot is known before any ladder stage: `solidSphere_inertiaTensor`
(`(2/5) m R² • 1`) is `@[sorryful]` upstream — the only `sorry` in either subtree. Per
the plan, the discharge is attempted as a standalone file after the ladder.
-/

import Physlib.ClassicalMechanics.HarmonicOscillator.Solution
import Physlib.ClassicalMechanics.RigidBody.KineticEnergy
import PropertyKindCalculus.BoundaryAudit
import PropertyKindCalculus.KindAlgebra
import PropertyKindCalculus.QuantityReal
import PropertyKindCalculus.SpecializationLift
import PropertyKindCalculus.Iso80000.Part3
import PropertyKindCalculus.Iso80000.Part4

namespace ForPhysLib.ClassicalMechanics

open PropertyKindCalculus
open PropertyKindCalculus.Iso80000
open Time ContDiff InnerProductSpace

-- PhysLib's oscillator, qualified past this file's own namespace.
local notation "HO" => _root_.ClassicalMechanics.HarmonicOscillator
local notation "E1" => EuclideanSpace ℝ (Fin 1)

/-! ## The kind vocabulary — lookups, and the mints the standard forces

Unlike directory 2 (lookups only) and like the pilot, this directory's physics uses
kinds the catalogue does not list: the spring constant (a system parameter), its `k/m`
radicand, the Lagrangian (the difference the joule vocabulary has no home for), and the
two kinetic-energy species König sums. The mints are declared here feasibility-local;
`Kinds.lean` owns the canonical literals. -/

/-- Mass, item 4-1. -/
def massK : KindOfProperty := (Part4.mass).kind

/-- Momentum, item 4-8 — what `toCanonicalMomentum` produces. -/
def momentumK : KindOfProperty := (Part4.momentum).kind

/-- Force, item 4-9.1. -/
def forceK : KindOfProperty := (Part4.force).kind

/-- Kinetic energy, item 4-28.2. -/
def kineticEnergyK : KindOfProperty := (Part4.kineticEnergy).kind

/-- Potential energy, item 4-28.1. -/
def potentialEnergyK : KindOfProperty := (Part4.potentialEnergy).kind

/-- Mechanical energy, item 4-28.3 — the join of the two above, and the kind of the
total energy and the on-trajectory Hamiltonian. -/
def mechanicalEnergyK : KindOfProperty := (Part4.mechanicalEnergy).kind

/-- Moment of inertia, item 4-7 — the kind of the tensor's entries. -/
def momentOfInertiaK : KindOfProperty := (Part4.momentOfInertia).kind

/-- Angular momentum, item 4-11. -/
def angularMomentumK : KindOfProperty := (Part4.angularMomentum).kind

/-- Displacement, item 3-1.11 — the oscillator's `x`, a displacement from
equilibrium in this coordinate model. -/
def displacementK : KindOfProperty := (Part3.displacement).kind

/-- Velocity, item 3-10.1. -/
def velocityK : KindOfProperty := (Part3.velocity).kind

/-- Acceleration, item 3-11. -/
def accelerationK : KindOfProperty := (Part3.acceleration).kind

/-- Angular frequency, item 3-18 — the oscillator's `ω`. -/
def angularFrequencyK : KindOfProperty := (Part3.angularFrequency).kind

/-- Angular velocity, item 3-12 — the rigid body's `ω`. Same dimension `T⁻¹`, same
letter, different catalogue item; separated from 3-18 by `decide` below. -/
def angularVelocityK : KindOfProperty := (Part3.angularVelocity).kind

/-- Period duration, item 3-14 — `T = 2π/ω`. -/
def periodDurationK : KindOfProperty := (Part3.periodDuration).kind

/-- Phase angle, item 3-7 — where `ω·t` lands, and the licence for `cos`/`sin`. -/
def phaseAngleK : KindOfProperty := (Part3.phaseAngle).kind

/-- Duration, item 3-9 — the trajectory parameter. -/
def durationK : KindOfProperty := (Part3.duration).kind

/-- **Mint.** The spring constant `k` — the input datum the catalogue does not list
(`M·T⁻²`; the certificate below derives it as force per displacement). -/
def springConstantK : KindOfProperty := { id := "spring constant", scale := .ratio }

/-- **Mint.** The `k/m` radicand — `T⁻²`, the square of the angular frequency; the
pilot's radicand-first pattern. -/
def omegaSquaredK : KindOfProperty :=
  { id := "squared angular frequency", scale := .ratio }

/-- **Mint.** The Lagrangian — `T − V`, at the joule but *not* an energy of the
system's state: the difference of the comparable pair, for which the catalogue's
vocabulary has no item. -/
def lagrangianK : KindOfProperty := { id := "Lagrangian", scale := .ratio }

/-- **Mint.** Translational kinetic energy — König's first summand, a species of
4-28.2. -/
def translationalKineticEnergyK : KindOfProperty :=
  { id := "translational kinetic energy", scale := .ratio }

/-- **Mint.** Rotational kinetic energy — König's second summand, the other species. -/
def rotationalKineticEnergyK : KindOfProperty :=
  { id := "rotational kinetic energy", scale := .ratio }

/-! ### Dimensional certificates

Each mint's dimension, and each edge's coherence, as a computation in the catalogue's
own dimension group. -/

/-- The spring constant's dimension, `M·T⁻²`. -/
def springConstantDim : Dimension LTMCTDimensionBase :=
  Dim.mass / (Dim.time * Dim.time)

/-- `[N] / [m] = [kg/s²]`: the spring constant is force per displacement — Hooke's law
fixes the mint's dimension. -/
theorem force_per_length_dim :
    Part4.MDim.force / Dim.length = springConstantDim := by decide

/-- `[kg/s²] / [kg] = [s⁻²]`: the radicand `k/m` is a squared angular frequency. -/
theorem springConstant_per_mass_dim :
    springConstantDim / Dim.mass = (Dim.time * Dim.time)⁻¹ := by decide

/-- `[kg] · [m/s] = [kg·m/s]`: the canonical momentum is the 4-8 edge. -/
theorem mass_times_velocity_dim :
    Dim.mass * Dim.speed = Part4.MDim.momentum := by decide

/-- `[kg] · [m/s²] = [N]`: Newton's reading is the 4-9.1 edge. -/
theorem mass_times_acceleration_dim :
    Dim.mass * (Dim.length / (Dim.time * Dim.time)) = Part4.MDim.force := by decide

/-- `[s⁻¹] · [s] = [1]`: `ω·t` is dimensionless — the phase. -/
theorem angularFrequency_times_duration_dim :
    Dim.time⁻¹ * Dim.time = Dim.one := by decide

/-- `[m/s] / [s⁻¹] = [m]`: `v/ω` is a length — the licence for the amplitude–phase
complex embedding. -/
theorem velocity_per_angularFrequency_dim :
    Dim.speed / Dim.time⁻¹ = Dim.length := by decide

/-- `[kg·m²] · [s⁻¹] = [kg·m²/s]`: `L = I·ω` is the 4-7 × 3-12 edge. -/
theorem inertia_times_angularVelocity_dim :
    Part4.MDim.momentOfInertia * Dim.time⁻¹ = Part4.MDim.angularMomentum := by decide

/-- `[s⁻¹] · [kg·m²/s] = [J]`: `ω·L` lands at the joule — twice the rotational kinetic
energy. -/
theorem angularVelocity_times_angularMomentum_dim :
    Dim.time⁻¹ * Part4.MDim.angularMomentum = Part4.MDim.energy := by decide

/-! ### The edges this file's probes ride -/

/-- `k / m → ω²` — the radicand edge (F1). -/
instance : KindDiv springConstantK massK omegaSquaredK :=
  ⟨QuotientKind.ofRatio _ _ _⟩

/-- `m · v → p` — the 4-8 edge (F3). -/
instance : KindMul massK velocityK momentumK :=
  ⟨ProductKind.ofRatio _ _ _⟩

/-- `m · a → F` — the 4-9.1 edge, Newton's reading (F4). -/
instance : KindMul massK accelerationK forceK :=
  ⟨ProductKind.ofRatio _ _ _⟩

/-- `ω · t → phase` — the trig boundary's licence (F5). -/
instance : KindMul angularFrequencyK durationK phaseAngleK :=
  ⟨ProductKind.ofRatio _ _ _⟩

/-- `v / ω → length` — the amplitude–phase embedding's licence (F5). -/
instance : KindDiv velocityK angularFrequencyK displacementK :=
  ⟨QuotientKind.ofRatio _ _ _⟩

/-- `I · ω → L` — the 4-7 × 3-12 edge (F6). -/
instance : KindMul momentOfInertiaK angularVelocityK angularMomentumK :=
  ⟨ProductKind.ofRatio _ _ _⟩

/-! ### The two joins — the directory's specialization lattice, in miniature

The pilot needed one curated join; directory 2 needed none; this directory needs two,
on a two-level lattice: kinetic and potential energy join at mechanical energy, and
König's two kinetic species join at kinetic energy. Feasibility-local edges;
`Kinds.lean` owns the canonical lattice. -/

/-- The energy family's direct-parent edges. -/
inductive EnergyEdge : KindOfProperty → KindOfProperty → Prop
  /-- Kinetic energy is a mechanical energy. -/
  | kinetic : EnergyEdge kineticEnergyK mechanicalEnergyK
  /-- Potential energy is a mechanical energy. -/
  | potential : EnergyEdge potentialEnergyK mechanicalEnergyK

/-- The kinetic family's direct-parent edges — König's summands. -/
inductive KineticEdge : KindOfProperty → KindOfProperty → Prop
  /-- Translational kinetic energy is a kinetic energy. -/
  | translational : KineticEdge translationalKineticEnergyK kineticEnergyK
  /-- Rotational kinetic energy is a kinetic energy. -/
  | rotational : KineticEdge rotationalKineticEnergyK kineticEnergyK

/-- `T + V` joins at mechanical energy — the pilot's join, at PhysLib's own `energy`. -/
instance : KindJoin EnergyEdge kineticEnergyK potentialEnergyK mechanicalEnergyK :=
  ⟨.of_edge .kinetic, .of_edge .potential, .ofScale⟩

/-- König: translational + rotational joins at kinetic energy. -/
instance : KindJoin KineticEdge translationalKineticEnergyK rotationalKineticEnergyK
    kineticEnergyK :=
  ⟨.of_edge .translational, .of_edge .rotational, .ofScale⟩

open scoped PropertyKindCalculus.OperatorTable

/-- A dimensionless numeral scales a quantity without changing its kind — the `½` of
every energy below, the `2π` of the period. Same honesty as the pilot's copy of this
instance: the action is the Mathlib-interface tier (MR30), and the mint is attested,
not raw, so the tier survives the mint ratchet. -/
@[carrierVocab]
scoped instance numeralSMul {k : KindOfProperty} {R : Type} [Mul R] :
    SMul R (Quantity k R) :=
  ⟨fun c q => .attest "a dimensionless numeral scales; the kind is unchanged"
    (c * q.magnitude)⟩

/-! ## F1 — the bare-real input data -/

/- Upstream, both recipes typecheck: `√(k/m)` is the angular frequency and `√(m/k)` is
dimensional nonsense at the same type. Exhibit C's finding, re-pinned at the source. -/
noncomputable example (S : HO) : ℝ := Real.sqrt (S.k / S.m)
noncomputable example (S : HO) : ℝ := Real.sqrt (S.m / S.k)

/-- The oscillator's mass, read at 4-1. -/
@[kindIngest]
def massQ (S : HO) : Quantity massK ℝ :=
  .attest "the input datum m" S.m

@[simp] theorem massQ_magnitude (S : HO) : (massQ S).magnitude = S.m := rfl

/-- The spring constant, read at the mint — the system parameter the catalogue does
not list. -/
@[kindIngest]
def springQ (S : HO) : Quantity springConstantK ℝ :=
  .attest "the input datum k — Hooke's constant, a mint" S.k

/-- The radicand `k/m`, through the registered edge — one `/`. -/
noncomputable def omegaSqQ (S : HO) : Quantity omegaSquaredK ℝ :=
  springQ S / massQ S

/-- The radicand erases to upstream's `k/m` — definitionally. -/
theorem omegaSqQ_magnitude (S : HO) : (omegaSqQ S).magnitude = S.k / S.m := rfl

/-- **The kind-level event**: the square root, radicand-first — a crossing from the
squared kind to the angular frequency, attested. -/
@[kindCrossing]
noncomputable def omegaQ (rq : Quantity omegaSquaredK ℝ) :
    Quantity angularFrequencyK ℝ :=
  .attest "the root of the radicand: √(k/m) lands at 3-18" (Real.sqrt rq.magnitude)

/-- The crossing erases to upstream's `ω` — definitionally. -/
theorem omegaQ_magnitude (S : HO) : (omegaQ (omegaSqQ S)).magnitude = S.ω := rfl

/-- Upstream's own `ω_sq` closes the round trip: the root's square is the radicand. -/
theorem omegaQ_sq (S : HO) :
    (omegaQ (omegaSqQ S)).magnitude ^ 2 = (omegaSqQ S).magnitude := by
  rw [omegaQ_magnitude, omegaSqQ_magnitude]
  exact S.ω_sq

/- **F1a.** The reciprocal dies before the root: `m / k` is no edge of the algebra. -/
#check_failure fun (S : HO) => massQ S / springQ S

/-! ## F2 — four energies, one dimension -/

/-- The kinetic energy along a trajectory, read at 4-28.2. -/
@[kindIngest]
noncomputable def kineticQ (S : HO) (xₜ : Time → E1) (t : Time) :
    Quantity kineticEnergyK ℝ :=
  .attest "the chain's kineticEnergy — ½m⟪ẋ,ẋ⟫" (S.kineticEnergy xₜ t)

/-- The potential energy at a displacement, read at 4-28.1. -/
@[kindIngest]
noncomputable def potentialQ (S : HO) (x : E1) : Quantity potentialEnergyK ℝ :=
  .attest "the chain's potentialEnergy — ½k⟪x,x⟫" (S.potentialEnergy x)

/-- **The first join, consumed**: `T + V` elaborates through the curated table and
lands at mechanical energy. -/
noncomputable def energyQ (Tq : Quantity kineticEnergyK ℝ)
    (Vq : Quantity potentialEnergyK ℝ) : Quantity mechanicalEnergyK ℝ :=
  Tq + Vq

/-- The join sum erases to upstream's `energy` — definitionally: `energy` *is* the sum
of the two readings. -/
theorem energyQ_erases (S : HO) (xₜ : Time → E1) (t : Time) :
    (energyQ (kineticQ S xₜ t) (potentialQ S (xₜ t))).magnitude = S.energy xₜ t := rfl

/-- The on-trajectory Hamiltonian, read at the join's kind — `hamiltonian_eq_energy`
licenses the reading below. -/
@[kindIngest]
noncomputable def hamiltonianAtQ (S : HO) (xₜ : Time → E1) (t : Time) :
    Quantity mechanicalEnergyK ℝ :=
  .attest "H on the trajectory — equal to the energy by hamiltonian_eq_energy"
    (S.hamiltonian t (S.toCanonicalMomentum t (xₜ t) (∂ₜ xₜ t)) (xₜ t))

/-- **Upstream's `hamiltonian_eq_energy` closes the reading**: the on-trajectory
Hamiltonian is the join sum's magnitude. -/
theorem hamiltonianAtQ_erases (S : HO) (xₜ : Time → E1) (t : Time) :
    (hamiltonianAtQ S xₜ t).magnitude =
      (energyQ (kineticQ S xₜ t) (potentialQ S (xₜ t))).magnitude :=
  congrFun (S.hamiltonian_eq_energy xₜ) t

/-- **The difference is not the sum**: `T − V` lands at the Lagrangian mint — a
crossing, because the join table licenses the sum of the comparable pair and the
standard has no item for its difference. -/
@[kindCrossing]
noncomputable def lagrangianQ (Tq : Quantity kineticEnergyK ℝ)
    (Vq : Quantity potentialEnergyK ℝ) : Quantity lagrangianK ℝ :=
  .attest "T − V — the difference the joule vocabulary has no home for"
    (Tq.magnitude - Vq.magnitude)

/-- The crossing erases to upstream's `lagrangian` on a trajectory — upstream's own
equality, consumed backwards. -/
theorem lagrangianQ_erases (S : HO) (xₜ : Time → E1) (t : Time) :
    (lagrangianQ (kineticQ S xₜ t) (potentialQ S (xₜ t))).magnitude =
      S.lagrangian t (xₜ t) (∂ₜ xₜ t) :=
  (S.lagrangian_eq_kineticEnergy_sub_potentialEnergy t xₜ).symm

/- **F2a.** Same joule, no join: the Lagrangian does not add to a mechanical energy. -/
#check_failure fun (L : Quantity lagrangianK ℝ) (E : Quantity mechanicalEnergyK ℝ) =>
  L + E

/-! ## F3 — the collisions of M6, paid down as refusals -/

/- Upstream, all three collisions typecheck. The momentum of a momentum
(`toCanonicalMomentum` is `E ≃ₗ E` between identical types): -/
noncomputable example (S : HO) (t : Time) (x p : E1) : E1 :=
  S.toCanonicalMomentum t x (S.toCanonicalMomentum t x p)
/- The force fed the canonical momentum: -/
noncomputable example (S : HO) (t : Time) (x v : E1) : E1 :=
  S.force (S.toCanonicalMomentum t x v)
/- The Hamiltonian with `p` and `x` swapped — the collision behind `hamiltonian_eq`'s
transposed `funext t x p`: -/
noncomputable example (S : HO) (t : Time) (p x : E1) : ℝ := S.hamiltonian t x p

/-- The kinded canonical momentum — kind-*changing* between identical carriers: a
velocity goes in, a momentum comes out (`m·v`, the 4-8 edge, on the vector carrier). -/
@[kindCrossing]
noncomputable def toCanonicalMomentumQ (S : HO) (t : Time)
    (xq : Quantity displacementK E1) (vq : Quantity velocityK E1) :
    Quantity momentumK E1 :=
  .attest "the canonical momentum m·v — the 4-8 edge at the vector carrier"
    (S.toCanonicalMomentum t xq.magnitude vq.magnitude)

/-- The kinded force — a displacement goes in. -/
@[kindCrossing]
noncomputable def forceQ (S : HO) (xq : Quantity displacementK E1) :
    Quantity forceK E1 :=
  .attest "−∇V — the force reading" (S.force xq.magnitude)

/-- The kinded Hamiltonian signature — momentum first, displacement second, the order
upstream's docstring intends. -/
@[kindCrossing]
noncomputable def hamiltonianQ (S : HO) (t : Time)
    (pq : Quantity momentumK E1) (xq : Quantity displacementK E1) : Quantity mechanicalEnergyK ℝ :=
  .attest "H(t, p, x) — at the kinded signature the argument order is checked"
    (S.hamiltonian t pq.magnitude xq.magnitude)

/- **F3a.** The momentum of a momentum is refused. -/
#check_failure fun (S : HO) (t : Time) (xq : Quantity displacementK E1)
  (vq : Quantity velocityK E1) =>
  toCanonicalMomentumQ S t xq (toCanonicalMomentumQ S t xq vq)

/- **F3b.** The force fed a momentum is refused. -/
#check_failure fun (S : HO) (t : Time) (xq : Quantity displacementK E1)
  (vq : Quantity velocityK E1) =>
  forceQ S (toCanonicalMomentumQ S t xq vq)

/- **F3c.** The swapped Hamiltonian is refused. -/
#check_failure fun (S : HO) (t : Time) (pq : Quantity momentumK E1)
  (xq : Quantity displacementK E1) =>
  hamiltonianQ S t xq pq

/- And the substrate probe: upstream a position plus a momentum compiles (one type);
kinded, it joins nothing. -/
noncomputable example (S : HO) (t : Time) (x v : E1) : E1 :=
  x + S.toCanonicalMomentum t x v
#check_failure fun (xq : Quantity displacementK E1) (pq : Quantity momentumK E1) =>
  xq + pq

/-! ## F4 — the tfae is the stress test -/

/-- A pointwise acceleration reading — the equation of motion compares *values*, so
the probe works at `ℝ`, where the table's edges live. -/
@[kindIngest]
noncomputable def accelerationAtQ (xₜ : Time → E1) (t : Time) :
    Quantity accelerationK ℝ :=
  .attest "the trajectory's second time derivative, component 0" (∂ₜ (∂ₜ xₜ) t 0)

@[simp] theorem accelerationAtQ_magnitude (xₜ : Time → E1) (t : Time) :
    (accelerationAtQ xₜ t).magnitude = ∂ₜ (∂ₜ xₜ) t 0 := rfl

/-- A pointwise force reading along the trajectory. -/
@[kindIngest]
noncomputable def forceAtQ (S : HO) (xₜ : Time → E1) (t : Time) :
    Quantity forceK ℝ :=
  .attest "the force at the trajectory's displacement, component 0"
    (S.force (xₜ t) 0)

@[simp] theorem forceAtQ_magnitude (S : HO) (xₜ : Time → E1) (t : Time) :
    (forceAtQ S xₜ t).magnitude = S.force (xₜ t) 0 := rfl

/-- Newton's left side, kinded: `m·a` through the 4-9.1 edge — one `*`. -/
noncomputable def newtonLHSQ (mq : Quantity massK ℝ)
    (aq : Quantity accelerationK ℝ) : Quantity forceK ℝ :=
  mq * aq

/-- The table product's magnitude, spelled out. -/
theorem newtonLHSQ_magnitude (mq : Quantity massK ℝ) (aq : Quantity accelerationK ℝ) :
    (newtonLHSQ mq aq).magnitude = mq.magnitude * aq.magnitude := rfl

/-- **`equationOfMotion_tfae`, consumed verbatim**: the equation of motion is
equivalent to the kinded Newton reading — `.out 0 1` of the upstream pentad, with only
the component bookkeeping proved here. -/
theorem equationOfMotion_iff_kinded_newton (S : HO) (xₜ : Time → E1)
    (hx : ContDiff ℝ ∞ xₜ) :
    S.EquationOfMotion xₜ ↔
      ∀ t, (newtonLHSQ (massQ S) (accelerationAtQ xₜ t)).magnitude
        = (forceAtQ S xₜ t).magnitude := by
  have htfae := (S.equationOfMotion_tfae xₜ hx).out 0 1
  rw [htfae]
  refine forall_congr' fun t => ?_
  rw [newtonLHSQ_magnitude]
  constructor
  · intro h
    have h0 := congrArg (fun v : E1 => v 0) h
    simpa using h0
  · intro h
    ext i
    fin_cases i
    simpa using h

/-! ## F5 — two ω's, the trig boundary, and the complex number that packs two lengths -/

/-- The trajectory parameter, read at 3-9. -/
@[kindIngest]
def durationQ (t : Time) : Quantity durationK ℝ :=
  .attest "the trajectory parameter" t.val

/-- **The trig boundary's licence**: `ω·t` through the registered edge lands at the
phase angle — one `*`, dimensionless, and only *then* does `cos` consume it. -/
noncomputable def phaseQ (ωq : Quantity angularFrequencyK ℝ)
    (tq : Quantity durationK ℝ) : Quantity phaseAngleK ℝ :=
  ωq * tq

/-- The phase erases to the trajectory's own trig argument — definitionally. -/
theorem phaseQ_magnitude (S : HO) (t : Time) :
    (phaseQ (omegaQ (omegaSqQ S)) (durationQ t)).magnitude = S.ω * t.val := rfl

/-- The period — `2π/ω`, a crossing to 3-14 (the dimensionless `2π` cannot ride the
table). -/
@[kindCrossing]
noncomputable def periodQ (ωq : Quantity angularFrequencyK ℝ) :
    Quantity periodDurationK ℝ :=
  .attest "2π/ω — the repetition interval" (2 * Real.pi / ωq.magnitude)

/-- The crossing erases to upstream's `period` — definitionally. -/
theorem periodQ_magnitude (S : HO) :
    (periodQ (omegaQ (omegaSqQ S))).magnitude = S.period := rfl

/-- The initial displacement, component 0. -/
@[kindIngest]
def displacement0Q (IC : _root_.ClassicalMechanics.HarmonicOscillator.InitialConditions) :
    Quantity displacementK ℝ :=
  .attest "x₀ — the initial displacement" (IC.x₀ 0)

/-- The initial velocity, component 0. -/
@[kindIngest]
def velocity0Q (IC : _root_.ClassicalMechanics.HarmonicOscillator.InitialConditions) :
    Quantity velocityK ℝ :=
  .attest "v₀ — the initial velocity" (IC.v₀ 0)

/-- **The complex number that packs two lengths**: the amplitude–phase inverse embeds
`(x₀, v₀/ω)` as one `ℂ` — licensed exactly because `v₀/ω` came through the registered
velocity/angular-frequency edge, so both components are displacements; `‖z‖` is then a
displacement too (the amplitude), read off by a crossing. -/
@[kindCrossing]
noncomputable def amplitudeQ (xq imq : Quantity displacementK ℝ) :
    Quantity displacementK ℝ :=
  .attest "‖z‖ — the polar radius of two like-kind components"
    ‖(⟨xq.magnitude, imq.magnitude⟩ : ℂ)‖

/-- The amplitude reading erases to upstream's `fromInitialConditions` —
definitionally, `v₀/ω` and all. -/
theorem amplitudeQ_erases (S : HO)
    (IC : _root_.ClassicalMechanics.HarmonicOscillator.InitialConditions) :
    (amplitudeQ (displacement0Q IC)
      (velocity0Q IC / omegaQ (omegaSqQ S))).magnitude =
      (_root_.ClassicalMechanics.HarmonicOscillator.AmplitudePhase.fromInitialConditions
        S IC).A := rfl

/-- **The two subtrees' shared letter, separated**: the oscillator's `ω` (angular
frequency, 3-18) and the rigid body's `ω` (angular velocity, 3-12) are distinct kinds
at one dimension. -/
theorem angularFrequency_ne_angularVelocity : angularFrequencyK ≠ angularVelocityK := by
  decide

/-! ## F6 — the functional ingest and the second join -/

/-- The rigid body's total mass — the zeroth moment of the distribution functional,
`ρ(1)`. -/
@[kindIngest]
noncomputable def rbMassQ {d : ℕ} (R : RigidBody d) : Quantity massK ℝ :=
  .attest "ρ(1) — the zeroth moment of the mass distribution" R.mass

/-- An inertia-tensor entry — the second moment, at 4-7. The functional's reading:
mass × (the test function's kind). -/
@[kindIngest]
noncomputable def inertiaAtQ {d : ℕ} (R : RigidBody d) (i j : Fin d) :
    Quantity momentOfInertiaK ℝ :=
  .attest "the second moment δᵢⱼ|x|² − xᵢxⱼ of the mass distribution"
    (R.inertiaTensor i j)

/-- An angular-velocity component, read at 3-12. -/
@[kindIngest]
def omegaCompQ (ωv : Fin 3 → ℝ) (j : Fin 3) : Quantity angularVelocityK ℝ :=
  .attest "an angular-velocity component" (ωv j)

/-- **`L = I·ω`, entrywise through the table**: the contraction is a same-kind sum of
`I·ω` edge products — three `*`, two `+`. -/
noncomputable def angularMomentumFromTableQ (R : RigidBody 3) (ωv : Fin 3 → ℝ)
    (i : Fin 3) : Quantity angularMomentumK ℝ :=
  inertiaAtQ R i 0 * omegaCompQ ωv 0 + inertiaAtQ R i 1 * omegaCompQ ωv 1
    + inertiaAtQ R i 2 * omegaCompQ ωv 2

/-- **Upstream's `L = I ω` theorem closes the contraction**: the table-built entry is
the angular momentum's. -/
theorem angularMomentumFromTableQ_erases (R : RigidBody 3) (ωv : Fin 3 → ℝ) (i : Fin 3) :
    (angularMomentumFromTableQ R ωv i).magnitude = R.angularMomentum ωv i := by
  rw [R.angularMomentum_eq_inertiaTensor_mulVec]
  show R.inertiaTensor i 0 * ωv 0 + R.inertiaTensor i 1 * ωv 1
      + R.inertiaTensor i 2 * ωv 2 = _
  simp [Matrix.mulVec, dotProduct, Fin.sum_univ_three]

/-- König's first summand: the translational kinetic energy of the centre of mass. -/
@[kindIngest]
noncomputable def translationalKEQ (M : RigidBodyMotion 3) (t : Time) :
    Quantity translationalKineticEnergyK ℝ :=
  .attest "½M⟪V,V⟫ — the centre of mass's kinetic energy"
    ((1 / (2 : ℝ)) * M.mass * ⟪M.centerOfMassVelocity t, M.centerOfMassVelocity t⟫_ℝ)

/-- König's second summand: the rotational kinetic energy about the centre of mass,
evaluated from the body-frame angular velocity. -/
@[kindIngest]
noncomputable def rotationalKEQ (M : RigidBodyMotion 3) (t : Time) :
    Quantity rotationalKineticEnergyK ℝ :=
  .attest "½ω·(Iω) — the rotational energy, body frame"
    (M.toRigidBody.rotationalKineticEnergy (M.bodyAngularVelocity t))

/-- **The second join, consumed**: König's split elaborates through the curated table
and lands at kinetic energy. -/
noncomputable def koenigQ (Tq : Quantity translationalKineticEnergyK ℝ)
    (Rq : Quantity rotationalKineticEnergyK ℝ) : Quantity kineticEnergyK ℝ :=
  Tq + Rq

/-- **Upstream's body-frame König theorem closes the join**: the split's sum is the
total kinetic energy. -/
theorem koenigQ_erases (M : RigidBodyMotion 3) (t : Time) (h : M.mass ≠ 0)
    (hR : DifferentiableAt ℝ (fun s => (M.orientation s).1) t)
    (hc : M.centerOfMass = 0) :
    (koenigQ (translationalKEQ M t) (rotationalKEQ M t)).magnitude =
      M.kineticEnergy t :=
  (M.kineticEnergy_eq_translational_add_bodyAngularVelocity t h hR hc).symm

/- **F6a.** A lab-frame reading plus a body-frame reading of `ω` still *adds* — both
are angular velocities, and the kind layer separates kinds, not frames: frame
discrimination is Exhibit A's `toFrameScalar` machinery, not this directory's. Pinned
as an example rather than a refusal — scope honesty (MR18). -/
noncomputable example (M : RigidBodyMotion 3) (t : Time) (i : Fin 3) :
    Quantity angularVelocityK ℝ :=
  omegaCompQ (M.angularVelocity t) i + omegaCompQ (M.bodyAngularVelocity t) i

end ForPhysLib.ClassicalMechanics
