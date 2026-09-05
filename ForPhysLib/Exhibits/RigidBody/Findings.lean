/-
# Exhibit A — RigidBody: the findings

**Source.** `Physlib/ClassicalMechanics/RigidBody/{AngularVelocity,Motion,KineticEnergy,
AngularMomentum}.lean`, imported below and probed directly — every claim here is a build
artifact against the real modules, per rule 2 of the
[rules of engagement](../../PLAN.md#rules-of-engagement).

**The defects, each exhibited by an `example` that should not type-check but does:**

1. **Velocity `+` momentum compiles, and either one displaces a position** (MR1).
   `centerOfMassVelocity` and `linearMomentum` are both `Time → EuclideanSpace ℝ (Fin d)`,
   so they add; `comTrajectory` is a `Space d` point over that same displacement space, so
   `+ᵥ` takes a momentum as readily as a velocity. PhysLib's affine typing (#1603) separates
   a point from a vector — the sum `position + momentum` is a type error below — and leaves
   the two vector *kinds* sharing one type.
2. **The lab/body mismatch** (M5). `angularVelocity` and `bodyAngularVelocity` are both
   `Time → Fin 3 → ℝ`; the inertia tensor is body-fixed, and
   `kineticEnergy_eq_translational_add_bodyAngularVelocity`'s own docstring is the only
   thing that says `rotationalKineticEnergy` must be fed `ω_body`. Feeding it the spatial
   `ω` type-checks — the constraint is enforced by not confusing two names.
3. **An indexed family is not a vector** (MR19). `ω : Fin 3 → ℝ` is a family of reals, so
   the pointwise product `ω * ω` — a per-axis list of squared coefficients, not any
   physical operation — elaborates via `Pi.instMul`.

**The kinded counter-forms**, and where the ceremony visibly returns something:
`rotationalContraction` states `ω · (I ω)` once, over any dimension `n`, any kinds under
their `ProductKind` laws, and any scalar carrier — where PhysLib's route through the hat
map pins `angularVelocity` and everything downstream to `d = 3`. The frame index then makes
finding 2 *unwritable* (`#check_failure`), and `ScalarCarrier` makes finding 3 unwritable,
while the body-frame form still bridges to PhysLib's own `rotationalKineticEnergy` by a
two-line computation. The König split closes the file: translational and rotational halves
read in *different* frames, combined only through `toFrameScalar` — the transport that is
free exactly because energy is scalar-variance (MR18: what survives a change of frame).
-/

import Physlib.ClassicalMechanics.RigidBody.KineticEnergy
import PropertyKindCalculus.Frame
import PropertyKindCalculus.Iso80000.Part3
import PropertyKindCalculus.Iso80000.Part4
import PropertyKindCalculus.QuantityReal
import ForPhysLib.Kinds.Space

namespace ForPhysLib.Exhibits.RigidBody

open PropertyKindCalculus

/-! ## Finding 1 — velocity + momentum compiles (MR1)

`comTrajectory` is a point of `Space 3`; `centerOfMassVelocity` and `linearMomentum` are
vectors of `EuclideanSpace ℝ (Fin 3)`, the space that acts on it. The point/vector half of
this finding is a type error upstream — the two `#check_failure`s record it, so a
regression here fails the build. What the affine typing does not distinguish is one vector
from another: a velocity and a momentum are one type, and the torsor action takes either. -/

/- A centre-of-mass position plus a linear momentum: no longer a sum. -/
#check_failure fun (M : RigidBodyMotion 3) (t : Time) =>
  M.comTrajectory t + M.linearMomentum t

/- A velocity plus a position — the other pairing, equally rejected. -/
#check_failure fun (M : RigidBodyMotion 3) (t : Time) =>
  M.centerOfMassVelocity t + M.comTrajectory t

/-- A velocity plus a momentum: one type, two kinds, and the sum elaborates. -/
noncomputable example (M : RigidBodyMotion 3) (t : Time) : EuclideanSpace ℝ (Fin 3) :=
  M.centerOfMassVelocity t + M.linearMomentum t

/-- The torsor action displaces a centre-of-mass position by a *momentum*: `+ᵥ` asks for a
vector of the displacement space, and a momentum is one. -/
noncomputable example (M : RigidBodyMotion 3) (t : Time) : Space 3 :=
  M.linearMomentum t +ᵥ M.comTrajectory t

/-- The same action fed the velocity — the reading `+ᵥ` is built for, and the one it cannot
tell from the line above. -/
noncomputable example (M : RigidBodyMotion 3) (t : Time) : Space 3 :=
  M.centerOfMassVelocity t +ᵥ M.comTrajectory t

/-! ## Finding 2 — the lab/body mismatch (M5)

The inertia tensor lives in body-fixed axes; the spatial `ω` does not. The contraction
below is the wrong physics whenever the body is actually rotating, and nothing rejects
it — the correct call in `KineticEnergy.lean` differs only by the *name* of its argument. -/

/-- The body-fixed inertia tensor contracted with the **spatial** angular velocity:
type-correct, physically wrong. -/
noncomputable example (M : RigidBodyMotion 3) (t : Time) : ℝ :=
  M.toRigidBody.rotationalKineticEnergy (M.angularVelocity t)

/-- The spatial and body-frame readings of the same angular velocity even *add*:
a mixed-frame vector with no meaning in either frame. -/
noncomputable example (M : RigidBodyMotion 3) (t : Time) : Fin 3 → ℝ :=
  M.angularVelocity t + M.bodyAngularVelocity t

/-! ## Finding 3 — an indexed family is not a vector (MR19) -/

/-- The pointwise product of an angular velocity with itself — squared coefficients,
per axis, which no change of basis respects — elaborates via `Pi.instMul`. -/
noncomputable example (M : RigidBodyMotion 3) (t : Time) : Fin 3 → ℝ :=
  M.angularVelocity t * M.angularVelocity t

/-! ## The kinded counter-forms

A small vocabulary for the directory — all ratio-scale, with the two product laws the
rotational contraction uses. The two frames are the ones the source's own docstrings
name: the inertial lab frame and the co-rotating body frame. -/

/-- Angular velocity — what `RigidBodyMotion.angularVelocity` reads; the catalogue's
own 3-12. -/
def angularVelocityK : KindOfProperty := (Iso80000.Part3.angularVelocity).kind

/-- Moment of inertia — what `RigidBody.inertiaTensor` holds, body-fixed; the
catalogue's own 4-7. -/
def momentOfInertiaK : KindOfProperty := (Iso80000.Part4.momentOfInertia).kind

/-- Angular momentum — `L = I ω`; the catalogue's own 4-11. -/
def angularMomentumK : KindOfProperty := (Iso80000.Part4.angularMomentum).kind

/-- Kinetic energy — where both halves of the König split land; the catalogue's own
4-28.2. -/
def kineticEnergyK : KindOfProperty := (Iso80000.Part4.kineticEnergy).kind

/-- Velocity — the translational half's first factor; the catalogue's own 3-10.1. -/
def velocityK : KindOfProperty := (Iso80000.Part3.velocity).kind

/-- Momentum — the translational half's second factor; the catalogue's own 4-8. -/
def linearMomentumK : KindOfProperty := (Iso80000.Part4.momentum).kind

/-- `I · ω` lands at angular momentum. -/
theorem inertia_mul_angularVelocity :
    ProductKind momentOfInertiaK angularVelocityK angularMomentumK :=
  ProductKind.ofRatio _ _ _

/-- `ω · L` lands at (twice the) kinetic energy — one kind; the factor 2 is a number. -/
theorem angularVelocity_mul_angularMomentum :
    ProductKind angularVelocityK angularMomentumK kineticEnergyK :=
  ProductKind.ofRatio _ _ _

/-- `v · p` lands at (twice the) kinetic energy likewise. -/
theorem velocity_mul_linearMomentum :
    ProductKind velocityK linearMomentumK kineticEnergyK :=
  ProductKind.ofRatio _ _ _

/-- Kinetic energies subtract — ratio scale allows difference. -/
theorem kineticEnergy_diff : DifferenceKind kineticEnergyK := .ofScale

/-- The inertial frame the trajectories of `RigidBodyMotion` are written in. -/
def lab : Frame := ⟨"lab"⟩

/-- The co-rotating frame in which the mass distribution is time-independent. -/
def body : Frame := ⟨"body"⟩

/-! ## The rotational contraction, stated once

Generic in the dimension `n`, the kinds (under their product laws) and the scalar
carrier. PhysLib's `angularVelocity` exists only at `d = 3` because it is dual to the
tensor through the hat map; the contraction below never consults the hat map, so the
kind-generic statement is dimension-generic for free. -/

/-- A rank-2 quantity applied to a vector quantity, in a shared frame: `(T x)ᵢ = Σⱼ Tᵢⱼ xⱼ`,
at the product kind. The shared frame `f` is the gate finding 2 lacked. -/
def applyRank2 {f : Frame} {n : Nat} {R : Type} [Zero R] [Add R] [Mul R] [ScalarCarrier R]
    {k₁ k₂ k : KindOfProperty} (_h : ProductKind k₁ k₂ k)
    (T : InFrame f .rank2 k₁ (Fin n → Fin n → R)) (x : InFrame f .vector k₂ (Fin n → R)) :
    InFrame f .vector k (Fin n → R) :=
  ⟨⟨fun i => sumFin (fun j => T.components i j * x.components j)⟩⟩

/-- `ω · (I ω)` — twice the rotational kinetic energy, as one contraction in one frame:
kind-generic, dimension-generic, carrier-generic. -/
def rotationalContraction {f : Frame} {n : Nat} {R : Type}
    [Zero R] [Add R] [Mul R] [ScalarCarrier R] {kI kω kL kE : KindOfProperty}
    (hIω : ProductKind kI kω kL) (hωL : ProductKind kω kL kE)
    (I : InFrame f .rank2 kI (Fin n → Fin n → R)) (ω : InFrame f .vector kω (Fin n → R)) :
    InFrame f .scalar kE R :=
  InFrame.dot hωL ω (applyRank2 hIω I ω)

/-- PhysLib's body-fixed inertia tensor, read where it lives: the body frame, rank 2. -/
noncomputable def bodyInertia (M : RigidBodyMotion 3) :
    InFrame body .rank2 momentOfInertiaK (Fin 3 → Fin 3 → ℝ) :=
  ⟨.attest "PhysLib's body-fixed inertia tensor, read in the body frame"
    (fun i j => M.toRigidBody.inertiaTensor i j)⟩

/-- PhysLib's body-frame angular velocity `ω_body`, read in the body frame. -/
noncomputable def bodyOmega (M : RigidBodyMotion 3) (t : Time) :
    InFrame body .vector angularVelocityK (Fin 3 → ℝ) :=
  ⟨.attest "PhysLib's body-frame angular velocity vector" (M.bodyAngularVelocity t)⟩

/-- PhysLib's spatial angular velocity `ω`, read in the lab frame. -/
noncomputable def labOmega (M : RigidBodyMotion 3) (t : Time) :
    InFrame lab .vector angularVelocityK (Fin 3 → ℝ) :=
  ⟨.attest "PhysLib's spatial angular velocity vector" (M.angularVelocity t)⟩

/-- The correct contraction — everything in the body frame — elaborates. -/
noncomputable example (M : RigidBodyMotion 3) (t : Time) :
    InFrame body .scalar kineticEnergyK ℝ :=
  rotationalContraction inertia_mul_angularVelocity angularVelocity_mul_angularMomentum
    (bodyInertia M) (bodyOmega M t)

/- **Finding 2, closed.** The body-fixed tensor against the spatial `ω` — the very
expression finding 2 exhibited — is now a type error, not a convention. -/
#check_failure fun (M : RigidBodyMotion 3) (t : Time) =>
  rotationalContraction inertia_mul_angularVelocity angularVelocity_mul_angularMomentum
    (bodyInertia M) (labOmega M t)

/- **Finding 2's sum, closed.** Lab and body readings no longer add. -/
#check_failure fun (M : RigidBodyMotion 3) (t : Time) =>
  InFrame.add (DifferenceKind.ofScale) (labOmega M t) (bodyOmega M t)

/- **Finding 3, closed.** `Quantity.mul` demands `ScalarCarrier`, and `Fin 3 → ℝ` is
not one: the pointwise product is unwritable at a kinded vector. -/
#check_failure fun (h : ProductKind angularVelocityK angularVelocityK kineticEnergyK)
    (x : Quantity angularVelocityK (Fin 3 → ℝ)) => Quantity.mul h x x

/- **Finding 1, closed.** A position and a linear momentum on the same carrier do not
add — `Quantity`'s homogeneous `instAdd` refuses distinct kinds. -/
#check_failure fun (p : Quantity Kinds.Space.positionVector (EuclideanSpace ℝ (Fin 3)))
    (l : Quantity linearMomentumK (EuclideanSpace ℝ (Fin 3))) => p + l

/- **Finding 1's residue, closed.** The half the affine typing leaves open closes at the
same instance: a velocity and a momentum are distinct kinds on one carrier, so their sum is
unwritable — and no displacement action can substitute one for the other, there being no
carrier-blind `+ᵥ` at a kind. -/
#check_failure fun (v : Quantity velocityK (EuclideanSpace ℝ (Fin 3)))
    (l : Quantity linearMomentumK (EuclideanSpace ℝ (Fin 3))) => v + l

/-- The contraction at `n = 7`, verbatim — the dimension-generality PhysLib's hat-map
route gives up. -/
noncomputable example (I : InFrame body .rank2 momentOfInertiaK (Fin 7 → Fin 7 → ℝ))
    (ω : InFrame body .vector angularVelocityK (Fin 7 → ℝ)) :
    InFrame body .scalar kineticEnergyK ℝ :=
  rotationalContraction inertia_mul_angularVelocity angularVelocity_mul_angularMomentum I ω

/-! ## The bridge to PhysLib, and the König split -/

/-- `sumFin` is `Finset.sum` — the bridge between PKC's recursion and Mathlib's sums. -/
theorem sumFin_eq_sum {R : Type} [AddCommMonoid R] :
    ∀ {n : ℕ} (v : Fin n → R), sumFin v = ∑ i, v i
  | 0, v => by simp
  | n + 1, v => by
    rw [sumFin_succ, sumFin_eq_sum (fun i => v i.succ), Fin.sum_univ_succ]

/-- **The bridge.** The kinded body-frame contraction *is* PhysLib's rotational kinetic
energy, doubled: the ceremony changed what elaborates, not what is computed. -/
theorem rotationalContraction_eq_physlib (M : RigidBodyMotion 3) (t : Time) :
    (rotationalContraction inertia_mul_angularVelocity angularVelocity_mul_angularMomentum
        (bodyInertia M) (bodyOmega M t)).components
      = 2 * M.toRigidBody.rotationalKineticEnergy (M.bodyAngularVelocity t) := by
  simp only [rotationalContraction, applyRank2, InFrame.dot, InFrame.components,
    RigidBody.rotationalKineticEnergy, Matrix.mulVec, dotProduct, sumFin_eq_sum,
    bodyInertia, bodyOmega, Quantity.attest]
  ring

/-- **The König split, kind-generic.** The translational half is read in the lab frame
(`V` is a lab velocity), the rotational half in the body frame (`I` is body-fixed) — as
in PhysLib's own `kineticEnergy_eq_translational_add_bodyAngularVelocity` — and the two
combine only through `toFrameScalar`: the transport that exists because energy carries
no basis index. One definition, every dimension, every carrier. -/
def koenigTwiceTotal {n : Nat} {R : Type}
    [Zero R] [Add R] [Mul R] [ScalarCarrier R] [Carrier R]
    {kv kp kI kω kL kE : KindOfProperty}
    (hE : DifferenceKind kE) (hvp : ProductKind kv kp kE)
    (hIω : ProductKind kI kω kL) (hωL : ProductKind kω kL kE)
    (v : InFrame lab .vector kv (Fin n → R)) (p : InFrame lab .vector kp (Fin n → R))
    (I : InFrame body .rank2 kI (Fin n → Fin n → R))
    (ω : InFrame body .vector kω (Fin n → R)) :
    InFrame body .scalar kE R :=
  InFrame.add hE (InFrame.toFrameScalar (InFrame.dot hvp v p))
    (rotationalContraction hIω hωL I ω)

/-- The split instantiated on PhysLib's own readings: `V`, `p = m V` in the lab,
`I`, `ω_body` in the body frame. It elaborates; nothing else in this file's vocabulary
would. -/
noncomputable example (M : RigidBodyMotion 3) (t : Time) :
    InFrame body .scalar kineticEnergyK ℝ :=
  koenigTwiceTotal kineticEnergy_diff velocity_mul_linearMomentum
    inertia_mul_angularVelocity angularVelocity_mul_angularMomentum
    ⟨.attest "PhysLib's centre-of-mass velocity, lab frame" (M.centerOfMassVelocity t).ofLp⟩
    ⟨.attest "PhysLib's linear momentum, lab frame" (M.linearMomentum t).ofLp⟩
    (bodyInertia M) (bodyOmega M t)

end ForPhysLib.Exhibits.RigidBody
