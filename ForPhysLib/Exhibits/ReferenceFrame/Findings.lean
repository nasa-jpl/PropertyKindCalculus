/-
# Exhibit B — ReferenceFrame: the findings

**Source.** `Physlib/SpaceAndTime/ReferenceFrame.lean` and its `API-map.yaml`, probed
directly below.

**Finding 1 — requirement 16 asks for one law where there are three (M7).** The API map's
undone requirement reads: *"…the boost, rotation and translation carrying one to the
other, together with **the** induced transformation law for frame vectors."* But
`frame.Vector` deliberately records the frame and not the physical role — the module doc
says the transformation law *"must be supplied by the surrounding definitions"* — so the
induced law is not a function of the type. Three candidate laws are written below, all of
type `F.Vector → G.Vector`: geometric transport (right for a displacement), transport
with the boost subtracted (right for a velocity), transport with the origin shift added
(right for a relative position). One `example` applies all three to the *same* vector;
nothing selects, and nothing can. The layer arrives as the design input that makes
requirement 16 satisfiable: with a kind index the three laws get three types, and the
wrong pairing stops elaborating.

**Finding 2 — quieter, and not a defect (MR30).** `IsInertial.velocity` has the *same
type* as the displacement it is defined from, and its defining equation
`origin t₂ -ᵥ origin t₁ = (t₂ - t₁).val • velocity` balances `L = T · L·T⁻¹` only
because `.val` erased `Time` first. That is the Mathlib-interface tier: the erasure is
how the scalar action becomes available at all. The kinded restatement
`origin_displacement_eq` keeps the same proof term (`Classical.choose_spec`) while making
every erasure a visible `.magnitude` — and it discharges, kinded, the API map's undone
requirement 17 ("the defining property of an inertial frame's origin velocity").
`#kind_unkinded` measures the surface rather than scoring it.

**The shape of the change is small.** `KVector` below is `frame.Vector` with a kind
index: `componentEquiv`'s analogue is still where the kind is dropped and is still a
definitional equivalence, and `AddCommGroup`/`Module` still arrive by the same one-line
transfer — now per kind. The current `Vector` is the erasure of this one.
-/

import Physlib.SpaceAndTime.ReferenceFrame
import ForPhysLib.Kinded.Space
import PropertyKindCalculus.KindLedger
import PropertyKindCalculus.Iso80000.Part3
import PropertyKindCalculus.Iso80000.Part4

namespace ForPhysLib.Exhibits.ReferenceFrame

open PropertyKindCalculus ClassicalMechanics ForPhysLib.Kinds.Space

/-! ## Finding 1 — three laws, one type -/

variable {d : ℕ}

/-- Geometric transport: read the displacement `v` stands for at `t`, re-read it in `G`.
The right law **for a displacement**. -/
noncomputable def geometricTransport (F G : ReferenceFrame d) (t : Time) :
    F.Vector → G.Vector :=
  fun v => (ReferenceFrame.Vector.dispEquiv (frame := G) t).symm
    (ReferenceFrame.Vector.dispEquiv (frame := F) t v)

/-- Transport with the boost subtracted: the right law **for a velocity** measured in
`F`, when `G`'s origin moves at `u` relative to `F`. -/
noncomputable def boostTransport (F G : ReferenceFrame d) (t : Time)
    (u : EuclideanSpace ℝ (Fin d)) : F.Vector → G.Vector :=
  fun v => (ReferenceFrame.Vector.dispEquiv (frame := G) t).symm
    (ReferenceFrame.Vector.dispEquiv (frame := F) t v - u)

/-- Transport with the origin shift added: the right law **for a relative position**
read from `F`'s origin. -/
noncomputable def originShiftTransport (F G : ReferenceFrame d) (t : Time) :
    F.Vector → G.Vector :=
  fun v => (ReferenceFrame.Vector.dispEquiv (frame := G) t).symm
    (ReferenceFrame.Vector.dispEquiv (frame := F) t v + (F.origin t -ᵥ G.origin t))

/-- **The finding.** All three laws accept the *same* vector — requirement 16's "the
induced transformation law" is three laws, and `F.Vector` cannot say which one `v`
deserves. -/
noncomputable example (F G : ReferenceFrame 3) (t : Time) (u : EuclideanSpace ℝ (Fin 3))
    (v : F.Vector) : G.Vector × G.Vector × G.Vector :=
  (geometricTransport F G t v, boostTransport F G t u v, originShiftTransport F G t v)

/-! ## The design input — `Vector` gains a parameter

The kind rides along; the components and every structure transfer exactly as before.
`kComponentEquiv` is the analogue of `componentEquiv`: still the place the kind is
dropped, still definitional, and it stays exactly where it is. -/

/-- Velocity — what requirement 16's boost acts on; the catalogue's own 3-10.1. -/
def velocityK : KindOfProperty := (Iso80000.Part3.velocity).kind

/-- Force — sharing `frame.Vector` today with velocity and position; the catalogue's
own 4-9.1. -/
def forceK : KindOfProperty := (Iso80000.Part4.force).kind

/-- Duration — what `(t₂ - t₁).val` silently erases; the catalogue's own 3-9. -/
def durationK : KindOfProperty := (Iso80000.Part3.duration).kind

/-- `frame.Vector`, with the physical role stated: one carrier *per kind* instead of one
carrier. The current `Vector` is the erasure of this one. -/
structure KVector (F : ReferenceFrame d) (k : KindOfProperty) where
  /-- The quantity whose magnitude holds the components. -/
  q : Quantity k (Fin d → ℝ)

/-- The kind is dropped here and only here — `componentEquiv`, one kind at a time. -/
def kComponentEquiv (F : ReferenceFrame d) (k : KindOfProperty) :
    KVector F k ≃ (Fin d → ℝ) :=
  ⟨fun x => x.q.magnitude, fun c => ⟨⟨c⟩⟩, fun _ => rfl, fun _ => rfl⟩

/-- The additive structure survives, per kind — the same one-line transfer. -/
instance (F : ReferenceFrame d) (k : KindOfProperty) : AddCommGroup (KVector F k) :=
  (kComponentEquiv F k).addCommGroup

/-- The scalar action survives, per kind — likewise. -/
instance (F : ReferenceFrame d) (k : KindOfProperty) : Module ℝ (KVector F k) :=
  (kComponentEquiv F k).module ℝ

/-- Same kind, same frame: the componentwise calculations requirement 8 wants are
untouched. -/
example (F : ReferenceFrame d) (v w : KVector F velocityK) : KVector F velocityK :=
  v + w

/- A velocity and a force no longer share a carrier: the sum that `frame.Vector`
accepts today does not elaborate. -/
#check_failure fun (F : ReferenceFrame 3) (v : KVector F velocityK)
    (f : KVector F forceK) => v + f

/-- The three laws, three types. Each transport now *names* the kind it is the law for —
this is requirement 16 made satisfiable. -/
noncomputable def kGeometricTransport (F G : ReferenceFrame d) (t : Time) :
    KVector F displacement → KVector G displacement :=
  fun v => ⟨⟨((ReferenceFrame.Vector.dispEquiv (frame := G) t).symm
    ((ReferenceFrame.Vector.dispEquiv (frame := F) t) ⟨v.q.magnitude⟩)).components⟩⟩

/-- The boost law, only for velocities — the boost itself arrives kinded. -/
noncomputable def kBoostTransport (F G : ReferenceFrame d) (t : Time)
    (u : Quantity velocityK (EuclideanSpace ℝ (Fin d))) :
    KVector F velocityK → KVector G velocityK :=
  fun v => ⟨⟨((ReferenceFrame.Vector.dispEquiv (frame := G) t).symm
    ((ReferenceFrame.Vector.dispEquiv (frame := F) t) ⟨v.q.magnitude⟩
      - u.magnitude)).components⟩⟩

/- **Finding 1, closed.** The boost law applied to a displacement — the pairing nothing
prevented above — is now a type error. -/
#check_failure fun (F G : ReferenceFrame 3) (t : Time)
    (u : Quantity velocityK (EuclideanSpace ℝ (Fin 3)))
    (v : KVector F displacement) => kBoostTransport F G t u v

/-! ## Finding 2 — `IsInertial.velocity`, reported at the right tier -/

/-- A displacement between two points plus an inertial frame's origin velocity: one
carrier, so the sum elaborates. `L + L·T⁻¹`, accepted. -/
noncomputable example (F : ReferenceFrame d) (h : F.IsInertial) (p q : Space d) :
    EuclideanSpace ℝ (Fin d) :=
  (p -ᵥ q) + h.velocity

/-- The frame's origin velocity, kinded at the boundary. The magnitude is PhysLib's own
`Classical.choose`; only the reading changes. -/
noncomputable def frameVelocityQ {F : ReferenceFrame d} (h : F.IsInertial) :
    Quantity velocityK (EuclideanSpace ℝ (Fin d)) :=
  .attest "IsInertial.velocity — the chosen witness of origin_moves_uniformly" h.velocity

/-- The elapsed time, kinded — this is where `.val` stops being silent. -/
def elapsedQ (t₁ t₂ : Time) : Quantity durationK ℝ := ⟨(t₂ - t₁).val⟩

/-- **Requirement 17, discharged kinded.** The defining property of the origin velocity —
the API map lists it as not done — with the same proof term PhysLib would use
(`Classical.choose_spec`), and every erasure now a visible `.magnitude`: the
`L = T · L·T⁻¹` balance is carried *through* the boundary instead of *by* it. -/
theorem origin_displacement_eq (F : ReferenceFrame d) (h : F.IsInertial) (t₁ t₂ : Time) :
    (Kinded.Space.displacementQ (F.origin t₂) (F.origin t₁)).magnitude
      = (elapsedQ t₁ t₂).magnitude • (frameVelocityQ h).magnitude :=
  Classical.choose_spec h.origin_moves_uniformly t₁ t₂

/- The kinded readings no longer add: the sum accepted above is unwritable here. -/
#check_failure fun (F : ReferenceFrame 3) (h : F.IsInertial) (p q : Space 3) =>
  Kinded.Space.displacementQ p q + frameVelocityQ h

/-! ## The measured surface (MR30)

Not a score — a measurement, in the manner of Stage 4's ingest boundary: the erasure
sites of this exhibit's own boundary, counted by the ledger. -/

/-- The boundary this exhibit minted through: the frame velocity and the elapsed time. -/
def inertialBoundary : Provenance.Contract Provenance.NodeId Provenance.KindRef where
  name := "ReferenceFrame inertial boundary"
  members := [``ForPhysLib.Exhibits.ReferenceFrame.frameVelocityQ, ``ForPhysLib.Exhibits.ReferenceFrame.elapsedQ]
  ports := []
  exits := []

/--
info: unkinded ledger of 'ReferenceFrame inertial boundary':
unkinded: 2 position(s), 2 flow(s)
unkinded input elapsedQ/t₁ : Time
unkinded input elapsedQ/t₂ : Time
unkinded flow: elapsedQ/t₁ ⇒ elapsedQ/result
unkinded flow: elapsedQ/t₂ ⇒ elapsedQ/result
-/
#guard_msgs (whitespace := lax) in
#kind_unkinded inertialBoundary

end ForPhysLib.Exhibits.ReferenceFrame
