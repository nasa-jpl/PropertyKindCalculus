/-
# Case study — the shared subject

[physlib#1612](https://github.com/leanprover-community/physlib/pull/1612) (head `3ae4ae20`,
unmerged) is the occasion, and the question it raises is narrower than the harmonic
oscillator's: **how does a quantity say which object it is a quantity of, and what does each
answer cost?** The PR answers with a `target` *field*; this case study puts that answer beside
three others and scores them.

Everything the four attempts share lives here, so that what differs between them is *only*
the typing of a force and of a per-particle quantity — the variable under study, and nothing
else.

## The system

`Particle` and `System` reproduce #1612's shape: a mass and a trajectory, and a system that
is a frame plus a **multiset** of particles, coerced to a type. Two properties of that shape
matter and both are the PR's own doing:

  * a particle has **no identity of its own** — no id, no name, no `DecidableEq` written for
    it. It is a *position* in a multiset. Every attempt below has to say something about an
    object that cannot be named;
  * multiplicity is kept, so two identical particles are two particles, and the particle type
    is a `Multiset.Fintype` coercion rather than a `Finset` subtype.

What is *not* reproduced: differentiability, `Time.deriv`, Newton's laws as structure fields,
and the force sum. Velocity and acceleration are fields here rather than derivatives, because
the derivation is orthogonal to the object question and carrying it would triple the file
without changing a single verdict. The PR's own three files were compiled verbatim out of
tree, against the same PhysLib commit, and the findings were established there first.

## The physics the attempts have to express

Five statements, chosen because each one fails differently under a different typing:

1. **Newton's second law**, per particle: `netForce p = p.mass • p.acceleration`. A *scalar*
   quantity acting on a *vector* one — `Quantity.smulK`, not `mul`.
2. **Newton's third law**: an internal force and its reverse are the same multiset. The
   reverse *swaps source and target*, which is a statement about an ordered **pair** of
   objects.
3. **The aggregates**: the system's mass and momentum are the sums of the particles'.
4. **The aggregate that is not one**: the sum of the particles' velocities is not the
   system's velocity, and the sum of their positions is nothing at all.
5. **The resultant that is not an aggregate**: the net force on one particle is a sum over
   several forces, and refusing *that* would be wrong. The two sums differ in whether the
   object changes.
-/

module

public import Mathlib.Data.Multiset.Fintype
public import Physlib.SpaceAndTime.ReferenceFrame
public import PropertyKindCalculus.CompositeReal
public import PropertyKindCalculus.QuantityReal
public import PropertyKindCalculus.Iso80000.Part3
public import PropertyKindCalculus.Iso80000.Part4

public section -- pkc-blanket
@[expose] section -- pkc-blanket-expose

namespace ForPhysLib.CaseStudies.PointParticle

open PropertyKindCalculus ClassicalMechanics

-- As in the PR: coercing a multiset to a type needs `DecidableEq` on the element type, and a
-- particle carries functions. #1612 opens `Classical` for exactly this reason.
open scoped Classical

noncomputable section

/-! ## The replica -/

variable {d : ℕ}

/-- A point particle in `frame`, after #1612's `PointParticle.Defs`: a mass and a trajectory,
and **no identity of its own**. -/
structure Particle (frame : ReferenceFrame d) where
  /-- The particle's mass. -/
  mass : ℝ
  /-- The particle's position in frame coordinates. -/
  pos : Time → frame.Vector
  /-- The particle's velocity (`Time.deriv pos` in the PR). -/
  velocity : Time → frame.Vector
  /-- The particle's acceleration (`Time.deriv velocity` in the PR). -/
  acceleration : Time → frame.Vector

/-- A system of point particles, after #1612's `NewtonianSystem.Defs`: a frame and a
**multiset** of particles. -/
structure System (d : ℕ) where
  /-- The system's reference frame. -/
  frame : ReferenceFrame d
  /-- The particles in the system. -/
  particles : Multiset (Particle frame)

namespace System

variable (s : System d)

/-- Vectors in the system's frame. -/
abbrev Vector := s.frame.Vector

/-- **A particle of the system** — the PR's own `abbrev Particle : Type := system.particles`,
the `Multiset.Fintype` coercion. An element is a *position* in the multiset: anonymous, and
distinguishable from every other position. -/
abbrev Particle : Type := s.particles

namespace Particle
variable {s : System d} (p : s.Particle) (t : Time)

/-- The particle's mass. -/
def mass : ℝ := p.1.mass
/-- The particle's position at `t`. -/
def pos : s.Vector := p.1.pos t
/-- The particle's velocity at `t`. -/
def velocity : s.Vector := p.1.velocity t
/-- The particle's acceleration at `t`. -/
def acceleration : s.Vector := p.1.acceleration t
/-- The particle's momentum at `t`. -/
def momentum : s.Vector := p.mass • p.velocity t

end Particle

/-- Total mass — the PR's aggregate, verbatim in shape. -/
def mass : ℝ := ∑ p : s.Particle, p.mass
/-- Total momentum at `t` — likewise. -/
def momentum (t : Time) : s.Vector := ∑ p : s.Particle, p.momentum t

end System

/-! ## The kind vocabulary — seven catalogue lookups, no mints

Every quantity the PR introduces is already an ISO 80000 item this repository holds. Adopting
a metrology layer for this PR mints nothing, which is worth stating before any attempt is
scored: the cost being measured is *typing*, not vocabulary. -/

/-- Mass — the catalogue's own 4-1. -/
def massK : KindOfProperty := (Iso80000.Part4.mass).kind
/-- Momentum — 4-8. -/
def momentumK : KindOfProperty := (Iso80000.Part4.momentum).kind
/-- Force — 4-9.1. -/
def forceK : KindOfProperty := (Iso80000.Part4.force).kind
/-- Kinetic energy — 4-25.1. -/
def kineticEnergyK : KindOfProperty := (Iso80000.Part4.kineticEnergy).kind
/-- Displacement — 3-1.11. -/
def displacementK : KindOfProperty := (Iso80000.Part3.displacement).kind
/-- Velocity — 3-10.1. -/
def velocityK : KindOfProperty := (Iso80000.Part3.velocity).kind
/-- Acceleration — 3-11. -/
def accelerationK : KindOfProperty := (Iso80000.Part3.acceleration).kind

/-- `m · a → F` — Newton's second law as a kind law. -/
theorem newtonEdge : ProductKind massK accelerationK forceK := ProductKind.ofRatio _ _ _
/-- `m · v → p` — the momentum edge. -/
theorem momentumEdge : ProductKind massK velocityK momentumK := ProductKind.ofRatio _ _ _

/-! ## What the object layer needs, registered once

Three registrations, and each is a claim rather than a formality. -/

/-- **The frame vector joins the carrier vocabulary** — `Carrier.ofZeroAdd` over PhysLib's own
`AddCommGroup frame.Vector`, which is the per-application decision `Carrier.ofZeroAdd` exists
to be. Registered here so that every refusal in the attempts below fails for exactly one
reason: without it, two vector quantities would fail to add whatever their kinds, and a kind
gate would be demonstrating nothing. -/
instance vectorCarrier {d : ℕ} (frame : ReferenceFrame d) : Carrier frame.Vector :=
  Carrier.ofZeroAdd _

/-- **The sort of whole** these systems compose — §20's "sort of system", minted once. The
assembly licenses are keyed by it: whether a kind aggregates is a fact about the sort of the
whole (volume over a rigid assembly versus over a mixture is the canonical split), and a
point-particle system is one sort. -/
def pointSystemS : SortOfSystem := ⟨"point-particle system"⟩

/-- Mass assembles: the system's mass is the sum of the particles'. -/
instance : Assembles pointSystemS massK := ⟨DifferenceKind.ofScale⟩
/-- Momentum assembles: the system's momentum is the sum of the particles'. -/
instance : Assembles pointSystemS momentumK := ⟨DifferenceKind.ofScale⟩
/-- Force assembles: the net force on the system is the sum of the net forces on its
particles. This is the registration momentum conservation rests on, and it is a *claim* —
Newton's third law is what makes the internal contributions cancel. -/
instance : Assembles pointSystemS forceK := ⟨DifferenceKind.ofScale⟩

-- Deliberately absent: `Assembles pointSystemS velocityK` and
-- `Assembles pointSystemS displacementK`. The sum of the particles' velocities is not the
-- system's velocity, and the sum of their positions is not a position at all. Attempts 3 and 4 refuse both; attempts 1 and 2 accept both.

end

end ForPhysLib.CaseStudies.PointParticle

end -- pkc-blanket-expose
end -- pkc-blanket
