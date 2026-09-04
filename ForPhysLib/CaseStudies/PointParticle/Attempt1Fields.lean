/-
# Attempt 1 — the target is a field (physlib#1612 as written)

The PR's own answer, reproduced in shape: a force carries the object it acts on as a
**structure field**, and its value is a bare `frame.Vector`.

```lean
structure Force (frame : ReferenceFrame d) (Object : Type) where
  value : Time → frame.Vector
  target : Object
```

**What this gets right, and it is not nothing.** Before the PR there was no way at all to say
which object a force acts on; upstream's `frame.Vector` is a coordinate carrier and carries no
such information. The field says it, the objects are runtime-quantifiable (so Newton's laws
can be `∀ particle : particles` *fields* of the system), and the multiset keeps multiplicity.
None of that is available from a naming convention, and none of it is in question below.

**What a field cannot do.** A field is data the *value* carries, not information the *type*
carries, so it is available to a runtime test and invisible to the checker. Six consequences
below, each an `example` that type-checks and should not. They fall into three groups:

  * **the dimensional collapse** — `frame.Vector` is one carrier for every vector quantity, so
    a displacement, a velocity and a force of one particle all add (§3.1);
  * **the object is not consulted** — the mass of one particle scales another's acceleration;
    a force is retargeted by a record update; a whole-system total adds to a part (§3.2);
  * **the laws are unenforced** — `reverse` that forgets to swap type-checks, and the sum of
    the particles' velocities is as well-typed as the sum of their momenta (§3.3).

The last group is the one to watch, because it is about code that has not been written yet:
momentum conservation and the work–energy theorem are both aggregation laws, and nothing here
distinguishes an aggregation that is licensed from one that is not.
-/

import ForPhysLib.CaseStudies.PointParticle.Common

namespace ForPhysLib.CaseStudies.PointParticle.Attempt1

open PropertyKindCalculus ClassicalMechanics ForPhysLib.CaseStudies.PointParticle
open scoped Classical

noncomputable section

variable {d : ℕ} {s : System d}

/-! ## 1. The forces -/

/-- A time-dependent force acting on a particle — #1612's shape: the target is a field, the
value a bare frame vector. -/
structure Force (s : System d) where
  /-- The force vector. -/
  value : Time → s.Vector
  /-- The target object. -/
  target : s.Particle

/-- A force between two particles — the PR's `InternalForce`, source and target both fields. -/
structure InternalForce (s : System d) extends Force s where
  /-- The source object. -/
  source : s.Particle
  /-- A particle does not act on itself. -/
  source_ne_target : source ≠ target

/-- The equal-and-opposite force, source and target exchanged — the PR's `reverse`. -/
def InternalForce.reverse (f : InternalForce s) : InternalForce s where
  value := fun t => -f.value t
  target := f.source
  source := f.target
  source_ne_target := f.source_ne_target.symm

/-! ## 2. What the model can say -/

/-- The net force on a particle: the forces whose `target` field tests equal to it. The filter
is a **runtime equality test on a field**; the type system is not consulted, and the result
type is the same `s.Vector` whatever particle was asked for. -/
def netForce (fs : Multiset (Force s)) (p : s.Particle) (t : Time) : s.Vector :=
  ∑ f : fs with f.1.target = p, f.1.value t

/-- Newton's second law, per particle — the shape the PR carries as a structure field. -/
def NewtonII (fs : Multiset (Force s)) : Prop :=
  ∀ (p : s.Particle) (t : Time), netForce fs p t = p.mass • p.acceleration t

/-- Newton's third law — the PR's own statement. -/
def NewtonIII (fs : Multiset (InternalForce s)) : Prop :=
  fs.map InternalForce.reverse = fs

/-! ## 3. What the model cannot check

Each `example` below type-checks. That is the finding: not that any of them is *written* in
#1612, but that nothing stops the next contributor writing them. -/

/-! ### 3.1 The dimensional collapse — one carrier for every vector quantity -/

/-- A position plus a force. Accepted: both are `s.Vector`. -/
example (p : s.Particle) (f : Force s) (t : Time) : s.Vector := p.pos t + f.value t

/-- A velocity plus an acceleration. Accepted for the same reason. -/
example (p : s.Particle) (t : Time) : s.Vector := p.velocity t + p.acceleration t

/-- A mass plus a kinetic energy — the scalar face of the same collapse. -/
example (p : s.Particle) : ℝ := p.mass + (p.mass * 2)

/-! ### 3.2 The object is data, so the object is not consulted -/

/-- **The substitution nothing prevents.** One particle's mass scaling another's acceleration
— dimensionally impeccable, physically wrong, and accepted. This is the exact shape of a
copy-paste error in a system with more than one particle. -/
example (p q : s.Particle) (t : Time) : s.Vector := p.mass • q.acceleration t

/-- **A record update retargets a force.** `target` is a field, so a force *for* `p` and a
force *for* `q` are the same type and one becomes the other by `{ f with target := q }`.
Whatever the field is for, it is not a gate. -/
def misdeliver (f : Force s) (q : s.Particle) : Force s := { f with target := q }

/-- **The whole and the part are one type.** A system's total mass and a particle's mass are
both `ℝ`, so they add — and so a total that quietly includes itself is arithmetic, not a type
error. -/
example (p : s.Particle) : ℝ := s.mass + p.mass

/-! ### 3.3 The laws are prose

`reverse` and the aggregates are *definitions that happen to do the right thing*. Nothing in
their types says so, and the wrong versions below are as well-formed as the right ones. -/

/-- **A `reverse` that forgets to swap.** Negates the value, leaves source and target where
they were, and type-checks — so `NewtonIII` holds of it or not depending on arithmetic, with
the checker silent about the swap that is the whole content of the law. -/
def badReverse (f : InternalForce s) : InternalForce s :=
  { f with value := fun t => -f.value t }

/-- **The aggregation that is not one.** The sum of the particles' velocities, written exactly
as the sum of their momenta is written, and as well-typed. It is not the system's velocity;
it is not any quantity of the system. Nothing here can say so. -/
def sumOfVelocities (t : Time) : s.Vector := ∑ p : s.Particle, p.velocity t

/-- And the sum of their positions — a sum of *points*, which is not a quantity at all. -/
def sumOfPositions (t : Time) : s.Vector := ∑ p : s.Particle, p.pos t

/-- **The two sums that must be told apart.** The net force on one particle and the total
momentum of the system are both `∑ … , …` at the same type. One combines quantities *of one
object*; the other combines quantities *of different objects* into a quantity of a third.
Attempt 1 cannot distinguish them, which is why it cannot refuse `sumOfVelocities` while
accepting `netForce`. -/
example (fs : Multiset (Force s)) (p : s.Particle) (t : Time) : s.Vector × s.Vector :=
  (netForce fs p t, s.momentum t)

end

end ForPhysLib.CaseStudies.PointParticle.Attempt1
