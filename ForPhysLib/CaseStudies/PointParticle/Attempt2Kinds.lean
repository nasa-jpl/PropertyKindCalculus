/-
# Attempt 2 — kind the values, keep the target a field

The obvious next move, and the one a reader of the proposal's Stage 2 would reach for first:
leave #1612's shape alone and give every value its ISO 80000 kind.

```lean
structure Force (s : System d) where
  value  : Time → Quantity forceK s.Vector      -- was `s.Vector`
  target : s.Particle                           -- unchanged
```

**It works, and it is cheap.** Every erasure below is `rfl`: the kinded reading of a force,
of a momentum, of the system's total is definitionally the bare-vector one. Nothing about
#1612's ergonomics changes — the target is still a field, forces are still one multiset,
`netForce` is still a filter. This is the whole of the proposal's Stage 2 applied to this PR,
and on its own terms it succeeds.

**It closes exactly one of Attempt 1's three groups.** The dimensional collapse is gone: a
position and a force no longer share a type, and the sum that Attempt 1 accepted does not
elaborate. The other two groups are untouched, and for one reason — *the object is still
data*. A kind index says what is measured; it does not say whose. So:

  * one particle's mass still scales another's acceleration (§3.2), because a kind cannot
    tell two particles apart;
  * the sum of the particles' velocities is still as well-typed as the sum of their momenta
    (§3.3), because both are sums of same-kind quantities and there is no object to change.

That second point is the one that matters for what comes next. Momentum conservation and the
work–energy theorem are aggregation laws, and a kind-only layer has no vocabulary for the
difference between a sum that crosses objects and one that does not.
-/

import ForPhysLib.CaseStudies.PointParticle.Common

namespace ForPhysLib.CaseStudies.PointParticle.Attempt2

open PropertyKindCalculus ClassicalMechanics ForPhysLib.CaseStudies.PointParticle
open scoped Classical

noncomputable section

variable {d : ℕ} {s : System d}

/-! ## 1. The forces — one field changed -/

/-- A force, kinded: the value is a force *quantity*, the target still a field. -/
structure Force (s : System d) where
  /-- The force, at its kind. -/
  value : Time → Quantity forceK s.Vector
  /-- The target object. -/
  target : s.Particle

/-- An internal force, likewise. -/
structure InternalForce (s : System d) extends Force s where
  /-- The source object. -/
  source : s.Particle
  /-- A particle does not act on itself. -/
  source_ne_target : source ≠ target

/-- The reverse force. -/
def InternalForce.reverse (f : InternalForce s) : InternalForce s where
  value := fun t => ⟨-(f.value t).magnitude⟩
  target := f.source
  source := f.target
  source_ne_target := f.source_ne_target.symm

/-! ## 2. The readings, and the erasures

Each per-particle quantity is read at its kind. Every one of these is a *projection with a
kind attached* — the magnitude is upstream's own, so the erasure is `rfl` and no arithmetic
changes. -/

/-- The particle's mass, at 4-1. -/
def massQ (p : s.Particle) : Quantity massK ℝ := ⟨p.mass⟩
/-- The particle's velocity, at 3-10.1. -/
def velocityQ (p : s.Particle) (t : Time) : Quantity velocityK s.Vector := ⟨p.velocity t⟩
/-- The particle's acceleration, at 3-11. -/
def accelerationQ (p : s.Particle) (t : Time) : Quantity accelerationK s.Vector :=
  ⟨p.acceleration t⟩
/-- The particle's position, at 3-1.11. -/
def positionQ (p : s.Particle) (t : Time) : Quantity displacementK s.Vector := ⟨p.pos t⟩

/-- The particle's momentum, through the kind law rather than by assertion: `m · v → p`. -/
def momentumQ (p : s.Particle) (t : Time) : Quantity momentumK s.Vector :=
  Quantity.smulK momentumEdge (massQ p) (velocityQ p t)

/-- **The erasure.** The kinded momentum is upstream's `mass • velocity`, definitionally. -/
theorem momentumQ_erases (p : s.Particle) (t : Time) :
    (momentumQ p t).magnitude = p.momentum t := rfl

/-- The net force on a particle — the same filter, at the kind. -/
def netForce (fs : Multiset (Force s)) (p : s.Particle) (t : Time) :
    Quantity forceK s.Vector :=
  Quantity.resultantOver DifferenceKind.ofScale
    (Finset.univ.filter (fun f : fs => f.1.target = p)) (fun f => f.1.value t)

/-- The system's mass, at the kind. -/
def totalMassQ : Quantity massK ℝ :=
  Quantity.resultantOver DifferenceKind.ofScale Finset.univ (fun p : s.Particle => massQ p)

/-- The system's momentum, at the kind. -/
def totalMomentumQ (t : Time) : Quantity momentumK s.Vector :=
  Quantity.resultantOver DifferenceKind.ofScale Finset.univ
    (fun p : s.Particle => momentumQ p t)

/-- **The erasure, at the aggregate.** The system's total is upstream's own sum. -/
theorem totalMassQ_erases : (totalMassQ (s := s)).magnitude = s.mass := rfl

/-- The same for momentum. -/
theorem totalMomentumQ_erases (t : Time) :
    (totalMomentumQ (s := s) t).magnitude = s.momentum t := rfl

/-! ## 3. What is now checked — the dimensional collapse, closed

Every acceptance of Attempt 1 §3.1 is a refusal here, at exactly one carrier and with the
kinds as the only difference. -/

/-- Two forces on one particle add — the acceptance the refusals below must be read against. -/
example (f g : Quantity forceK s.Vector) : Quantity forceK s.Vector := f + g

/- A position plus a force: refused. -/
#check_failure fun {d : ℕ} {s : System d} (p : s.Particle) (f : Force s) (t : Time) =>
  positionQ p t + (f.value t)

/- A velocity plus an acceleration: refused. -/
#check_failure fun {d : ℕ} {s : System d} (p : s.Particle) (t : Time) =>
  velocityQ p t + accelerationQ p t

/- A mass plus a momentum: refused (and at two different carriers besides). -/
#check_failure fun {d : ℕ} {s : System d} (p : s.Particle) (t : Time) =>
  massQ p + momentumQ p t

/-! ## 4. What is still not checked — everything about the object

The three groups of Attempt 1 §3.2 and §3.3, re-run. Each still type-checks, and each does so
because *a kind index cannot tell two particles apart*. -/

/-- **Still accepted.** One particle's mass scaling another's acceleration. Both operands are
correctly kinded, the kind law is the right one, and the answer is wrong. -/
example (p q : s.Particle) (t : Time) : Quantity forceK s.Vector :=
  Quantity.smulK newtonEdge (massQ p) (accelerationQ q t)

/-- **Still accepted.** A force is retargeted by a record update. -/
def misdeliver (f : Force s) (q : s.Particle) : Force s := { f with target := q }

/-- **Still accepted.** The system's total mass adds to a particle's — same kind, and there is
nothing else to disagree about. -/
example (p : s.Particle) : Quantity massK ℝ := totalMassQ (s := s) + massQ p

/-- **Still accepted.** A `reverse` that negates and forgets to swap. -/
def badReverse (f : InternalForce s) : InternalForce s :=
  { f with value := fun t => ⟨-(f.value t).magnitude⟩ }

/-- **Still accepted, and this is the one that matters.** The sum of the particles'
velocities, written exactly as `totalMomentumQ` is written and as well-typed. A kind-only
layer has no way to say that momentum aggregates over parts and velocity does not, because it
has no vocabulary for "over parts" at all. -/
def sumOfVelocitiesQ (t : Time) : Quantity velocityK s.Vector :=
  Quantity.resultantOver DifferenceKind.ofScale Finset.univ
    (fun p : s.Particle => velocityQ p t)

/-- And the sum of their positions. -/
def sumOfPositionsQ (t : Time) : Quantity displacementK s.Vector :=
  Quantity.resultantOver DifferenceKind.ofScale Finset.univ
    (fun p : s.Particle => positionQ p t)

end

end ForPhysLib.CaseStudies.PointParticle.Attempt2
