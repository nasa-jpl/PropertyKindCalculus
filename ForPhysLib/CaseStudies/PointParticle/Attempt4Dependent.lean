/-
# Attempt 4 — the target stays a field, and the value's type depends on it

The win-win, and the whole point of the case study. Attempt 3 established that indexing works
and costs the PR its shape; this attempt keeps the shape.

```lean
structure Force (s : System d) where
  target : s.Particle                                                      -- #1612's field
  value  : Time → IndividualQuantity (Composite.part (σ := pointSystemS) target) forceK s.Vector
```

One line differs from #1612. `target` is still a field, so:

  * the forces are still **one multiset** — `Multiset (Force s)`, not a multiset of dependent
    pairs, and every construction site is #1612's record syntax unchanged;
  * `netForce` is still a **filter on the field**, and Newton's laws are still `∀ particle`
    statements that can be fields of the system;
  * `CoeFun` is still uniform — its result type now mentions `f.target`, which is exactly the
    information the field was carrying all along and the type was not.

And the metrology is in the type, because the value's type *reads the field*. Everything
Attempt 3 checks, Attempt 4 checks.

## Three things this buys that Attempt 3 did not

**Newton's third law becomes a type.** An internal force is a quantity of an ordered *pair*
of particles — the joint object shape — and `reverse` must return one at the *transposed*
pair. A reverse that negates the coupling's force and forgets to exchange the endpoints has
the wrong type and does not elaborate. That law was prose in Attempts 1, 2 *and* 3.

**Momentum conservation becomes statable about the right object.** The net force on the
system is an *assembly* of the net forces on its particles, so it lands at
`Composite.whole` — and the conservation law is an equation between two whole-system
quantities, not between two vectors that happen to have the same dimension.

**The two sums are told apart.** `netForce` is a *resultant* — several forces on one
particle, one object throughout, gated only by the scale. `totalMomentum` is an *assembly* —
quantities of different objects combined into a quantity of a third, gated by `Assembles`.
Attempts 1 and 2 wrote both with the same `∑` and could refuse neither; this attempt writes
them with different combinators and refuses the sum of the velocities while accepting the sum
of the forces.

## What it does not buy — the next gap, named

Kinetic energy is `½ m ‖v‖²`, and `‖·‖` takes a *vector* quantity to a *scalar* one. There is
no licensed form for that: `mul` wants one carrier, `smulK` wants the scalar on the left, and
neither is a norm. §6 pins the gap as a refusal rather than leaving it as a remark.
-/

module

public import ForPhysLib.CaseStudies.PointParticle.Common
-- Private scope only: the checks below reduce through bodies sealed in the core
-- library; `import all` gives this file the reduction without exposing them.
import all PropertyKindCalculus.IndividualQuantity

@[expose] public section

namespace ForPhysLib.CaseStudies.PointParticle.Attempt4

open PropertyKindCalculus ClassicalMechanics ForPhysLib.CaseStudies.PointParticle
open scoped Classical

noncomputable section

variable {d : ℕ} {s : System d}

/-! ## 1. The forces — one line changed from #1612 -/

/-- A force acting on a particle. `target` is a field, exactly as in the PR; the value's type
depends on it. -/
structure Force (s : System d) where
  /-- The target object. -/
  target : s.Particle
  /-- The force, at its kind, characterizing the target. -/
  value : Time → IndividualQuantity (Composite.part (σ := pointSystemS) target) forceK s.Vector

/-- The PR's `CoeFun`, unchanged in spirit: a force applies to a time. Its result type now
names the target, which is the information the field always carried. -/
instance : CoeFun (Force s)
    (fun f => Time → IndividualQuantity (Composite.part (σ := pointSystemS) f.target) forceK s.Vector) where
  coe := Force.value

/-- **An internal force is a quantity of a pair.** Source and target are both fields, as in
the PR; the value characterizes the *ordered pair* — the joint object shape. -/
structure InternalForce (s : System d) where
  /-- The source object. -/
  source : s.Particle
  /-- The target object. -/
  target : s.Particle
  /-- A particle does not act on itself. -/
  source_ne_target : source ≠ target
  /-- The force the pair exerts, at its kind, characterizing the coupling. -/
  value : Time → IndividualQuantity ((source, target) : s.Particle × s.Particle)
    forceK s.Vector

/-- **Newton's third law, as a type.** The reverse exchanges the endpoints, so its value must
be a quantity of the *transposed* pair — which is what `transpose` is for, and what the
negation alone cannot supply. -/
def InternalForce.reverse (f : InternalForce s) : InternalForce s where
  source := f.target
  target := f.source
  source_ne_target := f.source_ne_target.symm
  value := fun t => (-(f.value t)).transpose

/-- The reversal negates, and the magnitude says so definitionally. -/
theorem InternalForce.reverse_value_magnitude (f : InternalForce s) (t : Time) :
    (f.reverse.value t).magnitude = -(f.value t).magnitude := rfl

/-- **The delivery claim, written once.** The force a coupling `(q, p)` exerts *is* a force on
`p` — a modeling statement, not a coercion, which is why it is a named declaration with a
docstring rather than an instance. It is the only place a magnitude crosses from one object to
another in this attempt, and that is exactly the property that makes it auditable. -/
def InternalForce.actsOn (f : InternalForce s) (t : Time) :
    IndividualQuantity (Composite.part (σ := pointSystemS) f.target) forceK s.Vector :=
  ⟨(f.value t).magnitude⟩

/-! ## 2. The readings, and the erasures -/

/-- The particle's mass, of that particle. -/
def massQ (p : s.Particle) : IndividualQuantity (Composite.part (σ := pointSystemS) p) massK ℝ := ⟨p.mass⟩
/-- The particle's velocity. -/
def velocityQ (p : s.Particle) (t : Time) :
    IndividualQuantity (Composite.part (σ := pointSystemS) p) velocityK s.Vector := ⟨p.velocity t⟩
/-- The particle's acceleration. -/
def accelerationQ (p : s.Particle) (t : Time) :
    IndividualQuantity (Composite.part (σ := pointSystemS) p) accelerationK s.Vector := ⟨p.acceleration t⟩
/-- The particle's position. -/
def positionQ (p : s.Particle) (t : Time) :
    IndividualQuantity (Composite.part (σ := pointSystemS) p) displacementK s.Vector := ⟨p.pos t⟩
/-- The particle's momentum, through the kind law: `m · v → p`. -/
def momentumQ (p : s.Particle) (t : Time) :
    IndividualQuantity (Composite.part (σ := pointSystemS) p) momentumK s.Vector :=
  IndividualQuantity.smulK momentumEdge (massQ p) (velocityQ p t)

/-- **The erasure.** The kinded momentum is upstream's `mass • velocity`, definitionally. -/
theorem momentumQ_erases (p : s.Particle) (t : Time) :
    (momentumQ p t).magnitude = p.momentum t := rfl

/-! ## 3. The two sums, told apart

`netForce` combines several forces **of one object** — a resultant, gated by the scale alone.
`totalMomentum` combines quantities **of different objects** into a quantity of the whole — an
assembly, gated by `Assembles`. -/

/-- A stored force contributes to the net force on `p` when its target field is `p`. The
transport is the one piece of machinery the field-plus-dependent-value shape still costs, and
it is written once. -/
def contribution (p : s.Particle) (f : Force s) (t : Time) :
    IndividualQuantity (Composite.part (σ := pointSystemS) p) forceK s.Vector :=
  if h : f.target = p then h ▸ f.value t else ⟨0⟩

/-- **The resultant**: the net force on a particle, over #1612's own multiset of forces. -/
def netForce (fs : Multiset (Force s)) (p : s.Particle) (t : Time) :
    IndividualQuantity (Composite.part (σ := pointSystemS) p) forceK s.Vector :=
  resultantAll DifferenceKind.ofScale (fun f : fs => contribution p f.1 t)

/-- **Newton's second law**, per particle — and now an equation between two quantities of
*that particle*, at the force kind, with `m · a` a licensed scalar action rather than an
unchecked `•`. -/
def NewtonII (fs : Multiset (Force s)) : Prop :=
  ∀ (p : s.Particle) (t : Time),
    netForce fs p t = IndividualQuantity.smulK newtonEdge (massQ p) (accelerationQ p t)

/-- **The assembly**: the system's mass, a quantity of the whole. -/
def totalMassQ : IndividualQuantity (Composite.whole : Composite pointSystemS s.Particle) massK ℝ :=
  assembleAll pointSystemS Composite.whole Composite.part (massQ (s := s))

/-- The system's momentum, likewise. -/
def totalMomentumQ (t : Time) :
    IndividualQuantity (Composite.whole : Composite pointSystemS s.Particle) momentumK s.Vector :=
  assembleAll pointSystemS Composite.whole Composite.part (fun p => momentumQ p t)

/-- The net force on the *system* — the assembly of the net forces on its particles. This is
the registration `Assembles pointSystemS forceK` was made for, and it is what momentum conservation is an
equation about. -/
def totalForceQ (fs : Multiset (Force s)) (t : Time) :
    IndividualQuantity (Composite.whole : Composite pointSystemS s.Particle) forceK s.Vector :=
  assembleAll pointSystemS Composite.whole Composite.part (fun p => netForce fs p t)

/-- **The erasures.** Every total is upstream's own sum, definitionally — the layer adds a
gate and changes no arithmetic. -/
theorem totalMassQ_erases : (totalMassQ (s := s)).magnitude = s.mass := rfl

/-- Likewise for momentum. -/
theorem totalMomentumQ_erases (t : Time) :
    (totalMomentumQ (s := s) t).magnitude = s.momentum t := rfl

/-- **Momentum conservation, statable.** The rate of change of the system's momentum is the
net external force on the system: an equation between two quantities *of the whole*, each at
its own kind. Attempts 1 and 2 could write the same equation over `s.Vector` and it would have
said nothing about which object either side belonged to; here both sides name
`Composite.whole`, and a right-hand side assembled from the wrong particles is a type error.

Stated, not proved — the proof is the multiset involution Newton's third law supplies, and it
is #1612's to write. What the layer contributes is that the statement is about the system. -/
def MomentumConserved (fs : Multiset (Force s))
    (dpdt : Time → IndividualQuantity (Composite.whole : Composite pointSystemS s.Particle) forceK s.Vector) :
    Prop :=
  ∀ t : Time, dpdt t = totalForceQ fs t

/-! ## 4. Everything the earlier attempts could not check -/

/- The dimensional collapse (Attempt 1 §3.1): a position and a force of one particle. -/
#check_failure fun {d : ℕ} {s : System d} (p : s.Particle) (f : Force s) (t : Time) =>
  IndividualQuantity.add DifferenceKind.ofScale (positionQ p t) (f.value t)

/- The object substitution (Attempt 2 §4): one particle's mass scaling another's
acceleration. -/
#check_failure fun {d : ℕ} {s : System d} (p q : s.Particle) (t : Time) =>
  IndividualQuantity.smulK newtonEdge (massQ p) (accelerationQ q t)

/- Two particles' masses do not add. -/
#check_failure fun {d : ℕ} {s : System d} (p q : s.Particle) =>
  IndividualQuantity.add (k := massK) DifferenceKind.ofScale (massQ p) (massQ q)

/- The whole is not a part (MR22). -/
#check_failure fun {d : ℕ} {s : System d} (p : s.Particle) =>
  IndividualQuantity.add (k := massK) DifferenceKind.ofScale (totalMassQ (s := s)) (massQ p)

/- The unlicensed aggregation: no `Assembles pointSystemS velocityK`, so no system velocity. -/
#check_failure fun {d : ℕ} {s : System d} =>
  assembleAll (k := velocityK) pointSystemS
    (Composite.whole : Composite pointSystemS s.Particle) Composite.part
    (fun p => velocityQ p (0 : Time))

/- Nor a sum of positions. -/
#check_failure fun {d : ℕ} {s : System d} =>
  assembleAll (k := displacementK) pointSystemS
    (Composite.whole : Composite pointSystemS s.Particle) Composite.part
    (fun p => positionQ p (0 : Time))

/-! ## 5. The third law, checked

The refusal Attempts 1–3 could not produce. -/

/-- A coupling's force reads at the pair. -/
example (f : InternalForce s) (t : Time) :
    IndividualQuantity ((f.source, f.target) : s.Particle × s.Particle) forceK s.Vector :=
  f.value t

/- **The bad reverse.** Negate the coupling's force, exchange the endpoint *fields*, and
forget to transpose the value: the value is a quantity of `(source, target)` where a reversed
force must be one of `(target, source)`. This is the definition that type-checked in every
earlier attempt. (It is written with the negation *operator*, which is why the check bites —
unwrapping to `⟨-…magnitude⟩` would rewrap at whatever object the field expects, and the
constructor is the boundary here as it is everywhere else in the layer.) -/
#check_failure fun {d : ℕ} {s : System d} (f : InternalForce s) =>
  ({ source := f.target, target := f.source,
     source_ne_target := f.source_ne_target.symm,
     value := fun t => -(f.value t) } : InternalForce s)

/- And a coupling's force is not, without the delivery claim, a force on its target: the two
quantities have different objects, and `actsOn` is where that crossing is written down. -/
#check_failure fun {d : ℕ} {s : System d} (f : InternalForce s) (g : Force s) (t : Time) =>
  IndividualQuantity.add DifferenceKind.ofScale (f.value t) (g.value t)

/-! ## 6. The gap this attempt does not close

Kinetic energy is `½ m ‖v‖²`. The norm takes a vector quantity to a scalar one, and no
licensed operation in the calculus does that: `mul` needs one carrier and `smulK` needs the
scalar on the left. The crossing below is therefore unwritable — which is the honest state of
the layer, pinned here rather than left as a remark. An inner product `⟪p, v⟫ → 2T` has the
same shape and the same gap. -/

/- No licensed product carries a velocity quantity to a speed. -/
#check_failure fun {d : ℕ} {s : System d} (p : s.Particle) (t : Time) =>
  IndividualQuantity.mul (k := kineticEnergyK) (ProductKind.ofRatio _ _ _)
    (velocityQ p t) (velocityQ p t)

end

end ForPhysLib.CaseStudies.PointParticle.Attempt4

