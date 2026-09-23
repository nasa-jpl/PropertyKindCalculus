/-
# Attempt 3 — move the target into the type

The direct fix for what Attempt 2 could not check: make the object a *parameter* of the force
type rather than a field of the force value.

```lean
structure Force (s : System d) (target : s.Particle) where
  value : Time → IndividualQuantity (Composite.part (σ := pointSystemS) target) forceK s.Vector
```

**It checks everything Attempt 2 could not** — a force for one particle is not a force for
another, the mass of `p` will not scale the acceleration of `q`, the system's total is not a
part's, and the sum of the particles' velocities has no license and does not elaborate.

**And it breaks the PR.** That is the finding, and it is the reason this attempt exists: a
maintainer reading it would be right to reject it.

  * **The forces no longer form one multiset.** `Multiset (Force s)` becomes
    `Multiset (Σ p : s.Particle, Force s p)`. Every construction site gains a `⟨p, …⟩`.
  * **`netForce` gains a transport.** The filter tests `x.fst = p` at runtime and then has to
    *move* a value of type `… (Composite.part x.fst) …` to `… (Composite.part p) …` along that
    proof — an `h ▸`, in the middle of what was a one-line sum. The non-matching summands need
    a value too, so a zero force has to be constructed where nothing was constructed before.
  * **`CoeFun` goes per-index**, so `force t` no longer reads uniformly.
  * **And the third law is still not typed.** The index records the *target* and not the
    source, so `reverse` — whose entire content is that source and target are exchanged — is
    once again a definition that happens to swap two fields. Attempt 3 pays the whole
    ergonomic price and still does not buy the one law that motivated `InternalForce`.

That last point is the useful one. It says the problem is not "field versus index"; it is
*which object* the quantity is of. An internal force is a quantity of an ordered **pair**, and
neither a target field nor a target index says so.
-/

module

public import ForPhysLib.CaseStudies.PointParticle.Common
-- Private scope only: the checks below reduce through bodies sealed in the core
-- library; `import all` gives this file the reduction without exposing them.
import all PropertyKindCalculus.IndividualQuantity

@[expose] public section

namespace ForPhysLib.CaseStudies.PointParticle.Attempt3

open PropertyKindCalculus ClassicalMechanics ForPhysLib.CaseStudies.PointParticle
open scoped Classical

noncomputable section

variable {d : ℕ} {s : System d}

/-! ## 1. The forces — the target is now a parameter -/

/-- A force *for a named particle*: the target is in the type, so two forces for two particles
are two types. -/
structure Force (s : System d) (target : s.Particle) where
  /-- The force, at its kind, characterizing the target. -/
  value : Time → IndividualQuantity (Composite.part (σ := pointSystemS) target) forceK s.Vector

/-- An internal force. The source is back to being a *field* — the index has room for one
object, and the target is the one Newton's second law needs. -/
structure InternalForce (s : System d) (target : s.Particle) extends Force s target where
  /-- The source object. -/
  source : s.Particle
  /-- A particle does not act on itself. -/
  source_ne_target : source ≠ target

/-! ## 2. The ergonomic cost, itemized

Each definition below is the Attempt 1 / Attempt 2 definition, with the extra machinery the
index forces. -/

/-- **The store.** What was `Multiset (Force s)` is a multiset of *dependent pairs*. -/
abbrev Forces (s : System d) := Multiset (Σ p : s.Particle, Force s p)

/-- **The transport.** A stored force contributes to the net force on `p` only if its index is
`p`, and saying so requires moving the value along the equality — plus a zero for the
summands that do not match, which the object-free versions never had to construct. -/
def contribution (p : s.Particle) (x : Σ q : s.Particle, Force s q) (t : Time) :
    IndividualQuantity (Composite.part (σ := pointSystemS) p) forceK s.Vector :=
  if h : x.1 = p then h ▸ x.2.value t else ⟨0⟩

/-- The net force on a particle. Compare Attempt 1's one-line filter. -/
def netForce (fs : Forces s) (p : s.Particle) (t : Time) :
    IndividualQuantity (Composite.part (σ := pointSystemS) p) forceK s.Vector :=
  resultantAll DifferenceKind.ofScale (fun x : fs => contribution p x.1 t)

/-! ## 3. What is now checked

The readings, first — each a projection with a kind and an object attached, so each erasure is
`rfl`. -/

/-- The particle's mass, of that particle. -/
def massQ (p : s.Particle) : IndividualQuantity (Composite.part (σ := pointSystemS) p) massK ℝ := ⟨p.mass⟩
/-- The particle's velocity, of that particle. -/
def velocityQ (p : s.Particle) (t : Time) :
    IndividualQuantity (Composite.part (σ := pointSystemS) p) velocityK s.Vector := ⟨p.velocity t⟩
/-- The particle's acceleration, of that particle. -/
def accelerationQ (p : s.Particle) (t : Time) :
    IndividualQuantity (Composite.part (σ := pointSystemS) p) accelerationK s.Vector := ⟨p.acceleration t⟩
/-- The particle's momentum, through the kind law. -/
def momentumQ (p : s.Particle) (t : Time) :
    IndividualQuantity (Composite.part (σ := pointSystemS) p) momentumK s.Vector :=
  IndividualQuantity.smulK momentumEdge (massQ p) (velocityQ p t)

/-- The system's mass, assembled from the parts. -/
def totalMassQ : IndividualQuantity (Composite.whole : Composite pointSystemS s.Particle) massK ℝ :=
  assembleAll pointSystemS Composite.whole Composite.part (massQ (s := s))

/-- The system's momentum, assembled. -/
def totalMomentumQ (t : Time) :
    IndividualQuantity (Composite.whole : Composite pointSystemS s.Particle) momentumK s.Vector :=
  assembleAll pointSystemS Composite.whole Composite.part (fun p => momentumQ p t)

/-- **The erasures survive the index**: the assembled totals are upstream's own sums. -/
theorem totalMassQ_erases : (totalMassQ (s := s)).magnitude = s.mass := rfl
/-- Likewise for momentum. -/
theorem totalMomentumQ_erases (t : Time) :
    (totalMomentumQ (s := s) t).magnitude = s.momentum t := rfl

/- Attempt 2's surviving acceptance, refused: one particle's mass will not scale another's
acceleration. -/
#check_failure fun {d : ℕ} {s : System d} (p q : s.Particle) (t : Time) =>
  IndividualQuantity.smulK newtonEdge (massQ p) (accelerationQ q t)

/- A force for `p` is not a force for `q` — retargeting by record update is unwritable, because
the two are different types. -/
#check_failure fun {d : ℕ} {s : System d} (p q : s.Particle) (f : Force s p) =>
  (f : Force s q)

/- The system's total mass does not add to a particle's (MR22). -/
#check_failure fun {d : ℕ} {s : System d} (p : s.Particle) =>
  IndividualQuantity.add (k := massK) DifferenceKind.ofScale (totalMassQ (s := s)) (massQ p)

/- And the aggregation that is not one: no `Assembles velocityK`, so no sum of velocities. -/
#check_failure fun {d : ℕ} {s : System d} =>
  assembleAll (k := velocityK) pointSystemS
    (Composite.whole : Composite pointSystemS s.Particle) Composite.part
    (fun p => velocityQ p (0 : Time))

/-! ## 4. What is still not checked — the third law

The index carries the target. Newton's third law is about the *pair*, and the pair is not in
the type, so `reverse` is a field swap again — and a `reverse` that negates without swapping
still type-checks, exactly as in Attempts 1 and 2. -/

/-- The reverse force: its *type* index is the old source, which is right, but nothing relates
the new source to the old target except the definition's own body. -/
def InternalForce.reverse (p : s.Particle) (f : InternalForce s p) :
    Σ q : s.Particle, InternalForce s q :=
  ⟨f.source, { value := fun t => ⟨-(f.value t).magnitude⟩,
               source := p,
               source_ne_target := f.source_ne_target.symm }⟩

/-- **Still accepted.** A reverse that negates the value and re-uses the *same* source — the
swap that is the whole content of the law, omitted, and the checker silent. -/
def badReverse (p : s.Particle) (f : InternalForce s p) :
    Σ q : s.Particle, InternalForce s q :=
  ⟨p, { value := fun t => ⟨-(f.value t).magnitude⟩,
        source := f.source,
        source_ne_target := f.source_ne_target }⟩

end

end ForPhysLib.CaseStudies.PointParticle.Attempt3

