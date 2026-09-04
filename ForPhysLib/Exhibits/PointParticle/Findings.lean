/-
# Exhibit F — PointParticle: an object index that is not a name

**Source.** [physlib#1612](https://github.com/leanprover-community/physlib/pull/1612)
(`ClassicalMechanics/Force.lean`, `PointParticle/Defs.lean`,
`PointParticle/NewtonianSystem/Defs.lean`), head `3ae4ae20`, unmerged at the time of
writing. The PR ties a quantity to an object without a metrology layer: `Force` carries a
`target` field, `InternalForce` a `source`, and a system's particles are a `Multiset`
coerced to a type.

**The subject.** The PR is not in this repository's pinned PhysLib, so the exhibit cannot
import it. It works against the replica of the PR's shape in
`CaseStudies/PointParticle/Common.lean` — the `Multiset frame.Particle` system, the coerced
particle type, and the aggregates written `∑ p : s.Particle, …`. That replica is written once
and shared with the case study; when #1612 merges, it is the one thing to delete.

**And the case study is where the alternatives are compared.** This exhibit reports what is
true of #1612 and of the layer applied to it. `CaseStudies/PointParticle/` puts four typings
of the same physics side by side — including the one that keeps the PR's `target` field and
makes the value's type depend on it — and scores their ergonomics. The findings below are the
inputs to that comparison, not a substitute for it.

**Finding 1 — the object index does not have to be a name.** `s.Particle` is a position in
a multiset. It has no `id` field, no `DecidableEq` written for it, and no designation
anywhere; a particle *is* the place it occupies. That is exactly the object type the
instance layer used to be unable to accept, and the parameterization of `IndividualQuantity`
over `{O : Type u}` accepts it with nothing supplied: every refusal in §2 below holds on the
PR's own data structures, with the PR unmodified.

**Finding 2 — and it cannot be named, which is the honest report.** `Designated s.Particle`
does not synthesize, and — since `Designated` carries an injectivity obligation — the
instance an author would otherwise write, sending every particle to one name, is not
writable either (§3). The §20 systematic term is unavailable here not through an oversight in
the layer but because Dybkær's `System — Component ; kind` triple has no input. Wanting one
is a *PhysLib-side* ask for a label field, and a separate one.

**Finding 3 — the gate refuses the library's own totals, and that is what the license is
for.** Object-gated addition refuses `p.mass + q.mass`, which is right, and equally refuses
`System.mass`, which is not a defect but a missing eliminator. `assembleAll` supplies it,
under `Assembles`; the totals it produces are the PR's own sums **definitionally** (§4), and
the sums the PR would also accept but should not — the particles' velocities, the particles'
positions — have no license and do not elaborate.
-/

import ForPhysLib.CaseStudies.PointParticle.Common

namespace ForPhysLib.Exhibits.PointParticle

open PropertyKindCalculus ClassicalMechanics ForPhysLib.CaseStudies.PointParticle
open scoped Classical

noncomputable section

/-! ## 1. The vocabulary — seven catalogue lookups, no mints

Every quantity #1612 introduces is already an ISO 80000 item this repository holds, so
adopting the layer for this PR mints nothing. The kinds, the two kind laws (`m·a → F`,
`m·v → p`), the `Carrier` registration for `frame.Vector` and the three `Assembles` entries
are all in `CaseStudies/PointParticle/Common.lean`, written once and shared. Notably absent
there, and deliberately: `Assembles pointSystemS velocityK` and
`Assembles pointSystemS displacementK`. -/

/-! ## 2. Finding 1 — the gate holds on #1612's particles, unmodified

No `DecidableEq`, no designation, no new field upstream. What separates two particles' mass
quantities is definitional equality of the object index, which the coerced multiset type
already provides. -/

section Gate
variable {d : ℕ} {s s₁ s₂ : System d}

/-- Two masses of the *same* particle add. -/
example (p : s.Particle) (x y : IndividualQuantity p massK ℝ) :
    IndividualQuantity p massK ℝ :=
  IndividualQuantity.add DifferenceKind.ofScale x y

/-- And two *displacements* of one particle add, at the frame-vector carrier — the acceptance
the refusal below has to be read against. -/
example (p : s.Particle) (x y : IndividualQuantity p displacementK s.Vector) :
    IndividualQuantity p displacementK s.Vector :=
  IndividualQuantity.add DifferenceKind.ofScale x y

/- Two *different* particles of one system: refused. -/
#check_failure fun {d : ℕ} {s : System d} (p q : s.Particle)
    (x : IndividualQuantity p massK ℝ) (y : IndividualQuantity q massK ℝ) =>
  IndividualQuantity.add DifferenceKind.ofScale x y

/- Particles of two *different systems*: refused a fortiori — the index types differ. -/
#check_failure fun {d : ℕ} {s₁ s₂ : System d} (p : s₁.Particle) (q : s₂.Particle)
    (x : IndividualQuantity p massK ℝ) (y : IndividualQuantity q massK ℝ) =>
  IndividualQuantity.add DifferenceKind.ofScale x y

/- **The dimensional collapse, closed at the quantity layer.** A displacement and a force of
one particle share `frame.Vector` upstream, and their sum elaborates there. Kinded, it does
not — and note what this did *not* need: no change to `frame.Vector`, no kinded vector type,
no touching of PhysLib at all. The gate is on the quantity, over the plain carrier. -/
#check_failure fun {d : ℕ} {s : System d} (p : s.Particle)
    (x : IndividualQuantity p displacementK s.Vector)
    (f : IndividualQuantity p forceK s.Vector) =>
  IndividualQuantity.add DifferenceKind.ofScale x f

end Gate

/-! ## 3. Finding 2 — the particle cannot be named, and the layer says so -/

section Designation
variable {d : ℕ} {s : System d}

/- There is no `Designated` instance to synthesize: neither `System` nor `Particle` carries
an identity field. -/
#check_failure (inferInstance : Designated s.Particle)

/- So the one operation of the layer that *reads* the object does not typecheck here. -/
#check_failure fun {d : ℕ} {s : System d} (p : s.Particle)
    (x : IndividualQuantity p massK ℝ) => x.toIndividualProperty

/- **And the fake is not writable.** The instance an author reaches for — send every particle
to one name — fails on `Designated`'s injectivity field, which is why that field exists: a
designation that collapses two objects reports them as one system, silently, everywhere it is
rendered. -/
#check_failure fun {d : ℕ} {s : System d} =>
  (⟨fun _ => ⟨"a particle"⟩, fun _ => rfl⟩ : Designated s.Particle)

end Designation

/-! ## 4. Finding 3 — assembly, and the PR's own totals recovered by `rfl` -/

section Assembly
variable {d : ℕ} (s : System d)

/-- The object type the system's own quantities need: its particles *and* the whole they
compose (MR22). `Composite` is the core construct; nothing model-specific is written here. -/
abbrev Obj := Composite pointSystemS s.Particle

/-! **The per-model abbreviation, and the MR11 note.** Generalizing the object index makes it
*visible*: `IndividualQuantity (Composite.part p) massK ℝ` where an ungated model writes
`Quantity massK ℝ`. That is the one ergonomic debit the object layer adds, and it is paid off
by two `abbrev`s per model — the object side of what `kind_algebra` does for the kind
equations. Every declaration below is written through them, so the index reads at the same
weight as the kind. -/

/-- A quantity of one particle. -/
abbrev PartQ {d : ℕ} {s : System d} (p : s.Particle) (k : KindOfProperty) (R : Type) :=
  IndividualQuantity (Composite.part (σ := pointSystemS) p) k R

/-- A quantity of the system as a whole. -/
abbrev WholeQ {d : ℕ} (s : System d) (k : KindOfProperty) (R : Type) :=
  IndividualQuantity (Composite.whole : Composite pointSystemS s.Particle) k R

/-- Each particle's mass, read at its kind and characterizing that particle. -/
def particleMass (p : s.Particle) : PartQ p massK ℝ := ⟨p.mass⟩

/-- Each particle's momentum at `t`, likewise. -/
def particleMomentum (t : Time) (p : s.Particle) : PartQ p momentumK s.Vector :=
  ⟨p.momentum t⟩

/-- The system's mass, assembled — a quantity of the *whole*, not of any particle. -/
def totalMass : WholeQ s massK ℝ :=
  assembleAll pointSystemS Composite.whole Composite.part (particleMass s)

/-- The system's momentum at `t`, assembled. -/
def totalMomentum (t : Time) : WholeQ s momentumK s.Vector :=
  assembleAll pointSystemS Composite.whole Composite.part (particleMomentum s t)

/-- **The payoff.** The assembled total *is* #1612's `System.mass` — definitionally, by
`rfl`. The layer adds a gate and changes no arithmetic. -/
theorem totalMass_eq : (totalMass s).magnitude = s.mass := rfl

/-- The same for momentum, at a vector carrier. -/
theorem totalMomentum_eq (t : Time) : (totalMomentum s t).magnitude = s.momentum t := rfl

end Assembly

section AssemblyRefusals
variable {d : ℕ} {s : System d}

/- **MR22.** A whole-system mass and a particle's mass do not add: different objects. -/
#check_failure fun {d : ℕ} {s : System d} (p : s.Particle) =>
  IndividualQuantity.add (k := massK) DifferenceKind.ofScale (totalMass s) (particleMass s p)

/- **The license bites.** The sum of the particles' *velocities* is not the system's
velocity; with no `Assembles velocityK` it is not a term. This is the aggregation upstream
would accept today, and the one most likely to be written next — momentum conservation and
the work–energy theorem are both aggregation laws. -/
#check_failure fun {d : ℕ} {s : System d}
    (f : (p : s.Particle) → PartQ p velocityK s.Vector) =>
  assembleAll (k := velocityK) pointSystemS
    (Composite.whole : Composite pointSystemS s.Particle) Composite.part f

/- Nor their positions — a sum of positions is not a position. -/
#check_failure fun {d : ℕ} {s : System d}
    (f : (p : s.Particle) → PartQ p displacementK s.Vector) =>
  assembleAll (k := displacementK) pointSystemS
    (Composite.whole : Composite pointSystemS s.Particle) Composite.part f

end AssemblyRefusals

end

end ForPhysLib.Exhibits.PointParticle
