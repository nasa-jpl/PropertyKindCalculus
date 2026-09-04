/-
# Exhibit G — Composition: the findings

**Source.** `Physlib/ClassicalMechanics/RigidBody/{Basic,AngularVelocity,KineticEnergy}.lean`,
imported below and probed directly — every claim here is a build artifact against the real
modules, per rule 2 of the [rules of engagement](../../PLAN.md#rules-of-engagement).

**The question.** A rigid body is a *many* treated as a *one*. Which of its quantities come
from its parts, which belong to the whole alone, and where does the library say so? The
answer, from the corpus in [MARMODORO-CORPUS.md](../../MARMODORO-CORPUS.md): the parts are
not in the representation, every parts-to-whole statement is an `informal_lemma`, and the
one aggregation with a side condition — the center of mass — is defined without it.

**The findings, each an artifact:**

1. **The bridge is data, not a theorem.** `informal_lemma` expands to a `def … :
   InformalLemma`, so the statements that would license aggregation type-check as *values*
   of a two-field structure. Exhibited by inhabiting `InformalLemma` with each of them.
2. **The whole has no parts, and the weighted mean has no license.** `RigidBody d` is one
   linear functional, so `⟨0⟩` is a rigid body: it has zero mass, and its center of mass —
   a ratio of integrals with no `mass ≠ 0` hypothesis anywhere — computes to the origin.
   Both are theorems below.
3. **Three aggregations, one syntax, and only one of them is a sum.** Composing two bodies
   takes one line PhysLib does not have (`union`, adding the mass distributions). With it,
   mass and the inertia tensor are additive by the linearity of `ρ` — the latter only about
   the common origin — while the center of mass is a mass-weighted mean whose law needs
   three hypotheses `centerOfMass` does not carry. All four sums type-check identically.
4. **The three-way split, typed.** The kinded counter-form separates them: mass is licensed
   at the rigid sort and cashed against a §13.5.1 `Extensive` witness; angular velocity is
   `Intensive` over that sort — shared by every part, and therefore *not* summable, which is
   a theorem rather than an omission; a coupled pair's normal-mode frequency is
   `WholeProper`, produced by neither route.
5. **The center of mass, licensed.** A weighted carving carries the nonzero-total-weight
   condition as a field, so the massless body of finding 2 is not a term of it, and the mean
   of a constant is that constant — the law that says this aggregation is a mean and not a
   sum. The mode is `PropertyKindCalculus.WeightedCarving`, beside the other two; the exhibit
   supplies the instance at this body's halves.

**What is *not* claimed.** Nothing here says PhysLib's numbers are wrong: `centerOfMass` is
the right formula wherever it is applied to a body with mass, and the informal lemmas are
honest markers of unformalized content. The claim is narrower and checkable — the library
has no way to *state* which quantities aggregate, so the three cases of finding 3 are one
case to the type system.
-/

import Physlib.ClassicalMechanics.RigidBody.KineticEnergy
import PropertyKindCalculus
import PropertyKindCalculus.AggregationLaws
import PropertyKindCalculus.Iso80000.Part3
import PropertyKindCalculus.Iso80000.Part4

namespace ForPhysLib.Exhibits.Composition

open PropertyKindCalculus
open Manifold InnerProductSpace

/-! ## Finding 1 — the parts-to-whole bridge is data

`informal_lemma name where …` is a macro for `def name : InformalLemma …`, so each of the
statements below — the ones that would license an aggregation, if they were theorems —
inhabits a two-field structure of a `List Name` and a `String`. That is the honest state of
the directory, and it is what makes the licensing question a *design* question rather than a
proving one. -/

/-- `P = ∑ Fᵢ ⋅ vᵢ = F_tot ⋅ V + M ⋅ ω` — the only place the parts of a rigid body appear in
a statement about the whole. -/
example : InformalLemma := RigidBody.rigid_body_work_and_power

/-- "The centre of mass … moves as if all mass were concentrated at that point" — the
re-individuation of a body as a particle. -/
example : InformalLemma := RigidBody.center_of_mass_point_moves_as_particle

/-- "The angular velocity … is independent of the system chosen" — carving-independence,
unformalized. -/
example : InformalLemma := RigidBody.angular_velocity_is_well_defined

/-- Normal modes, where a whole-proper quantity would first be needed. -/
example : InformalLemma := RigidBody.small_oscillations_about_equilibrium

/-! ## Finding 2 — a whole with no parts, and a mean with no license

`RigidBody d` carries one field, a mass distribution `ρ`. Nothing constrains it to be
positive, or nonzero, so the zero functional is a rigid body; and `centerOfMass` divides by
`mass` with no hypothesis, which in Lean is total. The body below therefore has a center of
mass, at the origin, for no physical reason. -/

/-- A rigid body with no mass anywhere: the type asks for a mass distribution, and `0` is
one. -/
noncomputable def massless : RigidBody 3 := ⟨0⟩

/-- Its total mass is zero — `mass` is `ρ` applied to the constant function 1. -/
theorem massless_mass : massless.mass = 0 := LinearMap.zero_apply _

/-- **And its center of mass is the origin.** `centerOfMass` is `(1 / mass) • ρ(xᵢ)`, and
`1 / 0 = 0` in Lean, so the weighted mean of nothing is a point — reported with the same
type, and by the same code path, as a real center of mass. -/
theorem massless_centerOfMass : massless.centerOfMass = 0 := by
  ext i
  simp [massless, RigidBody.centerOfMass, RigidBody.mass]
  exact Or.inr (LinearMap.zero_apply _)

/-! ## Finding 3 — three aggregations, one syntax, and only one of them is a sum

PhysLib has no operation composing two rigid bodies, and it takes one line: mass
distributions are linear functionals, so they add. With it, the directory's aggregate
quantities sort themselves into three modes — and the modes are invisible in the types,
which is the finding.

The composite's mass and inertia tensor are the *sums* of the parts', both by the linearity
of `ρ` alone. Its center of mass is a **mass-weighted mean**, and the law below needs three
hypotheses — each part massive, and the composite massive — that `centerOfMass` itself does
not carry. -/

/-- **The missing operation**: two rigid bodies composed, by adding their mass
distributions. One line, and PhysLib does not have it. -/
noncomputable def union (A B : RigidBody 3) : RigidBody 3 := ⟨A.ρ + B.ρ⟩

/-- The composite's mass distribution is the sum of the parts', applied to any test
function — the linearity everything below rests on. -/
theorem union_apply (A B : RigidBody 3) (f : C^⊤⟮𝓘(ℝ, Space 3), Space 3; 𝓘(ℝ, ℝ), ℝ⟯) :
    (union A B).ρ f = A.ρ f + B.ρ f := LinearMap.add_apply _ _ _

/-- **Mass assembles**, and definitionally: `mass` is `ρ` at the constant function 1. -/
theorem union_mass (A B : RigidBody 3) : (union A B).mass = A.mass + B.mass :=
  union_apply A B _

/-- **So does the inertia tensor** — *about the common origin*, which is the whole content of
the qualification. `inertiaTensor` is `ρ` at a fixed integrand, so it inherits linearity; two
tensors referred to their own centers of mass do not add, and the parallel-axis theorem
(`inertiaTensorAbout_eq_centerOfMass_add_pointMass`) is the correction that makes the axes
agree. The axis is a parameter neither the type nor this theorem's statement carries. -/
theorem union_inertiaTensor (A B : RigidBody 3) :
    (union A B).inertiaTensor = A.inertiaTensor + B.inertiaTensor := by
  ext i j
  simp only [union, RigidBody.inertiaTensor, Matrix.add_apply]
  exact LinearMap.add_apply _ _ _

/-- The `i`-th coordinate function as a test function — what `centerOfMass` integrates
against. -/
noncomputable def coordFn (i : Fin 3) : C^⊤⟮𝓘(ℝ, Space 3), Space 3; 𝓘(ℝ, ℝ), ℝ⟯ :=
  ⟨fun x => x i, ContDiff.contMDiff <| by fun_prop⟩

/-- `centerOfMass` read one component at a time: the first moment over the mass. Definitional
— the two proofs of smoothness differ and proof irrelevance closes the gap. -/
theorem centerOfMass_eq (R : RigidBody 3) (i : Fin 3) :
    R.centerOfMass i = (1 / R.mass) * R.ρ (coordFn i) := rfl

/-- **The center of mass is a weighted mean, not a sum** — and the law needs all three
hypotheses. This is the aggregation mode PhysLib's types spell exactly like the other two:
`Space 3` for the composite's center, `Space 3` for either part's, addition available
throughout. -/
theorem union_centerOfMass (A B : RigidBody 3) (hA : A.mass ≠ 0) (hB : B.mass ≠ 0)
    (hAB : A.mass + B.mass ≠ 0) (i : Fin 3) :
    (A.mass + B.mass) * (union A B).centerOfMass i
      = A.mass * A.centerOfMass i + B.mass * B.centerOfMass i := by
  rw [centerOfMass_eq, centerOfMass_eq, centerOfMass_eq, union_mass, union_apply]
  field_simp

/-! ### … and the types tell none of them apart

Four sums, one syntax. The first is the mass law above. The second is not a quantity of
anything. The third is the inertia law above *only* if the axes already agree. The fourth is
simply wrong — the center of mass of a composite is the weighted mean, never the sum — and
it is as well-typed as the rest. -/

/-- Two bodies' masses add: the licensed aggregation. -/
noncomputable example (A B : RigidBody 3) : ℝ := A.mass + B.mass

/-- Two bodies' angular velocities add just as readily. -/
noncomputable example (M N : RigidBodyMotion 3) (t : Time) : Fin 3 → ℝ :=
  M.angularVelocity t + N.angularVelocity t

/-- And so do their inertia tensors, whatever axes each was taken about. -/
noncomputable example (A B : RigidBody 3) : Matrix (Fin 3) (Fin 3) ℝ :=
  A.inertiaTensor + B.inertiaTensor

/-- And so do their centers of mass — a point that is the composite's center only if the two
bodies have equal mass. -/
noncomputable example (A B : RigidBody 3) : Space 3 := A.centerOfMass + B.centerOfMass

/-! ## Finding 4 — the three-way split, typed

The kinded counter-form. Two sorts of whole, one part type, and three aggregation modes —
§13.5.1 extensive, §13.5.4 intensive, and the whole-proper case Bunge's four types do not
name — carrying the three modes of finding 3, each with its own checked witness, so the
split is a build artifact and not a table in a comment. -/

/-- The two halves a body is carved into for the probes. Any carving would do: the laws
below are quantified over all of them. -/
inductive Half where
  /-- One half of the body. -/
  | left
  /-- The other half. -/
  | right
deriving DecidableEq, Repr

/-- The sort of whole a rigid body is. -/
def rigidBodyS : SortOfSystem := { id := "rigid body" }

/-- The sort of whole a coupled pair is — a different sort over the same parts, with its own
licenses. -/
def oscillatorPairS : SortOfSystem := { id := "coupled oscillator pair" }

/-- Mass — the catalogue's 4-1. -/
def massK : KindOfProperty := (Iso80000.Part4.mass).kind
/-- Angular velocity — the catalogue's 3-12, what `RigidBodyMotion.angularVelocity` reads. -/
def angularVelocityK : KindOfProperty := (Iso80000.Part3.angularVelocity).kind
/-- Angular frequency — the catalogue's 3-18, where a normal mode lands. -/
def angularFrequencyK : KindOfProperty := (Iso80000.Part3.angularFrequency).kind

/-! ### Mass assembles -/

/-- Mass is licensed at the rigid sort — the one registration this exhibit makes. -/
instance : Assembles rigidBodyS massK := ⟨DifferenceKind.ofScale⟩

/-- A mass measurement over the halves: each half reads its own mass, and any composition
reads the sum of its parts. -/
def massOfHalf : Measurement Half
  | .atom .left => { kind := massK, numeral := 3, reference := "kg" }
  | .atom .right => { kind := massK, numeral := 5, reference := "kg" }
  | .union a b =>
      { kind := massK, numeral := (massOfHalf a).numeral + (massOfHalf b).numeral,
        reference := "kg" }

/-- Mass is extensive under it, by construction. -/
theorem massOfHalf_extensive : Extensive massK massOfHalf := by
  refine ⟨fun d => ?_, fun _ _ => rfl⟩
  cases d with
  | atom p => cases p <;> rfl
  | union _ _ => rfl

/-- The body, carved in two. -/
def body : Decomposition Half := .union (.atom .left) (.atom .right)

/-- **The total mass is a term, and it is the mass of the whole.** The license lets the sum
be written; `assemble_eq_measured` against the `Extensive` witness is what says the sum is
the physics. -/
theorem body_mass_assembles :
    (assemble (k := massK) rigidBodyS (Composite.whole : Composite rigidBodyS Half)
      Composite.part body (fun p => ⟨(massOfHalf (.atom p)).numeral⟩)).magnitude
      = (massOfHalf body).numeral :=
  assemble_eq_measured rigidBodyS _ _ massOfHalf_extensive body

/-! ### Angular velocity is intensive — which is *why* it does not assemble

Every part of a rigid body turns with the body's own angular velocity; that is the content
of `velocity_decomposition` and `angular_velocity_is_well_defined` above. So ω is not merely
unlicensed for summing — it is constant under composition, and the two branches exclude each
other. -/

/-- The angular-velocity measurement of a rigid body: every part, and every composition of
parts, reads the body's 7 rad/s. -/
def omegaOfHalf : Measurement Half := fun _ =>
  { kind := angularVelocityK, numeral := 7, reference := "rad/s" }

/-- **ω is intensive over the parts of a rigid body.** -/
theorem omegaOfHalf_intensive : Intensive angularVelocityK omegaOfHalf :=
  ⟨fun _ => rfl, fun _ _ _ => rfl⟩

/-- **And therefore not extensive**: the halves both read 7 rad/s, and the body does not
read 14. -/
theorem omegaOfHalf_not_extensive : ¬ Extensive angularVelocityK omegaOfHalf :=
  not_extensive_of_intensive omegaOfHalf_intensive
    (a := .atom .left) (b := .atom .right) rfl (by decide)

-- Boundary: no license was registered for ω at the rigid sort, so the sum of the halves'
-- angular velocities is not a term anyone can write — the counter-form of finding 3's
-- second line.
#check_failure (inferInstance : Assembles rigidBodyS angularVelocityK)

/-! ### A normal-mode frequency is whole-proper

Same two parts, read as a *coupled pair* rather than as one rigid body — a different sort,
with different licenses. Each oscillator alone runs at ω₀ = 10 rad/s; the pair's upper normal
mode is at ω₊ = 14 rad/s (ω₊² = ω₀² + 2κ/m = 100 + 96). That is neither the sum nor the
shared value, and a lone oscillator has no normal mode to contribute in the first place. -/

/-- The pair's frequency measurement: 10 rad/s for either oscillator, 14 rad/s for the
pair. -/
def modeOfPair : Measurement Half
  | .atom _ => { kind := angularFrequencyK, numeral := 10, reference := "rad/s" }
  | .union _ _ => { kind := angularFrequencyK, numeral := 14, reference := "rad/s" }

/-- **The pair's normal-mode frequency is whole-proper** — neither branch of §13.5 applies,
and both refutations are exhibited on the two oscillators. -/
theorem modeOfPair_wholeProper : WholeProper angularFrequencyK modeOfPair :=
  { ofKind := fun d => by cases d <;> rfl
    notAdditive := ⟨.left, .right, by decide⟩
    notUniform := ⟨.left, .right, by decide, by decide⟩ }

/-- Neither of the other two modes: not extensive … -/
theorem modeOfPair_not_extensive : ¬ Extensive angularFrequencyK modeOfPair :=
  modeOfPair_wholeProper.not_extensive

/-- … and not intensive. The quantity belongs to the pair. -/
theorem modeOfPair_not_intensive : ¬ Intensive angularFrequencyK modeOfPair :=
  modeOfPair_wholeProper.not_intensive

-- Boundary: the pair's frequency has no assembly license either, so the sum is unwritable.
#check_failure (inferInstance : Assembles oscillatorPairS angularFrequencyK)

/-! ## Finding 5 — the center of mass, with its license attached

The center of mass is a third aggregation mode: a weighted mean, which is neither additive
nor constant. Its license is that the total weight is nonzero — the very hypothesis
`RigidBody.centerOfMass` does not carry, and finding 2 is what that costs. The mode and its
law are `PropertyKindCalculus.WeightedCarving` and `WeightedCarving.mean_const`, beside the
other two aggregation modes rather than in this exhibit; what the exhibit adds is the
instance, at the halves of the rigid body findings 3 and 4 carve. -/

/-- The halves of the rigid body, weighted by mass and carrying the license: one kilogram in
each half, so the total is 2 and the mean is defined. Where PhysLib's `centerOfMass` returns
the origin for a massless body (`massless_centerOfMass`, finding 2), there is here nothing to
build a term from — the license is a field, and `⟨0⟩` cannot discharge it. -/
noncomputable def halvesByMass : WeightedCarving ℝ Half where
  parts := .union (.atom .left) (.atom .right)
  weight := fun _ => 1
  total_ne_zero := by norm_num [totalWeight, Decomposition.fold, Carrier.add, Carrier.zero]

/-- **The rigid body's center of mass, licensed.** Both halves at the same place put the whole
at that place — the law that says this aggregation is a mean and not a sum, applied to a real
carving of a real body rather than stated in the abstract. -/
theorem halvesByMass_mean_const (v : ℝ) : halvesByMass.mean (fun _ => v) = v :=
  halvesByMass.mean_const v

/-- The license travels with the carving, so a massless body cannot be handed to the mean. -/
theorem halvesByMass_total_ne_zero : halvesByMass.total ≠ Carrier.zero :=
  halvesByMass.total_ne_zero'

end ForPhysLib.Exhibits.Composition
