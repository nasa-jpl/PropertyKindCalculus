/-
# The scorecard — the four attempts, head to head

Each attempt lives in one file and is scored there. This module is the only place they meet,
and it carries the part of the comparison a build can check, so the table in `README.md`
cannot quietly drift from the files.

Verdicts that are `#check_failure`-shaped stay in the attempts, since a rejection is witnessed
by the build succeeding with the probe in place, not by a term this module could import. What
is collected here is the facts about terms that *do* exist — including, crucially, the wrong
ones.

## What the checked facts below establish

1. **The metrology is free at the value level.** Attempts 2, 3 and 4 compute *the same
   numbers* as #1612 — `rfl`, not a rewriting lemma. So the whole difference between the four
   designs is which terms elaborate, and none of it is arithmetic. This is the fact that makes
   the comparison a comparison about typing rather than about physics.
2. **The wrong sum exists in Attempts 1 and 2, and is a number.** `sumOfVelocities` is a
   well-formed term with a value. Attempts 3 and 4 have no such term at all (`#check_failure`,
   in those files) because the aggregation is unlicensed. Adding kinds does not help here:
   Attempt 2's version is correctly kinded throughout.
3. **The reverse that does not reverse is provable in Attempts 1, 2 and 3.** Each attempt's
   `badReverse` is shown, by `rfl`, to leave the target exactly where it was — while the
   intended `reverse` moves it to the source. Newton's third law is prose in all three. Only
   Attempt 4 refuses the bad version, and it does so because the value is a quantity of an
   ordered *pair*.
4. **A force is retargeted by a record update in Attempts 1 and 2.** The `target` field is
   data; changing it is arithmetic on a record. In Attempts 3 and 4 the two forces have
   different types.
5. **Only Attempt 4 keeps both.** Its store is #1612's `Multiset (Force s)` and its target is
   #1612's field, and it refuses every substitution above.
-/

module

public import ForPhysLib.CaseStudies.PointParticle.Attempt1Fields
public import ForPhysLib.CaseStudies.PointParticle.Attempt2Kinds
public import ForPhysLib.CaseStudies.PointParticle.Attempt3Indexed
public import ForPhysLib.CaseStudies.PointParticle.Attempt4Dependent

public section -- pkc-blanket
@[expose] section -- pkc-blanket-expose

namespace ForPhysLib.CaseStudies.PointParticle.Scorecard

open PropertyKindCalculus ClassicalMechanics ForPhysLib.CaseStudies.PointParticle
open scoped Classical

noncomputable section

variable {d : ℕ} {s : System d}

/-! ## 1. The metrology is free at the value level

Three designs, one number. Every equation below is `rfl`. -/

/-- **The total masses agree, definitionally** — the kind-only, the indexed and the
dependent-field designs all compute #1612's own `System.mass`. -/
theorem totalMass_agrees :
    (Attempt2.totalMassQ (s := s)).magnitude = (Attempt3.totalMassQ (s := s)).magnitude
      ∧ (Attempt3.totalMassQ (s := s)).magnitude = (Attempt4.totalMassQ (s := s)).magnitude
      ∧ (Attempt4.totalMassQ (s := s)).magnitude = s.mass :=
  ⟨rfl, rfl, rfl⟩

/-- **And the total momenta**, at the frame-vector carrier. -/
theorem totalMomentum_agrees (t : Time) :
    (Attempt2.totalMomentumQ (s := s) t).magnitude
        = (Attempt3.totalMomentumQ (s := s) t).magnitude
      ∧ (Attempt3.totalMomentumQ (s := s) t).magnitude
        = (Attempt4.totalMomentumQ (s := s) t).magnitude
      ∧ (Attempt4.totalMomentumQ (s := s) t).magnitude = s.momentum t :=
  ⟨rfl, rfl, rfl⟩

/-- **And the per-particle momenta**, which is where the scalar action enters: `m · v` through
a kind law in Attempts 2–4, an unchecked `•` in #1612, and the same vector either way. -/
theorem momentum_agrees (p : s.Particle) (t : Time) :
    (Attempt2.momentumQ p t).magnitude = (Attempt4.momentumQ p t).magnitude
      ∧ (Attempt4.momentumQ p t).magnitude = p.momentum t :=
  ⟨rfl, rfl⟩

/-! ## 2. The aggregation that is not one

In Attempts 1 and 2 the sum of the particles' velocities is a term with a value, written
exactly as the momentum total is written. In Attempts 3 and 4 it does not elaborate. -/

/-- **Attempt 1 — ❌.** The velocity sum is a `s.Vector`, and it is upstream's own `∑`. -/
theorem attempt1_velocity_sum_exists (t : Time) :
    Attempt1.sumOfVelocities (s := s) t = ∑ p : s.Particle, p.velocity t := rfl

/-- **Attempt 2 — ❌, and correctly kinded while it is wrong.** Every summand is a velocity
quantity and the result is a velocity quantity; the kind layer has no objection to make,
because the objection is about objects. -/
theorem attempt2_velocity_sum_exists (t : Time) :
    (Attempt2.sumOfVelocitiesQ (s := s) t).magnitude = ∑ p : s.Particle, p.velocity t := rfl

-- **Attempts 3 and 4 — ✅.** No term: `assembleAll` at `velocityK` has no `Assembles`
-- instance, and the `#check_failure` witnessing that lives in each attempt's own file.

/-! ## 3. The reverse that does not reverse

Each `badReverse` negates a magnitude and leaves the endpoints alone. The pair of equations
below says so and says what the intended `reverse` does instead — so the contrast is checked,
not described. -/

/-- **Attempt 1 — ❌.** The bad reverse keeps the target; the good one moves it to the
source. Both type-check, so Newton's third law is carried by the definition's body alone. -/
theorem attempt1_badReverse_does_not_swap (f : Attempt1.InternalForce s) :
    (Attempt1.badReverse f).target = f.target
      ∧ (Attempt1.InternalForce.reverse f).target = f.source :=
  ⟨rfl, rfl⟩

/-- **Attempt 2 — ❌.** Identical verdict one layer up: kinding the value says nothing about
which endpoints it belongs to. -/
theorem attempt2_badReverse_does_not_swap (f : Attempt2.InternalForce s) :
    (Attempt2.badReverse f).target = f.target
      ∧ (Attempt2.InternalForce.reverse f).target = f.source :=
  ⟨rfl, rfl⟩

/-- **Attempt 3 — ❌, and this is the surprise.** Indexing by the target pays the whole
ergonomic price of §2 in that file and still does not buy the third law: the stored form is a
dependent *pair*, so the index is existentially quantified and the bad reverse's index is the
old target. -/
theorem attempt3_badReverse_does_not_swap (p : s.Particle) (f : Attempt3.InternalForce s p) :
    (Attempt3.badReverse p f).1 = p
      ∧ (Attempt3.InternalForce.reverse p f).1 = f.source :=
  ⟨rfl, rfl⟩

-- **Attempt 4 — ✅.** The bad reverse does not elaborate: its value is a quantity of
-- `(source, target)` where a reversed force must be one of `(target, source)`. The
-- `#check_failure` is in that file, beside the `transpose` that is the law's content.

/-- What Attempt 4 has instead — the reversal's magnitude, definitionally the negation, with
the endpoints exchanged in the *type* rather than in a field assignment. -/
theorem attempt4_reverse_negates (f : Attempt4.InternalForce s) (t : Time) :
    (f.reverse.value t).magnitude = -(f.value t).magnitude :=
  Attempt4.InternalForce.reverse_value_magnitude f t

/-! ## 4. Retargeting by record update -/

/-- **Attempt 1 — ❌.** A force for one particle becomes a force for another by
`{ f with target := q }`, and the type does not move. -/
theorem attempt1_retargets (f : Attempt1.Force s) (q : s.Particle) :
    (Attempt1.misdeliver f q).target = q ∧ (Attempt1.misdeliver f q).value = f.value :=
  ⟨rfl, rfl⟩

/-- **Attempt 2 — ❌.** The same, with the value correctly kinded throughout. -/
theorem attempt2_retargets (f : Attempt2.Force s) (q : s.Particle) :
    (Attempt2.misdeliver f q).target = q ∧ (Attempt2.misdeliver f q).value = f.value :=
  ⟨rfl, rfl⟩

-- **Attempts 3 and 4 — ✅.** `Force s p` and `Force s q` are different types (Attempt 3), and
-- a record update that changes `target` changes the type its `value` field must have
-- (Attempt 4), so neither can be written. Both `#check_failure`s are in their own files.

/-! ## 5. What only the fourth attempt has

The store is #1612's, the target is #1612's field, and the laws are types. -/

/-- **Newton's second law is an equation between two quantities of the same particle**, at the
force kind, with `m · a` a licensed scalar action. In Attempts 1 and 2 the same equation is
between two `s.Vector`s, and in Attempt 3 it is between two quantities of a particle reached
through a dependent pair. -/
example (fs : Multiset (Attempt4.Force s)) : Prop := Attempt4.NewtonII fs

/-- **Momentum conservation names the whole.** Both sides are quantities of
`Composite.whole` — the system — so a right-hand side assembled from the wrong particles, or
from a particle rather than the system, is a type error rather than a review comment. -/
example (fs : Multiset (Attempt4.Force s))
    (dpdt : Time → IndividualQuantity (Composite.whole : Composite pointSystemS s.Particle)
      forceK s.Vector) : Prop :=
  Attempt4.MomentumConserved fs dpdt

end

end ForPhysLib.CaseStudies.PointParticle.Scorecard

end -- pkc-blanket-expose
end -- pkc-blanket
