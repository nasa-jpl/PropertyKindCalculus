/-
# Stage 0 — the kind vocabulary of `Physlib/ClassicalMechanics` (two subtrees)

The first rung of [the adoption ladder](../PLAN.md#stage-0-the-kind-vocabulary), for
the campaign's third directory. One file, bare `KindOfProperty` declarations,
Mathlib-free and PhysLib-free — importable by anything, costing nothing until
something imports it. One vocabulary for both subtrees (`HarmonicOscillator/` and
`RigidBody/`): the directory's title finding — same-dimension discrimination — is a
*directory-level* fact, and splitting the vocabulary would hide it.

**Seventeen lookups, five mints, and the mints are two findings.** The catalogue
covers everything the two subtrees' APIs *export* — down to the phase angle and the
period. What it does not cover:

* **the input data and its radicand** — the spring constant `k` (a system parameter;
  no ISO 80000 item) and `k/m` (the squared angular frequency, the pilot's
  radicand-first pattern). The bare-real `HarmonicOscillator { m k : ℝ }` is where
  Exhibit C found `√(m/k)` as well-typed as the right recipe;
* **the difference without a home, and the sum's two species** — the Lagrangian
  `T − V` (the catalogue names the *sum* of the comparable pair — mechanical energy —
  and has no item for its difference), and König's translational/rotational split of
  kinetic energy (species the standard leaves to the application).

**Six kinds at one dimension.** The campaign table promised four energies at the
joule; the vocabulary needs six: kinetic, potential, mechanical, the Lagrangian, and
König's two species. Plus two kinds at `T⁻¹` — the oscillator's angular *frequency*
(3-18) and the rigid body's angular *velocity* (3-12), the same letter `ω` in the two
subtrees — and two at `T` (duration and period). Nothing dimensional separates any of
these; the kind layer does, decidably.

**Two joins, one two-level lattice — against the pilot's one and directory 2's none.**
Kinetic and potential energy join at mechanical energy (`E = T + V`,
`hamiltonian_eq_energy`); translational and rotational join at kinetic energy
(König). The lattice composes: a König summand specializes mechanical energy
transitively.
-/

import PropertyKindCalculus

namespace ForPhysLib.ClassicalMechanics.Kinds

open PropertyKindCalculus

/-! ## The lookups — ISO 80000-4 and ISO 80000-3, verbatim -/

/-- Mass — item 4-1 (`m`, kg): both subtrees' first input datum (`S.m`, `R.mass`). -/
def mass : KindOfProperty := { id := "mass", scale := .ratio }

/-- Momentum — item 4-8 (`p`, kg·m/s): what `toCanonicalMomentum` produces, and the
rigid body's `linearMomentum`. -/
def momentum : KindOfProperty := { id := "momentum", scale := .ratio }

/-- Force — item 4-9.1 (`F`, N): the oscillator's `force = −∇V`, and Newton's reading
in the tfae. -/
def force : KindOfProperty := { id := "force", scale := .ratio }

/-- Potential energy — item 4-28.1 (`V`, J): `½k⟪x,x⟫`. First of the six joules. -/
def potentialEnergy : KindOfProperty := { id := "potential energy", scale := .ratio }

/-- Kinetic energy — item 4-28.2 (`T`, J): `½m⟪ẋ,ẋ⟫`, and the König split's
join. Second joule. -/
def kineticEnergy : KindOfProperty := { id := "kinetic energy", scale := .ratio }

/-- Mechanical energy — item 4-28.3 (`E`, J): the `T + V` join, the total energy, and
the on-trajectory Hamiltonian (`hamiltonian_eq_energy`). Third joule. -/
def mechanicalEnergy : KindOfProperty := { id := "mechanical energy", scale := .ratio }

/-- Power — item 4-27 (`P`, W): `∂ₜE`'s kind — what energy conservation says is
zero. -/
def power : KindOfProperty := { id := "power", scale := .ratio }

/-- Moment of inertia — item 4-7 (`J`, kg·m²): the inertia tensor's entries — the
second moments of the mass-distribution functional. -/
def momentOfInertia : KindOfProperty := { id := "moment of inertia", scale := .ratio }

/-- Angular momentum — item 4-11 (`L`, kg·m²/s): `L = I·ω`. -/
def angularMomentum : KindOfProperty := { id := "angular momentum", scale := .ratio }

/-- Displacement — item 3-1.11 (`Δr`, m): the oscillator's `x`, a displacement from
equilibrium in this coordinate model, and the rigid body's `y − c`. The catalogue's
examination principle (between two points) is part of the literal. -/
def displacement : KindOfProperty :=
  { id := "displacement", scale := .ratio, examPrinciple := some "between-points" }

/-- Velocity — item 3-10.1 (`v`, m/s): `∂ₜ xₜ`, `V = ∂ₜ comTrajectory`. -/
def velocity : KindOfProperty := { id := "velocity", scale := .ratio }

/-- Acceleration — item 3-11 (`a`, m/s²): `∂ₜ∂ₜ xₜ`, Newton's other factor. -/
def acceleration : KindOfProperty := { id := "acceleration", scale := .ratio }

/-- Angular velocity — item 3-12 (`ω`, rad/s): the *rigid body's* `ω` — the dual of
`Ṙ Rᵀ`, lab- or body-frame. -/
def angularVelocity : KindOfProperty := { id := "angular velocity", scale := .ratio }

/-- Angular frequency — item 3-18 (`ω`, rad/s): the *oscillator's* `ω = √(k/m)`. Same
dimension and same letter as 3-12 — a different catalogue item, and the two subtrees'
shared-letter collision. -/
def angularFrequency : KindOfProperty := { id := "angular frequency", scale := .ratio }

/-- Period duration — item 3-14 (`T`, s): `2π/ω`. Same dimension as duration — the
repetition interval is not the trajectory parameter. -/
def periodDuration : KindOfProperty := { id := "period duration", scale := .ratio }

/-- Phase angle — item 3-7 (`φ`, rad): where `ω·t` (and the amplitude–phase `φ`)
lands — the licence `cos` and `sin` consume at the trig boundary. -/
def phaseAngle : KindOfProperty := { id := "phase angle", scale := .ratio }

/-- Duration — item 3-9 (`t`, s): the trajectory parameter, `∂ₜ`'s denominator. -/
def duration : KindOfProperty := { id := "duration", scale := .ratio }

/-! ## The five mints — what the standard leaves to the application -/

/-- **Mint.** The spring constant `k` — the input datum with no catalogue item
(`M·T⁻²`; Hooke's `F = −k·x` fixes the dimension, Stage 1 certifies it). The
bare-real system parameter is where the wrong recipe `√(m/k)` lived. -/
def springConstant : KindOfProperty := { id := "spring constant", scale := .ratio }

/-- **Mint.** The squared angular frequency — `k/m`, the radicand of `ω = √(k/m)`:
the pilot's radicand-first pattern (`T⁻²`; the catalogue's nearest neighbor, angular
acceleration 3-13, is a different property at the same dimension). -/
def squaredAngularFrequency : KindOfProperty :=
  { id := "squared angular frequency", scale := .ratio }

/-- **Mint.** The Lagrangian — `T − V`, at the joule but not an energy of the system's
state: the catalogue names the *sum* of the comparable pair (mechanical energy) and
has no item for its difference. Fourth joule. -/
def lagrangian : KindOfProperty := { id := "Lagrangian", scale := .ratio }

/-- **Mint.** Translational kinetic energy — `½M⟪V,V⟫`, König's first summand: a
species of 4-28.2 the standard leaves unnamed. Fifth joule. -/
def translationalKineticEnergy : KindOfProperty :=
  { id := "translational kinetic energy", scale := .ratio }

/-- **Mint.** Rotational kinetic energy — `½ω·(Iω)`, König's second summand. Sixth
joule. -/
def rotationalKineticEnergy : KindOfProperty :=
  { id := "rotational kinetic energy", scale := .ratio }

/-! ## Distinctness — the collisions the vocabulary exists to prevent

Six kinds at the joule, two at `T⁻¹`, two at `T`. Upstream all of them are `ℝ`;
every separation below is decidable. -/

/-- **A kinetic energy is not a potential energy** — the pilot's separation, at
PhysLib's own oscillator. -/
theorem kineticEnergy_ne_potentialEnergy : kineticEnergy ≠ potentialEnergy := by decide

/-- **A summand is not the sum**: kinetic energy is not mechanical energy (it
*specializes* it — the lattice below). -/
theorem kineticEnergy_ne_mechanicalEnergy : kineticEnergy ≠ mechanicalEnergy := by
  decide

/-- **The difference is not the sum**: the Lagrangian is not mechanical energy — same
joule, opposite sign convention on `V`, and no seat at the join. -/
theorem lagrangian_ne_mechanicalEnergy : lagrangian ≠ mechanicalEnergy := by decide

/-- The Lagrangian is not a kinetic energy either — the `V = 0` coincidence is not an
identity. -/
theorem lagrangian_ne_kineticEnergy : lagrangian ≠ kineticEnergy := by decide

/-- **König's two species are distinct** — what separates them is the reading (centre
of mass vs rotation about it), not the joule. -/
theorem translationalKineticEnergy_ne_rotationalKineticEnergy :
    translationalKineticEnergy ≠ rotationalKineticEnergy := by decide

/-- **The two subtrees' shared letter, separated**: the oscillator's `ω` (angular
frequency) is not the rigid body's `ω` (angular velocity) — one dimension `T⁻¹`, two
catalogue items. -/
theorem angularFrequency_ne_angularVelocity : angularFrequency ≠ angularVelocity := by
  decide

/-- **The repetition interval is not the trajectory parameter**: period duration and
duration share `T`. -/
theorem periodDuration_ne_duration : periodDuration ≠ duration := by decide

/-! ## The directory's specialization lattice

Four edges on two levels — the pilot's energy pair, plus König's split of the kinetic
summand. This is the lattice both curated joins stand on: `T + V` at mechanical
energy, translational + rotational at kinetic energy — and it composes. -/

/-- The direct-parent edges of the directory's kind family. -/
inductive Edge : KindOfProperty → KindOfProperty → Prop
  /-- Kinetic energy is a mechanical energy. -/
  | kineticEnergy_mechanicalEnergy : Edge kineticEnergy mechanicalEnergy
  /-- Potential energy is a mechanical energy. -/
  | potentialEnergy_mechanicalEnergy : Edge potentialEnergy mechanicalEnergy
  /-- Translational kinetic energy is a kinetic energy. -/
  | translational_kineticEnergy : Edge translationalKineticEnergy kineticEnergy
  /-- Rotational kinetic energy is a kinetic energy. -/
  | rotational_kineticEnergy : Edge rotationalKineticEnergy kineticEnergy

/-- Kinetic energy specializes mechanical energy. -/
theorem kineticEnergy_specializes : Specializes Edge kineticEnergy mechanicalEnergy :=
  .of_edge .kineticEnergy_mechanicalEnergy

/-- Potential energy specializes mechanical energy. -/
theorem potentialEnergy_specializes :
    Specializes Edge potentialEnergy mechanicalEnergy :=
  .of_edge .potentialEnergy_mechanicalEnergy

/-- Translational kinetic energy specializes kinetic energy. -/
theorem translational_specializes :
    Specializes Edge translationalKineticEnergy kineticEnergy :=
  .of_edge .translational_kineticEnergy

/-- Rotational kinetic energy specializes kinetic energy. -/
theorem rotational_specializes :
    Specializes Edge rotationalKineticEnergy kineticEnergy :=
  .of_edge .rotational_kineticEnergy

/-- **The lattice composes**: a König summand is a mechanical energy, transitively —
two levels, one preorder. -/
theorem rotational_specializes_mechanicalEnergy :
    Specializes Edge rotationalKineticEnergy mechanicalEnergy :=
  rotational_specializes.trans kineticEnergy_specializes

/-- **`T` and `V` are mutually comparable as energies** while staying distinct kinds —
the fact the first join stands on. -/
theorem kineticEnergy_comparable_potentialEnergy :
    MutuallyComparable Edge kineticEnergy potentialEnergy :=
  ⟨mechanicalEnergy, kineticEnergy_specializes, potentialEnergy_specializes⟩

/-- **König's summands are mutually comparable as kinetic energies** — the fact the
second join stands on. -/
theorem translational_comparable_rotational :
    MutuallyComparable Edge translationalKineticEnergy rotationalKineticEnergy :=
  ⟨kineticEnergy, translational_specializes, rotational_specializes⟩

/-- **The Lagrangian joins nothing**: it is comparable to no energy in the lattice —
the "difference without a home" as a checked fact about the edges, not a slogan.
(Stated as: no direct parent edge leaves it.) -/
theorem lagrangian_no_edge (k : KindOfProperty) : ¬ Edge lagrangian k := by
  intro h
  have hsrc : ∀ a b, Edge a b →
      a = kineticEnergy ∨ a = potentialEnergy ∨
      a = translationalKineticEnergy ∨ a = rotationalKineticEnergy := by
    intro a b hab
    cases hab
    · exact Or.inl rfl
    · exact Or.inr (Or.inl rfl)
    · exact Or.inr (Or.inr (Or.inl rfl))
    · exact Or.inr (Or.inr (Or.inr rfl))
  rcases hsrc _ _ h with h1 | h1 | h1 | h1 <;> exact absurd h1 (by decide)

end ForPhysLib.ClassicalMechanics.Kinds
