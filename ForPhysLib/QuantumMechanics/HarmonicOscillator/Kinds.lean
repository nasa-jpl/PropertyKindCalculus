/-
# Stage 0 — the kind vocabulary of `Physlib/QuantumMechanics/HarmonicOscillator`

The first rung of [the adoption ladder](../../PLAN.md#stage-0-the-kind-vocabulary), for
the campaign's pilot directory. One file, bare `KindOfProperty` declarations,
Mathlib-free and PhysLib-free — importable by anything, costing nothing until something
imports it.

**Mostly a lookup, not a design — and the remainder is named.** Every kind the standard
lists is copied *verbatim* from PKC's ISO 80000 catalogue — ids, scales, principles —
and Stage 1 (`Metrology.lean`) proves the agreement by `decide`, so this file cannot
silently drift from the standard it looks up. What stays local is exactly what the
standard does not list, and each mint says why it exists:

* the **characteristic length** `ξ` — a *species* of length in Part 3's own
  `lengthSpecies` pattern, individuated as the oscillator's ground-state width;
* **momentum squared** — `p̂²`'s kind, deliberately *not* an energy until `(2m)⁻¹`
  acts (the F1 refusal of `Feasibility.lean`);
* the **radicand chain** — "action per mass" and the ξ² radicand, the two derived
  kinds through which the only kindable spelling of `ξ = √(ℏ/(m·ω))` passes (the F2
  finding: the root-first spelling's half-power intermediates are named by *no* kind
  here, on purpose).

The ids of the two chain mints match `Feasibility.lean`'s `kind_algebra` block
character for character, so the pilot's probes and the ladder speak one vocabulary.

**The vocabulary is what the directory's own API speaks.** `Basic.lean` carries `m`,
`ω i` and `ξ i` as bare reals, `kineticOperator`/`potentialOperator` and their sum
`hamiltonian`; `Eigenstates.lean` carries `eigenEnergy = ∑ i, ℏ ωᵢ (nᵢ + ½)`; the 1D
file carries `ξ = √(ℏ/(m·ω))`. Everything below names a reading those files already
make — three of them at the *same* dimension `M·L²·T⁻²`, which is the collision the
vocabulary exists to prevent.
-/

import PropertyKindCalculus

namespace ForPhysLib.QuantumMechanics.HarmonicOscillator.Kinds

open PropertyKindCalculus

/-! ## The lookups — ISO 80000, verbatim -/

/-- Mass — ISO 80000-4 item 4-1: the particle's `m`, a bare `ℝ` field in both
oscillator structures. -/
def mass : KindOfProperty := { id := "mass", scale := .ratio }

/-- Action — item 4-32 (`S`, J·s): ℏ's kind. The same dimension as angular momentum,
a distinct kind. -/
def action : KindOfProperty := { id := "action", scale := .ratio }

/-- Angular frequency — ISO 80000-3 item 3-18 (`ω`, rad/s): the mode frequencies
`Q.ω i`. -/
def angularFrequency : KindOfProperty := { id := "angular frequency", scale := .ratio }

/-- Kinetic energy — item 4-28.2: `T̂`'s kind. -/
def kineticEnergy : KindOfProperty := { id := "kinetic energy", scale := .ratio }

/-- Potential energy — item 4-28.1: `V̂`'s kind. -/
def potentialEnergy : KindOfProperty := { id := "potential energy", scale := .ratio }

/-- Mechanical energy — item 4-28.3: the family's join target — exactly the `T̂ + V̂`
sum the Hamiltonian is, and where the eigenvalues `ℏ ωᵢ (nᵢ + ½)` land. -/
def mechanicalEnergy : KindOfProperty := { id := "mechanical energy", scale := .ratio }

/-- Momentum — item 4-8: `p̂`'s kind (the momentum operator the directory squares). -/
def momentum : KindOfProperty := { id := "momentum", scale := .ratio }

/-- Length — item 3-1.1, the genus the characteristic length specializes. -/
def length : KindOfProperty := { id := "length", scale := .ratio }

/-! ## The species and the local mints — what the standard does not list -/

/-- The characteristic length `ξ` — a species of length (item 3-1.1) in Part 3's
`lengthSpecies` pattern, individuated as the oscillator's ground-state width. -/
def characteristicLength : KindOfProperty :=
  { id := "characteristic length", scale := .ratio,
    examPrinciple := some "ground-state-width" }

/-- Momentum squared — `p̂²`'s kind. Deliberately *not* joined to the energy family:
`p̂²` is not an energy until `(2m)⁻¹` acts, and `T̂ + p̂²` must be refused. -/
def momentumSquared : KindOfProperty := { id := "momentum squared", scale := .ratio }

/-- Action per mass — the first link of the ξ² radicand chain (`ℏ/m`). Same id as
`Feasibility.lean`'s `kind_algebra` mint, so the two files' kinds are equal. -/
def specificAction : KindOfProperty := { id := "action per mass", scale := .ratio }

/-- The ξ² radicand — `ℏ/(m·ω)`, a length squared. The only spelling of the
characteristic length that survives kinding passes through this kind (F2); the
root-first spelling's half-power intermediates are named by no kind here, on purpose. -/
def xiSqRadicand : KindOfProperty :=
  { id := "length squared — the ξ² radicand", scale := .ratio }

/-! ## Distinctness — the collisions the vocabulary exists to prevent

The three energies share the dimension `M·L²·T⁻²`; nothing dimensional separates
`T̂` from `V̂` from `Ĥ`. The kind layer does, decidably. -/

/-- **Kinetic is not potential** — the two operators the directory adds are distinct
kinds; their sum is licensed only at the family's join. -/
theorem kineticEnergy_ne_potentialEnergy : kineticEnergy ≠ potentialEnergy := by decide

/-- Kinetic energy is not the joint energy it specializes. -/
theorem kineticEnergy_ne_mechanicalEnergy : kineticEnergy ≠ mechanicalEnergy := by decide

/-- Potential energy is not the joint energy it specializes. -/
theorem potentialEnergy_ne_mechanicalEnergy : potentialEnergy ≠ mechanicalEnergy := by
  decide

/-- The characteristic length is not bare length — the species carries its
examination principle (the ground-state width), the genus carries none. -/
theorem characteristicLength_ne_length : characteristicLength ≠ length := by decide

/-! ## The directory's specialization lattice

The direct-parent edges among the directory's own kinds. The energy pair is the
lattice the Hamiltonian join (`Feasibility.lean`'s `KindJoin`, Stage 3's table)
stands on: `T̂` and `V̂` are mutually comparable *as* energies while staying distinct
kinds — comparability without identity (R2), on exactly the pair the sum joins. -/

/-- The direct-parent edges of the oscillator directory's kind family. -/
inductive Edge : KindOfProperty → KindOfProperty → Prop
  /-- Kinetic energy is a mechanical energy. -/
  | kineticEnergy_mechanicalEnergy : Edge kineticEnergy mechanicalEnergy
  /-- Potential energy is a mechanical energy. -/
  | potentialEnergy_mechanicalEnergy : Edge potentialEnergy mechanicalEnergy
  /-- The characteristic length is a length. -/
  | characteristicLength_length : Edge characteristicLength length

/-- Kinetic energy specializes mechanical energy. -/
theorem kineticEnergy_specializes : Specializes Edge kineticEnergy mechanicalEnergy :=
  .of_edge .kineticEnergy_mechanicalEnergy

/-- Potential energy specializes mechanical energy. -/
theorem potentialEnergy_specializes : Specializes Edge potentialEnergy mechanicalEnergy :=
  .of_edge .potentialEnergy_mechanicalEnergy

/-- **`T̂` and `V̂` are mutually comparable as energies** while staying distinct kinds
— the lattice fact the Hamiltonian's join sum stands on. -/
theorem kineticEnergy_comparable_potentialEnergy :
    MutuallyComparable Edge kineticEnergy potentialEnergy :=
  ⟨mechanicalEnergy, .of_edge .kineticEnergy_mechanicalEnergy,
    .of_edge .potentialEnergy_mechanicalEnergy⟩

/-- The characteristic length specializes length. -/
theorem characteristicLength_specializes : Specializes Edge characteristicLength length :=
  .of_edge .characteristicLength_length

end ForPhysLib.QuantumMechanics.HarmonicOscillator.Kinds
