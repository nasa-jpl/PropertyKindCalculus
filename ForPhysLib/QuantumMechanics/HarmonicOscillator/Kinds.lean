/-
# Stage 0 — the kind vocabulary of `Physlib/QuantumMechanics/HarmonicOscillator`

The first rung of [the adoption ladder](../../PLAN.md#stage-0-the-kind-vocabulary), for
the campaign's pilot directory. One file of `KindOfProperty` declarations,
Mathlib-free and PhysLib-free — the only import beyond the calculus is PKC's own
`Iso80000` catalogue, itself Mathlib-free.

**Mostly a lookup, not a design — and the remainder is named.** Every kind the standard
lists *is* the catalogue's entry, projected to its kind — nothing is re-typed, so
nothing can drift; Stage 1 (`Metrology.lean`) records the identification definitionally
(`rfl`). What stays local is exactly what the standard does not list, and each mint
says why it exists:

* the **characteristic length** `ξ` — built by Part 3's own `lengthSpecies`
  constructor, individuated as the oscillator's ground-state width (the catalogue's
  species pattern, at this directory's species — a construction the catalogue itself
  provides, not a mint);
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

module

public import PropertyKindCalculus
public import PropertyKindCalculus.Iso80000.Part3
public import PropertyKindCalculus.Iso80000.Part4
public import PropertyKindCalculus.Iso80000.Part10

@[expose] public section

namespace ForPhysLib.QuantumMechanics.HarmonicOscillator.Kinds

open PropertyKindCalculus

/-! ## The lookups — ISO 80000, verbatim -/

/-- Mass — ISO 80000-4 item 4-1: the particle's `m`, a bare `ℝ` field in both
oscillator structures. -/
def mass : KindOfProperty := (Iso80000.Part4.mass).kind

/-- Action — item 4-32 (`S`, J·s): ℏ's kind. The same dimension as angular momentum,
a distinct kind. -/
def action : KindOfProperty := (Iso80000.Part4.action).kind

/-- Angular momentum — item 4-11 (`L`, kg·m²/s): the eigenvalue scale of `𝐋ᵢⱼ`. The
other half of the J·s collision: `m·ℏ` is an angular-momentum *reading* built from the
action constant, and the registry keeps the two kinds apart at their one shared
dimension. -/
def angularMomentum : KindOfProperty := (Iso80000.Part4.angularMomentum).kind

/-- Angular frequency — ISO 80000-3 item 3-18 (`ω`, rad/s): the mode frequencies
`Q.ω i`. -/
def angularFrequency : KindOfProperty := (Iso80000.Part3.angularFrequency).kind

/-- Kinetic energy — item 4-28.2: `T̂`'s kind. -/
def kineticEnergy : KindOfProperty := (Iso80000.Part4.kineticEnergy).kind

/-- Potential energy — item 4-28.1: `V̂`'s kind. -/
def potentialEnergy : KindOfProperty := (Iso80000.Part4.potentialEnergy).kind

/-- Mechanical energy — item 4-28.3: the family's join target — exactly the `T̂ + V̂`
sum the Hamiltonian is, and where the eigenvalues `ℏ ωᵢ (nᵢ + ½)` land. -/
def mechanicalEnergy : KindOfProperty := (Iso80000.Part4.mechanicalEnergy).kind

/-- Momentum — item 4-8: `p̂`'s kind (the momentum operator the directory squares). -/
def momentum : KindOfProperty := (Iso80000.Part4.momentum).kind

/-- Length — item 3-1.1, the genus the characteristic length specializes. -/
def length : KindOfProperty := (Iso80000.Part3.length).kind

/-- Quantum number — ISO 80000-10 item 10-13.1: the occupation labels `n : Fin d → ℕ`
that index the eigenstates. A catalogue lookup, not a mint — the standard lists the
kind the directory's `n` already is. -/
def quantumNumber : KindOfProperty := (Iso80000.Part10.quantumNumber).kind

/-! ## The species and the local mints — what the standard does not list -/

/-- The characteristic length `ξ` — a species of length (item 3-1.1), built by Part 3's
own `lengthSpecies` constructor, individuated as the oscillator's ground-state width. -/
def characteristicLength : KindOfProperty :=
  (Iso80000.Part3.lengthSpecies "characteristic length" { id := "ground-state-width" }).kind

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

/-- The dimensionless coordinate `x̃ᵢ = xᵢ/ξᵢ` — the argument the eigenfunctions hand
to the Hermite polynomials (`eigenfunction_apply` writes `x i / Q.ξ i`), and the
coordinate `ξEquiv` rescales. The nondimensionalization event, named as a kind. -/
def dimensionlessCoordinate : KindOfProperty :=
  { id := "dimensionless coordinate", scale := .ratio }

/-- The Born density `|ψ|²` — a probability density over position, the kinded object
the wavefunction is the root of. ψ itself carries the half-power dimension `L^(−d/2)`
and is named by **no kind here, on purpose** — the F2 radicand-first rule recurring at
the states themselves (the `1/√ξᵢ` each `eigenCoeff` carries is that root's trace). -/
def bornDensity : KindOfProperty :=
  { id := "probability density over position", scale := .ratio }

/-- The `d`-dimensional volume element the Born density integrates against. *Not* the
catalogue's volume (item 3-4, `L³`): its dimension is `Lᵈ`, fixed by the model's `d`,
which is why its dimensional pairing is a parametric theorem rather than a registry
entry. -/
def spatialVolume : KindOfProperty :=
  { id := "spatial volume — the d-dimensional volume element", scale := .ratio }

/-- Probability — dimension one, but not a bare number: the kind `∫ρ dV` lands in,
distinct from the quantum numbers that share its dimension. -/
def probability : KindOfProperty := { id := "probability", scale := .ratio }

/-- Energy squared — the energy variance's kind (`⟪Ĥψ,Ĥψ⟫ − ⟪ψ,Ĥψ⟫²`); its root, the
standard uncertainty σ, is one attested crossing back to energy (radicand-first
again). -/
def energySquared : KindOfProperty :=
  { id := "energy squared — the variance's kind", scale := .ratio }

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

/-- A probability is not a quantum number, though both live at dimension one — the
dimension-1 conflation is exactly what the kind layer exists to prevent. -/
theorem probability_ne_quantumNumber : probability ≠ quantumNumber := by decide

/-- The variance's kind is not the energy it is the variance of. -/
theorem energySquared_ne_mechanicalEnergy : energySquared ≠ mechanicalEnergy := by decide

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

