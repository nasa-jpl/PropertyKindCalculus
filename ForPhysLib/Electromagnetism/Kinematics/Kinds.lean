/-
# Stage 0 — the kind vocabulary of `Physlib/Electromagnetism/Kinematics`

The first rung of [the adoption ladder](../../PLAN.md#stage-0-the-kind-vocabulary), for
the campaign's second directory. One file of `KindOfProperty` declarations,
Mathlib-free and PhysLib-free — the only import beyond the calculus is PKC's own
`Iso80000` catalogue, itself Mathlib-free.

**Almost entirely a lookup — the mirror image of the pilot.** Every kind the chain's
API speaks *is* the corresponding IEC 80000-6 catalogue entry (plus three Part-3
coordinates), projected to its kind — nothing is re-typed, so nothing can drift;
Stage 1 (`Metrology.lean`) records the identification definitionally (`rfl`). **Eight** kinds are minted,
and they are one finding three ways: the standard catalogues *frame-bound, gauge-fixed,
measurable readings* (`E`, `B`, `φ`), so the readings the chain's own key results
export that are none of those — the two tensor entries, Maxwell's three derivative
readings, and the variational subtree's three (the Lagrangian density, the variational
gradient, the canonical momentum) — have no catalogue item to look up. The first two:

* the **potential-gradient entry** — `∂A`'s kind: *gauge-dependent* (it moves under
  `A ↦ A + ∂χ`), the tesla-dimensioned chart;
* the **field-strength entry** — `F`'s kind: *gauge-invariant and frame-covariant*
  (`toFieldStrength_gaugeTransform`, `toFieldStrength_equivariant` are upstream's own
  proofs), the tesla-dimensioned extent.

Both share the magnetic flux density's dimension; nothing dimensional separates the
three teslas. The kind layer does, decidably — the same-dimension discrimination the
pilot ran on three energies, recurring on gauge and frame.

**No join, and that is a finding.** The pilot's directory needed a curated `KindJoin`
(`T̂ + V̂` at mechanical energy). This chain needs none: every sum the physics writes —
`E = −∇φ − ∂ₜ𝐀`, the boost's `γ(E + cβ·B)`, the gauge shift `A + ∂χ` — is a *same-kind*
sum whose heterogeneous ingredient arrives through a registered edge or an attested
crossing first. The joins here are edge-mediated, not curated.

**The vocabulary is what the chain's own API speaks.** `EMPotential.lean` carries
`A^μ` and its derivative tensor; `ScalarPotential`/`VectorPotential` the two
time-sliced readings; `FieldStrength` the tensor and its matrix;
`ElectricField`/`MagneticField` the frame-bound fields; `Boosts` the mixing laws;
`GaugeTransformation` the shift by `χ`. Everything below names a reading those files
already make.
-/

module

public import PropertyKindCalculus
public import PropertyKindCalculus.Iso80000.Part3
public import PropertyKindCalculus.Iso80000.Part6

public section -- pkc-blanket
@[expose] section -- pkc-blanket-expose

namespace ForPhysLib.Electromagnetism.Kinematics.Kinds

open PropertyKindCalculus

/-! ## The lookups — IEC 80000-6 and ISO 80000-3, verbatim -/

/-- Magnetic vector potential — item 6-32 (`A`, Wb/m): the four-potential's *one*
kind. `A⁰ = φ/c` is made homogeneous with the spatial components by the `/c`
(Feasibility F2); the whole Lorentz vector sits here. -/
def magneticVectorPotential : KindOfProperty := (Iso80000.Part6.magneticVectorPotential).kind

/-- Electric potential — item 6-11.1 (`V`, V), **interval-scale in the standard
itself**: fixed only up to gauge freedom. The scale is load-bearing: the ratio table
refuses to land on it (Feasibility's pinned refusal), so `scalarPotential = c·A⁰` is a
named crossing, never a table edge. -/
def electricPotential : KindOfProperty := (Iso80000.Part6.electricPotential).kind

/-- Electric potential difference — item 6-11.2 (`U`, V), ratio-scale: the physical
extent, and the only member of the 6-11 family a table edge may target. -/
def electricPotentialDifference : KindOfProperty := (Iso80000.Part6.electricPotentialDifference).kind

/-- Electric field strength — item 6-10 (`E`, V/m): the chain's `electricField`, a
frame-bound reading (the boost laws mix it). -/
def electricFieldStrength : KindOfProperty := (Iso80000.Part6.electricFieldStrength).kind

/-- Magnetic flux density — item 6-21 (`B`, T): the chain's `magneticField` and the
entries of `magneticFieldMatrix` — the spatial block of the field strength, read in a
chosen frame. -/
def magneticFluxDensity : KindOfProperty := (Iso80000.Part6.magneticFluxDensity).kind

/-- Magnetic flux — item 6-22.1 (`Φ`, Wb): the *gauge function's* kind — `∂^μχ` sits
at the vector potential, so `χ` is a flux field. A lookup, not a mint: the standard
already lists the kind the gauge freedom is parameterized by (Feasibility F5). -/
def magneticFlux : KindOfProperty := (Iso80000.Part6.magneticFlux).kind

/-- Speed of light in vacuum — item 6-35.2 (`c₀`, m/s): the unit-system choice the
source elides behind `(c : SpeedOfLight := 1)` and the kinded chain declares once
(Feasibility F3); the velocity edge's other factor. -/
def speedOfLight : KindOfProperty := (Iso80000.Part6.speedOfLight).kind

/-- Speed — ISO 80000-3 item 3-10.2, the genus 6-35.2 specializes. -/
def speed : KindOfProperty := (Iso80000.Part3.speed).kind

/-- Length — item 3-1.1: the spacetime coordinate's kind (`x⁰ = c·t` — upstream's
`toTimeAndSpace` stores `c·t` in the time slot), and `∇`'s denominator. -/
def length : KindOfProperty := (Iso80000.Part3.length).kind

/-- Duration — item 3-9: `Time`'s kind, `∂ₜ`'s denominator in the sliced readings. -/
def duration : KindOfProperty := (Iso80000.Part3.duration).kind

/-- Electric charge density — item 6-3 (`ρ`, C/m³): the source Gauss's law reads. -/
def electricChargeDensity : KindOfProperty := (Iso80000.Part6.electricChargeDensity).kind

/-- Electric current density — item 6-8 (`J`, A/m²): Ampère's source — and where the
displacement current `ε₀·∂ₜE` lands, by the catalogue's own item. -/
def electricCurrentDensity : KindOfProperty := (Iso80000.Part6.electricCurrentDensity).kind

/-- The electric constant — item 6-14.1 (`ε₀`, F/m): `FreeSpace.ε₀`, a bare `ℝ`
field upstream. -/
def electricConstant : KindOfProperty := (Iso80000.Part6.electricConstant).kind

/-- The magnetic constant — item 6-26.1 (`μ₀`, H/m): `FreeSpace.μ₀`, a bare `ℝ`
field upstream — and `c = 1/√(ε₀μ₀)` is upstream's *definition* of `FreeSpace.c`. -/
def magneticConstant : KindOfProperty := (Iso80000.Part6.magneticConstant).kind

/-- Electromagnetic energy density — item 6-33 (`w`, J/m³): the Hamiltonian's kind.
The identification is upstream's own theorem — `hamiltonian_eq_electricField_magneticField`
writes `H` as the catalogue's `½(ε₀E² + B²/μ₀)` plus the source terms. -/
def electromagneticEnergyDensity : KindOfProperty := (Iso80000.Part6.electromagneticEnergyDensity).kind

/-- Linear electric current density — item 6-9 (`J_S`, A/m): registered as the
canonical momentum's *collision partner* — `π = ∂L/∂(∂₀A)` has exactly this dimension
and is not this kind (the decide below). -/
def linearElectricCurrentDensity : KindOfProperty := (Iso80000.Part6.linearCurrentDensity).kind

/-! ## The eight mints — the readings the standard does not list

The standard catalogues frame-bound, gauge-fixed readings; the chain's two exported
tensors are neither, so their entry kinds are minted here — both at the flux density's
dimension, individuated by what they are invariant under. -/

/-- The derivative tensor's entry kind — `∂_μ A^ν` (`EMPotential.lean`'s `deriv`).
Tesla-dimensioned but **gauge-dependent**: it moves under `A ↦ A + ∂χ` (only the
antisymmetrization cancels the shift). The chart, not the extent. -/
def potentialGradient : KindOfProperty :=
  { id := "potential gradient — the gauge-dependent tensor entry", scale := .ratio }

/-- The field-strength tensor's entry kind — `F^{μν}` (`FieldStrength.lean`).
Tesla-dimensioned, **gauge-invariant and frame-covariant** — upstream proves both
(`toFieldStrength_gaugeTransform`, `toFieldStrength_equivariant`). The frame-bound
readings come off it through one velocity edge (`E_i = −c·F⁰ⁱ`) and one block
identification (`B_ij = F^{ij}`). -/
def fieldStrength : KindOfProperty :=
  { id := "field strength — the frame-covariant tensor entry", scale := .ratio }

/-- The electric field's derivative reading (V/m²): `∇⬝E`, the entries of `∇⨯E`, and
`∂ₜB` all land here — the kind Maxwell's Gauss-electric and Faraday sides speak.
Unlisted: the standard catalogues fields, not their pointwise derivative readings. -/
def electricFieldDerivative : KindOfProperty :=
  { id := "electric field derivative", scale := .ratio }

/-- The magnetic field's per-length reading (T/m): the entries of `∇⨯B` and `μ₀·J` —
Ampère's two sides. -/
def magneticFieldDerivative : KindOfProperty :=
  { id := "magnetic field derivative", scale := .ratio }

/-- The electric field's time rate (V/(m·s)): `∂ₜE`, whose `ε₀`-scaling is the
displacement current density — landing back at the catalogue's 6-8. -/
def electricFieldRate : KindOfProperty :=
  { id := "electric field rate", scale := .ratio }

/-- The Lagrangian density — `L = −¼μ₀⁻¹·F·F − A·J` (`Dynamics/`), at the *energy
density's* dimension (J/m³) and deliberately not at 6-33: `L` is **gauge-dependent**
(`freeCurrentPotential_add_const` moves it; only its kinetic part is invariant), where
6-33 is the measurable field energy. The same-dimension discrimination that separated
the three teslas, at the density. -/
def lagrangianDensity : KindOfProperty :=
  { id := "Lagrangian density — the gauge-dependent volumetric reading", scale := .ratio }

/-- The variational gradient's entry kind — `δS/δA` (`gradLagrangian`,
`gradKineticTerm`), at the *current density's* dimension (A/m²) and deliberately not
at 6-8: it is the reading `IsExtrema` sets to zero, not a transported charge. The
Euler–Lagrange equation `gradKineticTerm − gradFreeCurrentPotential = 0` is a
same-kind subtraction *here*. -/
def variationalGradient : KindOfProperty :=
  { id := "variational gradient — the Euler–Lagrange reading", scale := .ratio }

/-- The canonical momentum's entry kind — `π = ∂L/∂(∂₀A)` (`Hamiltonian.lean`), at
6-9's dimension (A/m) and not 6-9: the Legendre-conjugate reading, `−E/(μ₀c)` in the
spatial slots (upstream's `canonicalMomentum_eq_electricField`), not a current
through a line. -/
def canonicalMomentumDensity : KindOfProperty :=
  { id := "canonical momentum — the Legendre-conjugate reading", scale := .ratio }

/-! ## Distinctness — the collisions the vocabulary exists to prevent

Three kinds at the tesla, two at the volt, and a field pair whose dimensional
distinctness is basis-relative (Exhibit E problem 2: in Gaussian–CGS, `E` and `B`
*share* a dimension). Kind identity is examination, not exponents; every separation
below is decidable and none moves with the basis. -/

/-- **An electric field is not a magnetic field** — in any basis. The dimensional
separation is SI-relative (Gaussian units collapse it, proved in Exhibit E); the kind
separation is not. -/
theorem electricFieldStrength_ne_magneticFluxDensity :
    electricFieldStrength ≠ magneticFluxDensity := by decide

/-- **The tensor entry is not the magnetic field it contains** — same dimension in
*every* basis (the spatial block *is* `B`); what separates them is frame behavior:
`F`'s kind survives a boost, `B`'s is a frame-bound reading. -/
theorem fieldStrength_ne_magneticFluxDensity :
    fieldStrength ≠ magneticFluxDensity := by decide

/-- **The extent is not the chart** — `F` and `∂A` share the tesla; what separates
them is gauge behavior: `F` is invariant under `A ↦ A + ∂χ`, `∂A` is not. -/
theorem fieldStrength_ne_potentialGradient :
    fieldStrength ≠ potentialGradient := by decide

/-- **A potential is not a potential difference** — same dimension (the volt), same
`ℝ` upstream; the standard separates them by *scale*, and so does the vocabulary. -/
theorem electricPotential_ne_electricPotentialDifference :
    electricPotential ≠ electricPotentialDifference := by decide

/-- The load-bearing scale, pinned: electric potential is interval — 6-11.1 as the
standard writes it, and the reason every ratio edge at the potential is refused. -/
theorem electricPotential_isInterval :
    electricPotential.scale = .interval := rfl

/-- **The Lagrangian density is not the energy density** — one dimension (J/m³),
separated by gauge behavior: `H`'s reading is measurable, `L`'s moves under
`A ↦ A + c`. -/
theorem lagrangianDensity_ne_electromagneticEnergyDensity :
    lagrangianDensity ≠ electromagneticEnergyDensity := by decide

/-- **The variational gradient is not a current density** — one dimension (A/m²);
Euler–Lagrange *equates* it to `μ₀`-scaled sources, which is an edge, not an
identity. -/
theorem variationalGradient_ne_electricCurrentDensity :
    variationalGradient ≠ electricCurrentDensity := by decide

/-- **The canonical momentum is not a linear current density** — one dimension
(A/m); the conjugate of a field coordinate is not a current through a line. -/
theorem canonicalMomentumDensity_ne_linearElectricCurrentDensity :
    canonicalMomentumDensity ≠ linearElectricCurrentDensity := by decide

/-- The speed of light is not bare speed — the constant species is not its genus. -/
theorem speedOfLight_ne_speed : speedOfLight ≠ speed := by decide

/-! ## The directory's specialization lattice

One edge. The chain's kinds are otherwise deliberately *flat*: its heterogeneous
combinations are all frame- or gauge-mediated (registered edges and attested
crossings), not genus/species relations, and no curated join exists because no sum in
the chain needs one — the contrast with the pilot's energy family is the finding in
this file's header. -/

/-- The direct-parent edges of the kinematics directory's kind family. -/
inductive Edge : KindOfProperty → KindOfProperty → Prop
  /-- The speed of light in vacuum is a speed. -/
  | speedOfLight_speed : Edge speedOfLight speed

/-- The speed of light specializes speed — 6-35.2 under 3-10.2, the catalogue's own
placement of the constant. -/
theorem speedOfLight_specializes : Specializes Edge speedOfLight speed :=
  .of_edge .speedOfLight_speed

end ForPhysLib.Electromagnetism.Kinematics.Kinds

end -- pkc-blanket-expose
end -- pkc-blanket
