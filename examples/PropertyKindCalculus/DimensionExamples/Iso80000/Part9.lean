/-
# Worked examples — ISO 80000-9 (Physical chemistry and molecular physics)

Part-9 examples, mirroring the `Iso80000` library's own `Iso80000/Part9` layout:

1. the dimensional algebra over the mole reduction (molar mass is a mass, amount
   concentration a number density, molar internal energy an energy);
2. **the mole reduces to dimension one (R13)** — amount of substance is dimension one, so
   every molar quantity carries the dimension of its non-molar counterpart, and amount of
   substance joins the dimensionless family alongside the number of entities;
3. **the seven-fold `J/mol` collision** — molar internal energy ≡ molar Gibbs energy in
   dimension (the mole reduced) yet distinct in kind, with the two joules-per-mole not
   commensurable;
4. **a second dimension-one family** — the fractions, activities, and partition functions;
5. **defining relations** — molar mass = mass / amount, amount concentration = amount /
   volume; the molar quantities cross to ISO 80000-3, -4 and -5;
6. **catalogue coverage** — all 62 items carry their source as data.

These live in the Mathlib-backed `DimensionExamples` library.
-/

module

public import PropertyKindCalculus.Iso80000.Part9
meta import PropertyKindCalculus.Iso80000.Part9
public import PropertyKindCalculus.Iso80000.Part9.DefiningRelations
meta import PropertyKindCalculus.Iso80000.Part9.DefiningRelations
public import PropertyKindCalculus.QuantityReal
meta import PropertyKindCalculus.QuantityReal

@[expose] public section Blanket

namespace PropertyKindCalculus.Examples.Iso80000.Part9

open PropertyKindCalculus
open PropertyKindCalculus.Iso80000
open PropertyKindCalculus.Iso80000.Part9
open PropertyKindCalculus.Iso80000.Part9.DefiningRelations

/-! ## (1) ISO 80000-9 — the dimensional algebra over the mole reduction -/

-- molar mass is a mass; molar internal energy is an energy (`M·L²·T⁻²`)
example : molarMass.dim = Dim.mass := molarMass_dim_eq_mass
example : molarInternalEnergy.dim.time = -2 := molarInternalEnergy_dim_time
-- molality is an inverse mass
example : molality.dim = Dim.mass⁻¹ := molality_dim_eq_inverseMass

-- each kind carries its exact item citation as data
#guard molarMassCK.item == "9-4"
#guard amountConcentrationCK.item == "9-12.1"
#guard amountConcentrationCK.cite == "ISO 80000-9, Second edition, 2019-08 item 9-12.1"
#guard molarGibbsEnergyCK.item == "9-6.4"

/-! ## (2) The mole reduces to dimension one (requirement R13, on the standard)

The mole is a human-selected dimensionless count `N_A`, so amount of substance is
dimension one, and every `/mol` factor disappears from the dimension. -/

-- THE MOLE REDUCES: amount of substance is dimension one.
example : amountOfSubstance.dim = 1 := amountOfSubstance_dim_eq_one
-- MOLAR MASS IS A MASS: the `/mol` is invisible to the dimension functor.
example : molarMass.dim = Dim.mass := molarMass_dim_eq_mass
-- AMOUNT CONCENTRATION IS A NUMBER DENSITY: `mol/m³` ≡ `m⁻³`, the same as a particle
-- concentration (item 9-12.1 ≡ 9-9.1).
example : amountConcentration.dim = particleConcentration.dim :=
  amountConcentration_dim_eq_particleConcentration
-- and amount of substance joins the dimensionless family, distinct from the number of
-- entities (`N = n·N_A`), both dimension one.
example : amountOfSubstance.kind ≠ numberOfEntities.kind :=
  amountOfSubstance_ne_numberOfEntities

/-! ## (3) The seven-fold `J/mol` collision (on the real standard)

Molar internal energy, molar enthalpy, molar Helmholtz and Gibbs energies, the chemical
potential, the standard chemical potential, and the affinity all carry the same dimension
`M·L²·T⁻²` (the mole reduced) and the same unit string `J/mol`, yet are seven kinds. -/

-- SAME DIMENSION: molar internal energy ≡ molar Gibbs energy (`M·L²·T⁻²`).
example : molarInternalEnergy.dim = molarGibbsEnergy.dim :=
  molarInternalEnergy_dim_eq_molarGibbsEnergy_dim
-- DISTINCT KIND: yet they are not the same kind.
example : molarInternalEnergy.kind ≠ molarGibbsEnergy.kind :=
  molarInternalEnergy_ne_molarGibbsEnergy
-- and the two joules-per-mole are not commensurable.
example : ¬ jPerMolInternalEnergy.Commensurable jPerMolGibbs :=
  jPerMol_internalEnergy_gibbs_not_commensurable
-- the `J/mol` collision capstone, on standard quantities.
example : ∃ a b : DimensionedKind, a.kind ≠ b.kind ∧ a.dim = b.dim := iso80000_9_dim_collision
-- the molar heat capacities collide too (`J/(mol·K)`).
example : molarHeatCapacity.dim = molarEntropy.dim :=
  molarHeatCapacity_dim_eq_molarEntropy_dim

/-! ## (4) A second dimension-one family (the fractions, activities, partition functions) -/

-- the dimension-1 capstone on standard quantities — with the mole *inside* the family.
example : ∃ a b : DimensionedKind, a.kind ≠ b.kind ∧ a.dim = b.dim ∧ a.dim = 1 :=
  iso80000_9_dim_one_collision

/-! ## (5) Defining relations: physical chemistry built by the kind algebra

Molar mass is mass per amount, amount concentration amount per volume; the molar
quantities cross to ISO 80000-3, -4 and -5, and the mole reduces as a checked computation. -/

-- DIM FROM RELATION: molar mass carries the dimension of mass *because* `M = m/n` and the
-- mole is dimension one (cross-part, the mass from ISO 80000-4).
example : molarMass.dim = Part4.mass.dim / amountOfSubstance.dim :=
  molarMass_dim_from_mass_amount
-- the amount concentration is a number density *because* `c = n/V` divides a dimensionless
-- count by a volume (cross-part, the volume from ISO 80000-3).
example : amountConcentration.dim = amountOfSubstance.dim / Part3.volume.dim :=
  amountConcentration_dim_from_amount_volume

-- VERIFIED CONSTRUCTION (item 9-4): a molar mass built as mass / amount carries its
-- quotient certificate by construction, over `ℝ`.
example (m : Quantity Part4.mass.kind ℝ) (n : Quantity amountOfSubstance.kind ℝ) :
    (molarMassOf m n).IsQuotient molarMass_quot_mass_amount m n :=
  molarMassOf_isQuotient m n

-- the molar-mass quotient instantiates at a *different* carrier (`Int`), where the
-- construction also computes: `12 kg / 3 mol = 4 kg/mol` (at `Int`).
def molarMassInt : Quantity molarMass.kind Int :=
  Quantity.div molarMass_quot_mass_amount
    (⟨12⟩ : Quantity Part4.mass.kind Int) (⟨3⟩ : Quantity amountOfSubstance.kind Int)
#guard molarMassInt.magnitude == 4

/-! ## (6) Catalogue coverage — all 62 items carry their source as data -/

#guard PropertyKindCalculus.Iso80000.Part9.catalogue.length == 62
#guard amountOfSubstanceCK.item == "9-2"
#guard molarEntropyCK.item == "9-8"
#guard standardAbsoluteActivitySolventCK.item == "9-27.3"
#guard specificRotatoryPowerCK.item == "9-49"
#guard molarMassCK.coherentUnit == "kg/mol"
#guard amountOfSubstanceCK.coherentUnit == "mol"

end PropertyKindCalculus.Examples.Iso80000.Part9

end Blanket
