/-
# Worked examples — ISO 80000-5 (Thermodynamics)

Part-5 examples, mirroring the `Iso80000` library's own `Iso80000/Part5` layout:

1. the dimensional algebra and unit facts (heat is `M·L²·T⁻²`, entropy is
   `M·L²·T⁻²·Θ⁻¹`, a linear expansion coefficient is `Θ⁻¹`; the kelvin well-formed;
   commensurability "of the same kind");
2. **the scale-type distinction (requirement R6)** — thermodynamic temperature
   (ratio-scale) versus Celsius temperature (interval-scale), the *same* dimension
   `Θ` separated by scale alone, with the degree Celsius a well-formed unit that
   nonetheless does not admit `×`,`÷`;
3. **the energy family as a specialization lattice (R2)** — internal energy, enthalpy,
   the Helmholtz and Gibbs energies as energy species individuated **by defining
   construction**; the Helmholtz and Gibbs energies comparable yet distinct;
4. **dimension collisions** — same dimension, distinct kind: entropy vs heat capacity
   (the J/K case, even down to the same unit string), specific entropy vs specific
   heat capacity, and the dimension-one family;
5. **cross-part defining relations** — specific heat capacity = heat capacity / mass
   and the density of heat flow rate = heat flow rate / area compose Part-5 kinds out
   of Part-4 and Part-3 kinds; the ratio of specific heat capacities is dimensionless
   because it is a ratio of two specific heat capacities;
6. **catalogue coverage** — all 54 items carry their source as data.

Series-wide catalogue examples are in the sibling
`PropertyKindCalculus.DimensionExamples.Iso80000.References`.
-/

module

public import PropertyKindCalculus.Iso80000
meta import PropertyKindCalculus.Iso80000
public import PropertyKindCalculus.QuantityReal
meta import PropertyKindCalculus.QuantityReal

@[expose] public section Blanket

namespace PropertyKindCalculus.Examples.Iso80000.Part5

open PropertyKindCalculus
open PropertyKindCalculus.Iso80000
open PropertyKindCalculus.Iso80000.Part5
open PropertyKindCalculus.Iso80000.Part5.DefiningRelations

/-! ## (1) ISO 80000-5 — Thermodynamics (the dimensional algebra and units) -/

-- the dimensional algebra is a checked computation, not an annotation
example : thermodynamicTemperature.dim = Dim.temperature := thermodynamicTemperature_dim
example : heat.dim.length = 2 := heat_dim_length
example : entropy.dim.temperature = -1 := entropy_dim_temperature
example : heatCapacity.dim.temperature = -1 := heatCapacity_dim_temperature
example : linearExpansionCoefficient.dim.temperature = -1 :=
  linearExpansionCoefficient_dim_temperature

-- each kind carries its exact item citation as data
#guard thermodynamicTemperatureCK.item == "5-1"
#guard entropyCK.item == "5-18"
#guard entropyCK.cite == "ISO 80000-5, Second edition, 2019-08 item 5-18"
#guard gibbsEnergyCK.item == "5-20.5"

-- the kelvin and the joule are well-formed units; commensurability is "of the same kind"
example : kelvin.WellFormed := kelvin_wellFormed
example : joule.WellFormed := joule_wellFormed
example : ¬ kelvin.Commensurable joule := kelvin_joule_not_commensurable

/-! ## (2) The scale-type distinction (requirement R6, on the real standard)

Thermodynamic temperature (5-1) and Celsius temperature (5-2) have the *same*
dimension `Θ`, yet are different kinds — separated not by dimension but by **scale
type**: thermodynamic temperature is ratio-scale (an absolute zero), Celsius
temperature interval-scale (an arbitrary zero at the ice point). -/

-- (a) thermodynamic temperature admits ×,÷ (ratio scale); Celsius temperature does NOT
example : ScaleType.AllowsRatio thermodynamicTemperature.kind.scale :=
  thermodynamicTemperature_allowsRatio
example : ¬ ScaleType.AllowsRatio celsiusTemperature.kind.scale :=
  celsiusTemperature_not_allowsRatio

-- (b) yet the degree Celsius is a WELL-FORMED unit — a kind bears a unit from the
--     differential (interval) scale upward, not only from ratio scale.
example : degreeCelsius.WellFormed := degreeCelsius_wellFormed

-- (c) DISTINCTION BY SCALE, NOT DIMENSION: same dimension `Θ`, distinct kinds.
example : thermodynamicTemperature.dim = celsiusTemperature.dim := rfl
example : thermodynamicTemperature.kind ≠ celsiusTemperature.kind :=
  thermodynamicTemperature_ne_celsiusTemperature

-- the scale capstone, on standard quantities.
example : ∃ a b : DimensionedKind, a.kind ≠ b.kind ∧ a.dim = b.dim ∧
    a.kind.scale ≠ b.kind.scale :=
  iso80000_5_scale_collision

/-! ## (3) The energy family: a specialization lattice individuated by defining
construction (requirement R2, on the real standard)

ISO 80000-5 lists internal energy (5-20.2), enthalpy (5-20.3), the Helmholtz energy
(5-20.4), and the Gibbs energy (5-20.5) as species of energy (5-20.1), all of
dimension `M·L²·T⁻²`, distinguished in the standard by *which thermodynamic variables
are natural to the potential*. Here each is a *species* of the general energy kind,
individuated **not by fiat but by an explicit defining-construction (examination)
principle**. -/

-- (a) internal energy specializes energy.
example : Specializes Edge internalEnergy.kind energy.kind :=
  internalEnergy_specializes_energy

-- (b) DISTINCTION NOT BY FIAT: the Helmholtz and Gibbs energies are distinct kinds
--     *because they are defined by different natural variables* (T,V vs T,p) —
--     proved via `distinct_of_examPrinciple`, not by `id` strings.
example : helmholtzEnergy.kind ≠ gibbsEnergy.kind := helmholtzEnergy_ne_gibbsEnergy

-- the link from the kind back to its defining construction is checked, too.
example : internalEnergy.kind.examinedBy EnergyPrinciple.stateOfSVN :=
  internalEnergy_examinedBy

-- (c) COMPARABILITY PRESERVED: though distinct, the Helmholtz and Gibbs energies
--     remain mutually comparable — they share the super-kind energy.
example : MutuallyComparable Edge helmholtzEnergy.kind gibbsEnergy.kind :=
  helmholtzEnergy_gibbsEnergy_comparable

-- (d) and the dimension cannot tell them apart: same dimension `M·L²·T⁻²`, distinct kinds.
example : helmholtzEnergy.dim = gibbsEnergy.dim := rfl

/-! ## (4) Dimension collisions: same dimension, distinct kind

The {dimension functor} identifies these pairs; the kind layer keeps them apart —
including their units, even when the units carry the same symbol. -/

-- entropy and heat capacity: both `M·L²·T⁻²·Θ⁻¹`, distinct kinds, and even the SAME
-- unit string "J/K" — yet not commensurable, because their kinds differ.
example : entropy.dim = heatCapacity.dim := entropy_dim_eq_heatCapacity_dim
example : entropy.kind ≠ heatCapacity.kind := entropy_ne_heatCapacity
example : ¬ joulePerKelvinEntropy.Commensurable joulePerKelvinHeatCapacity :=
  entropy_heatCapacity_unit_not_commensurable

-- specific entropy and specific heat capacity: both `L²·T⁻²·Θ⁻¹`, distinct kinds.
example : specificEntropy.dim = specificHeatCapacity.dim :=
  specificEntropy_dim_eq_specificHeatCapacity_dim
example : specificEntropy.kind ≠ specificHeatCapacity.kind :=
  specificEntropy_ne_specificHeatCapacity

-- the entropy/heat-capacity collision and the dimension-1 collision, on standard quantities.
example : ∃ a b : DimensionedKind, a.kind ≠ b.kind ∧ a.dim = b.dim :=
  iso80000_5_dim_collision
example : ∃ a b : DimensionedKind, a.kind ≠ b.kind ∧ a.dim = b.dim ∧ a.dim = 1 :=
  iso80000_5_dim_one_collision

/-! ## (5) Cross-part defining relations: thermodynamics built from the earlier parts

Specific heat capacity is heat capacity / mass and the density of heat flow rate is
heat flow rate / area — each composing a Part-5 kind out of an earlier part's kinds;
the ratio of specific heat capacities is dimensionless because it is a ratio of two
specific heat capacities. -/

-- DIM FROM RELATION (cross-part): specific heat capacity's `L²·T⁻²·Θ⁻¹` follows from
-- heat capacity / mass (mass crossing to Part 4).
example : specificHeatCapacity.dim = heatCapacity.dim / Part4.mass.dim :=
  specificHeatCapacity_dim_from_heatCapacity_mass
-- and the density of heat flow rate's heat-flow-rate / area (crossing to Part 3).
example : densityOfHeatFlowRate.dim = heatFlowRate.dim / Part3.area.dim :=
  densityOfHeatFlowRate_dim_from_heatFlowRate_area

-- ALGEBRAIC REMARK (item 5-17.1): the ratio of specific heat capacities is dimension
-- one *because* it is a ratio of two specific heat capacities (`γ = cp/cV`) — the
-- dimensionlessness is computed from the relation, the thermodynamic analogue of a
-- plane angle being a ratio of two lengths.
example : ratioOfSpecificHeatCapacities.dim =
    specificHeatCapacityConstantPressure.dim / specificHeatCapacityConstantVolume.dim :=
  ratio_dim_from_specific_heats

-- VERIFIED CONSTRUCTION (item 5-16.1): a specific heat capacity built as heat capacity
-- / mass carries its classification certificate by construction, over `ℝ`.
example (c : Quantity heatCapacity.kind ℝ) (m : Quantity Part4.mass.kind ℝ) :
    (specificHeatCapacityOf c m).IsQuotient
      specificHeatCapacity_quot_heatCapacity_mass c m :=
  specificHeatCapacityOf_isQuotient c m

-- the quotient kind-law instantiates at a *different* carrier (`Int`), where the
-- construction also computes: `6 J/K / 2 kg = 3 J/(kg·K)` (cross-part, at `Int`).
def specificHeatCapacityInt : Quantity specificHeatCapacity.kind Int :=
  Quantity.div specificHeatCapacity_quot_heatCapacity_mass
    (⟨6⟩ : Quantity heatCapacity.kind Int) (⟨2⟩ : Quantity Part4.mass.kind Int)
#guard specificHeatCapacityInt.magnitude == 3

/-! ## (6) Catalogue coverage — all 54 items carry their source as data -/

-- every ISO 80000-5 item is catalogued, in item order …
#guard PropertyKindCalculus.Iso80000.Part5.catalogue.length == 54
-- … with the item designations (including every sub-suffixed item) …
#guard linearExpansionCoefficientCK.item == "5-3.1"
#guard isentropicCompressibilityCK.item == "5-5.2"
#guard specificHeatCapacitySaturatedCK.item == "5-16.4"
#guard gibbsEnergyCK.item == "5-20.5"
#guard maximumEfficiencyCK.item == "5-25.2"
#guard dewPointTemperatureCK.item == "5-36"
-- … each citing its full source …
#guard entropyCK.cite == "ISO 80000-5, Second edition, 2019-08 item 5-18"
-- … and recording its coherent SI unit symbol as a locator.
#guard entropyCK.coherentUnit == "J/K"
#guard heatCapacityCK.coherentUnit == "J/K"
#guard specificEntropyCK.coherentUnit == "J/(kg·K)"
#guard celsiusTemperatureCK.coherentUnit == "°C"

end PropertyKindCalculus.Examples.Iso80000.Part5

end Blanket
