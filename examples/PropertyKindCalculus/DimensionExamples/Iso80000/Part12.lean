/-
# Worked examples — ISO 80000-12 (Condensed matter physics)

Part-12 examples, mirroring the `Iso80000` library's own `Iso80000/Part12` layout:

1. the dimensional algebra (Fermi energy is `M·L²·T⁻²`, lattice plane spacing a length,
   Debye temperature `Θ`, angular wavenumber `L⁻¹`);
2. **collisions everywhere** — seven energies on `M·L²·T⁻²` (Fermi ≠ gap energy), thirteen
   lengths on `L` (lattice spacing ≠ Burgers vector), five temperatures on `Θ` (Curie ≠
   Néel);
3. **units not commensurable** — the joule of Fermi energy not the joule of gap energy,
   the kelvin of the Curie temperature not the kelvin of the Néel temperature;
4. **the dimension-one family** — the Bragg angle, order parameters, Grüneisen parameters;
5. **defining relations** — Seebeck coefficient = thermoelectric voltage / temperature,
   Peltier coefficient = Seebeck coefficient × temperature; cross-part to ISO 80000-5;
6. **catalogue coverage** — all 60 items carry their source as data.

These live in the Mathlib-backed `DimensionExamples` library.
-/

module

public import PropertyKindCalculus.Iso80000.Part12
meta import PropertyKindCalculus.Iso80000.Part12
public import PropertyKindCalculus.Iso80000.Part12.DefiningRelations
meta import PropertyKindCalculus.Iso80000.Part12.DefiningRelations
public import PropertyKindCalculus.QuantityReal
meta import PropertyKindCalculus.QuantityReal

public section -- pkc-blanket
@[expose] section -- pkc-blanket-expose

namespace PropertyKindCalculus.Examples.Iso80000.Part12

open PropertyKindCalculus
open PropertyKindCalculus.Iso80000
open PropertyKindCalculus.Iso80000.Part12
open PropertyKindCalculus.Iso80000.Part12.DefiningRelations

/-! ## (1) ISO 80000-12 — the dimensional algebra -/

example : fermiEnergy.dim.time = -2 := fermiEnergy_dim_time
example : latticePlaneSpacing.dim = Dim.length := latticePlaneSpacing_dim_eq_length
example : debyeTemperature.dim.temperature = 1 := debyeTemperature_dim_temperature
example : angularWavenumber.dim.length = -1 := angularWavenumber_dim_length

-- each kind carries its exact item citation as data
#guard fermiEnergyCK.item == "12-27.1"
#guard curieTemperatureCK.item == "12-35.1"
#guard curieTemperatureCK.cite == "ISO 80000-12, Second edition, 2019-08 item 12-35.1"
#guard londonPenetrationDepthCK.item == "12-38.1"

/-! ## (2) Collisions everywhere (on the real standard)

Condensed matter physics collides on nearly every common dimension: seven energies, five
temperatures, thirteen lengths, five carrier densities, five reciprocal lengths. -/

-- SEVEN ENERGIES: Fermi energy ≡ gap energy in dimension, distinct in kind.
example : fermiEnergy.dim = gapEnergy.dim := fermiEnergy_dim_eq_gapEnergy_dim
example : fermiEnergy.kind ≠ gapEnergy.kind := fermiEnergy_ne_gapEnergy
-- THIRTEEN LENGTHS: lattice plane spacing ≡ Burgers vector in dimension.
example : latticePlaneSpacing.dim = burgersVector.dim :=
  latticePlaneSpacing_dim_eq_burgersVector_dim
-- FIVE TEMPERATURES: Curie ≡ Néel in dimension.
example : curieTemperature.dim = neelTemperature.dim :=
  curieTemperature_dim_eq_neelTemperature_dim
-- the collision capstone on standard quantities (the seven-energy family).
example : ∃ a b : DimensionedKind, a.kind ≠ b.kind ∧ a.dim = b.dim := iso80000_12_dim_collision

/-! ## (3) Units not commensurable — same unit, distinct kind -/

example : ¬ jouleFermi.Commensurable jouleGap := jouleFermi_jouleGap_not_commensurable
example : ¬ kelvinCurie.Commensurable kelvinNeel := kelvinCurie_kelvinNeel_not_commensurable

/-! ## (4) The dimension-one family -/

example : braggAngle.kind ≠ structureFactor.kind := braggAngle_ne_structureFactor
example : ∃ a b : DimensionedKind, a.kind ≠ b.kind ∧ a.dim = b.dim ∧ a.dim = 1 :=
  iso80000_12_dim_one_collision

/-! ## (5) Defining relations: thermoelectricity built by the kind algebra

The Seebeck coefficient is thermoelectric voltage per temperature; the Peltier coefficient
the Seebeck coefficient times temperature (the Kelvin relation); both cross to ISO 80000-5. -/

-- DIM FROM RELATION: the Seebeck coefficient is `V/K` *because* it is a voltage per
-- temperature (cross-part, the temperature from ISO 80000-5).
example : seebeckCoefficient.dim =
    thermoelectricVoltage.dim / Part5.thermodynamicTemperature.dim :=
  seebeck_dim_from_voltage_temperature

-- VERIFIED CONSTRUCTION (item 12-22): a Peltier coefficient built as Seebeck × temperature
-- carries its product certificate by construction, over `ℝ`.
example (s : Quantity seebeckCoefficient.kind ℝ)
    (t : Quantity Part5.thermodynamicTemperature.kind ℝ) :
    (peltierOf s t).IsProduct peltier_prod_seebeck_temperature s t :=
  peltierOf_isProduct s t

-- the Seebeck quotient instantiates at a *different* carrier (`Int`), where the
-- construction also computes: `12 V / 3 K = 4 V/K` (at `Int`).
def seebeckInt : Quantity seebeckCoefficient.kind Int :=
  Quantity.div seebeck_quot_voltage_temperature
    (⟨12⟩ : Quantity thermoelectricVoltage.kind Int)
    (⟨3⟩ : Quantity Part5.thermodynamicTemperature.kind Int)
#guard seebeckInt.magnitude == 4

/-! ## (6) Catalogue coverage — all 60 items carry their source as data -/

#guard PropertyKindCalculus.Iso80000.Part12.catalogue.length == 60
#guard latticeVectorCK.item == "12-1.1"
#guard energyDensityOfStatesCK.item == "12-16"
#guard acceptorDensityCK.item == "12-29.5"
#guard coherenceLengthCK.item == "12-38.2"
#guard fermiEnergyCK.coherentUnit == "J"
#guard curieTemperatureCK.coherentUnit == "K"

end PropertyKindCalculus.Examples.Iso80000.Part12

end -- pkc-blanket-expose
end -- pkc-blanket
