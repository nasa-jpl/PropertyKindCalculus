/-
# ISO 80000-12 — defining relations from the Remarks (the algebraic remarks)

Two ISO 80000-12 *Remarks* state the thermoelectric coefficients as a quotient and a
product of one another and the thermodynamic temperature — the constitutive laws of
thermoelectricity:

  * Seebeck coefficient `S = dE/dT` — thermoelectric voltage per temperature (item 12-21;
    the temperature is ISO 80000-5);
  * Peltier coefficient `Π = S·T` — Seebeck coefficient times temperature (item 12-22, the
    Kelvin relation).

This module formalizes each as an R12 *kind-law* over the catalogued kinds, using the
quotient and product families of `QuantityClassification`. Two payoffs:

  1. **Thermoelectricity is built from the kind algebra, crossing to ISO 80000-5.** The
     Seebeck and Peltier coefficients compose Part-12 kinds out of the thermoelectric
     voltage and the ISO 80000-5 thermodynamic temperature.
  2. **The dimension follows from the relation, as a checked computation.** The Seebeck
     coefficient is `V/K` *because* it is a voltage per temperature
     (`seebeck_dim_from_voltage_temperature`).

No normative text from the licensed standard is reproduced; the relations are restated in
this work's own formalism.
-/

module

public import PropertyKindCalculus.Iso80000.Part5
public import PropertyKindCalculus.Iso80000.Part12
public import PropertyKindCalculus.QuantityClassification
public import PropertyKindCalculus.QuantityReal

public section -- pkc-blanket
@[expose] section -- pkc-blanket-expose

namespace PropertyKindCalculus.Iso80000.Part12.DefiningRelations

open PropertyKindCalculus
open PropertyKindCalculus.Iso80000.Part12

/-! ## (1) The kind-laws (scale preconditions verified)

Each kind-law is a `QuotientKind` / `ProductKind` instance over ratio-scale kinds — the
precondition for dividing or multiplying quantities (Dybkær §13.3.5). The **cross-part**
ISO 80000-5 thermodynamic temperature is equally ratio-scale. -/

/-- **The Seebeck coefficient is thermoelectric voltage per temperature** (item 12-21:
`S = dE/dT`) — a *cross-part* law, the temperature an ISO 80000-5 quantity. -/
theorem seebeck_quot_voltage_temperature :
    QuotientKind thermoelectricVoltage.kind Part5.thermodynamicTemperature.kind
      seebeckCoefficient.kind := ⟨rfl, rfl, rfl⟩

/-- **The Peltier coefficient is the Seebeck coefficient times temperature** (item 12-22:
`Π = S·T`, the Kelvin relation) — a *cross-part* law. -/
theorem peltier_prod_seebeck_temperature :
    ProductKind seebeckCoefficient.kind Part5.thermodynamicTemperature.kind
      peltierCoefficient.kind := ⟨rfl, rfl, rfl⟩

/-! ## (2) The dimension follows from the relation (checked computations) -/

/-- The Seebeck coefficient's dimension is voltage over temperature: `V/K` because
`S = dE/dT`. A checked cross-part computation (the temperature is `Θ` from ISO 80000-5). -/
theorem seebeck_dim_from_voltage_temperature :
    seebeckCoefficient.dim = thermoelectricVoltage.dim / Part5.thermodynamicTemperature.dim :=
  rfl

/-! ## (3) Verified construction and certificates at the quantity level (`ℝ`)

The smart constructors build a classified quantity from its constituents, licensed by the
kind-law; the certificate holds by construction. -/

/-- A Seebeck coefficient built as thermoelectric voltage / temperature — classified **by
construction** (`S = dE/dT`). -/
noncomputable def seebeckOf (u : Quantity thermoelectricVoltage.kind ℝ)
    (t : Quantity Part5.thermodynamicTemperature.kind ℝ) :
    Quantity seebeckCoefficient.kind ℝ :=
  Quantity.div seebeck_quot_voltage_temperature u t

/-- The constructed Seebeck coefficient satisfies the quotient certificate by
construction. -/
theorem seebeckOf_isQuotient (u : Quantity thermoelectricVoltage.kind ℝ)
    (t : Quantity Part5.thermodynamicTemperature.kind ℝ) :
    (seebeckOf u t).IsQuotient seebeck_quot_voltage_temperature u t := rfl

/-- **Canonicity, instantiated.** Any Seebeck coefficient certified as a given
thermoelectric voltage per a given temperature equals the constructed one. -/
theorem seebeck_certificate_canonical
    {u : Quantity thermoelectricVoltage.kind ℝ}
    {t : Quantity Part5.thermodynamicTemperature.kind ℝ}
    {s : Quantity seebeckCoefficient.kind ℝ}
    (h : s.IsQuotient seebeck_quot_voltage_temperature u t) :
    s = seebeckOf u t :=
  Quantity.eq_div_of_isQuotient seebeck_quot_voltage_temperature h

/-- A Peltier coefficient built as Seebeck coefficient × temperature — classified **by
construction** (`Π = S·T`), over `ℝ`. -/
noncomputable def peltierOf (s : Quantity seebeckCoefficient.kind ℝ)
    (t : Quantity Part5.thermodynamicTemperature.kind ℝ) :
    Quantity peltierCoefficient.kind ℝ :=
  Quantity.mul peltier_prod_seebeck_temperature s t

/-- The constructed Peltier coefficient satisfies the product certificate by
construction. -/
theorem peltierOf_isProduct (s : Quantity seebeckCoefficient.kind ℝ)
    (t : Quantity Part5.thermodynamicTemperature.kind ℝ) :
    (peltierOf s t).IsProduct peltier_prod_seebeck_temperature s t := rfl

end PropertyKindCalculus.Iso80000.Part12.DefiningRelations

end -- pkc-blanket-expose
end -- pkc-blanket
