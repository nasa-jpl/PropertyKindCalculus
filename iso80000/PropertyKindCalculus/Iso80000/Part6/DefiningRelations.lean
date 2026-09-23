/-
# IEC 80000-6 — defining relations from the Remarks (the algebraic remarks)

Many IEC 80000-6 *Remarks* and definitions state a quantity's **defining relation** to
other quantities as a quotient, reciprocal, or product — the constitutive laws of
circuit theory and electromagnetism:

  * electric current `I = dQ/dt` — charge per time (item 6-1; the time is ISO 80000-3);
  * resistance `R = U/I` — voltage per electric current (Ohm's law, item 6-46);
  * conductance `G = 1/R` — the reciprocal of resistance (item 6-47);
  * capacitance `C = Q/U` — charge per voltage (item 6-13);
  * power `P = U·I` — voltage times electric current (item 6-45);
  * resistivity `ρ = 1/σ` — the reciprocal of conductivity (item 6-44);
  * admittance `Y = 1/Z` — the reciprocal of impedance (item 6-52.1);
  * permeance `Λ = 1/Rₘ` — the reciprocal of reluctance (item 6-40);
  * power factor `λ = P/S` — active power over apparent power (item 6-58), so the powers
    cancel and the factor is dimension one.

This module formalizes each as an R12 *kind-law* over the catalogued kinds, using the
product, quotient, and reciprocal families of `QuantityClassification`. Three payoffs:

  1. **Electromagnetism is built from one another by the kind algebra.** Ohm's law, the
     reciprocal pairs, and the power product compose Part-6 kinds out of one another —
     and electric current crosses to ISO 80000-3 for its time factor — so the
     constitutive structure of circuit theory is made explicit and checked, not left to
     prose.
  2. **The dimension follows from the relation, as a checked computation.** The power
     factor is dimension one *because* it is a ratio of two powers
     (`powerFactor_dim_from_powers`), exactly as a plane angle is dimensionless because
     it is a ratio of two lengths — yet it remains a distinct kind from every other
     dimension-one quantity.
  3. **Verified construction and certificates instantiate at the quantity level.** A
     resistance built as voltage / current carries its quotient certificate by
     construction (`resistanceOf_isQuotient`), and the certificate determines the
     quantity (canonicity), over the `ℝ` carrier.

No normative text from the licensed standard is reproduced; the relations are restated
in this work's own formalism.
-/

module

public import PropertyKindCalculus.Iso80000.Part3
public import PropertyKindCalculus.Iso80000.Part6
public import PropertyKindCalculus.QuantityClassification
public import PropertyKindCalculus.QuantityReal

@[expose] public section Blanket

namespace PropertyKindCalculus.Iso80000.Part6.DefiningRelations

open PropertyKindCalculus
open PropertyKindCalculus.Iso80000.Part6

/-! ## (1) The kind-laws (scale preconditions verified)

Each kind-law is a `ProductKind` / `QuotientKind` / `ReciprocalKind` instance: a proof
that the kinds involved are all ratio-scale, the precondition for multiplying, dividing,
or inverting quantities (Dybkær §13.3.5). For these catalogued kinds the scale facts
hold by reflexivity — including the **cross-part** electric-current law, whose ISO
80000-3 time factor (`Part3.duration`) is equally ratio-scale. -/

/-- **Electric current is charge per time** (item 6-1: `I = dQ/dt`) — a *cross-part*
law, since the time is an ISO 80000-3 quantity. -/
theorem electricCurrent_quot_charge_duration :
    QuotientKind electricCharge.kind Part3.duration.kind electricCurrent.kind :=
  ⟨rfl, rfl, rfl⟩

/-- **Resistance is voltage per electric current** (Ohm's law, item 6-46: `R = U/I`). -/
theorem resistance_quot_voltage_current :
    QuotientKind voltage.kind electricCurrent.kind resistance.kind := ⟨rfl, rfl, rfl⟩

/-- **Conductance is the reciprocal of resistance** (item 6-47: `G = 1/R`). -/
theorem conductance_recip_resistance :
    ReciprocalKind resistance.kind conductance.kind := ⟨rfl, rfl⟩

/-- **Capacitance is charge per voltage** (item 6-13: `C = Q/U`). -/
theorem capacitance_quot_charge_voltage :
    QuotientKind electricCharge.kind voltage.kind capacitance.kind := ⟨rfl, rfl, rfl⟩

/-- **Power is voltage times electric current** (item 6-45: `P = U·I`). -/
theorem power_prod_voltage_current :
    ProductKind voltage.kind electricCurrent.kind power.kind := ⟨rfl, rfl, rfl⟩

/-- **Resistivity is the reciprocal of conductivity** (item 6-44: `ρ = 1/σ`). -/
theorem resistivity_recip_conductivity :
    ReciprocalKind conductivity.kind resistivity.kind := ⟨rfl, rfl⟩

/-- **Admittance is the reciprocal of impedance** (item 6-52.1: `Y = 1/Z`). -/
theorem admittance_recip_impedance :
    ReciprocalKind impedance.kind admittance.kind := ⟨rfl, rfl⟩

/-- **Permeance is the reciprocal of reluctance** (item 6-40: `Λ = 1/Rₘ`). -/
theorem permeance_recip_reluctance :
    ReciprocalKind reluctance.kind permeance.kind := ⟨rfl, rfl⟩

/-- **The power factor is active power over apparent power** (item 6-58: `λ = P/S`). -/
theorem powerFactor_quot_active_apparent :
    QuotientKind activePower.kind apparentPower.kind powerFactor.kind := ⟨rfl, rfl, rfl⟩

/-! ## (2) The dimension follows from the relation (checked computations) -/

/-- Electric current's dimension is charge over time: `C·T⁻¹` because `I = dQ/dt`. A
checked cross-part computation (the time is `T` from ISO 80000-3). -/
theorem electricCurrent_dim_from_charge_duration :
    electricCurrent.dim = electricCharge.dim / Part3.duration.dim := rfl

/-- Resistance's dimension is voltage over current: `M·L²·T⁻¹·C⁻²` because `R = U/I`. A
checked computation realizing Ohm's law at the dimensional level. -/
theorem resistance_dim_from_voltage_current :
    resistance.dim = voltage.dim / electricCurrent.dim := rfl

/-- Power's dimension is voltage times current: `M·L²·T⁻³` because `P = U·I`. The charge
generator cancels (voltage carries `C⁻¹`, current carries `C`), a checked computation in
the dimension group. -/
theorem power_dim_from_voltage_current :
    power.dim = voltage.dim * electricCurrent.dim := by
  show EDim.power = EDim.voltage * Dim.current
  rw [EDim.power, EDim.voltage, Dim.current_eq]
  ext b
  simp only [Dimension.div_exponent, Dimension.mul_exponent]
  ring

/-- **The power factor is dimension one because it is a ratio of two powers.** Active and
apparent power are both `M·L²·T⁻³`, so `λ = P/S` cancels the dimension — the power
factor's dimensionlessness is a *checked computation from its defining relation*, not a
stipulation. (It nonetheless remains a distinct kind from every other dimension-one
quantity; see `Part6.iec80000_6_dim_one_collision`.) This is the electromagnetic
analogue of the plane angle being a ratio of two lengths and the thermodynamic
efficiency being a ratio of two powers. -/
theorem powerFactor_dim_from_powers :
    powerFactor.dim = activePower.dim / apparentPower.dim := by
  simp [powerFactor, activePower, apparentPower, powerSpecies, dimKind, Dim.one]

/-! ## (3) Verified construction and certificates at the quantity level (`ℝ`)

The smart constructors build a classified quantity from its constituents, licensed by
the kind-law; the certificate holds by construction, and (canonicity) any quantity
carrying the certificate equals the constructed one. -/

/-- A resistance built as voltage / current — classified as a resistance **by
construction** (Ohm's law `R = U/I`). -/
noncomputable def resistanceOf (u : Quantity voltage.kind ℝ)
    (i : Quantity electricCurrent.kind ℝ) : Quantity resistance.kind ℝ :=
  Quantity.div resistance_quot_voltage_current u i

/-- The constructed resistance satisfies the quotient certificate by construction. -/
theorem resistanceOf_isQuotient (u : Quantity voltage.kind ℝ)
    (i : Quantity electricCurrent.kind ℝ) :
    (resistanceOf u i).IsQuotient resistance_quot_voltage_current u i := rfl

/-- **Canonicity, instantiated.** Any resistance certified as a given voltage per a given
current equals the constructed one — Ohm's law applied at the quantity level. -/
theorem resistance_certificate_canonical
    {u : Quantity voltage.kind ℝ} {i : Quantity electricCurrent.kind ℝ}
    {r : Quantity resistance.kind ℝ}
    (h : r.IsQuotient resistance_quot_voltage_current u i) :
    r = resistanceOf u i :=
  Quantity.eq_div_of_isQuotient resistance_quot_voltage_current h

/-- A power built as voltage × current — classified as a power **by construction**
(`P = U·I`). -/
noncomputable def powerOf (u : Quantity voltage.kind ℝ)
    (i : Quantity electricCurrent.kind ℝ) : Quantity power.kind ℝ :=
  Quantity.mul power_prod_voltage_current u i

/-- The constructed power satisfies the product certificate by construction. -/
theorem powerOf_isProduct (u : Quantity voltage.kind ℝ)
    (i : Quantity electricCurrent.kind ℝ) :
    (powerOf u i).IsProduct power_prod_voltage_current u i := rfl

/-- A conductance built as the reciprocal of a resistance — classified **by
construction** (`G = 1/R`). -/
noncomputable def conductanceOf (r : Quantity resistance.kind ℝ) :
    Quantity conductance.kind ℝ :=
  Quantity.recip conductance_recip_resistance r

/-- The constructed conductance satisfies the reciprocal certificate by construction. -/
theorem conductanceOf_isReciprocal (r : Quantity resistance.kind ℝ) :
    (conductanceOf r).IsReciprocal conductance_recip_resistance r := rfl

end PropertyKindCalculus.Iso80000.Part6.DefiningRelations

end Blanket
