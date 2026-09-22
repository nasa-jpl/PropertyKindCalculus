/-
# ISO 80000-5 — defining relations from the Remarks (the algebraic remarks)

Many ISO 80000-5 *Remarks* state a quantity's **defining relation** to other
quantities as a quotient or reciprocal — and, characteristically of thermodynamics,
the other quantities are often from *earlier parts* (mass from ISO 80000-4, area from
ISO 80000-3) or from temperature, the base quantity Part 5 introduces:

  * heat capacity `C = dQ/dT` — added heat per thermodynamic temperature (item 5-15);
  * specific heat capacity `c = C/m` — heat capacity per mass (item 5-16.1; mass is
    ISO 80000-4);
  * specific entropy `s = S/m` — entropy per mass (item 5-19; mass is ISO 80000-4);
  * density of heat flow rate `q = Φ/A` — heat flow rate per area (item 5-8; area is
    ISO 80000-3);
  * thermal conductance `G = 1/R` — the reciprocal of thermal resistance (item 5-13);
  * thermal insulance `M = 1/K` — the reciprocal of the coefficient of heat transfer
    (item 5-11);
  * ratio of specific heat capacities `γ = cp/cV` — so the specific heat capacities
    cancel and the ratio is dimension one (item 5-17.1).

This module formalizes each as an R12 *kind-law* over the catalogued kinds, using the
quotient and reciprocal families of `QuantityClassification`. Three payoffs:

  1. **Thermodynamics is built from the earlier parts.** The kind-laws compose Part-5
     kinds out of Part-4 (mass) and Part-3 (area) kinds — specific heat capacity from
     heat capacity and mass, the density of heat flow rate from heat flow rate and
     area — so the cross-part dependency structure of the ISQ is made explicit and
     checked, not left to prose.
  2. **The dimension follows from the relation, as a checked computation.** The ratio
     of specific heat capacities is dimension one *because* it is a ratio of two
     specific heat capacities (`ratio_dim_from_specific_heats`), exactly as a plane
     angle is dimensionless because it is a ratio of two lengths — yet it remains a
     distinct kind from every other dimension-one quantity.
  3. **Verified construction and certificates instantiate at the quantity level.** A
     specific heat capacity built as heat capacity / mass carries its classification
     certificate by construction (`specificHeatCapacityOf_isQuotient`), and the
     certificate determines the quantity (canonicity), over the `ℝ` carrier.

No normative text from the licensed standard is reproduced; the relations are
restated in this work's own formalism.
-/

module

public import PropertyKindCalculus.Iso80000.Part3
public import PropertyKindCalculus.Iso80000.Part4
public import PropertyKindCalculus.Iso80000.Part5
public import PropertyKindCalculus.QuantityClassification
public import PropertyKindCalculus.QuantityReal

public section -- pkc-blanket
@[expose] section -- pkc-blanket-expose

namespace PropertyKindCalculus.Iso80000.Part5.DefiningRelations

open PropertyKindCalculus
open PropertyKindCalculus.Iso80000.Part5

/-! ## (1) The kind-laws (scale preconditions verified)

Each kind-law is a `QuotientKind` / `ReciprocalKind` instance: a proof that the kinds
involved are all ratio-scale, the precondition for dividing or inverting quantities
(Dybkær §13.3.5). For these catalogued kinds the scale facts hold by reflexivity —
including the **cross-part** ones, whose Part-4 factor (`Part4.mass`) and Part-3 factor
(`Part3.area`) are equally ratio-scale, and including the **temperature** factor
(`thermodynamicTemperature`, the ratio-scale base quantity). -/

/-- **Heat capacity is added heat per thermodynamic temperature** (item 5-15:
`C = dQ/dT`) — a quotient over the temperature base quantity. -/
theorem heatCapacity_quot_heat_temperature :
    QuotientKind heat.kind thermodynamicTemperature.kind heatCapacity.kind :=
  ⟨rfl, rfl, rfl⟩

/-- **Specific heat capacity is heat capacity per mass** (item 5-16.1: `c = C/m`) — a
*cross-part* law, since the mass is an ISO 80000-4 quantity. -/
theorem specificHeatCapacity_quot_heatCapacity_mass :
    QuotientKind heatCapacity.kind Part4.mass.kind specificHeatCapacity.kind :=
  ⟨rfl, rfl, rfl⟩

/-- **Specific entropy is entropy per mass** (item 5-19: `s = S/m`) — a *cross-part*
law, since the mass is an ISO 80000-4 quantity. -/
theorem specificEntropy_quot_entropy_mass :
    QuotientKind entropy.kind Part4.mass.kind specificEntropy.kind :=
  ⟨rfl, rfl, rfl⟩

/-- **The density of heat flow rate is heat flow rate per area** (item 5-8: `q = Φ/A`)
— a *cross-part* law, since the area is an ISO 80000-3 quantity. -/
theorem densityOfHeatFlowRate_quot_heatFlowRate_area :
    QuotientKind heatFlowRate.kind Part3.area.kind densityOfHeatFlowRate.kind :=
  ⟨rfl, rfl, rfl⟩

/-- **Thermal conductance is the reciprocal of thermal resistance** (item 5-13:
`G = 1/R`). -/
theorem thermalConductance_recip_thermalResistance :
    ReciprocalKind thermalResistance.kind thermalConductance.kind := ⟨rfl, rfl⟩

/-- **Thermal insulance is the reciprocal of the coefficient of heat transfer** (item
5-11: `M = 1/K`). -/
theorem thermalInsulance_recip_coefficientOfHeatTransfer :
    ReciprocalKind coefficientOfHeatTransfer.kind thermalInsulance.kind := ⟨rfl, rfl⟩

/-- **The ratio of specific heat capacities is `cp/cV`** (item 5-17.1). -/
theorem ratioOfSpecificHeatCapacities_quot_cp_cV :
    QuotientKind specificHeatCapacityConstantPressure.kind
      specificHeatCapacityConstantVolume.kind ratioOfSpecificHeatCapacities.kind :=
  ⟨rfl, rfl, rfl⟩

/-! ## (2) The dimension follows from the relation (checked computations) -/

/-- Heat capacity's dimension is energy over temperature: `M·L²·T⁻²·Θ⁻¹` because
`C = dQ/dT`. A checked computation over the temperature base quantity. -/
theorem heatCapacity_dim_from_heat_temperature :
    heatCapacity.dim = heat.dim / thermodynamicTemperature.dim := rfl

/-- Specific heat capacity's dimension is heat capacity over mass: `L²·T⁻²·Θ⁻¹` because
`c = C/m`. A checked cross-part computation (the mass is `M` from ISO 80000-4). -/
theorem specificHeatCapacity_dim_from_heatCapacity_mass :
    specificHeatCapacity.dim = heatCapacity.dim / Part4.mass.dim := rfl

/-- The density of heat flow rate's dimension is heat flow rate over area: `M·T⁻³`
because `q = Φ/A`. A checked cross-part computation (the area is `L²` from
ISO 80000-3). -/
theorem densityOfHeatFlowRate_dim_from_heatFlowRate_area :
    densityOfHeatFlowRate.dim = heatFlowRate.dim / Part3.area.dim := rfl

/-- **The ratio of specific heat capacities is dimension one because it is a ratio of
two specific heat capacities.** The constant-pressure and constant-volume specific
heat capacities are both `L²·T⁻²·Θ⁻¹`, so `γ = cp/cV` cancels the dimension — the
ratio's dimensionlessness is a *checked computation from its defining relation*, not a
stipulation. (It nonetheless remains a distinct kind from every other dimension-one
quantity; see `Part5.iso80000_5_dim_one_collision`.) This is the thermodynamic
analogue of the plane angle being a ratio of two lengths and the efficiency being a
ratio of two powers. -/
theorem ratio_dim_from_specific_heats :
    ratioOfSpecificHeatCapacities.dim =
      specificHeatCapacityConstantPressure.dim / specificHeatCapacityConstantVolume.dim := by
  simp [ratioOfSpecificHeatCapacities, specificHeatCapacityConstantPressure,
    specificHeatCapacityConstantVolume, dimKind, Dim.one]

/-! ## (3) Verified construction and certificates at the quantity level (`ℝ`)

The smart constructors build a classified quantity from its constituents, licensed by
the kind-law; the certificate holds by construction, and (canonicity) any quantity
carrying the certificate equals the constructed one. The specific-heat-capacity
constructor crosses parts: it consumes a heat capacity (Part 5) and a mass (Part 4). -/

/-- A specific heat capacity built as heat capacity / mass — classified as a specific
heat capacity **by construction** (and built from a Part-5 heat capacity and a Part-4
mass). -/
noncomputable def specificHeatCapacityOf (c : Quantity heatCapacity.kind ℝ)
    (m : Quantity Part4.mass.kind ℝ) : Quantity specificHeatCapacity.kind ℝ :=
  Quantity.div specificHeatCapacity_quot_heatCapacity_mass c m

/-- The constructed specific heat capacity satisfies the quotient certificate by
construction. -/
theorem specificHeatCapacityOf_isQuotient (c : Quantity heatCapacity.kind ℝ)
    (m : Quantity Part4.mass.kind ℝ) :
    (specificHeatCapacityOf c m).IsQuotient
      specificHeatCapacity_quot_heatCapacity_mass c m := rfl

/-- **Canonicity, instantiated.** Any specific heat capacity certified as a given heat
capacity per a given mass equals the constructed one — a kind-law applied at the
quantity level. -/
theorem specificHeatCapacity_certificate_canonical
    {c : Quantity heatCapacity.kind ℝ} {m : Quantity Part4.mass.kind ℝ}
    {sc : Quantity specificHeatCapacity.kind ℝ}
    (h : sc.IsQuotient specificHeatCapacity_quot_heatCapacity_mass c m) :
    sc = specificHeatCapacityOf c m :=
  Quantity.eq_div_of_isQuotient specificHeatCapacity_quot_heatCapacity_mass h

/-- A density of heat flow rate built as heat flow rate / area — classified **by
construction** (and built from a Part-5 heat flow rate and a Part-3 area). -/
noncomputable def densityOfHeatFlowRateOf (φ : Quantity heatFlowRate.kind ℝ)
    (a : Quantity Part3.area.kind ℝ) : Quantity densityOfHeatFlowRate.kind ℝ :=
  Quantity.div densityOfHeatFlowRate_quot_heatFlowRate_area φ a

/-- The constructed density of heat flow rate satisfies the quotient certificate by
construction. -/
theorem densityOfHeatFlowRateOf_isQuotient (φ : Quantity heatFlowRate.kind ℝ)
    (a : Quantity Part3.area.kind ℝ) :
    (densityOfHeatFlowRateOf φ a).IsQuotient
      densityOfHeatFlowRate_quot_heatFlowRate_area φ a := rfl

/-- A thermal conductance built as the reciprocal of a thermal resistance — classified
**by construction** (`G = 1/R`). -/
noncomputable def thermalConductanceOf (r : Quantity thermalResistance.kind ℝ) :
    Quantity thermalConductance.kind ℝ :=
  Quantity.recip thermalConductance_recip_thermalResistance r

/-- The constructed thermal conductance satisfies the reciprocal certificate by
construction. -/
theorem thermalConductanceOf_isReciprocal (r : Quantity thermalResistance.kind ℝ) :
    (thermalConductanceOf r).IsReciprocal
      thermalConductance_recip_thermalResistance r := rfl

end PropertyKindCalculus.Iso80000.Part5.DefiningRelations

end -- pkc-blanket-expose
end -- pkc-blanket
