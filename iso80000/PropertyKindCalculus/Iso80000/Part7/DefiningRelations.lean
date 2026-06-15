/-
# ISO 80000-7 — defining relations from the Remarks (the algebraic remarks)

Many ISO 80000-7 *Remarks* and definitions state a quantity's **defining relation** to
other quantities as a quotient — the constitutive laws of radiometry and photometry:

  * radiant flux `Φ_e = dQ_e/dt` — radiant energy per time (item 7-4.1; the time is
    ISO 80000-3);
  * photon flux `Φ_p = dN_p/dt` — photon number per time (item 7-20);
  * irradiance `E_e = dΦ_e/dA` — radiant flux per area (item 7-7.1; the area is
    ISO 80000-3);
  * radiant intensity `I_e = dΦ_e/dΩ` — radiant flux per solid angle (item 7-5.1; the
    solid angle is ISO 80000-3 and dimension one, so intensity shares the dimension of
    flux);
  * luminous efficacy of radiation `K = Φ_v/Φ_e` — luminous flux per radiant flux
    (item 7-11.1), so the two fluxes cancel and the efficacy is **dimension one**.

This module formalizes each as an R12 *kind-law* over the catalogued kinds, using the
quotient family of `QuantityClassification`. Three payoffs:

  1. **Radiometry and photometry are built from one another by the kind algebra.** The
     fluxes are time-derivatives of energy and count, irradiance and intensity are
     area- and solid-angle-densities of flux — and several cross to ISO 80000-3 for
     their time, area, and solid angle.
  2. **The dimension follows from the relation, as a checked computation.** The luminous
     efficacy is dimension one *because* it is a ratio of two fluxes of equal dimension
     (`luminousEfficacy_dim_from_fluxes`) — the candela reducing to power (R13) — exactly
     as the power factor is dimensionless in IEC 80000-6 and a plane angle in
     ISO 80000-3. And radiant intensity keeps the dimension of radiant flux *because*
     the solid angle it divides by is dimension one (`radiantIntensity_dim_from_flux_solidAngle`).
  3. **Verified construction and certificates instantiate at the quantity level.** An
     irradiance built as radiant flux / area carries its quotient certificate by
     construction, and the certificate determines the quantity, over the `ℝ` carrier.

No normative text from the licensed standard is reproduced; the relations are restated
in this work's own formalism.
-/

import PropertyKindCalculus.Iso80000.Part3
import PropertyKindCalculus.Iso80000.Part7
import PropertyKindCalculus.QuantityClassification

namespace PropertyKindCalculus.Iso80000.Part7.DefiningRelations

open PropertyKindCalculus
open PropertyKindCalculus.Iso80000.Part7

/-! ## (1) The kind-laws (scale preconditions verified)

Each kind-law is a `QuotientKind` instance: a proof that the kinds involved are all
ratio-scale, the precondition for dividing quantities (Dybkær §13.3.5). For these
catalogued kinds the scale facts hold by reflexivity — including the **cross-part**
laws, whose ISO 80000-3 time, area, and solid-angle factors are equally ratio-scale. -/

/-- **Radiant flux is radiant energy per time** (item 7-4.1: `Φ_e = dQ_e/dt`) — a
*cross-part* law, the time an ISO 80000-3 quantity. -/
theorem radiantFlux_quot_energy_duration :
    QuotientKind radiantEnergy.kind Part3.duration.kind radiantFlux.kind :=
  ⟨rfl, rfl, rfl⟩

/-- **Photon flux is photon number per time** (item 7-20: `Φ_p = dN_p/dt`). -/
theorem photonFlux_quot_number_duration :
    QuotientKind photonNumber.kind Part3.duration.kind photonFlux.kind :=
  ⟨rfl, rfl, rfl⟩

/-- **Irradiance is radiant flux per area** (item 7-7.1: `E_e = dΦ_e/dA`) — a
*cross-part* law, the area an ISO 80000-3 quantity. -/
theorem irradiance_quot_flux_area :
    QuotientKind radiantFlux.kind Part3.area.kind irradiance.kind :=
  ⟨rfl, rfl, rfl⟩

/-- **Radiant intensity is radiant flux per solid angle** (item 7-5.1: `I_e = dΦ_e/dΩ`)
— a *cross-part* law, the solid angle an ISO 80000-3 quantity (dimension one). -/
theorem radiantIntensity_quot_flux_solidAngle :
    QuotientKind radiantFlux.kind Part3.solidAngle.kind radiantIntensity.kind :=
  ⟨rfl, rfl, rfl⟩

/-- **Luminous efficacy of radiation is luminous flux per radiant flux** (item 7-11.1:
`K = Φ_v/Φ_e`). -/
theorem luminousEfficacy_quot_fluxes :
    QuotientKind luminousFlux.kind radiantFlux.kind luminousEfficacy.kind :=
  ⟨rfl, rfl, rfl⟩

/-! ## (2) The dimension follows from the relation (checked computations) -/

/-- Radiant flux's dimension is radiant energy over time: `M·L²·T⁻³` because
`Φ_e = dQ_e/dt`. A checked cross-part computation (the time is `T` from ISO 80000-3). -/
theorem radiantFlux_dim_from_energy_duration :
    radiantFlux.dim = radiantEnergy.dim / Part3.duration.dim := rfl

/-- Irradiance's dimension is radiant flux over area: `M·T⁻³` because `E_e = dΦ_e/dA`. -/
theorem irradiance_dim_from_flux_area :
    irradiance.dim = radiantFlux.dim / Part3.area.dim := rfl

/-- **Radiant intensity keeps the dimension of radiant flux because the solid angle is
dimension one.** From `I_e = dΦ_e/dΩ` with `dim Ω = 1`, the division by the solid angle
leaves `M·L²·T⁻³` unchanged — the steradian reducing away, made a checked computation. -/
theorem radiantIntensity_dim_from_flux_solidAngle :
    radiantIntensity.dim = radiantFlux.dim / Part3.solidAngle.dim := by
  show Dim.power = Dim.power / (1 : Dimension)
  rw [div_one]

/-- **The luminous efficacy is dimension one because it is a ratio of two fluxes of equal
dimension.** Luminous and radiant flux are both `M·L²·T⁻³` (the candela reducing to
power, R13), so `K = Φ_v/Φ_e` cancels the dimension — the efficacy's dimensionlessness is
a *checked computation from its defining relation*, the photometric analogue of the power
factor (IEC 80000-6) and the plane angle (ISO 80000-3). It nonetheless remains a distinct
kind from every other dimension-one quantity (see `Part7.iso80000_7_dim_one_collision`). -/
theorem luminousEfficacy_dim_from_fluxes :
    luminousEfficacy.dim = luminousFlux.dim / radiantFlux.dim := by
  simp [luminousEfficacy, luminousFlux, radiantFlux, modeKind, dimKind, RDim.power, Dim.one]

/-! ## (3) Verified construction and certificates at the quantity level (`ℝ`)

The smart constructor builds a classified quantity from its constituents, licensed by
the kind-law; the certificate holds by construction, and (canonicity) any quantity
carrying the certificate equals the constructed one. -/

/-- An irradiance built as radiant flux / area — classified as an irradiance **by
construction** (`E_e = dΦ_e/dA`). -/
noncomputable def irradianceOf (φ : Quantity radiantFlux.kind ℝ)
    (a : Quantity Part3.area.kind ℝ) : Quantity irradiance.kind ℝ :=
  Quantity.div irradiance_quot_flux_area φ a

/-- The constructed irradiance satisfies the quotient certificate by construction. -/
theorem irradianceOf_isQuotient (φ : Quantity radiantFlux.kind ℝ)
    (a : Quantity Part3.area.kind ℝ) :
    (irradianceOf φ a).IsQuotient irradiance_quot_flux_area φ a := rfl

/-- **Canonicity, instantiated.** Any irradiance certified as a given radiant flux per a
given area equals the constructed one. -/
theorem irradiance_certificate_canonical
    {φ : Quantity radiantFlux.kind ℝ} {a : Quantity Part3.area.kind ℝ}
    {e : Quantity irradiance.kind ℝ}
    (h : e.IsQuotient irradiance_quot_flux_area φ a) :
    e = irradianceOf φ a :=
  Quantity.eq_div_of_isQuotient irradiance_quot_flux_area h

/-- A luminous efficacy built as luminous flux / radiant flux — classified **by
construction** (`K = Φ_v/Φ_e`), over `ℝ`. -/
noncomputable def luminousEfficacyOf (φv : Quantity luminousFlux.kind ℝ)
    (φe : Quantity radiantFlux.kind ℝ) : Quantity luminousEfficacy.kind ℝ :=
  Quantity.div luminousEfficacy_quot_fluxes φv φe

/-- The constructed luminous efficacy satisfies the quotient certificate by
construction. -/
theorem luminousEfficacyOf_isQuotient (φv : Quantity luminousFlux.kind ℝ)
    (φe : Quantity radiantFlux.kind ℝ) :
    (luminousEfficacyOf φv φe).IsQuotient luminousEfficacy_quot_fluxes φv φe := rfl

end PropertyKindCalculus.Iso80000.Part7.DefiningRelations
