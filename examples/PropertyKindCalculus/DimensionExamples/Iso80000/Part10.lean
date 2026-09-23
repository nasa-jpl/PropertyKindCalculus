/-
# Worked examples — ISO 80000-10 (Atomic and nuclear physics)

Part-10 examples, mirroring the `Iso80000` library's own `Iso80000/Part10` layout:

1. the dimensional algebra (absorbed dose is `L²·T⁻²` with mass-exponent zero, activity
   `T⁻¹`, cross section an area, the molar attenuation coefficient an area);
2. **the gray/sievert collision** — absorbed dose ≡ dose equivalent in dimension (`L²·T⁻²`,
   energy per mass) yet distinct in kind, the gray and the sievert not commensurable: the
   standard's own two-name disambiguation of one dimension;
3. **the becquerel collision** — activity ≡ decay constant in dimension (`T⁻¹`) yet
   distinct in kind, the becquerel not commensurable with the reciprocal second;
4. **the widest dimension-one family in the physical parts** — the atomic and neutron
   numbers, the quantum numbers, the reactor factors;
5. **defining relations** — dose equivalent = absorbed dose × quality factor (same
   dimension because the quality factor is dimensionless), specific activity = activity /
   mass, mean life = 1 / decay constant; cross-part to ISO 80000-3 and -4;
6. **catalogue coverage** — all 125 items carry their source as data.

These live in the Mathlib-backed `DimensionExamples` library.
-/

module

public import PropertyKindCalculus.Iso80000.Part10
meta import PropertyKindCalculus.Iso80000.Part10
public import PropertyKindCalculus.Iso80000.Part10.DefiningRelations
meta import PropertyKindCalculus.Iso80000.Part10.DefiningRelations
public import PropertyKindCalculus.QuantityReal
meta import PropertyKindCalculus.QuantityReal

@[expose] public section Blanket

namespace PropertyKindCalculus.Examples.Iso80000.Part10

open PropertyKindCalculus
open PropertyKindCalculus.Iso80000
open PropertyKindCalculus.Iso80000.Part10
open PropertyKindCalculus.Iso80000.Part10.DefiningRelations

/-! ## (1) ISO 80000-10 — the dimensional algebra -/

-- absorbed dose is energy per mass: `L²·T⁻²`, mass-exponent zero
example : absorbedDose.dim.mass = 0 := absorbedDose_dim_mass
example : absorbedDose.dim.length = 2 := absorbedDose_dim_length
-- activity is `T⁻¹` (the becquerel); the cross section an area; the molar coefficient an
-- area (the mole reduced, R13)
example : activity.dim.time = -1 := activity_dim_time
example : crossSection.dim.length = 2 := crossSection_dim_length
example : molarAttenuationCoefficient.dim.length = 2 :=
  molarAttenuationCoefficient_dim_length

-- each kind carries its exact item citation as data
#guard absorbedDoseCK.item == "10-81.1"
#guard doseEquivalentCK.item == "10-83.1"
#guard doseEquivalentCK.cite == "ISO 80000-10, Second edition, 2019-08 item 10-83.1"
#guard activityCK.item == "10-27"

-- the gray and the sievert are well-formed units
example : gray.WellFormed := gray_wellFormed
example : sievert.WellFormed := sievert_wellFormed

/-! ## (2) The gray/sievert collision (on the real standard)

The absorbed dose (`Gy`) and the dose equivalent (`Sv`) carry the *same* dimension
`L²·T⁻²` — energy per mass — yet are different kinds. The standard coins two special unit
names for one dimension *because the kinds differ*. -/

-- SAME DIMENSION: absorbed dose ≡ dose equivalent (`L²·T⁻²`).
example : absorbedDose.dim = doseEquivalent.dim := absorbedDose_dim_eq_doseEquivalent_dim
-- DISTINCT KIND: yet they are not the same kind (the gray vs the sievert).
example : absorbedDose.kind ≠ doseEquivalent.kind := absorbedDose_ne_doseEquivalent
-- and the gray and the sievert are not commensurable, *though both are* `J/kg`.
example : ¬ gray.Commensurable sievert := gray_sievert_not_commensurable
-- the collision capstone on standard quantities.
example : ∃ a b : DimensionedKind, a.kind ≠ b.kind ∧ a.dim = b.dim := iso80000_10_dim_collision

/-! ## (3) The becquerel collision (on the real standard)

Activity (`Bq`) and the decay constant (`s⁻¹`) carry the *same* dimension `T⁻¹` yet are
different kinds. The becquerel is the special name SI reserves for `s⁻¹` as the unit of
activity. -/

example : activity.dim = decayConstant.dim := activity_dim_eq_decayConstant_dim
example : activity.kind ≠ decayConstant.kind := activity_ne_decayConstant
example : ¬ becquerel.Commensurable perSecondDecay := becquerel_perSecond_not_commensurable

/-! ## (4) The widest dimension-one family in the physical parts -/

example : atomicNumber.kind ≠ neutronNumber.kind := atomicNumber_ne_neutronNumber
-- the dimension-1 capstone on standard quantities.
example : ∃ a b : DimensionedKind, a.kind ≠ b.kind ∧ a.dim = b.dim ∧ a.dim = 1 :=
  iso80000_10_dim_one_collision

/-! ## (5) Defining relations: dosimetry built by the kind algebra

Dose equivalent is the product of absorbed dose and the dimensionless quality factor;
specific activity is activity per mass; mean life the reciprocal of the decay constant. -/

-- DIM FROM RELATION: dose equivalent keeps the dimension of absorbed dose *because* the
-- quality factor is dimension one (`H = D·Q`) — the two doses collide on `L²·T⁻²`.
example : doseEquivalent.dim = absorbedDose.dim * qualityFactor.dim :=
  doseEquivalent_dim_from_dose_quality
-- mean life is the reciprocal of the decay constant's dimension (`τ = 1/λ`).
example : meanLife.dim = decayConstant.dim⁻¹ := meanLife_dim_from_decayConstant
-- specific activity is activity / mass (cross-part, the mass from ISO 80000-4).
example : specificActivity.dim = activity.dim / Part4.mass.dim :=
  specificActivity_dim_from_activity_mass

-- VERIFIED CONSTRUCTION (item 10-83.1): a dose equivalent built as absorbed dose × quality
-- factor carries its product certificate by construction, over `ℝ`.
example (d : Quantity absorbedDose.kind ℝ) (q : Quantity qualityFactor.kind ℝ) :
    (doseEquivalentOf d q).IsProduct doseEquivalent_prod_dose_quality d q :=
  doseEquivalentOf_isProduct d q

-- the dose-equivalent product instantiates at a *different* carrier (`Int`), where the
-- construction also computes: `5 Gy · 2 = 10 Sv` (at `Int`).
def doseEquivalentInt : Quantity doseEquivalent.kind Int :=
  Quantity.mul doseEquivalent_prod_dose_quality
    (⟨5⟩ : Quantity absorbedDose.kind Int) (⟨2⟩ : Quantity qualityFactor.kind Int)
#guard doseEquivalentInt.magnitude == 10

/-! ## (6) Catalogue coverage — all 125 items carry their source as data -/

#guard PropertyKindCalculus.Iso80000.Part10.catalogue.length == 125
#guard atomicNumberCK.item == "10-1.1"
#guard spinCK.item == "10-10"
#guard hyperfineQuantumNumberCK.item == "10-13.8"
#guard exposureRateCK.item == "10-89"
#guard absorbedDoseCK.coherentUnit == "Gy"
#guard doseEquivalentCK.coherentUnit == "Sv"
#guard activityCK.coherentUnit == "Bq"

end PropertyKindCalculus.Examples.Iso80000.Part10

end Blanket
