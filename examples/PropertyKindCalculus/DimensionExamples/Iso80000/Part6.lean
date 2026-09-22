/-
# Worked examples — IEC 80000-6 (Electromagnetism)

Part-6 examples, mirroring the `Iso80000` library's own `Iso80000/Part6` layout:

1. the dimensional algebra and unit facts over the new electric-current base axis
   (electric current is `C·T⁻¹`, capacitance carries the charge generator squared,
   resistance `M·L²·T⁻¹·C⁻²`; the ampere well-formed; commensurability "of the same
   kind");
2. **the scale-type distinction (requirement R6)** — electric potential (interval-scale,
   gauge-dependent) versus electric potential difference (ratio-scale), the *same*
   dimension `V` separated by scale alone, with the volt of electric potential a
   well-formed unit that nonetheless does not admit `×`,`÷`;
3. **the AC power family as a specialization lattice (R2)** — active, reactive, apparent,
   complex, and non-active power as power species individuated **by defining
   construction**; active and reactive power comparable yet distinct;
4. **dimension collisions** — same dimension, distinct kind: active vs reactive power
   (one dimension, *three* unit strings `W`/`var`/`VA`), resistance vs reactance (both
   the ohm), and the dimension-one family;
5. **defining relations** — Ohm's law (resistance = voltage / current), the power product
   (power = voltage × current), the reciprocal pairs; the electric-current law crosses to
   ISO 80000-3 (time); the power factor is dimensionless because it is a ratio of two
   powers;
6. **catalogue coverage** — all 85 items carry their source as data.

Series-wide catalogue examples are in the sibling
`PropertyKindCalculus.DimensionExamples.Iso80000.References`.
-/

module

public import PropertyKindCalculus.Iso80000
meta import PropertyKindCalculus.Iso80000
public import PropertyKindCalculus.QuantityReal
meta import PropertyKindCalculus.QuantityReal

public section -- pkc-blanket
@[expose] section -- pkc-blanket-expose

namespace PropertyKindCalculus.Examples.Iso80000.Part6

open PropertyKindCalculus
open PropertyKindCalculus.Iso80000
open PropertyKindCalculus.Iso80000.Part6
open PropertyKindCalculus.Iso80000.Part6.DefiningRelations

/-! ## (1) IEC 80000-6 — Electromagnetism (the dimensional algebra and units)

The new SI base axis is electric current — the ampere, taken over PhysLib's charge
generator `C` as `C·T⁻¹`. The dimensional algebra is a checked computation. -/

-- electric current is `C·T⁻¹`; charge is `C`; the derived units carry the charge generator.
example : electricCurrent.dim.charge = 1 := electricCurrent_dim_charge
example : electricCurrent.dim.time = -1 := electricCurrent_dim_time
example : electricCharge.dim.charge = 1 := electricCharge_dim_charge
example : voltage.dim.charge = -1 := voltage_dim_charge
example : capacitance.dim.charge = 2 := capacitance_dim_charge
example : resistance.dim.charge = -2 := resistance_dim_charge
example : magneticFlux.dim.charge = -1 := magneticFlux_dim_charge

-- each kind carries its exact item citation as data
#guard electricCurrentCK.item == "6-1"
#guard impedanceCK.item == "6-51.1"
#guard impedanceCK.cite == "IEC 80000-6, Edition 2.0, 2022-11 item 6-51.1"
#guard activePowerCK.item == "6-56"

-- the ampere and the ohm are well-formed units; commensurability is "of the same kind"
example : ampere.WellFormed := ampere_wellFormed
example : ohm.WellFormed := ohm_wellFormed
example : ¬ ampere.Commensurable voltPotential := ampere_voltPotential_not_commensurable

/-! ## (2) The scale-type distinction (requirement R6, on the real standard)

Electric potential (6-11.1) and electric potential difference (6-11.2) have the *same*
dimension `M·L²·T⁻²·C⁻¹`, yet are different kinds — separated not by dimension but by
**scale type**: electric potential is interval-scale (gauge freedom — fixed only up to
an arbitrary additive reference), the difference ratio-scale. The gauge-dependent
potential is electromagnetism's Celsius temperature (Part 5). -/

-- (a) the difference admits ×,÷ (ratio scale); the gauge-dependent potential does NOT
example : ScaleType.AllowsRatio electricPotentialDifference.kind.scale :=
  electricPotentialDifference_allowsRatio
example : ¬ ScaleType.AllowsRatio electricPotential.kind.scale :=
  electricPotential_not_allowsRatio

-- (b) yet the volt of electric potential is a WELL-FORMED unit — a kind bears a unit
--     from the differential (interval) scale upward, not only from ratio scale.
example : voltPotential.WellFormed := voltPotential_wellFormed

-- (c) DISTINCTION BY SCALE, NOT DIMENSION: same dimension `V`, distinct kinds — and the
--     two volts, same string and same dimension, are not commensurable.
example : electricPotential.dim = electricPotentialDifference.dim := rfl
example : electricPotential.kind ≠ electricPotentialDifference.kind :=
  electricPotential_ne_electricPotentialDifference
example : ¬ voltPotential.Commensurable voltDifference :=
  voltPotential_voltDifference_not_commensurable

-- the scale capstone, on standard quantities.
example : ∃ a b : DimensionedKind, a.kind ≠ b.kind ∧ a.dim = b.dim ∧
    a.kind.scale ≠ b.kind.scale :=
  iec80000_6_scale_collision

/-! ## (3) The AC power family: a specialization lattice individuated by defining
construction (requirement R2, on the real standard)

IEC 80000-6 lists active power (6-56), reactive power (6-60), apparent power (6-57),
complex power (6-59), and non-active power (6-61) as power quantities of *one* dimension
`M·L²·T⁻³`, distinguished by which component of the periodic AC process each isolates.
Here each is a *species* of the general power kind (6-45), individuated **not by fiat but
by an explicit defining-construction (examination) principle**. -/

-- (a) active power specializes power.
example : Specializes Edge activePower.kind power.kind :=
  activePower_specializes_power

-- (b) DISTINCTION NOT BY FIAT: active and reactive power are distinct kinds *because they
--     isolate different components of the process* (the time-averaged real part vs the
--     imaginary part) — proved via `distinct_of_examPrinciple`, not by `id` strings.
example : activePower.kind ≠ reactivePower.kind := activePower_ne_reactivePower

-- the link from the kind back to its defining construction is checked, too.
example : activePower.kind.examinedBy PowerPrinciple.timeAveragedReal :=
  activePower_examinedBy

-- (c) COMPARABILITY PRESERVED: though distinct, active and reactive power remain mutually
--     comparable — they share the super-kind power (and combine into the complex power).
example : MutuallyComparable Edge activePower.kind reactivePower.kind :=
  activePower_reactivePower_comparable

-- (d) and the dimension cannot tell them apart: same dimension `M·L²·T⁻³`, distinct kinds.
example : activePower.dim = reactivePower.dim := activePower_dim_eq_reactivePower_dim

/-! ## (4) Dimension collisions: same dimension, distinct kind

The {dimension functor} identifies these pairs; the kind layer keeps them apart —
including their units, even where the standard spends three different unit strings on
one dimension. -/

-- active and reactive power: both `M·L²·T⁻³`, distinct kinds — and the watt and the var
-- are not commensurable, *though the dimension is one and the same*. (Sharper than Part
-- 5's J/K, where even the unit string agreed; here the standard itself differs the
-- strings: W, var, VA.)
example : activePower.dim = reactivePower.dim := activePower_dim_eq_reactivePower_dim
example : activePower.kind ≠ reactivePower.kind := activePower_ne_reactivePower
example : ¬ wattActive.Commensurable varReactive :=
  wattActive_varReactive_not_commensurable

-- resistance and reactance: both the ohm `M·L²·T⁻¹·C⁻²`, distinct kinds (real and
-- imaginary parts of an impedance).
example : resistance.dim = reactance.dim := resistance_dim_eq_reactance_dim
example : resistance.kind ≠ reactance.kind := resistance_ne_reactance

-- the power collision and the dimension-1 collision, on standard quantities.
example : ∃ a b : DimensionedKind, a.kind ≠ b.kind ∧ a.dim = b.dim :=
  iec80000_6_dim_collision
example : ∃ a b : DimensionedKind, a.kind ≠ b.kind ∧ a.dim = b.dim ∧ a.dim = 1 :=
  iec80000_6_dim_one_collision

/-! ## (5) Defining relations: electromagnetism built by the kind algebra

Ohm's law (resistance = voltage / current), the power product (power = voltage ×
current), and the reciprocal pairs compose Part-6 kinds out of one another; the
electric-current law crosses to ISO 80000-3 (time); the power factor is dimensionless
because it is a ratio of two powers. -/

-- DIM FROM RELATION: resistance's `M·L²·T⁻¹·C⁻²` follows from voltage / current (Ohm's
-- law), and power's `M·L²·T⁻³` follows from voltage × current.
example : resistance.dim = voltage.dim / electricCurrent.dim :=
  resistance_dim_from_voltage_current
example : power.dim = voltage.dim * electricCurrent.dim :=
  power_dim_from_voltage_current
-- CROSS-PART (item 6-1): electric current's `C·T⁻¹` follows from charge / time, the time
-- crossing to ISO 80000-3.
example : electricCurrent.dim = electricCharge.dim / Part3.duration.dim :=
  electricCurrent_dim_from_charge_duration

-- ALGEBRAIC REMARK (item 6-58): the power factor is dimension one *because* it is a ratio
-- of two powers (`λ = P/S`) — the dimensionlessness is computed from the relation, the
-- electromagnetic analogue of a plane angle being a ratio of two lengths.
example : powerFactor.dim = activePower.dim / apparentPower.dim :=
  powerFactor_dim_from_powers

-- VERIFIED CONSTRUCTION (item 6-46): a resistance built as voltage / current carries its
-- classification certificate by construction (Ohm's law), over `ℝ`.
example (u : Quantity voltage.kind ℝ) (i : Quantity electricCurrent.kind ℝ) :
    (resistanceOf u i).IsQuotient resistance_quot_voltage_current u i :=
  resistanceOf_isQuotient u i

-- the Ohm's-law quotient instantiates at a *different* carrier (`Int`), where the
-- construction also computes: `12 V / 3 A = 4 Ω` (at `Int`).
def resistanceInt : Quantity resistance.kind Int :=
  Quantity.div resistance_quot_voltage_current
    (⟨12⟩ : Quantity voltage.kind Int) (⟨3⟩ : Quantity electricCurrent.kind Int)
#guard resistanceInt.magnitude == 4

/-! ## (6) Catalogue coverage — all 85 items carry their source as data -/

-- every IEC 80000-6 item is catalogued, in item order …
#guard PropertyKindCalculus.Iso80000.Part6.catalogue.length == 85
-- … with the item designations (including every sub-suffixed item) …
#guard electricChargeCK.item == "6-2.1"
#guard electricPotentialCK.item == "6-11.1"
#guard totalMagneticFluxCK.item == "6-22.4"
#guard magneticVectorPotentialCK.item == "6-32"
#guard apparentAdmittanceCK.item == "6-52.5"
#guard activeEnergyCK.item == "6-62"
-- … each citing its full source (the one IEC-published part) …
#guard impedanceCK.cite == "IEC 80000-6, Edition 2.0, 2022-11 item 6-51.1"
-- … and recording its coherent SI unit symbol as a locator (three strings, one power
--   dimension).
#guard activePowerCK.coherentUnit == "W"
#guard reactivePowerCK.coherentUnit == "var"
#guard apparentPowerCK.coherentUnit == "VA"
#guard electricCurrentCK.coherentUnit == "A"

end PropertyKindCalculus.Examples.Iso80000.Part6

end -- pkc-blanket-expose
end -- pkc-blanket
