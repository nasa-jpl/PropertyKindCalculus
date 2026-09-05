/-
# ISO 80000-1 — *General*: the ISQ frame, checked against the parts that use it

Part 1 of the series defines **no quantities**. It defines the frame every other part is
written in: how a dimension is formed from the base quantities, how a unit and a
numerical value compose into a quantity, and — in two normative annexes — how quantity
names are formed and how numbers are rounded. So this module is not a catalogue like
`Part3` … `Part13`. It is a **conformance layer**: each clause is restated in this work's
formalism and discharged against the kinds the other parts already catalogue, so Part 1's
frame is a build artifact rather than an assumption the catalogue modules make silently.

What is checked here:

  * **§5, the dimensional product.** The clause's own worked table of ten quantities and
    their dimensions, discharged against the catalogued kinds of Parts 3–9. Each row is a
    *cross-part* statement — it fails if any of those catalogues moves — and each is
    stated as the defining relation the exponent vector comes from (energy is force along
    a length, a magnetic flux is a voltage over a duration) rather than as a transcribed
    string, so what is checked is the relation and not the transcription.
  * **§5, the two axes PhysLib does not generate.** The clause's `J` (candela) and `N`
    (mole) are absent from `Dimension LTMCTDimensionBase`. The two rows that carry them —
    illuminance and molar entropy — are checked *through* the scale-spanning reduction
    (R13), which is exactly the substitution `J := M·L²·T⁻³` and `N := 1`. Both hold
    definitionally, which is the precise sense in which the reduction factors the
    standard's table rather than departing from it.
  * **§5, the two directions of the kind/dimension implication.** The clause states one:
    quantities of the same kind have the same dimension, so quantities of different
    dimensions are of different kinds. It does not state the converse, and the converse is
    false — `dim_not_injective` exhibits distinct kinds at one dimension. Stating the
    sound direction beside the refuted one is the content of R1.
  * **§6.2, `Q = {Q}·[Q]`.** A quantity is a numerical value times a unit, and changing to
    a unit `k` times the first divides the numerical value by `k`. Both are laws of
    `RealUnit`, the chosen-reference unit that carries its own magnitude, read at the
    clause.
  * **§6.3, products and quotients.** The clause splits a product of quantities into a
    product of numerical values and a product of units. Here that split is two facts
    proved separately: the **kind** side is an R12 kind-law licensing the operation, and
    the **unit** side is the `dim` homomorphism. The clause's compound unit is the image
    of the second, and the first is what the dimension cannot supply.
  * **Annex A (normative), specific terms used for quantities.** Every naming term the
    annex defines becomes a predicate over catalogued kinds, and every witness composes an
    already-certified defining relation from Parts 4, 5, 6 and 9 — nothing is re-proved.
    The payoff is A.2.3 against A.3.3: "factor" is a same-*dimension* term and "ratio" a
    same-*kind* one, so the annex's own vocabulary cannot be applied by a dimension-only
    system (`powerFactor_is_factor_not_ratio`).

Annex B (normative), rounding of numbers, is in `Part1.Rounding`, beside the grid it
describes.

No normative text from the licensed standard is reproduced; the clauses are restated in
this work's own formalism.
-/

import PropertyKindCalculus.Iso80000.Part3.DefiningRelations
import PropertyKindCalculus.Iso80000.Part4.DefiningRelations
import PropertyKindCalculus.Iso80000.Part5.DefiningRelations
import PropertyKindCalculus.Iso80000.Part6.DefiningRelations
import PropertyKindCalculus.Iso80000.Part7
import PropertyKindCalculus.Iso80000.Part9.DefiningRelations
import PropertyKindCalculus.QuantityClassification
import PropertyKindCalculus.UnitReal

namespace PropertyKindCalculus.Iso80000.Part1

open PropertyKindCalculus

/-- The source: ISO 80000-1, the *General* part of the series. -/
def source : StandardRef := iso80000_1

/-! ## §5 — The dimensional product

The clause writes a general quantity's dimension as a product of powers of the base
dimensions over the ISQ's seven base quantities. PhysLib's `Dimension LTMCTDimensionBase`
carries five generators — length, mass, time, charge and temperature — because the ampere
is the coulomb per second, the candela reduces to power and the mole to one
(`ScaleSpanning`, R13). The seven-axis product and this five-axis one therefore agree on
every quantity, with the `I` exponent read off the charge exponent and the `J` and `N`
exponents discharged by the reduction rather than carried. -/

namespace Section5

/-- **The ISQ base quantity electric current is charge per time.** The clause's `I`
exponent and PhysLib's charge exponent are related by `C = I·T` — the identification the
catalogue's dimension renderer applies for citation fidelity. -/
theorem current_eq_charge_per_time : Dim.current = Dim.charge / Dim.time := rfl

/-! ### The clause's worked table

Ten quantities with their dimensions. Each row is discharged as the relation its exponent
vector comes from, over kinds Parts 3–9 already catalogue. -/

/-- **Speed** — length over duration (ISO 80000-3 item 3-8.1), the clause's `L·T⁻¹`. -/
theorem speed_dim : Part3.speed.dim = Part3.length.dim / Part3.duration.dim :=
  Part3.DefiningRelations.speed_dim_from_pathLength_duration

/-- **Frequency** — the reciprocal of a period (ISO 80000-3 item 3-15.1), the clause's
`T⁻¹`. -/
theorem frequency_dim : Part3.frequency.dim = Part3.periodDuration.dim⁻¹ :=
  Part3.DefiningRelations.frequency_dim_from_period

/-- **Force** — mass times acceleration (ISO 80000-4 item 4-9.1), the clause's `L·M·T⁻²`,
here as the dimension the mechanical layer names once. -/
theorem force_dim : Part4.force.dim = Dim.force := rfl

/-- **Energy** — force along a length (ISO 80000-4 item 4-27.1), the clause's `L²·M·T⁻²`.
ISO 80000-4 catalogues no bare *energy* kind: it catalogues the energies by species
(potential, kinetic, mechanical), all at this one dimension — R1 in the standard's own
tabulation. -/
theorem energy_dim : Part4.mechanicalEnergy.dim = Part4.force.dim * Part3.length.dim :=
  rfl

/-- **Entropy** — energy over thermodynamic temperature (ISO 80000-5 item 5-18), the
clause's `L²·M·T⁻²·Θ⁻¹`. Heat capacity shares the dimension and is a different kind. -/
theorem entropy_dim :
    Part5.entropy.dim = Part5.heat.dim / Part5.thermodynamicTemperature.dim :=
  Part5.DefiningRelations.heatCapacity_dim_from_heat_temperature

/-- **Electric tension** — energy per charge (IEC 80000-6 item 6-11.3). The clause prints
`L²·M·T⁻³·I⁻¹`; over PhysLib's charge generator the same quantity reads `L²·M·T⁻²·C⁻¹`, and
the two are the one dimension because `C = I·T` moves a factor of `T` between the current
and time exponents — the identification the catalogue's renderer applies. Annex A.1 records
the other identification this row needs: *electric tension* is the name voltage carries in
many languages other than English. -/
theorem electricTension_dim : Part6.voltage.dim = Part6.EDim.energy / Dim.charge := rfl

/-- **Magnetic flux** — a voltage over a duration (IEC 80000-6 item 6-22.1), the clause's
`L²·M·T⁻²·I⁻¹`. -/
theorem magneticFlux_dim : Part6.magneticFlux.dim = Part6.voltage.dim * Dim.time := rfl

/-- **Efficiency** — a ratio of two powers (ISO 80000-4 item 4-30), the clause's `1`. -/
theorem efficiency_dim : Part4.efficiency.dim = Part4.power.dim / Part4.power.dim :=
  Part4.DefiningRelations.efficiency_dim_from_power_ratio

/-! ### The two rows carrying an axis PhysLib does not generate -/

/-- **Illuminance** — the clause's `L⁻²·J` with the candela reduced to the power it
weights. -/
theorem illuminance_dim :
    Part7.illuminance.dim = Dim.luminousIntensity / Part3.area.dim := rfl

/-- **Molar entropy** — the clause's `L²·M·T⁻²·Θ⁻¹·N⁻¹` with the mole reduced to one. -/
theorem molarEntropy_dim :
    Part9.molarEntropy.dim = Part5.entropy.dim / Part9.amountOfSubstance.dim := by
  show Part5.TDim.heatCapacity = Part5.TDim.heatCapacity / Dim.amountOfSubstance
  rw [Dim.amountOfSubstance_eq_one, div_one]

/-! ### The direction the clause states, and the converse it does not -/

/-- **The sound direction.** A dimensioned kind has one dimension, so kinds that differ in
dimension differ — the comparability rule the clause draws. -/
theorem ne_of_dim_ne {a b : DimensionedKind} (h : a.toDimension ≠ b.toDimension) :
    a ≠ b := fun hab => h (congrArg DimensionedKind.toDimension hab)

/-- **The converse is refuted.** `dim_not_injective`, restated at the clause it bears on:
distinct kinds at one dimension, and that dimension is one. -/
theorem dim_not_determining :
    ∃ a b : DimensionedKind,
      a.kind ≠ b.kind ∧ a.toDimension = b.toDimension ∧ a.toDimension = 1 :=
  dim_not_injective

end Section5

/-! ## §6.2 — A quantity is a numerical value times a unit -/

namespace Section6

variable {k : KindOfProperty}

/-- **`Q = {Q}·[Q]`, forwards**: the numerical value of a quantity built from a number and
a unit is that number. -/
theorem numericalValue_of_number (u : RealUnit k) (n : ℝ) :
    RealUnit.measure (u.ofNumber n) u = n :=
  RealUnit.measure_ofNumber u n

/-- **`Q = {Q}·[Q]`, backwards**: a quantity is recovered from its numerical value and its
unit. With the previous law this is the clause's bijection between the quantities of a
kind and their numerical values in a chosen unit. -/
theorem quantity_of_numericalValue (u : RealUnit k) (q : Quantity k ℝ) :
    u.ofNumber (RealUnit.measure q u) = q :=
  RealUnit.ofNumber_measure u q

/-- **The change of unit.** The numerical value in `v` is the numerical value in `u` times
the factor from `u` to `v` — the clause's "a unit `k` times the first gives a numerical
value `1/k` times the first", with the factor named rather than assumed. -/
theorem numericalValue_change_of_unit (q : Quantity k ℝ) (u v : RealUnit k) :
    RealUnit.measure q v = RealUnit.measure q u * u.ratio v :=
  RealUnit.measure_eq_measure_mul_ratio q u v

/-- **The factor is reciprocal in the two directions**, which is what makes the clause's
`1/k` well posed. -/
theorem change_of_unit_roundtrip (u v : RealUnit k) : u.ratio v * v.ratio u = 1 :=
  RealUnit.ratio_mul_ratio_symm u v

/-! ## §6.3 — Products and quotients -/

/-- **The unit side of a product**: the forgetful map is a homomorphism, so the dimension
of a product is the product of the dimensions — the clause's compound unit. -/
theorem dim_of_product (a b : DimensionedKind) :
    (DimensionedKind.times a b).toDimension = a.toDimension * b.toDimension := rfl

/-- **The kind side of a product**: the operation is licensed by an R12 kind-law, a scale
precondition on all three kinds and not a consequence of the dimensions. Read at the
clause: a voltage times a current is a power. -/
theorem kindLaw_of_product :
    ProductKind Part6.voltage.kind Part6.electricCurrent.kind Part6.power.kind :=
  Part6.DefiningRelations.power_prod_voltage_current

/-- **The kind side of a quotient**: the same, for division — a voltage over a current is
a resistance. -/
theorem kindLaw_of_quotient :
    QuotientKind Part6.voltage.kind Part6.electricCurrent.kind Part6.resistance.kind :=
  Part6.DefiningRelations.resistance_quot_voltage_current

end Section6

/-! ## Annex A (normative) — Specific terms used for quantities

The annex names the terms an English quantity name is built from and fixes what each one
means: a *coefficient* multiplies across a change of dimension, a *factor* within one; a
*ratio* divides two quantities of the same kind; *specific* divides by mass, *density* by
volume, *surface density* by area, *linear density* by length, *molar* by amount of
substance, and a *concentration* by the total volume of a mixture.

Each becomes a predicate over catalogued kinds, carrying two obligations: the R12 kind-law
that licenses the division, and the dimensional consequence. Every witness below discharges
both by composing certificates the part modules already prove, so the annex is applied to
the catalogue rather than restated over it. -/

namespace AnnexA

/-- **A.2.2 — "coefficient".** `A = k·B` where `A` and `B` are of *different* dimensions,
so `k` carries the difference. (The annex's NOTE records "modulus" as a synonym.) -/
def IsCoefficient (a b k : DimensionedKind) : Prop :=
  QuotientKind a.kind b.kind k.kind ∧ a.dim ≠ b.dim ∧ k.dim = a.dim / b.dim

/-- **A.2.3 — "factor".** `A = k·B` where `A` and `B` are of the *same* dimension, so `k`
is of dimension one. -/
def IsFactor (a b k : DimensionedKind) : Prop :=
  QuotientKind a.kind b.kind k.kind ∧ a.dim = b.dim ∧ k.dim = 1

/-- **A.3.3 — "ratio".** A quotient of two quantities of the same *kind*. Strictly stronger
than `IsFactor`: same kind gives same dimension, and the converse fails. -/
def IsRatio (a b k : DimensionedKind) : Prop :=
  QuotientKind a.kind b.kind k.kind ∧ a.kind = b.kind ∧ k.dim = 1

/-- **A.5.1 — "specific".** The quotient of the quantity and mass. -/
def IsSpecific (a k : DimensionedKind) : Prop :=
  QuotientKind a.kind Part4.mass.kind k.kind ∧ k.dim = a.dim / Part4.mass.dim

/-- **A.5.2 — "density".** The quotient of the quantity and the volume. -/
def IsDensity (a k : DimensionedKind) : Prop :=
  QuotientKind a.kind Part3.volume.kind k.kind ∧ k.dim = a.dim / Part3.volume.dim

/-- **A.5.3 — "surface … density".** The quotient of the quantity and the area. -/
def IsSurfaceDensity (a k : DimensionedKind) : Prop :=
  QuotientKind a.kind Part3.area.kind k.kind ∧ k.dim = a.dim / Part3.area.dim

/-- **A.5.5 — "molar".** The quotient of the quantity and the amount of substance. The
annex's own NOTE records that the term violates A.1 by naming the mole. -/
def IsMolar (a k : DimensionedKind) : Prop :=
  QuotientKind a.kind Part9.amountOfSubstance.kind k.kind ∧
    k.dim = a.dim / Part9.amountOfSubstance.dim

/-- **A.5.6 — "concentration".** The quotient of the quantity and the total volume. The
formal content coincides with `IsDensity`; what separates them in the annex is that the
numerator is a quantity *of a substance in a mixture*, which is a fact about the numerator
and not about the division. Stated as a distinct name so a witness records which reading
the standard's own term carries. -/
def IsConcentration (a k : DimensionedKind) : Prop := IsDensity a k

/-! ### Witnesses, composed from the part modules' certificates -/

/-- Specific heat capacity is heat capacity per mass (ISO 80000-5 item 5-16.1). -/
theorem specificHeatCapacity_is_specific :
    IsSpecific Part5.heatCapacity Part5.specificHeatCapacity :=
  ⟨Part5.DefiningRelations.specificHeatCapacity_quot_heatCapacity_mass,
   Part5.DefiningRelations.specificHeatCapacity_dim_from_heatCapacity_mass⟩

/-- Mass density is mass per volume (ISO 80000-4 item 4-2). -/
theorem massDensity_is_density : IsDensity Part4.mass Part4.massDensity :=
  ⟨Part4.DefiningRelations.massDensity_quot_mass_volume,
   Part4.DefiningRelations.massDensity_dim_from_mass_volume⟩

/-- The density of heat flow rate is a *surface* density: heat flow rate per area
(ISO 80000-5 item 5-8). The annex's A.5.3 reading, not A.5.2's. -/
theorem densityOfHeatFlowRate_is_surfaceDensity :
    IsSurfaceDensity Part5.heatFlowRate Part5.densityOfHeatFlowRate :=
  ⟨Part5.DefiningRelations.densityOfHeatFlowRate_quot_heatFlowRate_area,
   Part5.DefiningRelations.densityOfHeatFlowRate_dim_from_heatFlowRate_area⟩

/-- Molar mass is mass per amount of substance (ISO 80000-9 item 9-4). -/
theorem molarMass_is_molar : IsMolar Part4.mass Part9.molarMass :=
  ⟨Part9.DefiningRelations.molarMass_quot_mass_amount,
   Part9.DefiningRelations.molarMass_dim_from_mass_amount⟩

/-- Molar volume is volume per amount of substance (ISO 80000-9 item 9-5). -/
theorem molarVolume_is_molar : IsMolar Part3.volume Part9.molarVolume :=
  ⟨Part9.DefiningRelations.molarVolume_quot_volume_amount,
   Part9.DefiningRelations.molarVolume_dim_from_volume_amount⟩

/-- The amount-of-substance concentration is an amount per total volume (ISO 80000-9
item 9-12.1) — the A.5.6 reading. -/
theorem amountConcentration_is_concentration :
    IsConcentration Part9.amountOfSubstance Part9.amountConcentration :=
  ⟨Part9.DefiningRelations.amountConcentration_quot_amount_volume,
   Part9.DefiningRelations.amountConcentration_dim_from_amount_volume⟩

/-- The modulus of elasticity is a *coefficient* in the annex's A.2.2 sense — normal
stress over relative linear strain, whose dimensions differ (the strain is dimension one).
A.2.2's NOTE is why the quantity is named a modulus rather than a coefficient. -/
theorem modulusOfElasticity_is_coefficient :
    IsCoefficient Part4.normalStress Part4.relativeLinearStrain Part4.modulusOfElasticity :=
  ⟨Part4.DefiningRelations.modulusOfElasticity_quot_normalStress_relativeLinearStrain,
   by decide,
   Part4.DefiningRelations.modulusOfElasticity_dim_from_stress_strain⟩

/-- Efficiency is a *ratio* in the annex's A.3.3 sense: it divides two quantities of one
kind (ISO 80000-4 item 4-30). -/
theorem efficiency_is_ratio : IsRatio Part4.power Part4.power Part4.efficiency :=
  ⟨Part4.DefiningRelations.efficiency_quot_power_power, rfl, rfl⟩

/-! ### A.2.3 against A.3.3 — the discrimination that needs the kind layer

The annex gives "factor" and "ratio" different conditions: a factor divides quantities of
the same *dimension*, a ratio quantities of the same *kind*. A dimension-only system
cannot tell the two conditions apart, so it cannot apply the annex's own vocabulary. The
power factor is the separating case: IEC 80000-6 catalogues active and apparent power as
distinct kinds at one dimension, individuated by their defining constructions. -/

/-- Active and apparent power are distinct kinds — by their differing defining
constructions (the time-averaged real component against the RMS product), the same way
active and reactive power are distinguished upstream. -/
theorem activePower_ne_apparentPower :
    Part6.activePower.kind ≠ Part6.apparentPower.kind :=
  KindOfProperty.distinct_of_examPrinciple (by decide)

/-- **The power factor is a factor and not a ratio.** It satisfies A.2.3 — its two
quantities share a dimension — and refutes A.3.3, because they are different kinds. The
two annex terms therefore come apart on a quantity the standard itself tabulates, and only
the kind layer can say which term applies. -/
theorem powerFactor_is_factor_not_ratio :
    IsFactor Part6.activePower Part6.apparentPower Part6.powerFactor ∧
      ¬ IsRatio Part6.activePower Part6.apparentPower Part6.powerFactor :=
  ⟨⟨Part6.DefiningRelations.powerFactor_quot_active_apparent, rfl, rfl⟩,
   fun h => activePower_ne_apparentPower h.2.1⟩

end AnnexA

end PropertyKindCalculus.Iso80000.Part1
