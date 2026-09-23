/-
# PropertyKindCalculus.Iso80000

The standards-grounded layer: quantity-kinds (QK) and units (U) organized to
mirror the **ISO/IEC 80000** *Quantities and units* series, each citing its source
by name and version only (no normative content is reproduced — the standards are
licensed and copyrighted).

  * `PropertyKindCalculus.Iso80000.References` — the citation catalogue: one
    `StandardRef` per licensed part (ISO/IEC 80000-1 … -13).
  * `PropertyKindCalculus.Iso80000.Catalogue` — the shared catalogue scaffolding
    reused by every part: the `CataloguedKind` record (a {dimensioned kind} plus its
    citation locators), the `cite` renderer, and the `dimKind` builder. Defined once
    here rather than restated per part.
  * `PropertyKindCalculus.Iso80000.Part1` — ISO 80000-1 *General*, the part that defines
    no quantities: it defines the frame the others are written in, so the module is a
    **conformance layer** rather than a catalogue. §5's own worked table of ten quantities
    and their dimensions is discharged against the catalogued kinds of Parts 3–9, each row
    stated as the defining relation its exponent vector comes from; the two rows carrying an
    ISQ axis PhysLib does not generate (`J`, `N`) hold definitionally through the
    scale-spanning reduction (R13). §5's stated implication sits beside the converse
    `dim_not_injective` refutes (R1), §6.2/§6.3 are `RealUnit`'s laws and the `dim`
    homomorphism plus the R12 kind-law, and **Annex A** (normative) becomes predicates over
    catalogued kinds whose witnesses compose the certificates Parts 4/5/9 already prove —
    with `powerFactor_is_factor_not_ratio` showing that the annex's own *factor* (same
    dimension) and *ratio* (same kind) come apart on a quantity the standard tabulates.
  * `PropertyKindCalculus.Iso80000.Part1.Rounding` — Annex B (normative), rounding of
    numbers, checked against this work's rounding grid. **Not imported here**: it is the one
    module in this library that reaches into the uncertainty stack (`Adequacy.Grid`), and
    importing the standards catalogue should not drag that in. Build it with the library or
    import it directly. The finding it records is that the fit is not clean — `gridRound`
    breaks ties toward `+∞`, giving Rule B's answer at a positive tie and neither rule's at
    a negative one.
  * `PropertyKindCalculus.Iso80000.Part2` — ISO 80000-2 *Mathematics*, a table of
    mathematical signs and symbols that defines no quantities and assigns no dimensions.
    Rather than transcribe it, the module records the intersection that carries weight: §7's
    standard number sets as the carriers of `Quantity k R` — and the carrier §7 does *not*
    list, `Float`, which is exactly the one that instantiates `Carrier` without
    `LawfulCarrier` (R15's premise at its source) — §7's closed interval as `IccQ`, §15's
    complex numbers as a carrier and not a kind, and §18 as the clause R11 is drawn from.
  * `PropertyKindCalculus.Iso80000.Part3` — the full catalogue of ISO 80000-3 *Space
    and time* (all of items 3-1.1 … 3-26.3), with the length family as a
    specialization lattice (R2) and the dimension-collision capstones.
  * `PropertyKindCalculus.Iso80000.Part3.AreaElement` / `.VolumeElement` — the
    surface- and volume-element *Remarks* (items 3-3, 3-4), formalized analytically.
  * `PropertyKindCalculus.Iso80000.Part3.AreaClassification` — verified classification
    of areas (R12).
  * `PropertyKindCalculus.Iso80000.Part3.DefiningRelations` — the algebraic *Remarks*
    (curvature, repetency, frequency, speed, plane angle) as R12 kind-laws.
  * `PropertyKindCalculus.Iso80000.Part4` — the full catalogue of ISO 80000-4
    *Mechanics* (all of items 4-1 … 4-32), with the force family as a specialization
    lattice (R2) and the torque/energy dimension-collision capstone.
  * `PropertyKindCalculus.Iso80000.Part4.DefiningRelations` — the algebraic *Remarks*
    (mass density, specific volume, momentum, pressure, kinematic viscosity,
    efficiency, modulus of elasticity) as R12 kind-laws, several composing Part-4
    kinds out of Part-3 (space-and-time) kinds.
  * `PropertyKindCalculus.Iso80000.Part5` — the full catalogue of ISO 80000-5
    *Thermodynamics* (all of items 5-1 … 5-36), with the energy family (the
    thermodynamic potentials) as a specialization lattice (R2), the
    entropy/heat-capacity dimension collision (both `J/K`), and — uniquely — the
    scale-type distinction between thermodynamic temperature (ratio-scale) and
    Celsius temperature (interval-scale), requirement R6 on the standard.
  * `PropertyKindCalculus.Iso80000.Part5.DefiningRelations` — the algebraic *Remarks*
    (specific heat capacity, specific entropy, density of heat flow rate, thermal
    conductance, the ratio of specific heat capacities) as R12 kind-laws, several
    composing Part-5 kinds out of Part-4 (mass) and Part-3 (area) kinds and the
    temperature base quantity.
  * `PropertyKindCalculus.Iso80000.Part6` — the full catalogue of IEC 80000-6
    *Electromagnetism* (all of items 6-1 … 6-62), the one IEC-published part: it brings
    in the electric-current base axis, the AC power family as a specialization lattice
    (R2) carrying three different unit strings (`W`/`var`/`VA`) over one dimension, and
    — as Part 5 did with temperature — the scale-type distinction between gauge-dependent
    electric potential (interval-scale) and potential difference (ratio-scale),
    requirement R6.
  * `PropertyKindCalculus.Iso80000.Part6.DefiningRelations` — the algebraic *Remarks*
    (Ohm's law, the conductance/admittance/permeance/resistivity reciprocals, the power
    product, the power factor) as R12 kind-laws, the electric-current law composing a
    Part-6 kind out of an ISO 80000-3 (time) kind.
  * `PropertyKindCalculus.Iso80000.Part7` — the full catalogue of ISO 80000-7 *Light and
    radiation* (all of items 7-1.1 … 7-37): the radiant / luminous / photon trios as
    distinct kinds individuated by *radiation mode* (R2), the candela and the mole handled
    by the Finkelstein–Whitehead *scale-spanning* reduction (R13, see `ScaleSpanning`) so
    that luminous flux ≡ radiant flux in dimension yet not in kind, and the widest
    dimension-one family in the series.
  * `PropertyKindCalculus.Iso80000.Part7.DefiningRelations` — the algebraic *Remarks*
    (radiant and photon flux as time-derivatives, irradiance and radiant intensity as
    area- and solid-angle-densities, the luminous efficacy as a flux ratio) as R12
    kind-laws, several composing a Part-7 kind out of ISO 80000-3 (time, area, solid
    angle) kinds.
  * `PropertyKindCalculus.Iso80000.Part8` (+ `.DefiningRelations`) — the full catalogue of
    ISO 80000-8 *Acoustics* (all 18 of items 8-1 … 8-17): the logarithmic *levels* collapse
    to dimension one (the acoustic face of R1), a genuine collision (sound pressure ≡ sound
    energy density, `M·L⁻¹·T⁻²`), and the boundary case where the dimension *does*
    discriminate (the two homonymous impedances); sound intensity is `p·u` as a kind-law.
  * `PropertyKindCalculus.Iso80000.Part9` (+ `.DefiningRelations`) — the full catalogue of
    ISO 80000-9 *Physical chemistry and molecular physics* (all 62 of items 9-1 … 9-49):
    the sharpest test of the *scale-spanning* mole reduction (R13) — molar mass *is* a mass,
    amount concentration *a number density* — the seven-fold `J/mol` collision, and a second
    dimension-one family; the molar quantities as `X/n` kind-laws crossing to ISO 80000-3/4/5.
  * `PropertyKindCalculus.Iso80000.Part10` (+ `.DefiningRelations`) — the full catalogue of
    ISO 80000-10 *Atomic and nuclear physics* (all 125 of items 10-1.1 … 10-89): the
    standard's own two-name disambiguation of one dimension — the gray and the sievert (both
    `J/kg`, `L²·T⁻²`) — the becquerel collision (`T⁻¹`), and the widest dimension-one family
    in the physical parts; dose equivalent is `D·Q` as a kind-law.
  * `PropertyKindCalculus.Iso80000.Part11` — the full catalogue of ISO 80000-11
    *Characteristic numbers* (all 115 of items 11-4.1 … 11-9.2): the part where R1 is
    total — *every* characteristic number is dimension one, so the dimension functor
    collapses the entire part to a single point, and the 115 kinds are held apart entirely
    by their *measurement principle* (R2). It carries the widest set of sub-suffixed
    homonyms in the series (the two Froude numbers, the five Stokes numbers, the four Bejan
    numbers, …), each a distinct kind sharing a name. With parts 8, 9, and 12 now mapped,
    its `workToGoParts` list is empty — every part it references is specified
    (`referencedParts_all_specified`).
  * `PropertyKindCalculus.Iso80000.Part12` (+ `.DefiningRelations`) — the full catalogue of
    ISO 80000-12 *Condensed matter physics* (all 60 of items 12-1.1 … 12-38.2): the part
    where collisions are the rule — thirteen lengths, seven energies, five (named)
    temperatures, five carrier densities, five reciprocal lengths — each family one
    dimension; the Seebeck and Peltier coefficients as kind-laws crossing to ISO 80000-5.
  * `PropertyKindCalculus.Iso80000.Part13` (+ `.DefiningRelations`) — the full catalogue of
    IEC 80000-13 *Information science and technology* (all 42 of items 13-1 … 13-42), the
    second IEC-published part: dimension one shared by distinct kinds with incommensurable
    *scale-spanning* special units (the shannon, the erlang, the bit; R13), the rates
    re-dimensioning to `T⁻¹`, and the signal energy `P_c·T_bit` as a kind-law.

This library is PhysLib-backed (its quantity-kinds carry PhysLib `Dimension`s); the
references catalogue alone is Mathlib-free.
-/

module

public import PropertyKindCalculus.Iso80000.References
public import PropertyKindCalculus.Iso80000.Catalogue
public import PropertyKindCalculus.Iso80000.Part1
public import PropertyKindCalculus.Iso80000.Part2
public import PropertyKindCalculus.Iso80000.Part3
public import PropertyKindCalculus.Iso80000.Part3.AreaElement
public import PropertyKindCalculus.Iso80000.Part3.AreaClassification
public import PropertyKindCalculus.Iso80000.Part3.VolumeElement
public import PropertyKindCalculus.Iso80000.Part3.DefiningRelations
public import PropertyKindCalculus.Iso80000.Part4
public import PropertyKindCalculus.Iso80000.Part4.DefiningRelations
public import PropertyKindCalculus.Iso80000.Part5
public import PropertyKindCalculus.Iso80000.Part5.DefiningRelations
public import PropertyKindCalculus.Iso80000.Part6
public import PropertyKindCalculus.Iso80000.Part6.DefiningRelations
public import PropertyKindCalculus.Iso80000.Part7
public import PropertyKindCalculus.Iso80000.Part7.DefiningRelations
public import PropertyKindCalculus.Iso80000.Part8
public import PropertyKindCalculus.Iso80000.Part8.DefiningRelations
public import PropertyKindCalculus.Iso80000.Part9
public import PropertyKindCalculus.Iso80000.Part9.DefiningRelations
public import PropertyKindCalculus.Iso80000.Part10
public import PropertyKindCalculus.Iso80000.Part10.DefiningRelations
public import PropertyKindCalculus.Iso80000.Part11
public import PropertyKindCalculus.Iso80000.Part12
public import PropertyKindCalculus.Iso80000.Part12.DefiningRelations
public import PropertyKindCalculus.Iso80000.Part13
public import PropertyKindCalculus.Iso80000.Part13.DefiningRelations
public import PropertyKindCalculus.Iso80000.IsqLift

@[expose] public section Blanket



end Blanket
