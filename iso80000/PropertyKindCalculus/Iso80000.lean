/-
# PropertyKindCalculus.Iso80000

The standards-grounded layer: quantity-kinds (QK) and units (U) organized to
mirror the **ISO/IEC 80000** *Quantities and units* series, each citing its source
by name and version only (no normative content is reproduced — the standards are
licensed and copyrighted).

  * `PropertyKindCalculus.Iso80000.References` — the citation catalogue: one
    `StandardRef` per licensed part (ISO/IEC 80000-1 … -12).
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

This library is PhysLib-backed (its quantity-kinds carry PhysLib `Dimension`s); the
references catalogue alone is Mathlib-free.
-/

import PropertyKindCalculus.Iso80000.References
import PropertyKindCalculus.Iso80000.Part3
import PropertyKindCalculus.Iso80000.Part3.AreaElement
import PropertyKindCalculus.Iso80000.Part3.AreaClassification
import PropertyKindCalculus.Iso80000.Part3.VolumeElement
import PropertyKindCalculus.Iso80000.Part3.DefiningRelations
import PropertyKindCalculus.Iso80000.Part4
import PropertyKindCalculus.Iso80000.Part4.DefiningRelations
import PropertyKindCalculus.Iso80000.Part5
import PropertyKindCalculus.Iso80000.Part5.DefiningRelations
import PropertyKindCalculus.Iso80000.Part6
import PropertyKindCalculus.Iso80000.Part6.DefiningRelations
import PropertyKindCalculus.Iso80000.Part7
import PropertyKindCalculus.Iso80000.Part7.DefiningRelations
