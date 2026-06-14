/-
# ISO 80000-3 — Space and time (seed)

A first, reviewable slice of the standards-grounded catalogue: a few
quantity-kinds (QK) and units (U) from ISO 80000-3 *Space and time*, each carrying
its exact source as data — the part (`iso80000_3`), the item designation, and the
principal symbol. Only **citation locators** are recorded (item number, symbol,
coherent SI unit); no normative content from the licensed standard is reproduced.

The dimensioned kinds reuse the {dimension functor} `dim` and PhysLib's
`Dimension`, so the standard's dimensional facts (area is `L²`, speed is `L·T⁻¹`)
are *checked computations*, not annotations. `displacement` is catalogued as a
**vector** quantity-kind (item 3-1.11): the vector-ness lives in the numeric
*carrier* of a `Quantity` (a numerical vector), while the kind and its single
scalar unit are carried here — the ISO 80000-2 §18 reading exercised in the
examples.

This is the pattern to review before extending to the other parts.
-/

import PropertyKindCalculus.Dimension
import PropertyKindCalculus.Iso80000.References

namespace PropertyKindCalculus.Iso80000.Part3

open PropertyKindCalculus

/-- The part of the series this module catalogues. -/
def source : StandardRef := iso80000_3

/-- A **catalogued quantity-kind**: a {dimensioned kind} together with its exact
source in the 80000 series (part + item designation + principal symbol). The
citation is *data*, so a downstream model can render or audit it. -/
structure CataloguedKind where
  /-- The part of the series this kind is defined in. -/
  ref : StandardRef
  /-- The item designation as printed, e.g. "3-1.1". -/
  item : String
  /-- The principal quantity symbol, e.g. "l". -/
  symbol : String
  /-- The dimensioned kind itself. -/
  qk : DimensionedKind

/-- The standard citation for a catalogued kind, e.g.
`ISO 80000-3, Second edition, 2019-10 item 3-1.1`. -/
def CataloguedKind.cite (c : CataloguedKind) : String :=
  c.ref.cite ++ " item " ++ c.item

/-! ## Quantity-kinds (a few, from ISO 80000-3) -/

/-- Length — item 3-1.1, dimension `L`. -/
def length : DimensionedKind :=
  { kind := { id := "length", scale := .ratio }, dim := Dim.length }

/-- Duration (time) — item 3-9.1, dimension `T`. -/
def time : DimensionedKind :=
  { kind := { id := "time", scale := .ratio }, dim := Dim.time }

/-- Area — item 3-2.1, dimension `L²`. -/
def area : DimensionedKind :=
  { kind := { id := "area", scale := .ratio }, dim := Dim.area }

/-- Volume — item 3-3.1, dimension `L³`. -/
def volume : DimensionedKind :=
  { kind := { id := "volume", scale := .ratio }, dim := Dim.area * Dim.length }

/-- Speed — item 3-10.2, dimension `L·T⁻¹`. -/
def speed : DimensionedKind :=
  { kind := { id := "speed", scale := .ratio }, dim := Dim.speed }

/-- Displacement — item 3-1.11, a **vector** quantity of dimension `L`. The kind
and its scalar unit are scalar data; the numerical vector is the carrier of a
`Quantity displacement.kind (Fin 3 → R)` (ISO 80000-2 §18). -/
def displacement : DimensionedKind :=
  { kind := { id := "displacement", scale := .ratio }, dim := Dim.length }

/-! ## The same kinds, as catalogued (citation carried as data) -/

/-- Length, catalogued at ISO 80000-3 item 3-1.1 (symbol `l`). -/
def lengthCK : CataloguedKind := { ref := source, item := "3-1.1", symbol := "l", qk := length }
/-- Duration, catalogued at item 3-9.1 (symbol `t`). -/
def timeCK : CataloguedKind := { ref := source, item := "3-9.1", symbol := "t", qk := time }
/-- Area, catalogued at item 3-2.1 (symbol `A`). -/
def areaCK : CataloguedKind := { ref := source, item := "3-2.1", symbol := "A", qk := area }
/-- Volume, catalogued at item 3-3.1 (symbol `V`). -/
def volumeCK : CataloguedKind := { ref := source, item := "3-3.1", symbol := "V", qk := volume }
/-- Speed, catalogued at item 3-10.2 (symbol `v`). -/
def speedCK : CataloguedKind := { ref := source, item := "3-10.2", symbol := "v", qk := speed }
/-- Displacement, catalogued at item 3-1.11 (the vector quantity). -/
def displacementCK : CataloguedKind :=
  { ref := source, item := "3-1.11", symbol := "Δr", qk := displacement }

/-! ## Units (a few coherent SI units of these kinds) -/

/-- The metre, the SI unit of length (item 3-1.1). -/
def metre : MetrologicalUnit := length.kind.unit "m"
/-- The centimetre as a **prefixed unit** (VIM4 §1.21): the `centi` submultiple of
the metre. Its symbol `"cm"` and its conversion factor (`10⁻²`) follow from the
prefix and the base, rather than being asserted independently. -/
def centimetrePrefixed : PrefixedUnit := metre.withPrefix SIPrefix.centi
/-- The centimetre, another unit of length — the projection of `centimetrePrefixed`
to a plain `MetrologicalUnit`, so it stays commensurable with the metre. -/
def centimetre : MetrologicalUnit := centimetrePrefixed.toUnit
/-- The second, the SI unit of duration (item 3-9.1). -/
def second : MetrologicalUnit := time.kind.unit "s"
/-- The square metre, the SI unit of area (item 3-2.1). -/
def squareMetre : MetrologicalUnit := area.kind.unit "m²"
/-- The cubic metre, the SI unit of volume (item 3-3.1). -/
def cubicMetre : MetrologicalUnit := volume.kind.unit "m³"
/-- The metre per second, the SI unit of speed (item 3-10.2). -/
def metrePerSecond : MetrologicalUnit := speed.kind.unit "m/s"

/-! ## Checked facts (the dimensional algebra and unit well-formedness) -/

/-- Length carries the length dimension `L`. -/
theorem length_dim : length.dim = Dim.length := rfl

/-- Area carries `L²`: its length-exponent is `2` — a checked computation in
PhysLib's group, matching ISO 80000-3 item 3-2.1. -/
theorem area_dim_length : area.dim.length = 2 := Dim.area_length

/-- Speed is length over time (`L·T⁻¹`), ISO 80000-3 item 3-10.2. -/
theorem speed_dim : speed.dim = Dim.length / Dim.time := Dim.speed_eq

/-- The metre is a well-formed metrological unit: length is a rational kind, so it
bears a unit (Dybkær §13.3.5). -/
theorem metre_wellFormed : metre.WellFormed :=
  KindOfProperty.rational_bears_unit rfl

/-- The metre and the centimetre are commensurable — both reference `length`. The
prefix leaves the kind unchanged, so this still holds for the prefixed centimetre. -/
theorem metre_centimetre_commensurable : metre.Commensurable centimetre :=
  centimetrePrefixed.commensurable_base

/-- The centimetre's symbol is `"cm"` — composed from the prefix symbol `"c"` and the
base symbol `"m"`, not asserted independently (VIM4 §1.19). -/
theorem centimetre_symbol : centimetre.symbol = "cm" := rfl

/-- The centimetre is a **submultiple** of the metre with conversion factor `10⁻²`:
`1 cm = 10⁻² m` (VIM4 §1.21 / §1.22). The exponent is a checked computation. -/
theorem centimetre_conversionExponent : centimetrePrefixed.conversionExponent = -2 := rfl

/-- The centimetre is a decimal *submultiple* of the metre (VIM4 §1.21). -/
theorem centimetre_isSubmultiple : centimetrePrefixed.IsSubmultiple := by
  unfold PrefixedUnit.IsSubmultiple
  decide

/-- The centimetre, being a prefixing of a well-formed base unit, is itself a
well-formed metrological unit (the kind is unchanged by the prefix). -/
theorem centimetre_wellFormed : centimetre.WellFormed :=
  centimetrePrefixed.toUnit_wellFormed metre_wellFormed

/-- The metre and the second are **not** commensurable — length and time are
distinct kinds (a type-level fact, not a runtime check). -/
theorem metre_second_not_commensurable : ¬ metre.Commensurable second := by
  unfold MetrologicalUnit.Commensurable metre second length time KindOfProperty.unit
  decide

/-- Length and time are distinct kinds. -/
theorem length_kind_ne_time_kind : length.kind ≠ time.kind := by
  unfold length time
  decide

end PropertyKindCalculus.Iso80000.Part3
