/-
# Unit prefixes — decimal multiples and submultiples (VIM4 2CD §1.19–1.22)

A *prefix* turns a unit into another unit of the **same kind** that differs from it
only by a decimal factor. The VIM4 2CD (2023-07-31) grounds the four notions used
here:

  * **§1.19 NOTE 5** — the SI prefixes: a table of `factor → name → symbol`, where
    every factor is a power of ten (kilo = `10³`, centi = `10⁻²`, …). Sourced from
    the SI Brochure.
  * **§1.20 multiple of a unit** — "measurement unit obtained by multiplying a given
    measurement unit by an integer greater than one" (e.g. the kilometre).
  * **§1.21 submultiple of a unit** — "measurement unit obtained by dividing a given
    measurement unit by an integer greater than one" (e.g. the millimetre).
  * **§1.22 conversion factor between units** — "ratio of two measurement units for
    quantities of the same kind" (e.g. `km/m = 1000`).

The design follows the metrological-unit layer (`Unit.lean`) rather than editing it:
a `PrefixedUnit` carries its *provenance* — which `SIPrefix` was applied to which
base `MetrologicalUnit` — and **projects** to a `MetrologicalUnit` via `toUnit`. So
every fact about ordinary units (commensurability, well-formedness, the §13.3.3
round-trip) transfers to the projection unchanged, while the provenance lets us add
what a bare unit cannot state: the §1.22 conversion factor, and whether the result
is a §1.20 multiple or a §1.21 submultiple.

The conversion factor is kept as its *exponent* (an `Int`), so all arithmetic stays
exact and Mathlib-free; turning the exponent into a numeric magnitude (1 cm = 10⁻² m
as a number) belongs to the real-carrier `Quantity` layer, not here.
-/

import PropertyKindCalculus.Unit

namespace PropertyKindCalculus

/-- **§1.19 NOTE 5 — an SI prefix.** A decimal factor `10 ^ exponent` used to form a
multiple (§1.20) or submultiple (§1.21) of a unit, carried with its name and symbol.
For example `centi` is `(name := "centi", symbol := "c", exponent := -2)`. -/
structure SIPrefix where
  /-- The prefix name, e.g. `"centi"`. -/
  name : String
  /-- The prefix symbol, prepended to the base unit symbol, e.g. `"c"`. -/
  symbol : String
  /-- The power of ten: the factor is `10 ^ exponent` (centi = `-2`, kilo = `3`). -/
  exponent : Int
deriving DecidableEq, Repr

namespace SIPrefix

/-! ## The SI prefixes (VIM4 §1.19 NOTE 5; SI Brochure)

The decimal prefixes, as data. These are general SI facts (factor, name, symbol),
not normative content of any ISO 80000 part. -/

/-- quetta — `10³⁰`. -/
def quetta : SIPrefix := { name := "quetta", symbol := "Q",  exponent := 30 }
/-- ronna — `10²⁷`. -/
def ronna  : SIPrefix := { name := "ronna",  symbol := "R",  exponent := 27 }
/-- yotta — `10²⁴`. -/
def yotta  : SIPrefix := { name := "yotta",  symbol := "Y",  exponent := 24 }
/-- zetta — `10²¹`. -/
def zetta  : SIPrefix := { name := "zetta",  symbol := "Z",  exponent := 21 }
/-- exa — `10¹⁸`. -/
def exa    : SIPrefix := { name := "exa",    symbol := "E",  exponent := 18 }
/-- peta — `10¹⁵`. -/
def peta   : SIPrefix := { name := "peta",   symbol := "P",  exponent := 15 }
/-- tera — `10¹²`. -/
def tera   : SIPrefix := { name := "tera",   symbol := "T",  exponent := 12 }
/-- giga — `10⁹`. -/
def giga   : SIPrefix := { name := "giga",   symbol := "G",  exponent := 9 }
/-- mega — `10⁶`. -/
def mega   : SIPrefix := { name := "mega",   symbol := "M",  exponent := 6 }
/-- kilo — `10³`. -/
def kilo   : SIPrefix := { name := "kilo",   symbol := "k",  exponent := 3 }
/-- hecto — `10²`. -/
def hecto  : SIPrefix := { name := "hecto",  symbol := "h",  exponent := 2 }
/-- deca — `10¹`. -/
def deca   : SIPrefix := { name := "deca",   symbol := "da", exponent := 1 }
/-- deci — `10⁻¹`. -/
def deci   : SIPrefix := { name := "deci",   symbol := "d",  exponent := -1 }
/-- centi — `10⁻²`. -/
def centi  : SIPrefix := { name := "centi",  symbol := "c",  exponent := -2 }
/-- milli — `10⁻³`. -/
def milli  : SIPrefix := { name := "milli",  symbol := "m",  exponent := -3 }
/-- micro — `10⁻⁶`. -/
def micro  : SIPrefix := { name := "micro",  symbol := "µ",  exponent := -6 }
/-- nano — `10⁻⁹`. -/
def nano   : SIPrefix := { name := "nano",   symbol := "n",  exponent := -9 }
/-- pico — `10⁻¹²`. -/
def pico   : SIPrefix := { name := "pico",   symbol := "p",  exponent := -12 }
/-- femto — `10⁻¹⁵`. -/
def femto  : SIPrefix := { name := "femto",  symbol := "f",  exponent := -15 }
/-- atto — `10⁻¹⁸`. -/
def atto   : SIPrefix := { name := "atto",   symbol := "a",  exponent := -18 }
/-- zepto — `10⁻²¹`. -/
def zepto  : SIPrefix := { name := "zepto",  symbol := "z",  exponent := -21 }
/-- yocto — `10⁻²⁴`. -/
def yocto  : SIPrefix := { name := "yocto",  symbol := "y",  exponent := -24 }
/-- ronto — `10⁻²⁷`. -/
def ronto  : SIPrefix := { name := "ronto",  symbol := "r",  exponent := -27 }
/-- quecto — `10⁻³⁰`. -/
def quecto : SIPrefix := { name := "quecto", symbol := "q",  exponent := -30 }

/-- The SI prefixes in descending order of factor (VIM4 §1.19 NOTE 5). -/
def all : List SIPrefix :=
  [quetta, ronna, yotta, zetta, exa, peta, tera, giga, mega, kilo, hecto, deca,
   deci, centi, milli, micro, nano, pico, femto, atto, zepto, yocto, ronto, quecto]

end SIPrefix

/-- **§1.20 / §1.21 — a prefixed unit.** A `MetrologicalUnit` formed by applying an
`SIPrefix` to a base unit: a decimal multiple (`exponent > 0`) or submultiple
(`exponent < 0`) of the same kind. The provenance — the prefix and the base — is
carried as data so the §1.22 conversion factor can be read off. -/
structure PrefixedUnit where
  /-- The prefix applied (named `siPrefix` because `prefix` is a Lean keyword). -/
  siPrefix : SIPrefix
  /-- The base unit the prefix is applied to. -/
  base : MetrologicalUnit
deriving DecidableEq, Repr

namespace PrefixedUnit

/-- The prefixed unit as an ordinary `MetrologicalUnit`: the **same kind** as the
base, with the prefix symbol prepended (e.g. `"c" ++ "m" = "cm"`). Projecting here
means every fact about units (commensurability, well-formedness, the §13.3.3
round-trip) applies to a prefixed unit unchanged. -/
def toUnit (p : PrefixedUnit) : MetrologicalUnit :=
  { kind := p.base.kind, symbol := p.siPrefix.symbol ++ p.base.symbol }

@[simp] theorem toUnit_kind (p : PrefixedUnit) : p.toUnit.kind = p.base.kind := rfl

@[simp] theorem toUnit_symbol (p : PrefixedUnit) :
    p.toUnit.symbol = p.siPrefix.symbol ++ p.base.symbol := rfl

/-- **§1.22 — the conversion factor as an exponent.** `1` of the prefixed unit equals
`10 ^ conversionExponent` of the base unit (e.g. centimetre → metre gives `-2`). -/
def conversionExponent (p : PrefixedUnit) : Int := p.siPrefix.exponent

/-- **§1.20 — a (decimal) multiple of a unit**: the prefix factor exceeds one. -/
def IsMultiple (p : PrefixedUnit) : Prop := p.siPrefix.exponent > 0

/-- **§1.21 — a (decimal) submultiple of a unit**: the prefix factor is below one. -/
def IsSubmultiple (p : PrefixedUnit) : Prop := p.siPrefix.exponent < 0

/-- A prefixed unit is **commensurable** with its base — they reference the same kind
(§1.22 "quantities of the same kind"; §9.13.4). -/
theorem commensurable_base (p : PrefixedUnit) : p.toUnit.Commensurable p.base := rfl

/-- Two prefixings of the **same** base are commensurable with each other: a
centimetre and a kilometre are both lengths. -/
theorem commensurable_of_eq_base {p q : PrefixedUnit} (h : p.base = q.base) :
    p.toUnit.Commensurable q.toUnit := by
  unfold MetrologicalUnit.Commensurable
  simp [toUnit, h]

/-- **Well-formedness transfers from the base.** A prefixed unit of a unitary kind is
itself well-formed — the kind is unchanged by the prefix (§13.3.3). -/
theorem toUnit_wellFormed {p : PrefixedUnit} (h : p.base.WellFormed) :
    p.toUnit.WellFormed := h

end PrefixedUnit

/-- **§1.20 / §1.21 — apply a prefix to a unit.** The ergonomic constructor:
`metre.withPrefix SIPrefix.centi` is the centimetre (as a `PrefixedUnit`); take
`.toUnit` for the plain unit. -/
def MetrologicalUnit.withPrefix (u : MetrologicalUnit) (p : SIPrefix) : PrefixedUnit :=
  { siPrefix := p, base := u }

@[simp] theorem MetrologicalUnit.withPrefix_base (u : MetrologicalUnit) (p : SIPrefix) :
    (u.withPrefix p).base = u := rfl

@[simp] theorem MetrologicalUnit.withPrefix_siPrefix (u : MetrologicalUnit) (p : SIPrefix) :
    (u.withPrefix p).siPrefix = p := rfl

end PropertyKindCalculus
