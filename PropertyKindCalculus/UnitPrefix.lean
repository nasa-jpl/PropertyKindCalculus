/-
# Unit prefixes — decimal and binary multiples (VIM4 §1.19–1.22, IEC 80000-13)

A *prefix* turns a unit into another unit of the **same kind** that differs from it
only by a fixed factor — a power of ten (SI) or a power of two (binary). The VIM4 2CD
(2023-07-31) grounds the four decimal notions, and IEC 80000-13 the binary ones:

  * **§1.19 NOTE 5** — the SI prefixes: a table of `factor → name → symbol`, where
    every factor is a power of ten (kilo = `10³`, centi = `10⁻²`, …). Sourced from
    the SI Brochure.
  * **§1.20 multiple of a unit** — "measurement unit obtained by multiplying a given
    measurement unit by an integer greater than one" (e.g. the kilometre).
  * **§1.21 submultiple of a unit** — "measurement unit obtained by dividing a given
    measurement unit by an integer greater than one" (e.g. the millimetre).
  * **§1.22 conversion factor between units** — "ratio of two measurement units for
    quantities of the same kind" (e.g. `km/m = 1000`).
  * **IEC 80000-13** — the *binary* prefixes (kibi = `2¹⁰`, mebi = `2²⁰`, …), for
    information quantities; a distinct standard artifact from the decimal SI prefixes,
    modeled as a distinct `BinaryPrefix` type.

The design follows the metrological-unit layer (`Unit.lean`) rather than editing it:
a `PrefixedUnit` carries its *provenance* in resolved form — the numeric `radix` (10
or 2), the power-of-radix `exponent`, and the prefix `symbol` — and **projects** to a
`MetrologicalUnit` via `toUnit`. So every fact about ordinary units (commensurability,
well-formedness, the §13.3.3 round-trip) transfers to the projection unchanged, while
the provenance lets us add what a bare unit cannot state: the §1.22 conversion factor,
and whether the result is a §1.20 multiple or a §1.21 submultiple. Recording the radix
lets the *same* prefixed unit and conversion round-trip serve both prefix families,
gated to a common radix.

The conversion factor is kept as its *exponent* (an `Int`), so all arithmetic stays
exact and Mathlib-free; turning the exponent into a numeric magnitude (1 cm = 10⁻² m
as a number) belongs to the real-carrier `Quantity` layer, not here.
-/

module

public import PropertyKindCalculus.Unit

public section -- pkc-blanket
@[expose] section -- pkc-blanket-expose

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

/-- **IEC 80000-13 — a prefix for binary multiples.** The information-technology
counterpart of an SI prefix, scaling by a power of *two* rather than ten: kibi
`= 2¹⁰`, mebi `= 2²⁰`, gibi `= 2³⁰`, …. IEC 80000-13 (*Information science and
technology*, Ed. 2.0, 2025-02) introduced these precisely to remove the "kilobyte"
ambiguity between `10³` and `2¹⁰` bytes — `kibi` names the binary one unambiguously.
These are **not** SI prefixes (the SI is decimal-only), which is why they are a
separate type; but they form multiples/submultiples and bear a §1.22 conversion
factor exactly as SI prefixes do — the two share the same prefixed-unit machinery. -/
structure BinaryPrefix where
  /-- The prefix name, e.g. `"kibi"`. -/
  name : String
  /-- The prefix symbol, prepended to the base unit symbol, e.g. `"Ki"`. -/
  symbol : String
  /-- The power of two: the factor is `2 ^ exponent` (kibi = `10`, mebi = `20`). -/
  exponent : Int
deriving DecidableEq, Repr

namespace BinaryPrefix

/-- The eight IEC 80000-13 binary prefixes, as data (name, symbol, power of two). -/
def kibi : BinaryPrefix := { name := "kibi", symbol := "Ki", exponent := 10 }
def mebi : BinaryPrefix := { name := "mebi", symbol := "Mi", exponent := 20 }
def gibi : BinaryPrefix := { name := "gibi", symbol := "Gi", exponent := 30 }
def tebi : BinaryPrefix := { name := "tebi", symbol := "Ti", exponent := 40 }
def pebi : BinaryPrefix := { name := "pebi", symbol := "Pi", exponent := 50 }
def exbi : BinaryPrefix := { name := "exbi", symbol := "Ei", exponent := 60 }
def zebi : BinaryPrefix := { name := "zebi", symbol := "Zi", exponent := 70 }
def yobi : BinaryPrefix := { name := "yobi", symbol := "Yi", exponent := 80 }

/-- The binary prefixes in ascending order of factor (IEC 80000-13). -/
def all : List BinaryPrefix := [kibi, mebi, gibi, tebi, pebi, exbi, zebi, yobi]

end BinaryPrefix

/-- **§1.20 / §1.21 — a prefixed unit.** A `MetrologicalUnit` formed by applying a
decimal (SI, §1.19) *or* binary (IEC 80000-13) prefix to a base unit: a multiple
(`exponent > 0`) or submultiple (`exponent < 0`) of the same kind. The provenance is
carried in *resolved* form — the numeric `radix` (`10` for an SI prefix, `2` for a
binary one), the power-of-radix `exponent`, and the prefix `symbol` — so that both
prefix families share one prefixed-unit and one conversion round-trip, and so
conversion can be gated to units of the *same radix* (`SameRadix`). -/
structure PrefixedUnit where
  /-- The numeric base of the prefix: `10` for an SI decimal prefix (§1.19), `2` for
  an IEC 80000-13 binary prefix. The §1.22 conversion factor is `radix ^ exponent`. -/
  radix : Nat
  /-- The power: `1` prefixed unit is `radix ^ exponent` base units (centi = `-2`,
  kilo = `3`; kibi = `10` at radix `2`). -/
  exponent : Int
  /-- The prefix symbol, prepended to the base unit symbol (`"c"`, `"k"`, `"Ki"`). -/
  symbol : String
  /-- The base unit the prefix is applied to. -/
  base : MetrologicalUnit
deriving DecidableEq, Repr

namespace PrefixedUnit

/-- The prefixed unit as an ordinary `MetrologicalUnit`: the **same kind** as the
base, with the prefix symbol prepended (e.g. `"c" ++ "m" = "cm"`). Projecting here
means every fact about units (commensurability, well-formedness, the §13.3.3
round-trip) applies to a prefixed unit unchanged. -/
def toUnit (p : PrefixedUnit) : MetrologicalUnit :=
  { kind := p.base.kind, symbol := p.symbol ++ p.base.symbol }

@[simp] theorem toUnit_kind (p : PrefixedUnit) : p.toUnit.kind = p.base.kind := rfl

@[simp] theorem toUnit_symbol (p : PrefixedUnit) :
    p.toUnit.symbol = p.symbol ++ p.base.symbol := rfl

/-- **§1.22 — the conversion factor as an exponent.** `1` of the prefixed unit equals
`radix ^ conversionExponent` of the base unit (e.g. centimetre → metre gives `-2` at
radix `10`; kibibyte → byte gives `10` at radix `2`). -/
def conversionExponent (p : PrefixedUnit) : Int := p.exponent

/-- **§1.20 — a multiple of a unit**: the prefix factor exceeds one. -/
def IsMultiple (p : PrefixedUnit) : Prop := p.exponent > 0

/-- **§1.21 — a submultiple of a unit**: the prefix factor is below one. -/
def IsSubmultiple (p : PrefixedUnit) : Prop := p.exponent < 0

/-- **Same radix** — two prefixed units scale by powers of the *same* base (both
decimal, or both binary). Conversion by an exact integer exponent is defined only
within a radix: no power of ten is a power of two, so a decimal and a binary prefix
share no exact power-of-radix factor. -/
def SameRadix (p q : PrefixedUnit) : Prop := p.radix = q.radix

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

/-! ## §1.22 — unit conversion is a faithful round-trip -/

/-- **§1.22 — the conversion shift from `p` to `q`**, as a power-of-*radix* exponent:
a magnitude reading `mantissa × radix ^ d` in `p`-units reads
`mantissa × radix ^ (d + shift p q)` in `q`-units, *when `p` and `q` share a radix*
(`SameRadix`). It is the difference of the two prefix exponents (`km → cm` is
`3 - (-2) = 5`; `MiB → KiB` is `20 - 10 = 10`), so it stays an exact `Int` — a
truncating *numeric* ratio (`cm/km = 10⁻⁵` in an integer type) could not. -/
def shift (p q : PrefixedUnit) : Int := p.conversionExponent - q.conversionExponent

/-- **§1.22 — convert a magnitude's radix exponent from `p`-units to `q`-units.**
The mantissa is untouched; only the power-of-radix exponent moves, by `shift p q`. -/
def convertExp (p q : PrefixedUnit) (decExp : Int) : Int := decExp + p.shift q

/-- Converting within one unit is the identity: a unit's shift to itself is zero. -/
@[simp] theorem convertExp_self (p : PrefixedUnit) (decExp : Int) :
    p.convertExp p decExp = decExp := by
  simp only [convertExp, shift]; omega

/-- **The two §1.22 conversion factors are reciprocal.** The shift from `p` to `q`
and the shift back cancel — their power-of-radix exponents sum to zero, so the
factors multiply to `radix⁰ = 1`. The exponent-level statement that conversion is
invertible, exact over `Int`. (Base-agnostic: it holds for the stored exponents
whatever the radix; the physical reading requires `p` and `q` commensurable and of
the same radix.) -/
theorem shift_add_symm (p q : PrefixedUnit) : p.shift q + q.shift p = 0 := by
  simp only [shift]; omega

/-- **§1.22 — unit conversion is a faithful round-trip.** Converting a magnitude
from `p`-units to `q`-units and back to `p`-units recovers it *exactly*: no
information is lost, because the power-of-radix exponent is an `Int` — an element of
an additive group — and the two conversion factors are reciprocal (`shift_add_symm`).
A truncating numeric ratio (over `Int`, or a rounded `Float`) could not close this
on the nose; keeping the §1.22 factor as its integer *exponent* is exactly what makes
the round-trip exact. Holds for SI decimal and IEC 80000-13 binary prefixes alike —
one proof, since the exponent bookkeeping is blind to the radix. -/
@[simp] theorem convertExp_roundtrip (p q : PrefixedUnit) (decExp : Int) :
    q.convertExp p (p.convertExp q decExp) = decExp := by
  simp only [convertExp, shift]; omega

end PrefixedUnit

/-- **§1.20 / §1.21 — apply an SI (decimal) prefix to a unit.** The ergonomic
constructor: `metre.withPrefix SIPrefix.centi` is the centimetre (as a
`PrefixedUnit`, radix `10`); take `.toUnit` for the plain unit. -/
def MetrologicalUnit.withPrefix (u : MetrologicalUnit) (p : SIPrefix) : PrefixedUnit :=
  { radix := 10, exponent := p.exponent, symbol := p.symbol, base := u }

/-- **IEC 80000-13 — apply a binary prefix to a unit.** `byte.withBinaryPrefix
BinaryPrefix.kibi` is the kibibyte (a `PrefixedUnit`, radix `2`). Same prefixed-unit
type as `withPrefix`, so all the conversion machinery applies uniformly. -/
def MetrologicalUnit.withBinaryPrefix (u : MetrologicalUnit) (p : BinaryPrefix) : PrefixedUnit :=
  { radix := 2, exponent := p.exponent, symbol := p.symbol, base := u }

@[simp] theorem MetrologicalUnit.withPrefix_base (u : MetrologicalUnit) (p : SIPrefix) :
    (u.withPrefix p).base = u := rfl

@[simp] theorem MetrologicalUnit.withPrefix_radix (u : MetrologicalUnit) (p : SIPrefix) :
    (u.withPrefix p).radix = 10 := rfl

@[simp] theorem MetrologicalUnit.withBinaryPrefix_base (u : MetrologicalUnit) (p : BinaryPrefix) :
    (u.withBinaryPrefix p).base = u := rfl

@[simp] theorem MetrologicalUnit.withBinaryPrefix_radix (u : MetrologicalUnit) (p : BinaryPrefix) :
    (u.withBinaryPrefix p).radix = 2 := rfl

end PropertyKindCalculus

end -- pkc-blanket-expose
end -- pkc-blanket
