/-
# The shared catalogue scaffolding for the ISO/IEC 80000 parts

Every part module (`Part3` … `Part13`) catalogues its quantity-kinds with the same
three pieces of infrastructure: the `CataloguedKind` record that pairs a
{dimensioned kind} with its citation locators, the `cite` renderer, and the
`dimKind` builder for a ratio-scale dimensioned kind. They are defined **once
here**, in the shared `PropertyKindCalculus.Iso80000` namespace, so that each part
reuses one common definition rather than restating it. Only the part-specific data
— the `source` reference and the `catalogue` list — lives in the part modules.

This module is PhysLib-backed (a `CataloguedKind` carries a PhysLib `Dimension`
through its `qk` field); the citation catalogue (`References`) alone is Mathlib-free.
-/

import PropertyKindCalculus.Dimension
import PropertyKindCalculus.Iso80000.References

namespace PropertyKindCalculus.Iso80000

open PropertyKindCalculus

/-- A **catalogued quantity-kind**: a {dimensioned kind} together with its exact
source in the 80000 series — the part, the printed item designation, the principal
quantity symbol, and the coherent SI unit symbol. Every field other than `qk` is a
*citation locator*; the citation travels with the kind as data, so a downstream
model can render or audit the source of each definition. Shared by every part
module, so the structure is defined once rather than per part. -/
structure CataloguedKind where
  /-- The part of the series this kind is defined in. -/
  ref : StandardRef
  /-- The item designation as printed, e.g. "3-3". -/
  item : String
  /-- The principal quantity symbol, e.g. "A". -/
  symbol : String
  /-- The coherent SI unit symbol, e.g. "m²" (a citation locator). -/
  coherentUnit : String
  /-- The dimensioned kind itself. -/
  qk : DimensionedKind

/-- The standard citation for a catalogued kind, e.g.
`ISO 80000-3, Second edition, 2019-10 item 3-3`. -/
def CataloguedKind.cite (c : CataloguedKind) : String :=
  c.ref.cite ++ " item " ++ c.item

/-- Build a catalogued kind from an explicit part reference and its locators. Each
part module wraps this with its own `cat`, fixing `ref` to the part's `source`. -/
def CataloguedKind.of (ref : StandardRef) (item symbol coherentUnit : String)
    (qk : DimensionedKind) : CataloguedKind :=
  { ref := ref, item := item, symbol := symbol, coherentUnit := coherentUnit, qk := qk }

/-- A ratio-scale dimensioned kind with a plain `id` and a given dimension. -/
def dimKind (id : String) (dim : Dimension LTMCTDimensionBase) : DimensionedKind :=
  { kind := { id := id, scale := .ratio }, dim := dim }

/-! ## Rendering a `Dimension` to its printed expression

The blueprint item-index tables print each kind's dimension (e.g. `L⁻¹`,
`M·L²·T⁻²`). Rather than transcribe those strings by hand — which had drifted into
inconsistent factor orderings — they are *computed* from the PhysLib `Dimension`
of each catalogued kind via `renderDimension`.

The kinds are dimensioned over PhysLib's *charge*-based `LTMCTDimensionBase`, but ISO 80000
tabulates electromagnetic dimensions over the ISQ base quantity electric *current* `I`.
For citation fidelity the renderer re-expresses the electromagnetic axis in current: since
the coulomb is the ampere-second, `C = I·T`, a charge factor with exponent `q` reads as
`Iq·Tq`, so the printed current exponent is the charge exponent and the printed time
exponent absorbs it.
The order is thus the ISQ order M·L·T·I·Θ (mass, length, time, current, temperature) — for
a charge-free quantity (`I`-exponent 0) this is exactly the mechanical `M·L·T·Θ`.
Dimension one renders as `1`. -/

/-- A natural number as Unicode superscript digits, e.g. `12 ↦ "¹²"`. -/
private def supDigits (n : Nat) : String :=
  (toString n).map fun c =>
    match c with
    | '0' => '⁰' | '1' => '¹' | '2' => '²' | '3' => '³' | '4' => '⁴'
    | '5' => '⁵' | '6' => '⁶' | '7' => '⁷' | '8' => '⁸' | '9' => '⁹' | c => c

/-- An integer exponent as a Unicode superscript, e.g. `-2 ↦ "⁻²"`. -/
private def supInt (z : Int) : String :=
  if z < 0 then "⁻" ++ supDigits z.natAbs else supDigits z.natAbs

/-- One base-dimension factor `symbol^exp`: `none` when the exponent is zero, the
bare symbol when it is one, `symbol⁻¹`/`symbol²`/… otherwise. A non-integer
exponent (none occur in the 80000 catalogue) falls back to `symbol^(p/q)`. -/
private def dimFactor (symbol : String) (q : ℚ) : Option String :=
  if q == 0 then none
  else if q.den == 1 then
    if q.num == 1 then some symbol else some (symbol ++ supInt q.num)
  else some (symbol ++ "^(" ++ toString q.num ++ "/" ++ toString q.den ++ ")")

/-- The printed dimension expression in the ISQ base-quantity order M·L·T·I·Θ (mass,
length, time, electric current, temperature); `1` for the dimensionless (unit-one)
dimension. The electromagnetic axis is re-expressed from PhysLib's internal charge
generator into the ISQ base quantity current via `C = I·T`: the current exponent is the
charge exponent, and the time exponent absorbs the charge exponent. -/
def renderDimension (d : Dimension LTMCTDimensionBase) : String :=
  let currentExp := d.charge
  let timeExp := d.time + d.charge
  let factors := [dimFactor "M" d.mass, dimFactor "L" d.length, dimFactor "T" timeExp,
      dimFactor "I" currentExp, dimFactor "Θ" d.temperature].filterMap id
  if factors.isEmpty then "1" else String.intercalate "·" factors

/-- The printed dimension expression of a catalogued kind (see `renderDimension`). -/
def CataloguedKind.dimString (c : CataloguedKind) : String :=
  renderDimension c.qk.dim
