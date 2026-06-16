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
def dimKind (id : String) (dim : Dimension) : DimensionedKind :=
  { kind := { id := id, scale := .ratio }, dim := dim }
