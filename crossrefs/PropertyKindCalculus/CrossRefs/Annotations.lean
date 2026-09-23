/-
# Cross-reference annotations — applied from afar

This module attaches the `@[dybkaer …]` and `@[vim4 …]` attributes to the
declarations of the core spine, using the standalone `attribute [..] decl`
command. The locators promoted here are exactly the ones already recorded, as
free text, in each declaration's own docstring — this module makes them typed,
decl-indexed, and auditable, without editing (or adding any `import`s to) the
Mathlib-free, prelude-only spine.

Several declarations carry *both* a Dybkær and a VIM 4 2CD locus (the examination
trio, the metrological unit, the same-kind relation); those appear in both index
tables, which is precisely the cross-reference value.

Only locators are carried — the external clause/section designation and term —
never any normative text from either copyrighted source.
-/

module

public import PropertyKindCalculus
meta import PropertyKindCalculus
public import PropertyKindCalculus.CrossRefs.Attributes
meta import PropertyKindCalculus.CrossRefs.Attributes

@[expose] public section Blanket

namespace PropertyKindCalculus

/-! ## Dybkær (2009) — *An Ontology on Property* -/

attribute [dybkaer "§3.3" "system"] System
attribute [dybkaer "§20" "sort of system"] SortOfSystem
attribute [dybkaer "§6.19" "kind-of-property"] KindOfProperty
attribute [dybkaer "§12" "operator-based scale types" "the four-way division, Fig. 12.21"] ScaleType
attribute [dybkaer "§20" "component"] Component
attribute [dybkaer "§20" "dedicated kind-of-property"
  "the System — Component ; kind-of-property triple (IUPAC/IFCC; the System slot names the sort)"] DedicatedKind
attribute [dybkaer "§18.12" "metrological unit"] MetrologicalUnit
attribute [dybkaer "§13.3.3" "quantity (number times reference)"] Quantity
attribute [dybkaer "§13.5.1" "unconditionally extensive unitary kind-of-quantity"
  "the value for the total equals the arithmetic sum of the values for the parts"] Extensive
attribute [dybkaer "§13.5.4" "intensive kind-of-quantity"
  "invariant with the extent of a system OF CONSTANT COMPOSITION — the clause carried as the law's hypothesis"]
  Intensive
attribute [dybkaer "§10.14" "property value scale"] ValueScale
attribute [dybkaer "§9.15" "property value"] PropertyValue
attribute [dybkaer "§6" "quantities of the same kind"] MutuallyComparable
attribute [dybkaer "§7.5" "examination principle"] ExaminationPrinciple
attribute [dybkaer "§7" "examination method" "Ch. 7"] ExaminationMethod
attribute [dybkaer "§7" "examination procedure" "Ch. 7"] ExaminationProcedure
attribute [dybkaer "§13.3.5" "product of two quantities"] ProductKind
attribute [dybkaer "§13.3.5" "quotient of two quantities"] QuotientKind
attribute [dybkaer "§13.3.5" "reciprocal of a quantity"] ReciprocalKind

/-! ## VIM 4 2CD (2023-07-31) — *International Vocabulary of Metrology* -/

attribute [vim4 "1.1" "quantity"] Quantity
attribute [vim4 "1.2" "quantities of the same kind"] MutuallyComparable
attribute [vim4 "1.3" "ratio quantity"] KindOfProperty.IsRational
attribute [vim4 "1.4" "interval quantity"] KindOfProperty.IsDifferential
attribute [vim4 "1.12" "measurement unit"] MetrologicalUnit
attribute [vim4 "1.20–1.21" "multiple / submultiple of a unit"
  "the decimal prefix factor"] SIPrefix
attribute [vim4 "1.23" "measurement scale"] ValueScale
attribute [vim4 "1.24" "value of a quantity"] PropertyValue
attribute [vim4 "1.30" "quantity equation" "realized as R12 kind-laws"] ProductKind
attribute [vim4 "1.33" "ordinal quantity"] KindOfProperty.IsOrdinal
attribute [vim4 "2.4" "measurement principle"] ExaminationPrinciple
attribute [vim4 "2.5" "measurement method"] ExaminationMethod
attribute [vim4 "2.7" "measurement procedure"] ExaminationProcedure
attribute [vim4 "2.12" "measurement model"
  "the mathematical relation among the quantities involved, attached to a declared boundary as a checked theorem edge"] Provenance.Relation
attribute [vim4 "2.13" "measurement function"
  "\"f may symbolize an algorithm\" — the four ways an implementing function may relate to its model: equals, inverts, refines, bounded by"] Provenance.RelationKind

end PropertyKindCalculus

end Blanket
