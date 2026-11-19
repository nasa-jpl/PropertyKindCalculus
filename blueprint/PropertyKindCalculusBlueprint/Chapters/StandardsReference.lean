import Verso
import VersoManual
import VersoBlueprint
-- The directive that renders the tables, and the row type they are written in.
import PropertyKindCalculusBlueprint.StandardsRefTable
-- The declarations the rows name. The directive checks each name against the
-- environment, so every library a row reaches into is imported here.
import PropertyKindCalculus
import PropertyKindCalculus.Iso80000.Part9
-- The chapters that define the blueprint nodes the rows link to.
import PropertyKindCalculusBlueprint.Chapters.Spine
import PropertyKindCalculusBlueprint.Chapters.Units
import PropertyKindCalculusBlueprint.Chapters.Foundations

open Verso.Genre
open Verso.Genre.Manual
open Informal
open PropertyKindCalculusBlueprint.StandardsRef

namespace PropertyKindCalculusBlueprint.Chapters.StandardsReference

/-- No corresponding term in the source. -/
def none' : String := "—"

/-- Scale types and the operations each licenses (`Scale.lean`). -/
def scaleRows : List StandardsRow := [
  ⟨`PropertyKindCalculus.ScaleType, "ScaleType",
    "Ch. 12, Fig. 12.21", "4.1 (no term)", none', "1.1 Note 3 (no term)"⟩,
  ⟨`PropertyKindCalculus.ScaleType.AllowsOrder, "ScaleType.AllowsOrder",
    "§12.16", "4.1 (comparable by order)", "1.26 *ordinal quantity*", "1.33 *ordinal quantity*"⟩,
  ⟨`PropertyKindCalculus.ScaleType.AllowsDifference, "ScaleType.AllowsDifference",
    "§12.19", none', none', "1.4 *interval quantity*"⟩,
  ⟨`PropertyKindCalculus.ScaleType.AllowsRatio, "ScaleType.AllowsRatio",
    "§12.20", "4.1 (comparable by ratio)", none', "1.3 *ratio quantity*"⟩,
  ⟨`PropertyKindCalculus.ScaleType.HasMagnitude, "ScaleType.HasMagnitude",
    "§13.3.1", "4.1 *quantity*", "1.1 *quantity*", "1.1 *quantity*"⟩,
  ⟨`PropertyKindCalculus.ScaleType.allows_mono, "ScaleType.allows_mono",
    "Ch. 12 (no section given)", none', none', "1.3 Note 2, 1.4 Note 2 (no term)"⟩]

/-- Kinds of property and the individual property (`Kind.lean`). -/
def kindRows : List StandardsRow := [
  ⟨`PropertyKindCalculus.KindOfProperty, "KindOfProperty",
    "§6.19", "4.1 *general quantity*", "1.2 *kind of quantity*",
    "1.1 Note 1 *general quantity* (no entry)"⟩,
  ⟨`PropertyKindCalculus.KindOfProperty.IsQuantity, "KindOfProperty.IsQuantity",
    "§13.3.1", "4.1 *quantity*", "1.1 *quantity*", "1.1 *quantity*"⟩,
  ⟨`PropertyKindCalculus.KindOfProperty.IsNominal, "KindOfProperty.IsNominal",
    "§13.2.1", "Clause 1 (*nominal properties*, not covered)", "1.30 *nominal property*", "6.1 *nominal property*"⟩,
  ⟨`PropertyKindCalculus.KindOfProperty.IsOrdinal, "KindOfProperty.IsOrdinal",
    "§13.2.2", "Clause 1 (*ordinal quantities*, not covered)", "1.26 *ordinal quantity*", "1.33 *ordinal quantity*"⟩,
  ⟨`PropertyKindCalculus.KindOfProperty.IsDifferential, "KindOfProperty.IsDifferential",
    "§13.2.3", none', none', "1.4 *interval quantity*"⟩,
  ⟨`PropertyKindCalculus.KindOfProperty.IsRational, "KindOfProperty.IsRational",
    "§13.2.4", "4.1 (comparable by ratio)", none', "1.3 *ratio quantity*"⟩,
  ⟨`PropertyKindCalculus.KindOfProperty.nominal_not_quantity,
    "KindOfProperty.nominal_not_quantity",
    "§13.3.1", "Clause 1; 4.1", "1.30 *nominal property*",
    "1.1 Note 3; 6.1 *nominal property*"⟩,
  ⟨`PropertyKindCalculus.IndividualProperty, "IndividualProperty",
    "no section given", "4.1 *individual quantity*",
    "1.1 Note 1 (individual quantities)", "1.1 Notes 1–2 *individual quantity* (no entry)"⟩]

/-- Property values and their comparability (`PropertyValue.lean`). -/
def valueRows : List StandardsRow := [
  ⟨`PropertyKindCalculus.PropertyValue, "PropertyValue",
    "§9.15", "6.2 (product of a unit and a number)", "1.19 *quantity value*",
    "1.24 *value of a quantity*; 1.35 *value of an ordinal quantity*; 6.5 *value of a nominal property*"⟩,
  ⟨`PropertyKindCalculus.PropertyValue.kind, "PropertyValue.kind",
    "§9.15", "4.1 *of the same kind*", "1.2 *kind of quantity*",
    "1.2 *quantities of the same kind*"⟩,
  ⟨`PropertyKindCalculus.PropertyValue.numeral, "PropertyValue.numeral",
    "§16.10", "6.2 *numerical value*", "1.20 *numerical quantity value*", "1.25 *numerical value of a quantity*"⟩,
  ⟨`PropertyKindCalculus.PropertyValue.reference, "PropertyValue.reference",
    "§16.10", "6.2 *unit*", "1.1 Note 2 (reference)",
    "1.12 *measurement unit*; 1.34 *ordinal scale*"⟩,
  ⟨`PropertyKindCalculus.PropertyValue.Comparable, "PropertyValue.Comparable",
    "§9.15", "4.1 *of the same kind*", "1.2 *kind of quantity*",
    "1.2 *quantities of the same kind*"⟩,
  ⟨`PropertyKindCalculus.PropertyValue.Comparable.refl, "Comparable.refl",
    "§9.15", none', none', none'⟩,
  ⟨`PropertyKindCalculus.PropertyValue.Comparable.symm, "Comparable.symm",
    "§9.15", none', none', none'⟩,
  ⟨`PropertyKindCalculus.PropertyValue.Comparable.trans, "Comparable.trans",
    "§9.15", none', none', none'⟩,
  ⟨`PropertyKindCalculus.PropertyValue.IsQuantityValue, "PropertyValue.IsQuantityValue",
    "§16.10", "6.2 (product of a unit and a number)", "1.19 *quantity value*", "1.24 *value of a quantity*"⟩]

/-- Quantities, their number carriers, and the count (`Quantity.lean`). -/
def quantityRows : List StandardsRow := [
  ⟨`PropertyKindCalculus.Quantity, "Quantity",
    "§13.3.3", "4.1 *quantity*", "1.1 *quantity*", "1.1 *quantity*"⟩,
  ⟨`PropertyKindCalculus.Carrier, "Carrier",
    "§13.5 (extensive aggregation)", none', none', none'⟩,
  ⟨`PropertyKindCalculus.LawfulCarrier, "LawfulCarrier",
    "no section given", none', none', none'⟩,
  ⟨`PropertyKindCalculus.instCarrierNat, "instCarrierNat",
    "no section given", "5 (dimension 1; counts not named)",
    "1.8 Note 4 (*quantity of dimension one*)",
    "1.10 *quantity with unit one*; 1.6 Note 4"⟩,
  ⟨`PropertyKindCalculus.Iso80000.Part9.numberOfEntities, "Part9.numberOfEntities",
    "no section given", "5 (dimension 1; counts not named)", "1.8 Note 4", "1.6 Note 4; 1.2 Note 3"⟩,
  ⟨`PropertyKindCalculus.Quantity.instLE, "Quantity.instLE",
    "§12.16", "4.1 (comparable by order)", "1.26 *ordinal quantity*", "1.33 Note 2"⟩,
  ⟨`PropertyKindCalculus.Quantity.instDecidableLE, "Quantity.instDecidableLE",
    "no section given", none', none', none'⟩,
  ⟨`PropertyKindCalculus.DifferenceKind, "DifferenceKind",
    "§12.19", none', "1.21 *quantity calculus*",
    "1.29 *quantity calculus*; 1.4 *interval quantity*"⟩]

/-- Specialization among kinds (`Specialization.lean`). -/
def specializationRows : List StandardsRow := [
  ⟨`PropertyKindCalculus.Specializes, "Specializes",
    "no section given", none',
    "1.1 Note 1 (levels of specific concepts)", "1.1 Note 1 (more specific general quantities)"⟩,
  ⟨`PropertyKindCalculus.MutuallyComparable, "MutuallyComparable",
    "§6", "4.1 *of the same kind*", "1.2 *kind of quantity*",
    "1.2 *quantities of the same kind*"⟩]

/-- Units and the individual quantity (`Unit.lean`, `IndividualQuantity.lean`). -/
def unitRows : List StandardsRow := [
  ⟨`PropertyKindCalculus.MetrologicalUnit, "MetrologicalUnit",
    "§18.12", "6.2 *unit*", "1.9 *measurement unit*", "1.12 *measurement unit*"⟩,
  ⟨`PropertyKindCalculus.MetrologicalUnit.Commensurable, "MetrologicalUnit.Commensurable",
    "§9.13.4", "6.2 (of the same kind)", "1.24 *conversion factor between units*",
    "1.22 *conversion factor between units*"⟩,
  ⟨`PropertyKindCalculus.MetrologicalUnit.measure, "MetrologicalUnit.measure",
    "§13.3.3", "6.2 (Q = {Q} [Q])", "1.19 *quantity value*; 1.20 Note 2",
    "1.24 *value of a quantity*; 1.25 Note 1"⟩,
  ⟨`PropertyKindCalculus.IndividualQuantity, "IndividualQuantity",
    "Ch. 3", "4.1 *individual quantity*", "1.1 Note 1 (individual quantities)",
    "1.1 Notes 1–2 *individual quantity* (no entry)"⟩]

/-- The secondary entries: bounds and the kind edges. -/
def secondaryRows : List StandardsRow := [
  ⟨`PropertyKindCalculus.LowerBound, "LowerBound", "§12.16 (order)", none', none', none'⟩,
  ⟨`PropertyKindCalculus.UpperBound, "UpperBound", "§12.16 (order)", none', none', none'⟩,
  ⟨`PropertyKindCalculus.ProductKind, "ProductKind",
    "§13.3.5", "6.3 (product of two quantities)", "1.22 *quantity equation*", "1.30 *quantity equation*"⟩,
  ⟨`PropertyKindCalculus.QuotientKind, "QuotientKind",
    "§13.3.5", "6.3 (quotient of two quantities)", "1.22 *quantity equation*", "1.30 *quantity equation*"⟩,
  ⟨`PropertyKindCalculus.ReciprocalKind, "ReciprocalKind",
    "§13.3.5", "6.3 (quotient of two quantities)", "1.22 *quantity equation*", "1.30 *quantity equation*"⟩]

end PropertyKindCalculusBlueprint.Chapters.StandardsReference

open PropertyKindCalculusBlueprint.Chapters.StandardsReference

#doc (Manual) "Standards Reference — PKC beside ISO 80000-1 and the VIM" =>
%%%
tag := "standards-reference"
%%%

The rest of this blueprint follows Dybkær's section numbers. A standard that cites this
work for its formal definitions will cite ISO 80000-1 and the _International Vocabulary of
Metrology_ (VIM) for the terms. This chapter is the bridge: for each definition of the
core calculus that a vocabulary of quantities, units and numbers needs, it gives the Lean
declaration, the Dybkær section the source file names, and the corresponding term and
clause of ISO 80000-1 and of the VIM, in one row. Under each table it says where the
sources agree and where this work, or Dybkær, departs from ISO 80000-1 and the VIM.

Only locators and terms are recorded. No definition, note or example of a copyrighted
source is reproduced.

# The sources, and what was checked

Each column is a specific document, and a locator in a column was read in that document.

- *Dybkær (2009)* — _An Ontology on Property for Physical, Chemical, and Biological
  Systems_. The sections are the ones the documentation comments of the Lean sources
  give. Where a declaration's comment names no section, the cell says so; none was added
  for this chapter.
- *ISO 80000-1:2022* — _Quantities and units — Part 1: General_, second edition.
  Read in full. Its clause 3 defines no terms of its own: it states that the terms and
  definitions of ISO/IEC Guide 99 apply. Guide 99 is the VIM, so for a defined term the
  normative locator is the VIM 3 column, and the ISO column gives the clause of the
  running text (4.1 the concept of quantity, 5 dimensions, 6.2 units and numerical
  values, 6.3 mathematical operations) where the standard uses the concept. Its scope
  states that the ISO/IEC 80000 series does not yet cover ordinal quantities and nominal
  properties.
- *VIM 3* — JCGM 200:2012, _International vocabulary of metrology — Basic and general
  concepts and associated terms_, third edition, as published by the BIPM (also issued as
  ISO/IEC Guide 99:2007). Read in full for the clauses cited.
- *VIM 4 2CD* — the second committee draft of the fourth edition, dated 2023-07-31,
  the edition the `@[vim4 …]` annotations of the
  {ref "cross-references"}[cross-reference chapter] use. Read in full for the clauses
  cited. It is a draft: its numbering and wording can change before publication. Each of
  its entries prints the corresponding VIM 3 clause, and the two VIM columns below follow
  that concordance.

The first edition, ISO 80000-1:2009, restated the Guide 99 entries in its own clause 3
(3.1 _quantity_, 3.2 _kind of quantity_, 3.9 _unit of measurement_, and so on). That
edition is withdrawn and the second edition has no such entries, so a reference to
"ISO 80000-1, 3.x" for a term is a reference to the 2009 edition only.

A dash means that no corresponding term or passage was found in the source. "No term" or
"no entry" beside a locator means that the concept appears there in running text or in a
note, not as a defined term.

# Scale types and the operations they license

:::standards_ref_table scaleRows
:::

- *Agreement.* All four sources separate properties by the comparisons that apply to
  them. `HasMagnitude` draws the line where VIM 3 draws it: a quantity
  has a magnitude and a nominal property has none. `AllowsOrder` begins at the ordinal
  level, as the ordinal quantity of both VIM editions does.
- *VIM 3 names two levels, not four.* It defines the ordinal quantity and the nominal
  property and leaves the interval and ratio levels without a term: every quantity that
  is not ordinal is treated as entering quantity calculus. `AllowsDifference` has no
  counterpart there.
- *ISO 80000-1:2022 describes three comparisons and covers one.* Clause 4.1 says that
  properties make things comparable by equivalence, some also by order, and some also by
  ratio. It does not mention comparison by difference, and its scope leaves ordinal
  quantities and nominal properties out. The quantities it treats are the ratio-scale
  ones.
- *VIM 4 2CD names all four*, and defines quantity itself by them (comparability by
  ratio, by difference, or by order). It gives no term for the classification as a whole,
  which is what `ScaleType` is; the four levels are listed in a note.
- *Departure in terms.* Dybkær and this work say _differential_ and _rational_ for the
  kinds, and _interval_ and _ratio_ for the scale types; VIM 4 2CD says _interval
  quantity_ and _ratio quantity_.
- *Departure in content.* `allows_mono` is a theorem: an operation licensed at one scale
  type is licensed at every richer one. The VIM 4 2CD notes state the two instances that
  matter (a ratio quantity is ordered and has differences; an interval quantity is
  ordered) and no source states the general law.

# Kinds of property

:::standards_ref_table kindRows
:::

- *Agreement.* `IsQuantity` holds of exactly the ordinal, interval and ratio kinds. All
  four sources count the ordinal level as quantity and the nominal level as not, which is
  the content of `nominal_not_quantity`.
- *`KindOfProperty` is broader than _kind of quantity_.* The VIM 3 term
  covers quantities only. Following Dybkær §6.19, a `KindOfProperty` may also be nominal,
  so it is the common genus of _kind of quantity_ and of the kind of a nominal property.
  The ISO/VIM _kind of quantity_ corresponds to a `KindOfProperty` for which `IsQuantity`
  holds.
- *Identity of a kind.* VIM 3 defines a kind as the aspect common to mutually comparable
  quantities and notes that the division into kinds is to some extent arbitrary. A
  `KindOfProperty` is a declared value with an identifier, a scale type and an optional
  examination principle (Dybkær §7.5), and two kinds are the same exactly when these
  three agree. Two kinds that share a dimension are therefore distinct unless declared
  equal, which makes formal the remark of VIM 3 1.2 Note 2 and VIM 4 2CD 1.2 Note 3 that
  quantities of the same dimension are not necessarily of the same kind. ISO
  80000-1:2022 clause 5 states only the other direction: quantities of the same kind
  have the same dimension, and quantities of different dimensions are of different
  kinds.
- *ISO 80000-1:2022 says _general quantity_.* Clause 4.1 does not use _kind of
  quantity_; it says that comparable quantities are of the same kind and are instances
  of the same general quantity, as VIM 4 2CD does.
- *VIM 4 2CD drops the term.* It has no entry _kind of quantity_; it speaks of a
  _general quantity_ in the notes to 1.1 and defines _quantities of the same kind_ (1.2)
  instead. `KindOfProperty` corresponds to its general quantity, or general nominal
  property.
- *`IndividualProperty`* is the individual quantity of the notes to 1.1, widened in the
  same way to nominal kinds. ISO 80000-1:2022 4.1 names the individual quantity in its
  text; none of the ISO or VIM documents gives it an entry of its own, and the Lean source cites no Dybkær section for it.

# Property values

:::standards_ref_table valueRows
:::

- *Agreement.* A value is a number together with a reference, and it belongs to one
  kind. `IsQuantityValue` holds exactly when the kind is a kind of quantity, which is the
  scope of _quantity value_ in VIM 3 and of _value of a quantity_ in VIM 4 2CD.
- *`PropertyValue` is broader than _quantity value_.* It also represents the value of a
  nominal property. VIM 3 notes that a nominal property has a value but defines no term
  for it; VIM 4 2CD defines one in a separate entry (6.5). The ISO/VIM _quantity value_
  corresponds to a `PropertyValue` for which `IsQuantityValue` holds.
- *The number is an integer.* `numeral` is an `Int`. VIM 3 1.19 allows any number,
  including a complex one. A real-valued magnitude is represented in this work by
  `Quantity k R` at a suitable carrier, not by `PropertyValue`.
- *`numeral` is not always a numerical value.* VIM 3 defines the numerical quantity
  value only for quantities that have a unit, and VIM 4 2CD 1.35 says that the numeral of
  an ordinal value is an identifier of a position, not a numerical value. `numeral` holds
  the number in every case, including the code of a nominal value. It is a _numerical
  value_ in the VIM sense only when the kind is interval or ratio.
- *The reference is an identifier.* `reference` is a `String` naming a unit or a
  category. In VIM 3 a reference is a measurement unit, a measurement
  procedure, a reference material, or a combination. This work represents the unit by
  `MetrologicalUnit` and the procedure by the kind's examination principle; the value
  carries only the name.
- *What a value is.* VIM 4 2CD defines a value as an individual quantity identified in a
  particular way. Here a value is a separate record that names a kind; it is not an
  `IndividualProperty` and has no bearer.
- *`Comparable` is stricter and is proved an equivalence.* Two values are comparable
  when their kinds are equal. The sources say that quantities of the same kind are
  comparable and state no laws; `Comparable.refl`, `Comparable.symm` and
  `Comparable.trans` prove that the relation is an equivalence. Values of two kinds that
  specialize a common kind are not `Comparable` at the value layer; that wider relation
  is `MutuallyComparable`, below.

# Quantities, numbers, and the count

:::standards_ref_table quantityRows
:::

- *Agreement.* The count is a quantity. VIM 3 1.8 Note 4 states that numbers of entities
  are quantities of dimension one, and VIM 4 2CD adds that number of entities can be
  regarded as a base quantity. This work carries a count in `Nat` (`instCarrierNat`), at
  a ratio-scale kind, and its ISO 80000-9 catalogue entry `numberOfEntities` has
  dimension one. A count is therefore a `Quantity k Nat` of a declared kind and never a
  bare number: two counts of different kinds cannot be added or compared.
- *ISO 80000-1:2022 does not name the count.* Clause 5 treats quantities whose
  dimensional exponents are all zero, notes that there is no agreed name for them, and
  says that such quantities are dimensionally simply numbers. It does not mention
  numbers of entities. Here a dimension-one quantity keeps its kind, so it is never
  merely a number.
- *`Quantity k R` is narrower than _quantity_.* In ISO 80000-1 and the VIM a quantity is
  a property, and the word covers both the general and the individual quantity. A
  `Quantity k R` is a magnitude of one fixed kind `k`, held in a number type `R`. It has
  no bearer and no unit. The general quantity is the kind `k`; the individual quantity is
  `IndividualQuantity o k R`; and the number-and-unit form is produced by
  `MetrologicalUnit.measure`.
- *`Quantity k R` is not restricted by scale.* The type can be formed at any kind,
  nominal included. What the scale restricts is the operations: addition and subtraction
  require a `DifferenceKind`, and products, quotients and reciprocals require the kind
  edges below. This matches quantity calculus in VIM 3 1.21, which excludes ordinal
  quantities, and in VIM 4 2CD 1.29, which applies to ratio and interval quantities.
- *The order is per kind.* `Quantity.instLE` compares two quantities of the same kind
  only; a comparison across kinds does not type-check. `Quantity.instDecidableLE` makes
  it decidable whenever the carrier's order is. The instance exists at every kind whose
  carrier is ordered; whether the order is meaningful for the kind is the separate
  condition `AllowsOrder`, which bounds require.
- *No counterpart: the number type.* ISO 80000-1 and the VIM take "number" as given.
  `Carrier` and `LawfulCarrier` state what a number type must provide (a zero and an
  addition, then the laws of a commutative monoid). `Nat` and `Int` are lawful carriers.
  The sources have no term for this, and it is where a vocabulary of numbers attaches to
  a vocabulary of quantities.

# Specialization and mutual comparability

:::standards_ref_table specializationRows
:::

- *Agreement.* The sources show a quantity such as length divided into more specific
  ones such as radius and wavelength, and treat all of them as mutually comparable.
  `Specializes` is that division and `MutuallyComparable` is that comparability.
- *The sources have a table, not a relation.* The division appears as an example table
  in a note to the entry _quantity_ in all three ISO and VIM documents. `Specializes` is
  a relation between kinds, generated from the direct-parent edges an application
  declares, and it is proved reflexive and transitive. The Lean source cites no Dybkær
  section for it.
- *`MutuallyComparable` is relative and is not an equivalence.* Two kinds are mutually
  comparable when they specialize a common kind under the declared edges. The relation
  is proved reflexive and symmetric. It is not transitive in general, because two kinds
  may each share a parent with a third without sharing one with each other. VIM 3
  uses _mutually comparable_ in the definition of _kind of quantity_ as if it
  partitioned quantities into kinds; that reading holds here only when the declared
  hierarchy gives every kind a single root.
- *It relates kinds.* VIM 4 2CD 1.2 defines _quantities of the same kind_ for individual
  quantities and extends it to general quantities in Note 2. `MutuallyComparable` is the
  relation of that note.

# Units and the individual quantity

:::standards_ref_table unitRows
:::

- *Agreement.* A unit belongs to one kind, a quantity of that kind is expressed as a
  number times the unit, and only quantities above the ordinal level have units.
  `MetrologicalUnit.WellFormed` requires an interval or ratio kind, which agrees with
  VIM 3 1.26 Note 1 and VIM 4 2CD 1.33 Note 4 that ordinal quantities have no units.
- *A `MetrologicalUnit` is not itself a quantity.* VIM 3 defines the unit as a quantity
  adopted by convention, and VIM 4 2CD and ISO 80000-1:2022 6.2 as a reference quantity. A
  `MetrologicalUnit` is a record of the kind it references and its symbol. It is not a
  `Quantity`, and no magnitude is attached to it.
- *One unit, one kind.* The withdrawn ISO 80000-1:2009 3.9 Note 2 observes that units of
  quantities of the
  same dimension may share a name and symbol even when the quantities are not of the same
  kind. Here a unit names exactly one kind, so the joule of energy and a unit of moment
  of force with the same symbol are two units.
- *`Commensurable`* holds when two units reference the same kind. It is the condition
  under which the sources define a conversion factor between units; the factor itself is
  not part of the relation. It is proved an equivalence.
- *`measure`* forms the number-and-unit value, the product ISO 80000-1:2022 6.2 writes
  for an individual quantity, its numerical value and its unit. Its number is an `Int`,
  as for `PropertyValue`.
- *`IndividualQuantity o k R` makes the bearer explicit.* The sources distinguish the
  individual quantity from the general one in a note and rely on context to tell them
  apart. Here the bearer `o` is a parameter of the type, so quantities of two different
  objects cannot be combined by mistake. The Lean source cites Dybkær's Chapter 3 for the
  object.

# Secondary entries: bounds and kind edges

:::standards_ref_table secondaryRows
:::

- *Bounds have no counterpart.* `LowerBound` and `UpperBound` are quantities of one kind
  in the role of an endpoint. Neither ISO 80000-1:2022 nor either VIM edition defines
  a bound or an interval of quantity values as a term. They rest on the order that the
  ordinal level provides.
- *Kind edges are declared, not derived from dimensions.* `ProductKind`, `QuotientKind`
  and `ReciprocalKind` record that one kind is the product, quotient or reciprocal of
  others, and require every kind involved to be ratio-scale (Dybkær §13.3.5). In the VIM
  a quantity equation relates quantities, and the kind of a product follows from the
  equation and is checked by dimension. Here the product of two quantities exists only
  where an edge is declared, and the dimension is a consequence that certifies the edge
  without deciding it: two kinds of the same dimension, such as energy and moment of
  force, remain distinct results. ISO 80000-1:2022 6.3 gives the product and the
  quotient of two quantities for any two quantities, with no such condition, and does
  not treat the reciprocal separately.

# Summary of the differences in meaning

A reference that cites ISO 80000-1 or the VIM for a term and this work for its formal
definition should take account of these:

- `KindOfProperty` and `PropertyValue` are _broader_ than _kind of quantity_ and
  _quantity value_: they include the nominal case. Restrict them by `IsQuantity` and
  `IsQuantityValue` to obtain the ISO/VIM concepts.
- `Quantity k R` is _narrower_ than _quantity_: it is a kind-indexed magnitude. The
  general quantity is the kind, and the individual quantity is `IndividualQuantity`.
- `MetrologicalUnit` is a reference to a kind with a symbol, not a quantity.
- `PropertyValue.numeral` and `measure` hold an integer, and `numeral` is a numerical
  value in the VIM sense only at interval and ratio kinds.
- `PropertyValue.Comparable` requires equal kinds, and `MutuallyComparable` requires a
  common declared ancestor and is not transitive.
- `KindOfProperty.IsDifferential`, `IsRational`, `ScaleType.AllowsDifference` and
  `AllowsRatio` have a defined term only in VIM 4 2CD.
- `Carrier`, `LawfulCarrier`, `Quantity.instDecidableLE`, `LowerBound`, `UpperBound` and
  the three `Comparable` laws have no counterpart in any of the ISO or VIM documents.
