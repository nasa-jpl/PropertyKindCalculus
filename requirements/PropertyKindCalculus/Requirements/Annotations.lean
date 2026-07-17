/-
# Requirement annotations on the core spine — applied from afar

This module attaches the `@[requirement …]` traceability attribute to the
Mathlib-free core-spine declarations that discharge requirements R1–R12, using the
standalone `attribute [..] decl` command. It promotes the correspondences hitherto
recorded only in the blueprint's `requirementsTable` "Specified as" column to
typed, decl-indexed, auditable metadata — without editing (or adding any `import`s
to) the prelude-only spine.

Requirements whose declarations live in the PhysLib/Mathlib-backed layers are
annotated in the sibling modules `DimensionAnnotations` (R1 dimension-1
disambiguation, R5 interaction algebra, R7 dimension homomorphism, R13
scale-spanning) and `UncertaintyAnnotations` (R14, R15).

A declaration may discharge more than one requirement (e.g. `KindOfProperty` both
*specifies* R1 and grounds R3), and a requirement is discharged by more than one
declaration; the attribute simply records each (decl, requirement, role) triple.
-/

import PropertyKindCalculus
import PropertyKindCalculus.Requirements.Attributes

namespace PropertyKindCalculus

/-! ## Kind structure (R1, R2, R3) -/

attribute [requirement "R1" specifies "the kind-indexed value type; distinct kinds are distinct types"]
  KindOfProperty
attribute [requirement "R1" specifies "Quantity k R records the kind as a type index"] Quantity

attribute [requirement "R2" specifies "the reflexive–transitive specialization closure (a preorder)"]
  Specializes
attribute [requirement "R2" proves "specialization is transitive"] Specializes.trans
attribute [requirement "R2" specifies "sub-kinds sharing a super-kind stay mutually comparable"]
  MutuallyComparable
attribute [requirement "R2" specifies "individuation by examination principle, not by name"]
  ExaminationPrinciple
attribute [requirement "R2" proves "kinds with different examination principles are distinct"]
  KindOfProperty.distinct_of_examPrinciple

attribute [requirement "R3" specifies "a kind is a type"] KindOfProperty
attribute [requirement "R3" specifies "an individual measured value is a term of that type"] Quantity

/-! ## Object identity, first-class (R19) -/

attribute [requirement "R19" specifies "a quantity that characterizes an object — the object rides in the type, alongside the kind"]
  IndividualQuantity
attribute [requirement "R19" proves "quantities of different objects are provably distinct: differing systems ⇒ differing dedicated kinds"]
  DedicatedKind.distinct_of_system

/-! ## Operation gating (R4, R5, R6) -/

attribute [requirement "R4" implements "same-kind addition; cross-kind addition is a type error"]
  Quantity.add
attribute [requirement "R4" proves "the same-kind additivity laws (comm, assoc, unit), one proof for every lawful carrier"]
  Quantity.laws_parametric

-- R5 (the interaction algebra) lives in the Dimension layer; see `DimensionAnnotations`.

attribute [requirement "R6" specifies "the four operator-based scale types, ordered by richness"]
  ScaleType
attribute [requirement "R6" proves "a richer scale licenses every operation a poorer one does (monotonicity)"]
  ScaleType.allows_mono

/-! ## Soundness bridges (R7, R8, R16, R17) -/

-- R7 (dim is a forgetful homomorphism) lives in the Dimension layer; see `DimensionAnnotations`.

-- R8 (expressiveness) — a metrological unit *is* one chosen value of a kind: the
-- referenced kind together with its symbol. A capability the type system affords,
-- not a theorem; it is discharged by the construction that typechecks (see
-- `ExampleAnnotations`), so here it is only *specified*.
attribute [requirement "R8" specifies "a metrological unit is one chosen value of a kind — the referenced kind together with its unit symbol"]
  MetrologicalUnit

-- R16 (verifiable) — unit references are faithful: commensurability ("of the same
-- kind") is an equivalence relation, and the §13.3.3 number-and-reference form is a
-- round-trip. This is the faithfulness R8 used to promise; it is now its own
-- verifiable requirement, discharged by these checked theorems.
attribute [requirement "R16" specifies "commensurability — \"of the same kind\", the only relation a unit converts along"]
  MetrologicalUnit.Commensurable
attribute [requirement "R16" proves "commensurability is reflexive"] MetrologicalUnit.Commensurable.refl
attribute [requirement "R16" proves "commensurability is symmetric"] MetrologicalUnit.Commensurable.symm
attribute [requirement "R16" proves "commensurability is transitive — completing the equivalence a description logic cannot state"]
  MetrologicalUnit.Commensurable.trans
attribute [requirement "R16" specifies "the number-and-reference form: measuring a numeral against a unit's reference (§13.3.3)"]
  MetrologicalUnit.measure
attribute [requirement "R16" proves "quantity / unit = number: the numeral reads back off a measured value"]
  MetrologicalUnit.measure_numeral
attribute [requirement "R16" proves "number × unit = quantity: re-applying the unit to a value's numeral recovers it — the faithful round-trip"]
  MetrologicalUnit.measure_eq_of_measures

-- R17 (verifiable) — unit *conversion* between commensurable units is a faithful
-- round-trip. Distinct from R16's number-and-reference inversion: here the §1.22
-- conversion factor between two prefixed units of the same base and radix composes
-- with its reciprocal to the identity. Kept as a power-of-radix *exponent*, so it is
-- exact over `Int`, and one proof serves both the SI decimal and IEC 80000-13 binary
-- prefix families — this is their home in the matrix. The companion numeric (ℝ)
-- statement is proved in `DimensionAnnotations`.
attribute [requirement "R17" specifies "the SI decimal prefix — the §1.22 conversion factor as a power-of-ten exponent"]
  SIPrefix
attribute [requirement "R17" specifies "the IEC 80000-13 binary prefix — the same conversion factor at radix two (kibi = 2¹⁰)"]
  BinaryPrefix
attribute [requirement "R17" specifies "a prefixed unit: a unit related to a base by a power-of-radix conversion factor (decimal or binary)"]
  PrefixedUnit
attribute [requirement "R17" specifies "the §1.22 conversion factor of a prefixed unit, read off as an exponent"]
  PrefixedUnit.conversionExponent
attribute [requirement "R17" proves "the two conversion factors between commensurable units are reciprocal (their exponents cancel)"]
  PrefixedUnit.shift_add_symm
attribute [requirement "R17" proves "converting a magnitude between units and back recovers it exactly — the faithful round-trip, exact over Int"]
  PrefixedUnit.convertExp_roundtrip

/-! ## Aggregation (R9) -/

attribute [requirement "R9" specifies "extensive kinds aggregate additively over a decomposition"]
  Extensive
attribute [requirement "R9" proves "the ∀-quantified additive law lifts to the whole decomposition"]
  extensive_additive
attribute [requirement "R9" proves "volume on mixing is sub-additive — a checked non-extensive counterexample"]
  mixing_subadditive

/-! ## Representation parametricity (R10, R11) -/

attribute [requirement "R10" specifies "the numeric-representation typeclass bounding the carrier"]
  Carrier
attribute [requirement "R10" specifies "the lawful carrier over which additivity is proved once"]
  LawfulCarrier
attribute [requirement "R10" specifies "the exec/spec carrier refinement bridge"] CarrierRefinement
attribute [requirement "R10" proves "a law over the spec carrier descends to the exec carrier as one rounding step"]
  Quantity.add_refines

attribute [requirement "R11" implements "a function-space carrier: a vector quantity is a numerical array under one scalar unit"]
  instCarrierPi
attribute [requirement "R11" proves "the additivity laws transfer to the vector carrier by the same parametric proof"]
  instLawfulCarrierPi

/-! ## Verified classification (R12) -/

attribute [requirement "R12" specifies "the product kind-law family"] ProductKind
attribute [requirement "R12" specifies "the quotient kind-law family"] QuotientKind
attribute [requirement "R12" specifies "the reciprocal kind-law family"] ReciprocalKind
attribute [requirement "R12" specifies "the by-construction product certificate"] Quantity.IsProduct
attribute [requirement "R12" proves "the smart-constructed product satisfies its certificate by construction"]
  Quantity.mul_isProduct

end PropertyKindCalculus
