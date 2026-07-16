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

/-! ## Soundness bridges (R7, R8) -/

-- R7 (dim is a forgetful homomorphism) lives in the Dimension layer; see `DimensionAnnotations`.

attribute [requirement "R8" specifies "a unit is a chosen value of a kind (conversion round-trip is planned)"]
  MetrologicalUnit

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
