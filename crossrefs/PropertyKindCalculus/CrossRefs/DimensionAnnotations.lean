/-
# Cross-references into the Dimension layer

The VIM concepts of *quantity dimension* (1.9), *quantity with the unit one*
(1.10), and *quantity calculus* (1.29) are realized in the PhysLib-backed
`Dimension` and `Interaction` libraries, not the core spine. This module attaches
the `@[vim4 …]` annotations to those declarations; importing it pulls in those
libraries (and transitively Mathlib/PhysLib), which is why the cross-reference
layer — a documentation/metadata layer — is not Mathlib-free even though the core
spine it annotates is.
-/

import PropertyKindCalculus.Dimension
import PropertyKindCalculus.Interaction
import PropertyKindCalculus.CrossRefs.Attributes

namespace PropertyKindCalculus

attribute [vim4 "1.9" "quantity dimension" "the forgetful dim map into PhysLib"]
  DimensionedKind.toDimension
attribute [vim4 "1.10" "quantity with the unit one"
  "the dimension-1 thesis: distinct kinds collapse to one dimension"] dim_not_injective
attribute [vim4 "1.29" "quantity calculus" "kind interaction (KMul / KDiv)"]
  InteractionAlgebra.KMul

end PropertyKindCalculus
