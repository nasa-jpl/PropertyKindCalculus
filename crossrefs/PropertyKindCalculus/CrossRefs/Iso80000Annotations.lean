/-
# Cross-references into the ISO/IEC 80000 layer

The VIM concept of the *international system of quantities* (1.8) is, in this work,
the ISO/IEC 80000 catalogue; the *coherent derived unit* (1.15) is carried by each
catalogued kind. This module attaches the `@[vim4 …]` annotations to those
declarations in the (PhysLib-backed) `Iso80000` library.
-/

import PropertyKindCalculus.Iso80000
import PropertyKindCalculus.CrossRefs.Attributes

namespace PropertyKindCalculus.Iso80000

attribute [vim4 "1.8" "international system of quantities (ISQ)"
  "the ISO/IEC 80000 catalogue of quantity-kinds"] catalogue
attribute [vim4 "1.15" "coherent derived unit" "the coherentUnit of each kind"]
  CataloguedKind

end PropertyKindCalculus.Iso80000
