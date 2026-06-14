/-
# PropertyKindCalculus.Iso80000

The standards-grounded layer: quantity-kinds (QK) and units (U) organized to
mirror the **ISO/IEC 80000** *Quantities and units* series, each citing its source
by name and version only (no normative content is reproduced — the standards are
licensed and copyrighted).

  * `PropertyKindCalculus.Iso80000.References` — the citation catalogue: one
    `StandardRef` per licensed part (ISO/IEC 80000-1 … -12).
  * `PropertyKindCalculus.Iso80000.Part3` — a seed of ISO 80000-3 *Space and time*:
    a few dimensioned quantity-kinds and their coherent SI units, the pattern to
    review before extending to the other parts.

This library is PhysLib-backed (its quantity-kinds carry PhysLib `Dimension`s); the
references catalogue alone is Mathlib-free.
-/

import PropertyKindCalculus.Iso80000.References
import PropertyKindCalculus.Iso80000.Part3
