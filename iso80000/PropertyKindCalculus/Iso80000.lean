/-
# PropertyKindCalculus.Iso80000

The standards-grounded layer: quantity-kinds (QK) and units (U) organized to
mirror the **ISO/IEC 80000** *Quantities and units* series, each citing its source
by name and version only (no normative content is reproduced — the standards are
licensed and copyrighted).

  * `PropertyKindCalculus.Iso80000.References` — the citation catalogue: one
    `StandardRef` per licensed part (ISO/IEC 80000-1 … -12).
  * `PropertyKindCalculus.Iso80000.Part3` — the full catalogue of ISO 80000-3 *Space
    and time* (all of items 3-1.1 … 3-26.3), with the length family as a
    specialization lattice (R2) and the dimension-collision capstones.
  * `PropertyKindCalculus.Iso80000.Part3.AreaElement` / `.VolumeElement` — the
    surface- and volume-element *Remarks* (items 3-3, 3-4), formalized analytically.
  * `PropertyKindCalculus.Iso80000.Part3.AreaClassification` — verified classification
    of areas (R12).
  * `PropertyKindCalculus.Iso80000.Part3.DefiningRelations` — the algebraic *Remarks*
    (curvature, repetency, frequency, speed, plane angle) as R12 kind-laws.

This library is PhysLib-backed (its quantity-kinds carry PhysLib `Dimension`s); the
references catalogue alone is Mathlib-free.
-/

import PropertyKindCalculus.Iso80000.References
import PropertyKindCalculus.Iso80000.Part3
import PropertyKindCalculus.Iso80000.Part3.AreaElement
import PropertyKindCalculus.Iso80000.Part3.AreaClassification
import PropertyKindCalculus.Iso80000.Part3.VolumeElement
import PropertyKindCalculus.Iso80000.Part3.DefiningRelations
