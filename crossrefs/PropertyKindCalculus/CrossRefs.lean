/-
# PropertyKindCalculus.CrossRefs

Typed, decl-indexed cross-references from this work's declarations to the loci
where the corresponding concepts are defined in two external sources:

  * **Dybkær (2009)**, *An Ontology on Property for Physical, Chemical, and
    Biological Systems* — the ontology this work formalizes.
  * **VIM 4 2CD (2023-07-31)**, the *International Vocabulary of Metrology*, 4th
    edition, Committee Draft 2 — the metrology vocabulary this work aligns to.

The correspondences are recorded as two parametric attributes (`@[dybkaer …]`,
`@[vim4 …]`), each backed by an environment extension, so any consumer — the
blueprint's two index tables, or a future query tool — can ask, for a given
declaration, where its concept lives in the external sources. The attributes are
applied *from afar* (in `Annotations`), keeping the Mathlib-free core spine
prelude-only. Only locators are carried; no normative text is reproduced.

  * `PropertyKindCalculus.CrossRefs.Attributes`  — the attributes, their env
    extensions (`dybkaerExt` / `vim4Ext`), and the harvest API (`dybkaerRefs` /
    `vim4Refs`).
  * `PropertyKindCalculus.CrossRefs.Sources`     — the bibliographic identity of the
    two sources.
  * `PropertyKindCalculus.CrossRefs.Annotations` — the cross-reference annotations
    on the (Mathlib-free) core spine.
  * `PropertyKindCalculus.CrossRefs.DimensionAnnotations` /
    `PropertyKindCalculus.CrossRefs.Iso80000Annotations` — the annotations that
    reach into the Dimension and ISO/IEC 80000 layers (quantity dimension, the
    dimension-one thesis, quantity calculus, the ISQ, coherent units). These pull
    in PhysLib/Mathlib, so the cross-reference layer as a whole is not Mathlib-free
    even though the core spine it annotates is.
-/

import PropertyKindCalculus.CrossRefs.Attributes
import PropertyKindCalculus.CrossRefs.Sources
import PropertyKindCalculus.CrossRefs.Annotations
import PropertyKindCalculus.CrossRefs.DimensionAnnotations
import PropertyKindCalculus.CrossRefs.Iso80000Annotations
