import Lake
open Lake DSL

/-!
# PropertyKindCalculus — a Lean formalization of Dybkær's ontology on property,
#                 extended with Flater's full tracking of kinds of quantities.

Motivation. Description logic (OWL2/SROIQ) — the substrate of the author's
prior OML metrology vocabularies — faithfully captures the *taxonomy* of
quantities (specialization, instantiation, dimensional factoring) but cannot
express the *calculus*: arithmetic on dimensions, the interaction algebra
between kinds (Flater, NIST TN 1943, App. C), the operator-availability that
Dybkær's scale stratification turns on, or any algebraic *law* as a provable
theorem. PropertyKindCalculus formalizes the ontology in dependent type theory, where
all of that is native.

Sources are vendored under `References/` for clickable markdown links:
  * `References/ontology-on-property.pdf` — Dybkær (2009)
  * `References/NIST.TN.1943.pdf`         — Flater (2016)

## Libraries

  * `PropertyKindCalculus` (default target) — the **exportable core**. Downstream users
    `require` the package and `import PropertyKindCalculus` to get only this. Its
    ontological spine is Mathlib-free, so it builds with just the toolchain:
      - `PropertyKindCalculus.Foundations`     — system / object            (Dybkær Ch. 3)
      - `PropertyKindCalculus.Scale`           — operator-based scale types  (Ch. 12)
      - `PropertyKindCalculus.Kind`            — kind-of-property / -quantity (Ch. 6, 13)
      - `PropertyKindCalculus.Specialization`  — Specializes closure, comparability (OML)

  * `Examples` — worked examples, in a **separate source tree** (`examples/`)
    and namespace `PropertyKindCalculus.Examples`. Kept out of the core so consumers can
    take `PropertyKindCalculus` alone, or additionally `import PropertyKindCalculus.Examples`.

The later `Dimension`/coherence layer (PhysLib `Dimension` as a forgetful
functor) pulls in PhysLib + Mathlib and is added as a further library once the
spine stabilizes. The soil-moisture *retrieval* model is a downstream
application, kept in a separate repository so this package stays focused on
metrology and the ISO/IEC 80000 parts.
-/

package «PropertyKindCalculus» where
  leanOptions := #[
    ⟨`autoImplicit, false⟩,
    ⟨`relaxedAutoImplicit, false⟩]

-- PhysLib (and, transitively, Mathlib) backs *only* the `Dimension` library
-- below — the dimension/coherence layer that maps each kind to its physical
-- `Dimension`. PhysLib HEAD tracks the same toolchain this package pins
-- (`leanprover/lean4:v4.30.0`, Mathlib `v4.30.0`). The core spine never imports
-- it, so a plain `import PropertyKindCalculus` stays Mathlib-free.
require «Physlib» from git
  "https://github.com/leanprover-community/physlib.git" @
  "v4.30.0"

-- TorchLean (this work's fork, `combined` branch) backs *only* the `Torch` library
-- below: the concrete IEEE-754 binary32 carriers (`FP32` rounding spec,
-- `IEEE32Exec` executable) that instantiate the R10 exec/spec refinement bridge.
-- It tracks the same toolchain and Mathlib rev (`v4.30.0`) this package already
-- pins via PhysLib, so it adds no version skew. The core spine never imports it.
require «TorchLean» from git
  "https://github.com/NicolasRouquette/TorchLean.git" @
  "combined"

/-- The exportable core library (Mathlib-free spine). -/
@[default_target]
lean_lib «PropertyKindCalculus» where
  -- The library root `PropertyKindCalculus.lean` plus every submodule under
  -- `PropertyKindCalculus/`. Examples live elsewhere, so they are not swept in here.
  globs := #[.andSubmodules `PropertyKindCalculus]

/-- Worked examples — a separate library so the core can be imported alone. -/
lean_lib «Examples» where
  srcDir := "examples"
  globs := #[.andSubmodules `PropertyKindCalculus.Examples]

/-- The PhysLib-backed coherence layer, in a **separate** source tree
(`dimension/`) so the PhysLib + Mathlib dependency lands here and nowhere else.
Build with `lake build Dimension`. It carries three *library* modules (no example
code — worked examples live in the `DimensionExamples` library below):
  * `PropertyKindCalculus.Dimension`    — `dim` as the forgetful functor into PhysLib's `Dimension`
  * `PropertyKindCalculus.Interaction`  — Flater's interaction algebra (`KMul`/`KDiv`),
    with the dimensional-coherence homomorphism (Flater, NIST TN 1943, App. C).
  * `PropertyKindCalculus.QuantityReal` — the `ℝ` carrier for the representation-parametric
    `Quantity k R` (R10): the proof representation, which needs Mathlib's `ℝ`. -/
lean_lib «Dimension» where
  srcDir := "dimension"
  globs := #[
    .one `PropertyKindCalculus.Dimension,
    .one `PropertyKindCalculus.ScaleSpanning,
    .one `PropertyKindCalculus.Interaction,
    .one `PropertyKindCalculus.Function,
    .one `PropertyKindCalculus.QuantityReal]

/-- Worked examples for the Mathlib-backed `Dimension` library — the dimension
functor, the interaction algebra, and the `ℝ` quantity carrier. Kept in the
`examples/` source tree as a **separate library** so that no *library* module
carries `example`/`#eval`/`#guard` code; it pulls in PhysLib + Mathlib
transitively, through the `Dimension`-library modules it imports. Build with
`lake build DimensionExamples`. -/
lean_lib «DimensionExamples» where
  srcDir := "examples"
  globs := #[.andSubmodules `PropertyKindCalculus.DimensionExamples]

/-- The **standards-grounded** layer: quantity-kinds and units organized to mirror
the ISO/IEC 80000 *Quantities and units* series, citing each part by name and
version only (no normative content is reproduced). PhysLib-backed (its
quantity-kinds carry PhysLib `Dimension`s); the references catalogue alone is
Mathlib-free. Build with `lake build Iso80000`. It carries:
  * `PropertyKindCalculus.Iso80000.References` — the citation catalogue (parts 1–12)
  * `PropertyKindCalculus.Iso80000.Part3`      — a seed of ISO 80000-3 *Space and time* -/
lean_lib «Iso80000» where
  srcDir := "iso80000"
  globs := #[.andSubmodules `PropertyKindCalculus.Iso80000]

/-- The **external cross-reference** layer: typed, decl-indexed annotations that
map this work's declarations to the loci where the corresponding concepts are
defined in Dybkær's *Ontology on Property* (2009) and the VIM 4 2CD (2023-07-31).
The annotations are applied *from afar* (a separate `Annotations` module attaches
the attributes to spine declarations), so the Mathlib-free, meta-free core spine
stays prelude-only. This library imports `Lean` for the attribute/extension
machinery; it does **not** pull in PhysLib or Mathlib. Build with
`lake build CrossRefs`. It carries:
  * `PropertyKindCalculus.CrossRefs.Attributes`  — the `@[dybkaer …]` / `@[vim4 …]`
    parametric attributes, their env extensions, and the harvest API.
  * `PropertyKindCalculus.CrossRefs.Sources`     — the bibliographic identity of the
    two external sources (mirroring `Iso80000.StandardRef`).
  * `PropertyKindCalculus.CrossRefs.Annotations` — the cross-reference annotations,
    promoting the locators already recorded in the spine docstrings to typed data. -/
lean_lib «CrossRefs» where
  srcDir := "crossrefs"
  globs := #[.andSubmodules `PropertyKindCalculus.CrossRefs]

/-- The **TorchLean-backed instance** of the R10 exec/spec refinement bridge: the
concrete IEEE-754 binary32 carriers (TorchLean's `FP32` rounding spec and
`IEEE32Exec` executable) realizing `CarrierRefinement` over `ℝ`. This is the one
library that depends on TorchLean. Build with `lake build Torch`. -/
lean_lib «Torch» where
  srcDir := "torch"
  globs := #[.andSubmodules `PropertyKindCalculus.Torch]
