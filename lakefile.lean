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
functor) and the soil-moisture *model* pull in PhysLib + Mathlib and will be
added as further libraries once the spine stabilizes.
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
    .one `PropertyKindCalculus.Interaction,
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
