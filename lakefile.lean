import Lake
open Lake DSL

/-!
# KindCalculus — a Lean formalization of Dybkær's ontology on property,
#                 extended with Flater's full tracking of kinds of quantities.

Motivation. Description logic (OWL2/SROIQ) — the substrate of the author's
prior OML metrology vocabularies — faithfully captures the *taxonomy* of
quantities (specialization, instantiation, dimensional factoring) but cannot
express the *calculus*: arithmetic on dimensions, the interaction algebra
between kinds (Flater, NIST TN 1943, App. C), the operator-availability that
Dybkær's scale stratification turns on, or any algebraic *law* as a provable
theorem. KindCalculus formalizes the ontology in dependent type theory, where
all of that is native.

Sources are vendored under `References/` for clickable markdown links:
  * `References/ontology-on-property.pdf` — Dybkær (2009)
  * `References/NIST.TN.1943.pdf`         — Flater (2016)

## Libraries

  * `KindCalculus` (default target) — the **exportable core**. Downstream users
    `require` the package and `import KindCalculus` to get only this. Its
    ontological spine is Mathlib-free, so it builds with just the toolchain:
      - `KindCalculus.Foundations`     — system / object            (Dybkær Ch. 3)
      - `KindCalculus.Scale`           — operator-based scale types  (Ch. 12)
      - `KindCalculus.Kind`            — kind-of-property / -quantity (Ch. 6, 13)
      - `KindCalculus.Specialization`  — Specializes closure, comparability (OML)

  * `Examples` — worked examples, in a **separate source tree** (`examples/`)
    and namespace `KindCalculus.Examples`. Kept out of the core so consumers can
    take `KindCalculus` alone, or additionally `import KindCalculus.Examples`.

The later `Dimension`/coherence layer (PhysLib `Dimension` as a forgetful
functor) and the soil-moisture *model* pull in PhysLib + Mathlib and will be
added as further libraries once the spine stabilizes.
-/

package «KindCalculus» where
  leanOptions := #[
    ⟨`autoImplicit, false⟩,
    ⟨`relaxedAutoImplicit, false⟩]

/-- The exportable core library (Mathlib-free spine). -/
@[default_target]
lean_lib «KindCalculus» where
  -- The library root `KindCalculus.lean` plus every submodule under
  -- `KindCalculus/`. Examples live elsewhere, so they are not swept in here.
  globs := #[.andSubmodules `KindCalculus]

/-- Worked examples — a separate library so the core can be imported alone. -/
lean_lib «Examples» where
  srcDir := "examples"
  globs := #[.andSubmodules `KindCalculus.Examples]
