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

/-- Forward this package's `-K cuda` / `-K cuda_home` / `-K isoc23_shim` options to the
TorchLean dependency (Lake applies command-line `-K` to the root package only). This
package produces only libraries — its `Torch` library uses TorchLean's CPU executable
carrier (`IEEE32Exec`), never the CUDA backend — so it never links the isoc23 shim
directly; the clause is here so the option threads uniformly through the store build and a
`-K cuda=true` at this root would still reach TorchLean. Empty when no option is set, so
the default build is byte-for-byte the same `require` as before (no resolution change). -/
private def torchLeanOpts : Lean.NameMap String := Id.run do
  let mut m : Lean.NameMap String := Lean.mkNameMap String
  if let some v := get_config? cuda then m := m.insert `cuda v
  if let some v := get_config? cuda_home then m := m.insert `cuda_home v
  if let some v := get_config? isoc23_shim then m := m.insert `isoc23_shim v
  return m

package «PropertyKindCalculus» where
  -- The package version — the single source of truth. `scripts/bump-version.sh`
  -- reads and bumps it here, and the blueprint reads this same line at build time
  -- (its `{version}[]` role) so the published document never drifts from the source.
  version := v!"0.59.0"
  leanOptions := #[
    ⟨`autoImplicit, false⟩,
    ⟨`relaxedAutoImplicit, false⟩]

-- PhysLib (and, transitively, Mathlib) backs *only* the `Dimension` library
-- below — the dimension/coherence layer that maps each kind to its physical
-- `Dimension`. This package's dimension layer is *parametric in the base-dimension
-- basis*, which requires the parametric `Dimension B` API: the author's own
-- contribution to PhysLib (feature request issue #1441, PR #1447), stacked on the
-- `v4.32.0` toolchain bump (PR #1445). Both are now merged upstream, so we track
-- the upstream `leanprover-community/physlib` `master` branch directly; the exact
-- commit is recorded in `lake-manifest.json`, so the build stays reproducible.
-- NOTE (2026-08-18, v4.33 bump landed upstream): upstream `master` (a7a6d465) did not
-- compile under Lean/Mathlib `v4.33.0` — NNReal mk-coercion proofs in the five `*Unit`
-- modules and the derived `Fintype` on `LTMCTDimensionBase` had rotted. Those repairs
-- were carried on the fork branch `NicolasRouquette/physlib` `lean-4.33` and are now
-- **merged upstream** as PR #1521 (merge commit `a50684a1`, 2026-08-17), so this
-- require is back on `leanprover-community/physlib` `master`. Do not re-pin the fork
-- branch: GitHub deletes a merged PR's head branch, which makes the fork commit
-- unreachable from every remote ref and breaks any *fresh* clone (`fatal: reference is
-- not a tree`) even while a stale local tracking ref still resolves it. A dependency's
-- `lean-toolchain` is informational (the ROOT toolchain builds the closure); the
-- `require mathlib` at `v4.33.0` is kept *last* below (Lake resolves later requires over
-- earlier ones, so Mathlib `v4.33.0`'s own dependency versions take precedence and
-- `lake exe cache get` computes matching hashes).
require «Physlib» from git
  "https://github.com/leanprover-community/physlib.git" @
  "master"

-- TorchLean (this work's fork, `combined` branch) backs *only* the `Torch` library
-- below: the concrete IEEE-754 binary32 carriers (`FP32` rounding spec,
-- `IEEE32Exec` executable) that instantiate the R10 exec/spec refinement bridge.
-- Its `combined` branch carries upstream's Lean `v4.33.0` / Mathlib `v4.33.0`
-- upgrade; this package pins the same toolchain. Required after PhysLib so its
-- `doc-gen4 v4.33.0` wins. The core spine never imports it, so
-- `import PropertyKindCalculus` stays Mathlib-free.
require «TorchLean» from git
  "https://github.com/NicolasRouquette/TorchLean.git" @
  "combined"
  with torchLeanOpts

-- Mathlib is pinned directly at the root, at `v4.33.0`, and kept LAST so that its
-- dependency versions win over PhysLib's older transitive pins (see above). This
-- is the same discipline TorchLean's lakefile follows. The core spine never
-- imports Mathlib, so a plain `import PropertyKindCalculus` stays Mathlib-free.
require mathlib from git
  "https://github.com/leanprover-community/mathlib4" @
  "v4.33.0"

-- NOTE (2026-08-04): there is deliberately **no doc-gen4 require here**. doc-gen4 is pulled
-- transitively (PhysLib and TorchLean each require it; TorchLean's stock `leanprover/doc-gen4` `v4.33.0`
-- pin wins, being required later — see the ordering discipline above; formerly both sat at `v4.32.0`
-- tag `092d631`), so it stays in the closure regardless — but this package no longer *overrides* it.
-- As of the pivot in `RENDERING.md` §6 v2 (after doc-gen4 PR #403 was closed on maintainer feedback),
-- `@[pkc_math]` writes its rendered math + source into each declaration's own docstring via core Lean's
-- `Lean.addDocStringCore`, so **no module here imports doc-gen4** — it is only ever resolved, never
-- built by this package. The former `require «doc-gen4» from "../doc-gen4"` dev override (which carried
-- a now-abandoned `DeclMath` hook) has been removed; the API site is produced by the stock transitive
-- doc-gen4 via the ordinary docstring path.
--
-- **(2026-08-04) doc-gen4 is now BUILT here**, by `scripts/build-api-docs.sh` (the `:docs` facets it
-- contributes to the workspace), which publishes the API site under `docs/api/` alongside the Verso
-- blueprint. Still no `require` and still no *import* — the facets come from the transitive package.
--
-- **GOTCHA for anyone adding a library to that docs build:** doc-gen4's `library_facet docs` renders
-- `lib.rootModules`, and Lake defaults `roots := #[<target name>]` — *not* the glob prefix. So a library
-- declared with only `globs := #[.andSubmodules `PropertyKindCalculus.Foo]` has the non-existent root
-- `Foo`, and `lake build Foo:docs` **silently succeeds while generating nothing** ("0 root modules").
-- Every library in the docs build must therefore declare `roots` explicitly, as `Examples` and
-- `DocGenMath` do below.

/-- The exportable core library (Mathlib-free spine). -/
@[default_target]
lean_lib «PropertyKindCalculus» where
  -- The library root `PropertyKindCalculus.lean` plus every submodule under
  -- `PropertyKindCalculus/`. Examples live elsewhere, so they are not swept in here.
  globs := #[.andSubmodules `PropertyKindCalculus]

/-- Worked examples — a separate library so the core can be imported alone. -/
lean_lib «Examples» where
  srcDir := "examples"
  -- `roots` is explicit because the doc build renders `lib.rootModules` (see the NOTE above).
  roots := #[`PropertyKindCalculus.Examples]
  globs := #[.andSubmodules `PropertyKindCalculus.Examples]

/-- **The validation-test suite** (source tree `tests/`, namespace
`PropertyKindCalculus.Tests`). Distinct from the pedagogical `Examples` library: these are
build-time *regression probes* for the two properties a "machine-checked" claim rests on but
that `lake build` does not check on its own —

  * **inhabitation / non-vacuity.** Each verifiable requirement's theorem is applied to a
    *concrete* witness whose hypotheses are discharged by `decide`/`rfl`, so a theorem that
    were vacuously true (an empty universal, an unsatisfiable premise) would fail to compile
    here — the "validate the target is inhabited, not merely well-formed" discipline.
  * **axiom profile.** Each requirement theorem's `#print axioms` is pinned with
    `#guard_msgs`, so a proof silently relocated behind a `sorry` (which emits *no* warning
    on its caller) is caught by the axiom set, not the absence of the `sorry` keyword.

Every probe file is imported by the tier index it belongs to, and the tiers by
`PropertyKindCalculus.Tests` — an *unindexed* probe is never built and guards nothing, so
indexing is part of landing one. Build with `lake build Tests`; CI builds it (and the
Dimension/Uncertainty layers it reaches into) so all sixteen verifiable requirements are
CI-enforced, not just the nine in the core spine. -/
lean_lib «Tests» where
  srcDir := "tests"
  globs := #[.andSubmodules `PropertyKindCalculus.Tests]

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
    .one `PropertyKindCalculus.AngleReform,
    .one `PropertyKindCalculus.IsqBase,
    .one `PropertyKindCalculus.ScaleSpanning,
    .one `PropertyKindCalculus.Interaction,
    .one `PropertyKindCalculus.Function,
    .one `PropertyKindCalculus.DimensionalCoverage,
    .one `PropertyKindCalculus.QuantityReal,
    .one `PropertyKindCalculus.BoundsReal,
    .one `PropertyKindCalculus.UnitConversion]

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

/-- The **requirement-traceability** layer: typed, decl-indexed `@[requirement …]`
annotations mapping each blueprint requirement (R1–R17) to the declarations that
specify, prove, implement, or exemplify it, plus the canonical requirement
catalogue. The blueprint harvests these into a traceability matrix, so it cannot
drift from the source — a renamed declaration is a compile error. The annotations
are applied *from afar*, mirroring `CrossRefs`. The core mechanism
(`Attributes`, `Catalogue`, core-spine `Annotations`) is Mathlib-free; the
`DimensionAnnotations` (R1/R5/R7/R13/R17) and `UncertaintyAnnotations` (R14/R15)
modules reach into the PhysLib/Mathlib-backed layers. Build with
`lake build Requirements`. -/
lean_lib «Requirements» where
  srcDir := "requirements"
  globs := #[.andSubmodules `PropertyKindCalculus.Requirements]

/-- The **TorchLean-backed instance** of the R10 exec/spec refinement bridge: the
concrete IEEE-754 binary32 carriers (TorchLean's `FP32` rounding spec and
`IEEE32Exec` executable) realizing `CarrierRefinement` over `ℝ`. This is the one
library that depends on TorchLean. Build with `lake build Torch`. -/
lean_lib «Torch» where
  srcDir := "torch"
  globs := #[.andSubmodules `PropertyKindCalculus.Torch]

/-- **Stage 0 of the uncertainty workstream** (see `UNCERTAINTY.md`): carrier-parametric input
distributions, the inverse-CDF sampler shared by Monte Carlo and systematic propagation, the
Monte Carlo reference propagator, and the linearized GUM/Willink moment-combine methods.
Mathlib- and TorchLean-free — it depends only on the core spine, so it builds with just the
toolchain. Build with `lake build Uncertainty`.

The module list is **explicit** (not `.andSubmodules`) precisely so that the Stage-1 rigor
modules (`.Ladder` over Mathlib's `ℝ`, `.Sensitivity` over TorchLean autograd) can live in the
same `uncertainty/` source tree and namespace **without** being swept into this Mathlib-free
library — they belong to `UncertaintyRigor` below. -/
lean_lib «Uncertainty» where
  srcDir := "uncertainty"
  globs := #[
    .one `PropertyKindCalculus.Uncertainty,
    .one `PropertyKindCalculus.Uncertainty.Carriers,
    .one `PropertyKindCalculus.Uncertainty.Sampling,
    .one `PropertyKindCalculus.Uncertainty.InputDist,
    .one `PropertyKindCalculus.Uncertainty.Budget,
    .one `PropertyKindCalculus.Uncertainty.BudgetDag,
    .one `PropertyKindCalculus.Uncertainty.UncertainQuantity,
    .one `PropertyKindCalculus.Uncertainty.Mcm,
    .one `PropertyKindCalculus.Uncertainty.Combine,
    .one `PropertyKindCalculus.Uncertainty.EvidenceKinds,
    .one `PropertyKindCalculus.Uncertainty.Roles,
    .one `PropertyKindCalculus.Uncertainty.Evidence,
    .one `PropertyKindCalculus.Uncertainty.Conformity,
    .one `PropertyKindCalculus.Uncertainty.Ssprc,
    .one `PropertyKindCalculus.Uncertainty.Allocation,
    .one `PropertyKindCalculus.Uncertainty.Adequacy,
    .one `PropertyKindCalculus.Uncertainty.Adequacy.Serialization]

/-- **Stage 1 of the uncertainty workstream** (see `UNCERTAINTY.md` §6): the rigor and
sensitivity layer that the Mathlib- and TorchLean-free Stage-0 `Uncertainty` library above cannot
carry. Two modules, sharing the `uncertainty/` source tree and the `PropertyKindCalculus.Uncertainty`
namespace but built as a separate library so the dependency expansion lands *here* and Stage 0
stays toolchain-only:
  * `PropertyKindCalculus.Uncertainty.Ladder`      — the GUM ⊂ Willink nesting theorems T1
    (cumulant additivity) and T2 (`gum = willink|κ₄=0`), stated and proved over Mathlib's `ℝ`.
  * `PropertyKindCalculus.Uncertainty.ConformityLadder` — why an acceptance limit may tighten
    itself: it rises as `u` falls, never past the tolerance limit, and — the load-bearing one —
    the specific consumer's risk AT that limit does not depend on `u` at all, so a rule built for
    a target risk runs it at every stage of evidence including the first. The fleet's speedup is
    then a corollary of a risk bound rather than a hope.
  * `PropertyKindCalculus.Uncertainty.Sensitivity` — the autograd bridge sourcing the GUM/Willink
    sensitivity coefficients `cᵢ = ∂f/∂Xᵢ` from a WO1 kernel via TorchLean's reverse-mode tape
    (`TapeBuilder`), reusing the model with no rewrite.
Build with `lake build UncertaintyRigor`. Pulls in Mathlib (via `Ladder`) and TorchLean (via
`Sensitivity`). -/
lean_lib «UncertaintyRigor» where
  srcDir := "uncertainty"
  globs := #[
    .one `PropertyKindCalculus.Uncertainty.Ladder,
    .one `PropertyKindCalculus.Uncertainty.ConformityLadder,
    .one `PropertyKindCalculus.Uncertainty.BudgetDagLaws,
    .one `PropertyKindCalculus.Uncertainty.Convolution,
    .one `PropertyKindCalculus.Uncertainty.Coverage,
    .one `PropertyKindCalculus.Uncertainty.Sensitivity,
    .one `PropertyKindCalculus.Uncertainty.Adequacy.Grid,
    .one `PropertyKindCalculus.Uncertainty.Adequacy.Absorption,
    .one `PropertyKindCalculus.Uncertainty.Adequacy.Soundness,
    .one `PropertyKindCalculus.Uncertainty.Adequacy.Sterbenz32,
    .one `PropertyKindCalculus.Uncertainty.Adequacy.Fp32Grounding,
    .one `PropertyKindCalculus.Uncertainty.Adequacy.DagBound,
    .one `PropertyKindCalculus.Uncertainty.Adequacy.ExecBridge,
    .one `PropertyKindCalculus.Uncertainty.Adequacy.Significance,
    .one `PropertyKindCalculus.Uncertainty.Experiments.PRSimulation,
    .one `PropertyKindCalculus.Uncertainty.Experiments.EagerProvenance]

/-- **Stage 4 of the uncertainty workstream** (see `UNCERTAINTY.md` §6, "Scale"): the batched
SSPRC/MCM propagators that run the write-once `[NumCarrier α]` kernel at the `CudaT` batch carrier —
all `Nᵢ` samples of an input in one launch (a GPU kernel under `-K cuda`, the portable CPU stub
otherwise). Its own library because it depends on the TorchLean `CudaT` carrier, which the
Mathlib/TorchLean-free Stage-0 `Uncertainty` library cannot carry. Note `lake build` only
*typechecks* these modules: `CudaT`'s device ops are `@[extern]` FFI with no interpreter fallback,
and `precompileModules` cannot load the TorchLean graph into the elaborator (it shared-links whole
libraries, and the upstream `ProofWidgets`/`QuantumInfo` `:shared` facets do not build), so a batched
result is *run* — and checked against the scalar reference — only by the `ssprc_batched_parity`
executable below. Build with `lake build UncertaintyBatch`. -/
lean_lib «UncertaintyBatch» where
  srcDir := "uncertainty"
  globs := #[.one `PropertyKindCalculus.Uncertainty.SsprcBatched]

/-- **Stage-4 parity harness** (the one executable this package produces). `CudaT`'s device ops are
`@[extern]` FFI with no interpreter fallback, and the TorchLean dependency graph cannot be
`precompileModules`-loaded into the elaborator (upstream `ProofWidgets`/`QuantumInfo` `:shared`
facets do not build), so the batched propagator's numbers cannot be `#guard`ed at build. A compiled
executable links the native `CudaT` code directly, so this harness *runs* `SsprcBatched.run` and
asserts it agrees with the scalar `Ssprc.run`. Run with `lake exe ssprc_batched_parity` — the default
build uses the portable CPU stub (float32, no GPU), a `-K cuda=true` container build runs it on the
device. Exits `0` on parity, `1` on mismatch. -/
lean_exe «ssprc_batched_parity» where
  srcDir := "apps"
  root := `PropertyKindCalculus.Apps.SsprcBatchedParity

/-- Worked uncertainty examples grounded in the two source papers (Degenhardt 2025 fictive
example; Willink 2005 gauge-block), in the `examples/` source tree as a **separate library** so
no *library* module carries `#eval`/`#guard`. Build with `lake build UncertaintyExamples`. -/
lean_lib «UncertaintyExamples» where
  srcDir := "examples"
  globs := #[.andSubmodules `PropertyKindCalculus.UncertaintyExamples]

/-- **Documentation-math rendering** (`docgen/` source tree, namespace
`PropertyKindCalculus.DocGenMath`; see `RENDERING.md`). Renders a `@[pkc_math]`-annotated `Quantity`
definition as human-friendly typeset LaTeX on its doc-gen4 page, via a three-stage presentation
pipeline (lift `Expr → MathTerm`, faithful normalize, precedence pretty-print). It writes the
rendered `$$…$$` equation **and** the definition's Lean source into each decl's own docstring via
core Lean's `Lean.addDocStringCore` (2026-08-04 pivot — `RENDERING.md` §6 v2), so it depends on the
core spine + core `Lean` only, **not** on doc-gen4; the core spine never imports it either. doc-gen4
(and the Lean InfoView) then typeset the docstring math with no special support. The worked example
and its `#guard_msgs` regression pins live in the `Examples` library
(`PropertyKindCalculus.Examples.DocGenMathDemo`), so no module here carries `#eval`/`#guard`.
Build with `lake build DocGenMath`. -/
lean_lib «DocGenMath» where
  srcDir := "docgen"
  -- `roots` is explicit because the doc build renders `lib.rootModules` (see the NOTE above).
  roots := #[`PropertyKindCalculus.DocGenMath]
  globs := #[.andSubmodules `PropertyKindCalculus.DocGenMath]

/-- **The self-index** (source tree `index/`, namespace `PropertyKindCalculus.Index`): the
environment walks that enumerate the library's own annotations, kinds, ontology values, kinded
records and kinded operations as *data* — `IndexTable`s of `IndexCell`s — rather than as the `info`
messages `#kind_edges` and `#kind_boundary_audit` print.

It exists because a *document* needs the rows. The blueprint chapter "Using the library" and the
doc-gen4 index page both render these tables, and both live in Verso-backed packages that the core
must not depend on; so the harvest lives here (plain `Lean` + the core spine + `DocGenMath` for the
rendering attributes) and each document supplies its own ~30-line adapter. That split is also what
lets **downstream** repositories render the same tables: soil-moisture-model requires this package
from git and so can import `PropertyKindCalculus.Index`, but cannot reach `blueprint/`.

`roots` is explicit because the doc build renders `lib.rootModules` (see the NOTE above).
Build with `lake build Index`. -/
lean_lib «Index» where
  srcDir := "index"
  roots := #[`PropertyKindCalculus.Index]
  globs := #[.andSubmodules `PropertyKindCalculus.Index]

/-- **The generated index page** — one module whose *module docstring* is written by
`#pkc_index_page` from the environment, so doc-gen4 renders the whole self-index as that module's
page. Same trick `@[pkc_math]` uses to get typeset equations onto an API page: write markdown into a
docstring and let doc-gen4 do the rest.

A separate library from `Index` because it must **import what it indexes** (the worked examples, the
rendering pipeline), and the harvest has to stay importable by anything without dragging those along.
Build with `lake build IndexPage`; `scripts/build-api-docs.sh` renders it. -/
lean_lib «IndexPage» where
  srcDir := "index"
  roots := #[`PropertyKindCalculus.IndexPage]
  globs := #[.one `PropertyKindCalculus.IndexPage]
