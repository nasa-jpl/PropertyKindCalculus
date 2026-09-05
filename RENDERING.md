# PKC ↔ doc-gen4 Math Rendering — Cross-Session Plan

**Status:** 2026-08-04 — **ARCHITECTURE PIVOT (per doc-gen4 maintainer review) — DONE.** The doc-gen4
PR #403 (env-extension hook) was **closed**: maintainer `hargoniX` pointed out (1) most projects don't
have doc-gen4 in their dependency closure (docs are built by a separate docbuild project), so a producer
API *in* doc-gen4 is unreachable; and (2) the built-in **docstring** env-extension already flows into
doc-gen4 for free. Both correct. **New design: `@[pkc_math]` writes the rendered `$$…$$` (now *plus* the
definition's Lean source) into the declaration's own docstring via core Lean's `Lean.addDocStringCore`
— no doc-gen4 dependency, no doc-gen4 changes.** This also reaches the **Lean InfoView** (whose bundle
ships MathJax, so docstring math typesets in its **hover popups** — note the *goal* panel shows a type and
never a docstring, and VS Code's *native* editor hover has no math renderer), which the doc-gen-only hook
never could. Rendering default = **F (faithful),
CONFIRMED**. Remaining = follow-on (apply `@[pkc_math]` to real SMM/EM models). No library module imports
doc-gen4; the `../doc-gen4` **dev override was removed** — doc-gen4 is resolved at the stock tag that
PhysLib and TorchLean already pin transitively (`v4.33.0`, `aceca4ee`; it cannot be dropped *entirely* —
both require it, this Mathlib pin does not), and is only ever resolved, never built here.
**This file is the durable, multi-session tracker.** Update the checkboxes and the "Session log"
at the bottom every time you make progress. A fresh session should read this header, §2 (repo map) and §4
(checklist) first.

> **Superseded below:** Phase P and Phase S describe the *old* doc-gen4-hook route (`addDeclMath` /
> `getDeclMath?` / the `getDocString?` edit / PR #403). That route is **abandoned**; it is kept for the
> record. The live mechanism is the docstring-append in Phase B / §6, marked **(v2)**.

---

## 0. TL;DR

Render PKC-annotated `Quantity` definitions as human-friendly **typeset math** on the doc-gen4 HTML
pages — like the ASCII comment `σ⁰ = a·ndvi + exp(−2·b·ndvi)·c·r + d` in
`soil-moisture-model/src/algorithm/avs/linearized/kinds.lean`, but real LaTeX.

**One deliverable (B) + one enabling PR (P):**

- **B — typeset LaTeX from the def, via an IR + rewriting/recognition pipeline.** A `@[pkc_math]`
  attribute lifts the def's value `Expr` into a presentation AST, normalizes/recognizes it, and emits
  `$$…$$`. **Not** a 1-1 transcription — see §5. This is the whole project.
- **P — a small, generic doc-gen4 PR** (env-extension `addDeclMath`/`getDeclMath` + `Info.extraDocs` +
  a MathJax-processed render block) so B injects cleanly instead of abusing docstrings.

**~~C — unexpanders~~ DROPPED (2026-08-03):** only improved the raw Lean-code equation block (which
MathJax skips anyway), stayed ASCII, and would perturb `Quantity.mul` printing everywhere. Not worth it.

**Order of work:** P (hook) → B (IR + walker + attribute) → V (build docs, verify) → S (submit PR).
Applying B to SMM's real models (`lavsForwardQ`, and Xiaolan's EM models) is a follow-on, not in scope.

---

## 1. Background — how doc-gen4 renders, and why B needs its own block

doc-gen4 does **no math rendering of its own**. For a `def` it renders the defining equation `lhs = rhs`
by delegating to Lean's pretty-printer, then tags → HTML (`Process/DefinitionInfo.lean:15` `valueToEq`
→ `Process/Base.lean:235` `prettyPrintTerm` → `ppExprWithInfos` → `RenderedCode.lean:240` `renderTagged`
→ `Output/Definition.lean:11` → `<li class="equation">`).

Two facts that shape B:

- **MathJax is loaded** (`Output/Template.lean:29-31`) and processes **docstrings** (`$…$`/`$$…$$`,
  `Output/DocString.lean:266-273`) — **but not the equation block** (`equation`/`equations` are in
  MathJax's `skipHtmlTags`, `static/mathjax-config.js`). So B cannot piggyback on the equation block; it
  needs its **own** MathJax-processed block → that is what Phase P adds.
- The equation body is a **tiny closed alphabet**: `Quantity.mul (_h : ProductKind ..) a b`
  (`PropertyKindCalculus/QuantityClassification.lean:99` — `ProductKind` is a **`Prop`** → `_h` is a
  droppable proof), `instAdd`/`instSub` (`PropertyKindCalculus/Quantity.lean:228-230`), `Quantity.exp`
  (drop the `TranscendentalKind` Prop), `Quantity.mk` literals. Small alphabet ⇒ the lift in §5 is small.

---

## 2. Repo & toolchain map — READ FIRST every session

*Environment recorded 2026-08-04. The rows below name checkouts outside this repository, so
`scripts/check-doc-pins.py` reports them rather than gating them; only this package's own pins are
gated.*

| Repo / clone | Path | Branch | Toolchain | Role |
|---|---|---|---|---|
| doc-gen4 (our copy) | `/home/nfr/projects/lean/doc-gen4` | `pkc-math-hook` (off tag `v4.32.0`, `092d631`) | **v4.32.0** | dev + PR branch. **Builds green** (mathlib-free). |
| doc-gen4 `main` | same repo | `main` = upstream `feb58b8` | v4.33.0-rc2 | tracks upstream; **PR rebases onto this before submit** |
| doc-gen4 `fix/*` | same repo | `fix/combined-img-svg`, `fix/generalize-git-forge-urls` | — | **user's own work — do not touch** |
| PKC (this session) | `/home/nfr/projects/lean/PKC` | `feat/pkc-math-rendering` (re-synced to `71b7508`) | v4.32.0 | **where we implement B** |
| PKC (concurrent session) | `/home/nfr/projects/lean/PropertyKindCalculus` | `main` (`71b7508`, + uncommitted WIP) | v4.32.0 | **another Claude session — do not touch** |

**Toolchain tension (critical):** upstream doc-gen4 `main` is v4.33.0-rc2, but PKC is v4.32.0, and
doc-gen4 is built with the *root project's* toolchain when required as a dependency. So all dev/testing
happens on doc-gen4 **`pkc-math-hook` (v4.32.0)**. Only at submit (Phase S) do we rebase the small hook
diff onto `main` — the hook is toolchain-agnostic, so trivial.

**Concurrency rules:**
- Never edit `/home/nfr/projects/lean/PropertyKindCalculus` (concurrent session).
- Pull its *committed* progress into our clone: `git fetch local && git rebase local/main` (the `local`
  remote = the sibling working copy). It has advanced to `49ab475`; rebase before Phase B. Their
  uncommitted WIP (incl. `QuantityClassification.lean`) is intentionally excluded.
- A third peer clone, if needed: mirror the pattern (clone from `local`, repoint remotes).

---

## 3. Where the code lives (design decision)

The **reusable mechanism goes in PKC**, over PKC's own `Quantity`/`Quantity.mul`/`Quantity.exp`/
`ProductKind` — fully general, not SMM-specific. `lavsForwardQ` & Xiaolan's EM models are *follow-on*
applications. In PKC we build the mechanism + a **self-contained demo** using PKC primitives + demo kinds.

Proposed new PKC lib (keep the core spine clean — mirror the blueprint/crossref separation):

- `docgen/` → `lean_lib «DocGenMath»` — the **B** IR + walker + `@[pkc_math]` attribute + the
  presentation-rewrite/recognition registry. **(v2) Imports core Lean + PKC core only — NOT doc-gen4.**
  `Attr.lean` writes into the built-in docstring extension (`Lean.addDocStringCore`); the library has no
  doc-gen4 dependency at all. Docs-only; never imported by the core spine.
- demo/tests under `examples/`/`tests/`: `#eval`/`#guard_msgs` pins for the LaTeX of demo defs, plus a
  demo def rendered end-to-end. **(v3, 2026-08-04) — as planned:** `examples/PropertyKindCalculus/
  Examples/DocGenMathDemo.lean` (`lean_lib «Examples»`). It briefly lived inside `DocGenMath` as
  `Demo.lean`; moved back out so no library module carries `#eval`/`#guard`.

---

## 4. Phased checklist

### Phase 0 — Setup ✅ DONE (2026-08-03)
- [x] Fetch upstream doc-gen4; `main` ff'd to `feb58b8` (v4.33.0-rc2).
- [x] doc-gen4 dev branch `pkc-math-hook` off tag `v4.32.0`; **builds green** (194 jobs, exe produced).
- [x] Clone PKC → `/home/nfr/projects/lean/PKC`; remotes repointed (`origin`=JPL, `maap`, `local`=sibling); branch `feat/pkc-math-rendering`.
- [x] Plan written; option C dropped; IR design folded in (§5).

### Phase P — doc-gen4 hook PR (see §6) — ⛔️ SUPERSEDED 2026-08-04 (route abandoned; kept for record)
- [x] New `DocGen4/Process/DeclMath.lean`: `declMathExt` (`SimplePersistentEnvExtension (Name×String) (NameMap String)`) + `addDeclMath declName markdown` (downstream API) + `getDeclMath? env declName` (reader).
- [x] `getDocString?` (`DocGen4/Process/NameInfo.lean`) appends the attached markdown to the docstring (none/`.inl`/`.inr`) → renders through the existing **MathJax-processed** docstring path. **No new `Info` field, no Output change, no DB-schema change.** Mirrors the `getRecommendedSpellingText` precedent.
- [x] Wired into `DocGen4/Process.lean`; `lake build` **green (196 jobs)**.
- [ ] Commit on `pkc-math-hook` (awaiting user OK). Do NOT push until Phase V green (Phase S).

### Phase B — IR + Expr→LaTeX + `@[pkc_math]` (see §5) — the core — ✅ DONE + green 2026-08-03
All in `docgen/PropertyKindCalculus/DocGenMath/` (`lean_lib «DocGenMath»`, `srcDir := "docgen"`):
- [x] **Stage 0 IR** `Term.lean`: `MathTerm` = `sym/num/neg/add/mul/frac/pow/fn/tuple` (n-ary add/mul/tuple; sub = `add[a, neg b]`), plus `MathNotation` = `latex` + `operator` (the resolved-token record the printer consumes).
- [x] **Stage 1 (Lift)** `Lift.lean`: `liftExpr : Expr → MetaM MathTerm`, defensive/total; matches PKC alphabet by head (`Quantity.mul/div/add/sub/exp/log/…/mk`, `HAdd/HSub/HMul/HDiv/HPow/Neg`, `OfNat`), drops witnesses/instances via **last-N args** + `getFunInfo` explicit-filter for unknown heads; flattens assoc. Imports `PropertyKindCalculus` (uses `` `` ``-checked names).
- [x] **Stage 2 (Normalize)** `Normalize.lean`: faithful — flatten, integer fold (`2·3→6`, `2+3→5`), drop `1·`/`+0`, `−1·x→−x`, double-neg, adjacent `x·x→x²`, scalar-first product sort (sum order preserved), **(v3)** sign hoisting `(−x)·y·z → −(x·y·z)` collected from the integer coefficient *and* negated factors together (a ring law, so still faithful) — this is what makes an exponent read `e^{-\mathrm{AvsConfig.two}\,b\,\mathrm{NDVI}}` instead of `e^{\left(-…\right)\,b\,\mathrm{NDVI}}`. (Structural `@[pkc_math_rule]` shape-rules = documented future; named-operator recognition is the registry, below.)
- [x] **Stage 3 (Pretty)** `Pretty.lean`: precedence printer (sum 10 < neg 15 < mul 20 < pow 30 < atom/tuple 40); `e^{…}`, `\sin/\cos/\log/\arcsin…`, `\frac`, sign-aware sums (`a − b`), `\left(a, b, c\right)` tuples; takes a `resolve : String→MathNotation` closure (pure/testable via `MathNotation.ofLatex`).
- [x] Symbol table + registry `Registry.lean`: `@[pkc_math_symbol "…"]` per-decl LaTeX override (the practical recognition registry) + `builtinSymbol` heuristic (Greek, `s0→s_{0}`, `ndvi→\mathrm{NDVI}`, single-letter italic, multi-letter `\mathrm`). The optional `operator` marker (`@[pkc_math_symbol "\\nabla" operator]`) declares a **bare prefix operator** so a 1-arg application juxtaposes (`\nabla x`); layout is *declared*, never inferred from the LaTeX (the heuristic `\mathrm{…}` also starts with `\` and must stay parenthesized). **(v3)** `@[pkc_math_config]` tags a *structure* as a configuration type (`TagAttribute`, `validate` rejects a non-structure), and `configFieldName?` = core's `Environment.getProjectionStructureName?` + `hasTag`. `resolveToken env` is now three tiers: `@[pkc_math_symbol]` override → configuration qualification (`\mathrm{AvsConfig.two}`) → heuristic.
- [x] **(v3)** **Derivations** `Attr.lean` + `Lift.lean`: `substitute names e` is the opt-in **delta** pre-pass (`Meta.transform`, `instantiateLevelParams` + `mkAppN … |>.headBeta`, `.visit` so nested occurrences expand) run *before* the lift, so an inlined body's `let`s zeta-reduce as usual. `isSubstitutable` rejects a self-mentioning definition (which would not terminate) at attribute time, alongside rejecting a literal override combined with `substituting`. Idents in the attribute resolve through `realizeGlobalConstNoOverload` in `AttrM` — the ambient namespace *is* available at `afterCompilation` (verified by the demo pins).
- [x] `@[pkc_math]` attribute `Attr.lean`: `quantityToLatex declName : MetaM String` (lambdaTelescope value → lift → normalize → pretty; LHS via `resolveToken`), `@[pkc_math]` / `@[pkc_math "…literal…"]`. **(v2, 2026-08-04)** — no longer `addDeclMath`; instead runs at `applicationTime := .afterCompilation` and writes into the declaration's **own docstring** via `Lean.addDocStringCore`, appending both the `$$…$$` and (new) the **definition's Lean source** as a ```` ```lean ```` block (`defSource?` = `ppSignature` + delaborated body, decl name shortened to its base). `afterCompilation` is required so the authored `/-- … -/` docstring is already attached and preserved (at the default `afterTypeChecking` it is not yet present and would clobber ours — verified empirically). **No doc-gen4 import.**
- [x] The demo + regression pins: dimensionless-kind demo; `@[pkc_math_symbol "\\sigma^0", pkc_math] def avsForward` renders `\sigma^0 = a\,\mathrm{NDVI} + e^{-2\,b\,\mathrm{NDVI}}\,c\,r + d`; **(v3)** 8 `#guard_msgs` pins (4 pure-stage incl. tuples + 3 `quantityToLatex` incl. `columns` for tuple/head-layout + 1 docstring read-back on `noted` asserting prose + `$$…$$` + the ```` ```lean ```` source) — all green. **(v3, 2026-08-04)** moved out of the `DocGenMath` library to `examples/PropertyKindCalculus/Examples/DocGenMathDemo.lean` (`lean_lib «Examples»`, namespace `PropertyKindCalculus.Examples.DocGenMathDemo`), so no `DocGenMath` module carries `#eval`/`#guard` — the same library/example split as `UncertaintyExamples`. Build with `lake build PropertyKindCalculus.Examples.DocGenMathDemo`.
- [x] **(v4, 2026-08-05)** **Systems, cases, `where`, transparent wrappers** — the shapes a model
  outside this repo is actually written in (found by rendering soil-moisture-model's Mironov
  dielectric, where the old output was *malformed LaTeX* on the published page):
  `Term.lean` gains `record` / `cases` / `raw` nodes plus `MathSystem` (a term + its auxiliary
  equations); `raw` is what guarantees an unreadable leaf degrades to escaped `\text{…}` instead of
  pretty-printed Lean inside `\mathrm{…}` (`Registry.latexText`).
  `Lift.lean` gains `KeepPolicy` (`inlineAll`/`keepAll`/`keepOnly`) and runs in
  `LiftM = StateRefT (Array (MathTerm × MathTerm)) MetaM` so a kept `let` (bound via `withLetDecl`,
  so the body keeps the author's name) emits an auxiliary equation; `liftMatcher` reads
  `Meta.matchMatcherApp?` — one alternative = a destructuring binder (name the components, emit
  `(n, k) = …`), several = `cases`, with patterns from `Match.getEquationsFor` (**not** constructor
  order, which would mislabel a reordered match); structure literals lift to `record` via
  `getStructureFields` (guarded by `isStructure` — `getStructureFields` *panics* otherwise, and Lean's
  strict `let` made an unguarded call crash the whole elaboration); `letBinderNames` backs the
  attribute's rejection of an unbound `keeping` name.
  `Term.lean` also carries the two name refinements: `MathTerm.countSym` + `MathSystem.collapseAliases`
  (a single-use field alias absorbs its auxiliary equation), and the lift disambiguates a re-bound
  `let` name (`ωτ`, `ωτ2`) rather than dropping or shadowing it.
  `Pretty.lean` gains `\begin{cases}`, inline records, and `prettyEquation`/`prettyAux` (the aligned
  system, and the `where` block; one row prints as a plain equation, not a one-line `aligned`).
  `Registry.lean` gains `@[pkc_math_transparent]` + `latexText`. `Attr.lean` gains the `keeping`
  clause, `MathRendering` (equation + optional `where`), and `quantityToRendering`; `mathMarkdown`
  interleaves the `where` block after the equation and after each derivation step.
  6 new `#guard_msgs` pins (transparent wrapper, record system, destructuring docstring read-back,
  a **reverse-order** `match`, and `keeping` in all three modes) — all green, and the 12 pre-existing
  pins are byte-identical, so an un-annotated definition renders exactly as before.
- [x] **(v2)** `lakefile.lean`: `Attr.lean` no longer imports doc-gen4, so `lean_lib «DocGenMath»` depends on core Lean + PKC core only; `lake build DocGenMath` green (31 jobs) **without building doc-gen4**. The `require «doc-gen4» from "../doc-gen4"` **override was removed** and `lake update doc-gen4` reconciled the manifest (doc-gen4 `path → git` at the stock `092d631`/`v4.32.0` already in `.lake/packages`, now `inherited:true`; the only other diff is a benign `Cli` `inputRev` metadata shift — same resolved rev; **PhysLib/TorchLean/mathlib unchanged, no branch drift, no network**). doc-gen4 stays only because PhysLib and TorchLean each require it transitively — it can't be dropped entirely — but nothing here imports or builds it.

### Phase V — verification / end-to-end (see §7)
**(v2, 2026-08-04) — re-verified with the docstring-append mechanism + source block, STOCK doc-gen4 path.**
`lake build DocGenMath` green (31 jobs, **no doc-gen4 built** — DocGenMath imports core Lean + PKC only).
The `noted` `#guard_msgs` pin reads the docstring back at build time = transport proof (prose + `$$…$$`
+ ```` ```lean ```` source). Re-ran `lake build …Demo:docs` (had to `rm -rf .lake/build/doc` to defeat a
stale `fromDb` replay; genCore/`api-docs.db` cache reused): `avsForward`'s page now shows, in order,
(1) the authored prose `<p>`, (2) `<p>$$\sigma^0 = a\,\mathrm{NDVI} + e^{-2\,b\,\mathrm{NDVI}}\,c\,r + d$$</p>`
(MathJax typesets — `$$`=displayMath, `<p>`∉skipHtmlTags), (3) a `<pre>` Lean code block with the real
source `def avsForward … := Quantity.mul pk a ndvi + …` (`⟨-2⟩`→`{ magnitude := -2 }`). Rendered by the
**normal docstring path** — the inert `pkc-math-hook` in `../doc-gen4` contributes nothing (nothing calls
`addDeclMath`), so this is what unmodified doc-gen4 produces. **InfoView:** the shipped
`lean4-infoview` bundle carries MathJax + remark-math/rehype-mathjax, so the same docstring math typesets
in the editor's InfoView (native mouse-hover tooltip uses VS Code markdown → shows literal `$$…$$`).

**(v1) — original Phase V (doc-gen4-hook route):**
- [x] Local doc-gen4 override wired; `lake update doc-gen4` repoints the manifest to the local path (`"dir": "/home/nfr/projects/lean/doc-gen4"`). `lake build DocGenMath` **green, 33 jobs**.
- [x] **Transport proven** (this substitutes for most of Phase V): a separate `lake env lean` process imported the `Demo` olean and read back `$$\sigma^0 = …$$` via `getDeclMath?` — exactly doc-gen4's own path (load target oleans → `getDocString?` → `getDeclMath?`). So the data reaches the renderer.
- [x] **HTML generated + verified** (2026-08-03): `lake build PropertyKindCalculus.DocGenMath.Demo:docs`
  (doc-gen4 v4.32.0 DB pipeline `genCore`→`single`→`fromDb`; module facet `docs`) → **300 jobs green**.
  Output: `.lake/build/doc/PropertyKindCalculus/DocGenMath/Demo.html`. `avsForward`'s doc carries
  `<p>$$\sigma^0 = a\,\mathrm{NDVI} + e^{-2\,b\,\mathrm{NDVI}}\,c\,r + d$$</p>` in the **docstring prose**
  (after the description `<p>`, before the auto `<details>Equations</details>` — i.e. NOT the skipped
  `equations` block). MathJax is loaded (`mathjax@3/es5/tex-mml-chtml.js` + `mathjax-config.js`), and
  `mathjax-config.js` has `displayMath: [["$$","$$"]]` with `skipHtmlTags` listing `code`/`equation`/
  `equations`/`decl_*` but **not `p`** → the block is processed and typeset. **Acceptance met** (only the
  literal browser-pixel view is left to the user). bibPrepass handled the missing bib gracefully
  ("reference page disabled"). doc-gen4 exe built from the local override; no mathlib compiled.

### Phase S — submit PR — ⛔️ SUPERSEDED 2026-08-04 — **PR #403 CLOSED** (maintainer review → library-side pivot; see header + §6 (v2))
- [x] Rebased the Phase-P diff onto doc-gen4 `main` (v4.33.0-rc2) **in a git worktree** (so the main
  `../doc-gen4` checkout stays on `pkc-math-hook` for the PKC override + a concurrent editor). Branch
  `declmath-hook` = `feb58b8` + `aad7b98`. **Drift fixed:** on v4.33 `getDocString?` returns
  `Option (String ⊕ (VersoDocString × String))` and `Output.docStringToHtml` uses **only the Markdown
  string** for both cases (`versoDocToMarkdown` renders Verso→md; native Verso render is a TODO) — so the
  hook now appends the attached Markdown to that `md` string (cleaner than the v4.32 edit). `DeclMath.lean`
  is toolchain-agnostic, copied verbatim. **Build-verified: `lake build DocGen4` green, 131 jobs on v4.33.0-rc2.**
- [x] Pushed `declmath-hook` to `origin` (NicolasRouquette/doc-gen4); opened PR #403 against
  `leanprover/doc-gen4:main`, ready-for-review (user chose non-draft). 3 files: `Process.lean` (+1 import),
  `Process/DeclMath.lean` (new), `Process/NameInfo.lean` (`getDocString?`). Generic wording, no PKC vocab.

### Follow-on
- [x] **Apply `@[pkc_math]` to the kinded PKC example models** — DONE 2026-08-04 (session 4):
  `attenuationQ`, `lavsForwardQ`, `lavsResidualQ` (`Examples/AvsForward.lean`), `wcmForwardQ`
  (`UncertaintyExamples/WaterCloudModel.lean`), `fictiveModelQ` (`UncertaintyExamples/DegenhardtFictive.lean`).
  See session log for the let-zeta engine change + the auto-vs-override split.
- [x] **Publish the API site** — DONE 2026-08-04 (session 5). `scripts/build-api-docs.sh` renders the
  doc-gen4 site and stages it under `docs/api/`, next to the Verso blueprint at the `docs/` root; both
  go to the orphan `gh-pages` branch via the existing `scripts/publish-pages.sh`. Wired into
  `.github/workflows/blueprint.yml` (Phase 4b) and `blueprint/scripts/ci-pages.sh` (`--no-api` to skip),
  always **after** `stage-docs.sh`, which wipes `docs/`. This is the first stage that *builds* doc-gen4
  (~131 jobs); nothing imports it. Scope = the **Mathlib-free tier** (`PropertyKindCalculus`, `Examples`,
  `DocGenMath`) — see the session log for why the Mathlib-backed libraries are excluded.
- [ ] Register SMM/EM named helpers + apply `@[pkc_math]` to the *downstream* SMM `lavsForwardQ` and
  Xiaolan's models (in `soil-moisture-model`, not the PKC example mirror).
- [x] **Engine knob — derivations** — DONE 2026-08-04 (session 6), shipped as `substituting` rather than
  `expand`, together with `@[pkc_math_config]` and sign hoisting; see §5 and the session log. The caveat
  recorded when this was proposed still holds and is now the documented policy line: a derivation does
  **not** recover the authored `e^{-2\,b\,\mathrm{NDVI}}`, because `cfg.two` is a `def` parameter — it
  recovers `e^{-\mathrm{AvsConfig.two}\,b\,\mathrm{NDVI}}`. Folding that to the literal `-2` asserts
  `cfg.two = 2`, which is **E tier** and out of policy; the literal `@[pkc_math "…"]` override remains
  the sanctioned escape hatch.

---

## 5. Design — B: the IR + rewriting/recognition pipeline (the crux)

**Do NOT map `Expr → LaTeX` directly.** Real models (Xiaolan's computational-EM) are deep and their
*computed* op-tree deliberately differs from the *intended* math (e.g. LAVS left-associates
`((((2·ndvi)·c)·r)·att)` for bit-identity with the kernel). Direct transcription = unreadable. Three stages:

**Stage 1 — Lift `Expr → MathTerm`.** Presentation AST; strip Prop/instance/mdata noise; **flatten
associativity** to n-ary `Mul`/`Add`. Most ugliness dies here, faithfully.

**Stage 2 — Normalize + Recognize `MathTerm → MathTerm`.** Two kinds of transform:
- *Faithful normalizer* (always on): comm-sort (scalars first), numeral folding, `x·x→x²`, `exp x→e^x`,
  `a+(−b)→a−b`, common-subexpr → `\text{where}` bindings. All meaning-preserving under ring/field laws.
- *Recognition registry* (`@[pkc_math_rule]`, global): match a sub-term → a **named operator/notation**
  (`curl E ↦ \nabla\times E`, inner products, Green's functions). Faithful-by-construction (just notation)
  and the **highest-leverage** prettifier for complex models. (This is where the ex-C "recognize a shape,
  emit notation" idea now lives — at the IR level, with global CSE/reassoc that syntax unexpanders can't do.)

**Stage 3 — Pretty-print `MathTerm → LaTeX`.** Operator-precedence printer owning all parenthesization
and spacing, so stage-2 rules never think about parens.

Worked example (LAVS ∂/∂b): `mul h₁ (mul h₂ (mul h₃ (mul h₄ ⟨2⟩ ndvi) c) r) att)`
→ (lift+flatten) `Mul[2,NDVI,c,r,att]` → (sort + recognize `att`=`E`) `Mul[2,c,r,NDVI,E]`
→ (print) `2\,c\,r\,\mathrm{NDVI}\,E`. **Entirely faithful** — no editorial assertion needed.

### Constants and configuration types (`@[pkc_math_config]`)

A model's named constants live in a configuration structure and are read through a field projection
(`cfg.two` = `AvsConfig.two cfg`). Untagged, that is just an unrecognized application and renders
`\mathrm{two}\left(\mathrm{cfg}\right)` — the field stripped of the type it belongs to, applied to a
value that carries nothing for the reader. `@[pkc_math_config]` on the **structure** declares its
fields to be constants of the model, so the projection renders as the qualified constant
`\mathrm{AvsConfig.two}` and the configuration value is elided.

The tag is what makes this safe. A blanket "drop the receiver of any projection" rule would turn
`p.fst` into `\mathrm{fst}`; opting in per type confines the rule to structures whose fields really
are constants. An individual field can still be given its own notation with `@[pkc_math_symbol]`,
which wins over the qualification.

**This is F tier**: qualifying a name is notation, and eliding the configuration value asserts
nothing about it. Rendering `cfg.two` as `2` would be a different claim entirely — `two` is a `def`
*parameter*, so a value for it is an **E**-tier assertion about the configuration and is out of
policy. Use the literal `@[pkc_math "…"]` override when a doc page must show the deployed numeral.

### Derivations by substitution (`@[pkc_math substituting …]`)

The equation as written is faithful but often folded: `lavsForwardQ` renders
`a\,\mathrm{NDVI} + \mathrm{attenuationQ}\left(\mathrm{cfg}, b, \mathrm{NDVI}\right)\,c\,r + d`.
A reader wants both that *and* the expanded form. `@[pkc_math substituting attenuationQ]` renders the
equation as written, then again with the named helper inlined. Each `substituting` clause is one
**step**, and step *n* applies the union of clauses 1..*n*, so the equations refine one another:

```lean
@[pkc_math substituting lavsForwardQ substituting attenuationQ]
def lavsResidualQ … := s0 - lavsForwardQ cfg a b c d ndvi r
```

⟶ `s_{0} - \mathrm{lavsForwardQ}\left(…\right)`, then
`s_{0} - \left(a\,\mathrm{NDVI} + \mathrm{attenuationQ}\left(…\right)\,c\,r + d\right)`, then
`s_{0} - \left(a\,\mathrm{NDVI} + e^{-\mathrm{AvsConfig.two}\,b\,\mathrm{NDVI}}\,c\,r + d\right)`.
Zero clauses ⟶ byte-identical output to a bare `@[pkc_math]`.

Substitution is **delta**, the opt-in counterpart to the `let`-**zeta** Stage 1 always performs. It
runs as a pre-pass on the `Expr` before the lift, so an inlined body's own `let`s are zeta-reduced
exactly as if written at the use site. Delta is meaning-preserving, so **every line of the chain is F
tier** — each still denotes exactly what the definition computes. It is therefore *not* a way in to
editorial rewriting: a literal override and a derivation are mutually exclusive and rejected
together, and a recursive definition is rejected as unsubstitutable (inlining would not terminate).

This gives the F tier a second answer to *"the source form is faithful but hard to read"*, next to
the presentational-sibling escape hatch below. Prefer `substituting` when the helper is a real
definition the reader should see expanded; keep the sibling for when genuine **algebra** — not mere
unfolding — is what makes the equation legible.

### Systems of equations — record results, `match`, and `where` (v4, 2026-08-05)

Three shapes that real models are written in, none of which the F-tier pipeline could read until
now. All three were found by rendering `soil-moisture-model`'s Mironov dielectric — the first model
outside this repo with a genuinely non-trivial authored surface — where the `@[pkc_math]` output was
not merely ugly but **malformed LaTeX**: unbalanced parens and pretty-printed Lean source dumped
inside `\mathrm{…}`, published to the API site.

**A record result is a system, not an equation.** `mironovNK` returns a seven-field record of
refractive-index parameters. A definition like that has no single defining equation, so the lift
reads the structure literal as a `record` node and the printer emits the aligned system

```latex
\begin{aligned} n_d &= … \\ k_d &= … \end{aligned}
```

one row per field, each left-hand side resolved through the registry like any other token. (A record
met *inside* a larger expression stays inline, `\{ n_d = …,\; k_d = … \}`.)

**`match` is case analysis.** A multi-alternative match renders `\begin{cases}`, each branch labelled
with the pattern it holds for. The patterns come from the matcher's own **equation lemmas** —
`MatcherInfo` records arities, not patterns — which matters: alternatives are compiled in the order
*written*, so guessing labels from constructor order silently mislabels every `match` that lists its
cases in another order. The demo pins a match written in reverse constructor order for exactly this
reason. When the equations are unavailable the branch is labelled `\text{case i}`, never guessed.

**A destructuring `let` is a `where` equation.** `let (n, k) := nkOfEps …` elaborates to a one-branch
match. There is no case analysis to show, and inlining it repeats the scrutinee once per component,
so the binder is *named*: the pair becomes one auxiliary equation `(n, k) = \mathrm{nkOfEps}(…)`
below the equation it serves.

**`@[pkc_math keeping …]` — the inverse of the `let`-zeta.** Stage 1 inlines `let` bindings, which is
right for one threaded intermediate and ruinous for a shared one: a Debye denominator used by four
outputs is duplicated four times and the equation grows past reading (the un-kept `mironovNK`
rendered a single 2 587-character line). `keeping` binds them instead, as the equation's `where`
block — `keeping` alone keeps every binding, `keeping d, ω` keeps the named ones and inlines the
rest. A name that binds nothing is rejected at attribute time rather than silently ignored.

Two refinements the Mironov model forced, both about *names*:

- **Aliases collapse.** A definition that binds its outputs with `let` and then packs them into a
  record renders `n_d = \mathrm{nd}` above `\mathrm{nd} = …` — the same thing said twice. When a
  field's value is nothing but the name of an auxiliary equation used **exactly once**, the field
  takes that equation's right-hand side and the equation goes away. The single-use condition is what
  keeps this from duplicating anything: an intermediate two fields share stays a named equation,
  which is the entire point of keeping it.
- **Shadowed names disambiguate.** `denomB` and `denomU` each open with their own `let ωτ := ω·τ`,
  so keeping both would put two equations with one left-hand side and two right-hand sides in a
  single block. The second becomes `\mathrm{ωτ}_{2}` (the suffix rides the trailing-digit subscript
  rule). Inlining the shadowed bindings instead was the first attempt and read *worse* — it turned
  `ωτ² + 1` into `ω\,τ\,ω\,τ + 1`, because the faithful normalizer folds powers only from adjacent
  equal factors.

All of this is **F tier**: naming a subterm, splitting a record into its fields, and showing a branch
under the condition that selects it are presentation, not algebra. Each rendering still denotes
exactly what the definition computes.

### Notational wrappers (`@[pkc_math_transparent]`)

A carrier's numeral injection — `ofN (n : Nat) : α := (n : α)` — is notation, not content, but it
renders `\mathrm{ofN}\left(2\right)` wherever a model writes a constant. Tagging it
`@[pkc_math_transparent]` renders an application as its argument, so the equation reads `2`. Still F
tier: `ofN 2` *is* `2`.

The tag belongs only on a wrapper that is genuinely transparent. A crossing that **scales** —
`clayPctOfMassFraction c = c·100` — is not: hiding it would drop the factor. Those keep the ordinary
application layout, and `@[pkc_math_symbol]` gives them their conventional notation. This is the same
opt-in discipline as `@[pkc_math_config]`, and for the same reason: the blanket rule is wrong.

### Breaking a wide equation (v5, 2026-08-05)

A rendered equation had no width limit, and some are far wider than a documentation page:
`lavsJacResidualQ`, a four-component Jacobian tuple, came out at ~240 characters of LaTeX on one
line and made the whole doc-gen4 page scroll horizontally.

**MathJax cannot be asked to fix this.** Automatic display-math line breaking is a MathJax **4**
feature (`displayOverflow: 'linebreak'`); doc-gen4 loads MathJax 3, and upstream `main` still does as
of its v4.33.0-rc2 toolchain bump (`DocGen4/Output/Template.lean` hardcodes
`cdn.jsdelivr.net/npm/mathjax@3/es5/tex-mml-chtml.js`). Bumping it upstream is a small, worthwhile PR
— one CDN URL plus a `chtml` config key — and would benefit every Lean doc site; it is not a
prerequisite for the below.

So the break is authored into the LaTeX, in `Pretty`, which is the right stage for it: it already
owns every space and parenthesis, and `MathTerm` is **n-ary**, so the seams a reader would break at
are explicit nodes (`add`'s summands, `tuple`'s components) rather than something to recover from a
string.

* `latexWidth` — the *visible* width of a piece of LaTeX, which is not its length: `\mathrm{}` costs
  eight characters and no glyphs, `\left(` six and one, `\tau` four and one.
* `estWidth` — the estimate over a term, charging each leaf its resolved notation's glyph count and
  accounting for the constructors that lay out **vertically**: a fraction is as wide as the wider of
  its parts, a superscript renders small, and `record`/`cases` are as wide as their widest row.
* `wideThreshold` (90 glyphs) — past it, `prettyEquation` breaks a top-level sum before each `+`/`−`
  (`\begin{aligned}` with indented continuation rows) and a top-level tuple one component per row
  (`\begin{pmatrix}` — a wide tuple here *is* a column vector, and `pmatrix` is AMSmath, which
  MathJax bundles).

Anything else is left alone: a single wide product or function application has no seam a reader would
break at, and inventing one reads worse than the scroll. Still **F** tier — the same term, laid out
over more lines.

Belt and braces: `scripts/build-api-docs.sh` also appends
`mjx-container[display="true"]{overflow-x:auto}` to the API stylesheet, so anything that still
overflows scrolls inside its own box rather than widening the page.

### Rendering philosophy — three tiers (pick the default)
- **(F) Faithful only** — normalizer + recognition; LaTeX denotes exactly what the def computes. Simplest.
- **(E) Editorial (opt-in, flagged)** — factoring/regrouping/Horner-unroll that change incidental
  structure; the pretty form becomes an *assertion* of equivalence, not a transcription.
- **(P) Proof-carrying editorial** — same as E but each rewrite discharges a `rfl`/`ring`/`simp`
  obligation proving pretty = def. Uniquely-PKC (write-once / no-naked-math applied to rendering).

**Default: F only — CONFIRMED by user (2026-08-03).** Faithful normalizer + named-operator recognition;
the LaTeX denotes exactly what the def computes. E (editorial) and P (proof-carrying) are **not**
implemented; the sibling-def path (below) is the escape hatch when a model needs real algebra to look
right. Escalate to P as a flagship feature only if we later decide certified-pretty-math is a headline.

### Scope discipline + the escape hatch
Stage 2 is **presentation-normalization + recognition, NOT a CAS/solver.** When a model needs genuine
algebra to look right, prefer PKC's existing discipline over a rewriter: author a clean **presentational
sibling** `def foo_math` and prove `foo = foo_math` (the op-tree-witness/parity pattern), then render the
sibling. Reuses `ring`/`rfl`/parity you already trust; likely cleaner than rewrite rules for the hardest
EM models.

### Rule locality (mirror mathlib's `@[simp]` split)
- **Global registry** (`@[pkc_math_rule]` / notation-recognizer table): domain conventions written once
  (EM operators, tensor conventions) → apply library-wide. The workhorse.
- **Per-decl `@[pkc_math ...]`**: what *this* declaration's doc should show — the literal-LaTeX escape
  hatch, the derivation steps (`substituting f`) whose expansions are meaningful *here* and not
  library-wide, and which `let` bindings to keep as a `where` block (`keeping`), which is a property
  of this definition's shape and nothing else. Still not a rewrite language: every per-decl knob is
  notation, delta, or naming, so it cannot make the rendering say something the definition does not
  compute. **Resolved** — see §9 #2.
- **Per-type `@[pkc_math_config]`**: one tag on a configuration structure covers all of its fields.
  Between global and per-decl: it is a property of the *type*, so it is stated once where the type is
  declared rather than repeated at every model that reads a constant from it.
- **Per-declaration-of-a-wrapper `@[pkc_math_transparent]`**: likewise stated once, where the wrapper
  is declared, rather than at each of the hundreds of call sites that write a constant through it.

---

## 6. Design — the docstring-append mechanism

### (v2, 2026-08-04) — THE LIVE DESIGN: write into the built-in docstring, no doc-gen4 change

doc-gen4 maintainer `hargoniX` (PR #403 review) made the pivot obvious:
1. Users of doc-gen4 usually do **not** have it in their dependency closure — docs are built by a
   separate docbuild project — so a producer API living *in* doc-gen4 is unreachable by the libraries
   that would use it.
2. Lean's **built-in docstring env-extension** already flows into doc-gen4 (and the InfoView) with no
   extra work; just write the rendered content into the docstring from a metaprogram.

So `@[pkc_math]` (in PKC, depending on **core Lean only**) computes the LaTeX + source and calls
`Lean.addDocStringCore declName combined` — writing `docStringExt` (a `MapDeclarationExtension String`
that serializes into the `.olean`). doc-gen4 reads it via the normal `findDocString?` → `docStringToHtml`
path and MathJax typesets the `$$…$$`; the Lean InfoView renders the same docstring math via its bundled
MathJax (`remark-math`/`rehype-mathjax`). **No doc-gen4 dependency, no doc-gen4 changes.**

Two facts pinned empirically (v4.32.0):
- **Timing.** The attribute must run at `applicationTime := .afterCompilation`; the elaborator attaches
  the authored `/-- … -/` docstring *between* the default `afterTypeChecking` attributes and the
  `afterCompilation` ones (`Lean.Elab.PreDefinition.Basic.addNonRecAux`). At the default time the
  docstring is absent and the authored one clobbers ours; at `afterCompilation` we read-and-append it.
- **Source block.** `defSource? = ppSignature + delaborated body`; the delaborator shortens names in the
  ambient `open`/namespace context, but `ppSignature` prints the full decl name in the header, so we
  string-replace it with the base name. `⟨-2⟩` prints as `{ magnitude := -2 }` (faithful, acceptable).

Trade-off: content lands *inside* the docstring (so the `$$…$$`/source also show in editor hover as
literal text, and a Verso docstring is flattened to Markdown by the append). Both acceptable; the win is
zero coupling and reaching every docstring consumer.

### (v1, 2026-08-03) — ⛔️ SUPERSEDED — the doc-gen4 env-extension hook (PR #403, closed)

Generic, upstreamable hook: any library attaches extra rendered docs to a decl. Transport is an
**environment extension** (doc-gen4 loads the target `.olean` in a separate process). Implemented by
**mirroring doc-gen4's existing `getRecommendedSpellingText` / `getTacticExtensionText` precedent** —
it already augments docstrings with env-derived content:

- `DocGen4/Process/DeclMath.lean` (new): `declMathExt : SimplePersistentEnvExtension (Name×String)
  (NameMap String)`, `addDeclMath declName markdown` (downstream API), `getDeclMath? env declName`.
- `getDocString?` (`NameInfo.lean`) appends the markdown to the docstring — `none` → math-only `.inl`;
  `.inl s` → `s ++ "\n\n" ++ md`; `.inr verso` → append a `.para` block. Since `docStringToHtml`
  (`Output/DocString.lean:384`) reduces both `.inl`/`.inr` to markdown and MathJax processes docstrings,
  the `$$…$$` typesets with **no Output change, no new `Info` field, no DB-schema change**.

Net PR = **1 new file + 2 tiny edits** (NameInfo `getDocString?`, Process aggregator import); no PKC
vocabulary. `lake build` green (196 jobs).

Trade-off: the math rides *inside the docstring* (like recommended-spellings), not a separate block. If
reviewers want separation, the alternative is a dedicated `Info.extraDocs` field rendered in
`docInfoToHtml` — bigger (touches Output + DB schema). Started with docstring-append (smaller, matches
precedent). The old `addDocStringCore` no-PR fallback is now moot — the hook is cleaner.

---

## 7. Build strategy — the 9.3G problem (Phase V)

Clone has **no `.lake`**. PKC depends on mathlib (v4.32.0), PhysLib, TorchLean, doc-gen4.
- **(a) clean build (recommended, safe):** `lake exe cache get` (mathlib oleans, fast) then `lake build`
  PhysLib/TorchLean/PKC/doc-gen4 (slow, ~hours, ~9G). No interference with the concurrent session.
- **(b) reuse deps (faster, some risk):** copy `.lake/packages` (deps only, *not* `.lake/build`) from the
  sibling; build only PKC + `DocGenMath`. Risk: sibling `.lake` being written by the concurrent session.
Scope the doc-gen build to the demo module, not all of PKC. *(open decision #3)*

---

## 8. Verification / acceptance
- `#eval quantityToLatex ...` / `#guard_msgs` assert the expected LaTeX for demo defs.
- End-to-end: local-override doc-gen4, generate HTML for the demo module, `grep` for the `$$…$$` block,
  open in a browser to confirm MathJax renders. **Acceptance = a doc page showing the typeset equation.**

---

## 9. Open decisions
1. Rendering philosophy default: **F (faithful only) — CONFIRMED by user 2026-08-03.** The LaTeX denotes
   exactly what the definition computes; no editorial (E) or proof-carrying (P) rewriting is applied.
   E/P are not built; when a model needs genuine algebra to look right, use the sibling-def escape hatch
   (author `def foo_math`, prove `foo = foo_math`, render the sibling) — §5. This is the standing default.
2. `@[pkc_math]` attribute surface syntax — **DONE**, and extended 2026-08-04. The full surface:
   - `@[pkc_math]` — auto-render; `@[pkc_math "…literal…"]` — override (the E-tier escape hatch).
   - `@[pkc_math substituting f, g substituting h]` — auto-render plus a derivation, one step per
     clause, cumulative (§5, *Derivations by substitution*). Mutually exclusive with the override.
   - `@[pkc_math_symbol "…"]` — named-operator notation; `@[pkc_math_symbol "\\nabla" operator]`
     additionally declares a bare prefix operator (juxtaposed, not parenthesized).
   - `@[pkc_math_config]` — on a *structure*: its fields are the model's named constants and render
     qualified by their type (§5, *Constants and configuration types*).
   - **(v4, 2026-08-05)** `@[pkc_math keeping]` / `@[pkc_math keeping x, y]` — render those `let`
     bindings as the equation's `where` block instead of inlining them (§5, *Systems of equations*).
     Composes with `substituting`; mutually exclusive with the literal override, like it. An unbound
     name is an error.
   - **(v4)** `@[pkc_math_transparent]` — on a notational wrapper (a numeral injection): an
     application renders as its argument (§5, *Notational wrappers*).

   Structural `@[pkc_math_rule]` shape-recognition DSL = still deferred (documented future extension
   in §5; named-operator recognition already covered by `@[pkc_math_symbol]`).
3. Build strategy — **RESOLVED**: neither (a) nor (b). `DocGenMath` compiles only core + the Lean-only
   `DeclMath`, so the heavy deps are merely *resolved*, never built; the clone's own `.lake/packages`
   sufficed. `lake update doc-gen4` once to activate the local override. (§7's 9.3G problem was moot.)
4. doc-gen4 PR transport: env-extension hook (§6, preferred) — **shipped as Phase P**; docstring-append
   variant chosen (mirrors `getRecommendedSpellingText`). Verified end-to-end this session.

---

## Session log
- **2026-08-05 (session 9):** **v5 — equation width.** `Pretty` gained `latexWidth`/`estWidth`/
  `wideThreshold` and breaks a wide top-level sum (`aligned`) or tuple (`pmatrix`); `lavsJacResidualQ`
  went from one 240-char line to a four-row column vector, and all 18 `DocGenMathDemo` pins stayed
  green (the estimator measures *rendered glyphs*, so `lavsResidualQ` at 139 LaTeX characters but ~50
  glyphs is correctly left alone). Confirmed doc-gen4 upstream still pins MathJax 3, so the
  `displayOverflow: 'linebreak'` route is unavailable — see §5 *Breaking a wide equation*.
  Separately: `@[pkc_math]` now records its applications in a `SimplePersistentEnvExtension`
  (`pkcMathUses`), because the attribute previously kept nothing and so could not be **indexed** — see
  the new `PropertyKindCalculus.Index` library and the blueprint chapter *Using the library*.
- **2026-08-03 (session 1):** Investigated doc-gen4 render pipeline; confirmed pretty-printer seam +
  MathJax-in-docstrings + equation-block-skip facts. Phase 0 setup done (doc-gen4 `pkc-math-hook` builds
  green; PKC clone). Design discussion → **option C dropped**; B redesigned around a 3-stage IR
  (lift/normalize+recognize/pretty) with F/E/P philosophy tiers, a global `@[pkc_math_rule]` recognition
  registry, and a presentational-sibling-def escape hatch. Wrote this plan.
- **2026-08-03 (session 1, cont.):** **Phase P implemented + green.** Reading the code found a smaller,
  more idiomatic hook than planned: mirror `getRecommendedSpellingText` (doc-gen4 already appends
  env-derived content to docstrings) → append via `getDocString?`, no `Info` field / Output / DB change
  (see §6). Files: `DocGen4/Process/DeclMath.lean` (new), `NameInfo.lean` (`getDocString?`),
  `Process.lean` (aggregator import). `lake build` 196 jobs green. Next: Phase B (IR walker).
- **2026-08-03 (session 1, cont.):** Re-synced the PKC clone `feat/pkc-math-rendering` to sibling
  `local/main` = `71b7508` (v0.24.0 + blueprint update; clean ff, RENDERING.md preserved). Committed:
  RENDERING.md on the PKC feat branch; the Phase-P hook on doc-gen4 `pkc-math-hook`. Neither pushed.
- **2026-08-03 (session 2):** Rebased `feat/pkc-math-rendering` onto sibling `local/main` = `b43f9c0`
  (v0.25.0). **Implemented + verified all of Phase B.** Smoke-tested the pure stages (Term/Normalize/
  Pretty import only `Lean`) against the bare toolchain by hand-compiling oleans with `lean --root`
  — all 4 LaTeX predictions matched before touching the heavy build. Then `lake build DocGenMath`
  green (33 jobs); the `@[pkc_math]` attribute runs over `avsForward` at build time, and a separate
  `lake env lean` process read the attached `$$…$$` back via `getDeclMath?` (transport proven).
  **Build strategy that worked (supersedes §7's open decision):** the clone already had its **own**
  resolved `.lake/packages` (848M, sources only, *not* the sibling's — no sharing/interference).
  `DocGenMath` builds only the mathlib-free core spine + the `Lean`-only `DocGen4.Process.DeclMath`,
  so **no** mathlib/PhysLib/TorchLean module is compiled — the heavy deps only need to be *resolved*.
  `lake update doc-gen4` was required once to make the local `from path` override win over the cached
  git manifest entry (it also decompressed the mathlib cache as a harmless side effect, ~3 min).
  **Gotchas fixed:** (1) `String` is ByteArray-backed in v4.32.0 → `⟨List Char⟩` fails; use
  `String.ofList`. (2) `s!"…{{…}}…"` literal-brace escaping is fragile → build LaTeX with `++` and an
  explicit `br`/`"{"++…++"}"`. (3) `macro` is a reserved keyword — can't name a `match` binder that.
  (4) Reading an `OfNat` numeral: **`Expr.nat?` silently returns none** on the raw `Nat` index and
  **`Expr.natLit?` does not exist** in v4.32.0 — match `Expr.lit (.natVal n)` directly. (5) `Lift` uses
  `` `` ``-checked PKC names, so it must `import PropertyKindCalculus` (couples the lift to the core —
  honest, since it hard-codes PKC's alphabet). (6) `where`-clause helpers don't see the outer `let fn`
  — recompute `e.getAppFn` inside. Committed Phase B as `f6a07a8` (switched the override to the portable
  relative `../doc-gen4`; `lake update doc-gen4` rewrote the manifest `dir` to `../doc-gen4` — resolved
  revs unchanged, only transitive-dep `inputRev` metadata now sourced from the local doc-gen4 lakefile).
- **2026-08-03 (session 2, cont.):** **Phase V done + F confirmed.** User confirmed **F (faithful)** as
  the standing rendering default (E/P not built; sibling-def escape hatch for hard algebra). Generated
  the doc HTML: `lake build PropertyKindCalculus.DocGenMath.Demo:docs` → 300 jobs green (builds the
  doc-gen4 exe from the local override + `genCore` over Lean core + `single` over the Demo closure +
  `fromDb`; ~several min, dominated by `genCore Lean`). Verified `Demo.html` carries
  `<p>$$\sigma^0 = a\,\mathrm{NDVI} + e^{-2\,b\,\mathrm{NDVI}}\,c\,r + d$$</p>` in the docstring prose,
  MathJax loaded, `$$…$$` = displayMath and `<p>` not in `skipHtmlTags` → typesets. Page:
  `.lake/build/doc/PropertyKindCalculus/DocGenMath/Demo.html`.
- **2026-08-03 (session 2, cont.):** **Phase S done — PR #403 opened.** Rebased the hook onto doc-gen4
  `main` (v4.33.0-rc2) in a throwaway git **worktree** (kept the `../doc-gen4` checkout on `pkc-math-hook`).
  Re-authored `getDocString?` for v4.33 (return type gained the `(VersoDocString × String)` pair; the
  Markdown string is what `docStringToHtml` renders — appended the attached md there). `lake build DocGen4`
  green (131 jobs, v4.33.0-rc2). Committed `aad7b98` on `declmath-hook`, pushed to fork `origin`, opened
  https://github.com/leanprover/doc-gen4/pull/403 against `leanprover/doc-gen4:main` (ready-for-review).
  Worktree removed after. **Workstream complete pending maintainer review.**
- **2026-08-04 (session 3):** **ARCHITECTURE PIVOT — PR #403 closed; doc-gen4 route abandoned.** Maintainer
  `hargoniX` reviewed #403: (1) most projects lack doc-gen4 in their dep closure (docs = separate docbuild
  project) → a producer API in doc-gen4 is unreachable; (2) the built-in docstring env-extension already
  flows into doc-gen4 for free. Both correct → posted a concession + closed #403 (comment `5181046146`).
  **Reworked `@[pkc_math]` to the library-side design (§6 v2):** it now writes the rendered `$$…$$` **plus
  the definition's Lean source** (```` ```lean ```` block) into the decl's own docstring via
  `Lean.addDocStringCore`; `Attr.lean` dropped `import DocGen4.*`; the library depends on core Lean + PKC
  only. **Gotcha (pinned empirically):** the attribute must run at `applicationTime := .afterCompilation`,
  because the elaborator attaches the authored `/-- -/` docstring *between* the default `afterTypeChecking`
  attrs and the `afterCompilation` ones (`Lean.Elab.PreDefinition.Basic.addNonRecAux`); at the default time
  the docstring is absent and the authored one clobbers ours. **Source block:** `findDeclarationRanges?`/
  `getRef` can't reach the decl source span at `afterCompilation` (ranges unstored, `getRef` = attr node
  only), so `defSource?` uses `ppSignature` + delaborated body (names shorten in the ambient `open`; the
  full decl name in the `ppSignature` header is string-replaced with its base name). v4.32 String churn:
  `trim`/`trimRight`/`trimAscii*`/`dropRightWhile` all deprecated→`Slice`; used `doc.trimAsciiEnd.toString`.
  Added a `noted` prose def + docstring-read-back `#guard_msgs` pin (build-time transport proof). Verified
  the doc HTML shows prose + typeset math + source (Phase V v2). Confirmed the Lean InfoView bundle ships
  MathJax + remark-math/rehype-mathjax (so it typesets docstring math; native hover does not). Then
  **removed the `../doc-gen4` override** (`lake update doc-gen4` reverted doc-gen4 to the stock `092d631`
  `v4.32.0` tag that PhysLib/TorchLean already pin transitively — clean manifest diff, no drift, no
  network; `lake build DocGenMath` still green). Files (all UNPUSHED on `feat/pkc-math-rendering`):
  `Attr.lean`, `Demo.lean`, `lakefile.lean` (override removed + NOTE comment), `lake-manifest.json`
  (doc-gen4 path→git), `RENDERING.md`. The `62439e4`/`aad7b98` doc-gen4 hooks are now dead ends kept only
  for the record.
- **2026-08-04 (session 4):** **Committed the pivot + rebased onto v0.27.0 + applied `@[pkc_math]` to the
  kinded PKC example models.** Committed the session-3 pivot (`2454054`). Rebased `feat/pkc-math-rendering`
  onto sibling `local/main` = `8481845` (v0.27.0 — the concurrent session's *"Kind the PKC example physical
  models"* commit, which authored `AvsForward.lean` / `WaterCloudModel.lean` / kinded `DegenhardtFictive`
  but added **no** `@[pkc_math]`): clean, **no conflicts** (our `DocGenMath` lib + doc-gen4-override removal
  and their version bump / `Allocation` glob / `UncertaintyBatch` lib touched disjoint lakefile regions).
  **Engine change (user chose "improve the renderer first"):** added a `.letE` **zeta** case to
  `Lift.liftExpr` (inline the `let`-bound value on the way in) — a presentation-only zeta, *not* a delta of
  named helpers — so let-threaded model bodies render as their operators instead of falling to the opaque
  `sym (ppExpr e)` leaf. Empirically, before the fix `lavsForwardQ` rendered `\mathrm{_proof_3 att c) r + d}`
  (garbage); after, `a\,\mathrm{NDVI} + \mathrm{attenuationQ}(cfg,b,NDVI)\,c\,r + d`. Pinned by a new Demo
  `letExample` (`q = a^{2} + a`). **Auto-vs-override split:** the flat `fictiveModelQ` auto-renders cleanly
  → bare `@[pkc_math]` + `@[pkc_math_symbol "Y"]` (⟶ `Y = \left(x_{1} + x_{2}^{2}\right)\,x_{3}`); the
  config/numeral models get `@[pkc_math "…"]` overrides because **`cfg.two` is a `def` *parameter`, never
  bound to `2`** in the generic kernel, so the `−2` can't fold (`attenuationQ` post-zeta = `e^{(-\mathrm{two}
  \,\mathrm{cfg})\,b\,\mathrm{NDVI}}`). Overrides: `attenuationQ` `\tau = e^{-2\,b\,\mathrm{NDVI}}`,
  `lavsForwardQ` the full σ⁰, `lavsResidualQ` `s_0 - \sigma^0`, `wcmForwardQ` the expanded WCM. **Source-block
  polish:** `defSource?` now inlines the elaborator-lifted `<decl>._proof_k` kind witnesses — they are
  `thmInfo`, so `ConstantInfo.value?` withholds the value (read `thmInfo.value` directly) — and the
  pretty-printer then **elides the proof term to the idiomatic `⋯`** instead of leaking
  `attenuationQ._proof_1`; the source reads as a clean op skeleton (`Quantity.mul ⋯ a ndvi + …`).
  **Wiring:** each annotated example `import PropertyKindCalculus.DocGenMath` (intra-package cross-lib import;
  the `pkc_math`/`pkc_math_symbol` attribute names are global, no `open` needed). **Safety/verification:** the
  attribute is docstring-only at `afterCompilation`, so it cannot change elaboration — the codegen bit-exact
  `#guard`s + faithfulness proofs are untouched (`Examples`/`UncertaintyExamples` libs + AvsForward's codegen
  dependents all green); readback of all 5 docstrings shows prose + `$$…$$` + clean ```` ```lean ```` source.
  Files (UNPUSHED on `feat/pkc-math-rendering`): `Lift.lean`, `Attr.lean`, `Demo.lean` (engine); `AvsForward.lean`,
  `WaterCloudModel.lean`, `DegenhardtFictive.lean` (annotations); `RENDERING.md`.
- **2026-08-04 (session 5):** **Two auto-render defects fixed + the demo moved into `examples/`.** Triggered
  by a user question about the *InfoView*: the `⊢ …` panel is the **term goal**, not a docstring surface, so
  no attribute can put math there — the typesetting surfaces are the doc-gen4 page and the InfoView's own
  **hover popups** (re-confirmed against the installed `leanprover.lean4-0.0.239`: `dist/lean4-infoview/
  index.production.min.js` carries MathJax + `rehype-mathjax` with `displayMath: [["$$","$$"],["\\[","\\]"]]`).
  The **native VS Code editor hover** renders docstrings with VS Code's own markdown, which has no math
  renderer *and* eats `\,` as a CommonMark escape of `,` — so a product `a\,b` reads there as `a,b`. That is a
  hover artifact only (doc-gen4's HTML keeps `a\,\mathrm{NDVI}`), but it is what made `lavsJacResidualQ` look
  like a comma-separated argument list. Two **real** defects behind it, both now fixed:
  (1) **No `Prod.mk` handler** — a multi-output model's tuple fell to the generic `fn` fallback and printed
  `\mathrm{mk}(x, \mathrm{mk}(y, z))`. `Term.lean` gains a `tuple` constructor (n-ary), `Lift.liftExpr` matches
  `Prod.mk` and flattens the **right**-nested chain (a genuinely nested left component keeps its parentheses),
  `Normalize` maps componentwise, `Pretty` prints `\left(a, b, c\right)` at precedence 40.
  (2) **The `sym.startsWith "\\"` prefix guess** in `Pretty.renderFn` fired for *every* multi-letter
  identifier, because `builtinSymbol`'s fallback is `\mathrm{…}` — so `cfg.two` printed as the juxtaposition
  `\mathrm{two} \mathrm{cfg}`. Replaced by an **explicit registration**: `resolveToken` now returns a
  `MathNotation` (`latex` + `operator`), and only `@[pkc_math_symbol "…" operator]` selects the juxtaposed
  prefix layout. Syntax is `str (ppSpace &"operator")?`; the attribute is now `ParametricAttribute
  MathNotation`. Net effect on `lavsJacResidualQ`: was `\mathrm{mk}(-\mathrm{NDVI}, \mathrm{mk}(\mathrm{two}
  \mathrm{cfg}\,…))`, now `\left(-\mathrm{NDVI}, \mathrm{two}\left(\mathrm{cfg}\right)\,\mathrm{NDVI}\,c\,r\,
  \mathrm{attenuationQ}\left(\mathrm{cfg}, b, \mathrm{NDVI}\right), -\mathrm{attenuationQ}\left(…\right)\,r,
  -1\right)`. **Demo moved** out of the library (see Phase B bullet). **Verification:** `lake build DocGenMath`
  green (30 jobs); `PropertyKindCalculus.Examples.DocGenMathDemo` green with 8 pins; `AvsForward` +
  `DegenhardtFictive` + `WaterCloudModel` green (2118 jobs) and `fictiveModelQ` reads back **unchanged**
  (`Y = \left(x_{1} + x_{2}^{2}\right)\,x_{3}`) — the prefix-guess removal regressed nothing.
  **Still open (known, deliberate):** a *structure projection* (`cfg.two` = `AvsConfig.two cfg`) has no handler,
  so it prints honestly but noisily as `\mathrm{two}\left(\mathrm{cfg}\right)`. The natural fix is a second
  registration marker on the same syntax — e.g. `@[pkc_math_symbol "2" atom]`, "render as this symbol,
  discard the arguments" — which is an author-notation API decision, not a bug fix; **not** done here.
  Files (UNPUSHED on `feat/pkc-math-rendering`): `Term.lean`, `Lift.lean`, `Normalize.lean`, `Pretty.lean`,
  `Registry.lean`, `Attr.lean`, `DocGenMath.lean` (engine); `Demo.lean` **deleted** →
  `examples/PropertyKindCalculus/Examples/DocGenMathDemo.lean` **added**; `lakefile.lean`; `RENDERING.md`.
- **2026-08-04 (session 5b): the doc-gen4 API site is wired into the blueprint pipeline.** The site now
  publishes to `docs/api/` alongside the Verso blueprint at `docs/`, on the same orphan `gh-pages` branch.
  **Two real defects found and fixed while wiring — both silent:**
  1. **`lake build :docs` renders only `pkg.defaultTargets`.** PKC marks only `«PropertyKindCalculus»`
     `@[default_target]`, so the run reported *"(1 root modules)"* and generated the core spine **only** —
     none of the `@[pkc_math]` models were on the site, which is the entire point of publishing it.
  2. **`library_facet docs` renders `lib.rootModules`, and Lake defaults `roots := #[<target name>]`, not
     the glob prefix.** `lean_lib «DocGenMath»` sets only `globs := #[.andSubmodules
     `PropertyKindCalculus.DocGenMath]`, so its root was the non-existent module `DocGenMath` and
     `lake build DocGenMath:docs` **succeeded while generating nothing** — *"Generating documentation for
     DocGenMath (0 root modules)"*, exit 0. That is the worst possible CI failure mode, so
     `build-api-docs.sh` greps its own log for `(0 root modules)` and fails the job on it.
     Fixed by declaring `roots` explicitly on `Examples` and `DocGenMath`; every other library still
     carries the bogus default and must declare `roots` before being added (NOTE in `lakefile.lean`).
  **Scope = Mathlib-free tier only.** `module_facet docInfo` recurses into a module's transitive imports
  and `fromDb` emits HTML for the closure of the roots, so adding `Dimension`/`Uncertainty`/`Torch`/
  `UncertaintyExamples` would drag **all of Mathlib** through both passes (hours, multi-GB). Cost of the
  trade: `wcmForwardQ` and `fictiveModelQ` are absent from the site. (This corrects an earlier estimate in
  this session that the facet would not reach into dependencies — it does.)
  `examples/…/Examples.lean` was completed with `AvsForward` + `DocGenMathDemo` (both Mathlib-free) since
  it *is* the library root and thus defines the rendered closure; the `TapeCodegen*`/`TapeCse*`/
  `LmStepCodegenDemo` demos stay out because they reach `Torch`'s Mathlib-importing carriers. They are
  still built by `lake build Examples`, which works off globs, not roots (verified: 2141 jobs green).
  **Verified:** `docs/index.html` (blueprint, 723 files) + `docs/api/index.html` (2470 files);
  `docs/api/PropertyKindCalculus/Examples/AvsForward.html` carries all four `$$…$$` equations; MathJax is
  loaded there (`mathjax-config.js` + the `tex-mml-chtml` CDN) with `displayMath: [["$$","$$"]]` and `<p>`
  absent from `skipHtmlTags`, so they typeset. The blueprint front matter now links to `api/index.html`
  (blueprint rebuilt, 7198 jobs, link present in the rendered `html-multi/index.html`).
  **Log noise that is NOT a problem:** `INFO: reference page disabled` (no `docs/references.bib` in the
  repo — the bibliography lives in the Verso blueprint, not doc-gen4), and the `WARNING: Failed to
  calculate equational lemmata for Lean.…/Std.…` block, which comes from `genCore` over **Lean core** and
  is unrelated to PKC.
  Files: `scripts/build-api-docs.sh` **added**; `lakefile.lean`, `.github/workflows/blueprint.yml`,
  `blueprint/scripts/ci-pages.sh`, `blueprint/PropertyKindCalculusBlueprint/Blueprint.lean`,
  `examples/PropertyKindCalculus/Examples.lean`, `RENDERING.md`.
- **2026-08-04 (session 6): textbook rendering — qualified configuration constants + derivations.**
  Driven by two concrete complaints about `AvsForward`'s auto-render. **(1) `cfg.two` rendered
  `\mathrm{two}\left(\mathrm{cfg}\right)`** — the field stripped of its type, applied to a value that
  tells the reader nothing. Fixed with `@[pkc_math_config]` on the *structure*, a `TagAttribute` whose
  tag is what makes the receiver-elision safe (a blanket projection rule would turn `p.fst` into
  `\mathrm{fst}`). **(2) only the literal source form was shown** — `Lift` did zeta but never delta.
  Fixed with `@[pkc_math substituting f, g substituting h]`: one derivation step per clause, step *n*
  substituting the union of clauses 1..*n*, rendered under a `**Derivation**` heading as numbered
  steps (user chose this layout over paragraph captions and a bulleted list; user also chose cumulative
  steps over a single flat substitution set). Zero clauses ⟶ byte-identical to before, so every prior
  pin stayed green untouched. A third, small change carries most of the visual win: **sign hoisting**
  in `Normalize` (`(−x)·y·z → −(x·y·z)`, folded into the existing coefficient-sign path rather than
  added beside it). Net effect on `attenuationQ`: was `e^{\left(-\mathrm{two}\left(\mathrm{cfg}
  \right)\right)\,b\,\mathrm{NDVI}}`, now `e^{-\mathrm{AvsConfig.two}\,b\,\mathrm{NDVI}}`.
  **Policy** (§5, and the reason both additions were acceptable at all): qualification is notation and
  delta is meaning-preserving, so **both are F tier** — no line of a derivation asserts anything the
  definition does not compute. The boundary is drawn explicitly in §5: rendering `cfg.two` as `2`
  asserts a value for a `def` parameter, which is E tier and stays out; a literal override and
  `substituting` are mutually exclusive and rejected together, and a self-mentioning definition is
  rejected as unsubstitutable (`.visit` would not terminate).
  **Risk that did not materialize:** the attribute resolves its `ident`s with
  `realizeGlobalConstNoOverload` in `AttrM`; the ambient namespace *is* available at
  `afterCompilation`, so unqualified helper names work (the fallback of demanding fully-qualified
  names was not needed). **Verified:** `DocGenMath` 30 jobs; `DocGenMathDemo` green with 14 pins
  (added: 2 sign-hoist pure-stage, 1 `@[pkc_math_config]` end-to-end, 2 substitution end-to-end, 1
  full two-step `**Derivation**` docstring read-back); `Examples` + `DegenhardtFictive` 2152 jobs, with
  `fictiveModelQ` unchanged. `lavsResidualQ` now reads back a two-step chain ending in
  `s_{0} - \left(a\,\mathrm{NDVI} + e^{-\mathrm{AvsConfig.two}\,b\,\mathrm{NDVI}}\,c\,r + d\right)`.
  **Two more silent doc-gen4 traps, found by checking the published HTML rather than trusting the
  build** — both fixed in `scripts/build-api-docs.sh`:
  1. **Stale HTML.** The assembly steps (`fromDb`, `headerData`) are guarded by `*_built` markers whose
     traces do **not** change when a module's `docInfo` marker does. Observed directly: editing a
     docstring rebuilt `doc-data/…AvsForward.doc` (17:54) while `doc/…/AvsForward.html` kept its old
     content and timestamp (15:50). Lake reports success, and CI would publish documentation that does
     not match the source. This is the same failure the 2026-08-03 session worked around by hand with
     `rm -rf .lake/build/doc`; the script now clears **only** `doc-data/*_built*`, so the expensive
     `genCore`/`single` passes are reused and just the assembly repeats.
  2. **`references.bib` is traced but not emitted.** `generateHtmlDocs` ends by tracing a fixed static
     list including `doc/references.bib`, which doc-gen4 only writes when a bibliography is configured.
     With none (this repo's bibliography lives in the Verso blueprint), a build tree that does not
     already carry the file fails with a bare `no such file or directory` — **including a fresh CI
     runner**. Wiping `doc/` is therefore *not* a safe way to force regeneration, which is why (1) is
     marker-only; the script pre-creates the empty file. Note doc-gen4 reads a bibliography from
     `<root>/docs/references.bib`, which collides with the published-site `docs/` that
     `stage-docs.sh` wipes — so supplying a real one is not an option here.
  **Verified in the published HTML:** `docs/api/…/AvsForward.html` carries
  `<p><strong>Derivation</strong></p>` + `<ol><li>substituting <code><a …>attenuationQ</a></code>` +
  `<p>$$…$$</p>`, with the second step emitted as `<ol start="2">` — so the numbering survives the
  interleaved display math, and doc-gen4 auto-links each substituted helper to its declaration.
  Files: `Registry.lean`, `Lift.lean`, `Normalize.lean`, `Attr.lean` (engine);
  `Examples/DocGenMathDemo.lean` (pins), `Examples/AvsForward.lean` (annotations);
  `scripts/build-api-docs.sh`; `RENDERING.md`.
- **2026-08-05 (session 8): v4 — the shapes a real model is written in.** Rendering
  `soil-moisture-model`'s Mironov dielectric was the first test of `@[pkc_math]` on an authored
  surface not written here, and it failed in a way the demo could not have caught: of the 12
  annotated declarations in `algorithm/dielectric/core.lean`, three rendered **malformed LaTeX** —
  `\mathrm{match_}_{1}\left(\mathrm{fun x ↦ MironovNK α}, …\right)` with unbalanced parens and
  pretty-printed Lean dumped inside `\mathrm{…}` — and were live on the published API site. Three
  independent gaps, now all closed (§5 *Systems of equations*, *Notational wrappers*; Phase B v4):
  1. **`match`.** A matcher was an ordinary application to the lift, so its motive lambda and its
     branches were rendered as *arguments*. Now: one alternative = a destructuring binder → a `where`
     equation; several = `\begin{cases}` with patterns from `Match.getEquationsFor`. Reading the
     patterns from the equation lemmas rather than from constructor order is load-bearing — `match`
     alternatives compile in the order *written*, so the demo pins a reverse-order match to prove it.
  2. **Record results.** `mironovNK` returns a 7-field record; there is no single defining equation.
     Now an aligned *system*, one row per field — which is what its own docstring always promised
     ("as a sequence of quantity equations").
  3. **Zeta blowup.** With every `let` inlined, `mironovNK`'s shared Debye denominator was duplicated
     into a single 2 587-character line (`ω τ ω τ + 1` instead of `1 + (ωτ)²`). `@[pkc_math keeping]`
     is the inverse of the `let`-zeta: bindings become the equation's `where` block.
  Plus `@[pkc_math_transparent]` for a carrier's numeral injection (`ofN 2` → `2`, not
  `\mathrm{ofN}(2)`), and a `raw`/`latexText` leaf so an unreadable subterm degrades to escaped
  `\text{…}` — **the general lesson**: the old fallback put pretty-printed Lean into a `sym`, and a
  `sym` is a token to be resolved, so anything it could not read became invalid math on a published
  page rather than an ugly-but-valid one.
  Two Lean-side traps worth remembering: `getStructureFields` **panics** on a non-structure and
  Lean's `let` is strict, so an unguarded call crashed the entire elaboration (guard with
  `isStructure` *before* binding); and `if h : xs.size == 1` gives `omega` a `Bool` equation it
  cannot use — write `if h : xs.size = 1`.
  Files: `Term.lean`, `Lift.lean`, `Normalize.lean`, `Pretty.lean`, `Registry.lean`, `Attr.lean`
  (engine); `Examples/DocGenMathDemo.lean` (+6 pins); `RENDERING.md`.
