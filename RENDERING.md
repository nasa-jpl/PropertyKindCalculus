# PKC ↔ doc-gen4 Math Rendering — Cross-Session Plan

**Status:** 2026-08-04 — **ARCHITECTURE PIVOT (per doc-gen4 maintainer review) — DONE.** The doc-gen4
PR #403 (env-extension hook) was **closed**: maintainer `hargoniX` pointed out (1) most projects don't
have doc-gen4 in their dependency closure (docs are built by a separate docbuild project), so a producer
API *in* doc-gen4 is unreachable; and (2) the built-in **docstring** env-extension already flows into
doc-gen4 for free. Both correct. **New design: `@[pkc_math]` writes the rendered `$$…$$` (now *plus* the
definition's Lean source) into the declaration's own docstring via core Lean's `Lean.addDocStringCore`
— no doc-gen4 dependency, no doc-gen4 changes.** This also reaches the **Lean InfoView** (which renders
docstring math via MathJax), which the doc-gen-only hook never could. Rendering default = **F (faithful),
CONFIRMED**. Remaining = follow-on (apply `@[pkc_math]` to real SMM/EM models). No library module imports
doc-gen4; the `../doc-gen4` **dev override was removed** — doc-gen4 reverts to the stock `v4.32.0` tag
(`092d631`) that PhysLib and TorchLean already pin transitively (it cannot be dropped *entirely* — both
require it; this Mathlib pin does not), and is only ever resolved, never built here.
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
  demo def rendered end-to-end.

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
- [x] **Stage 0 IR** `Term.lean`: `MathTerm` = `sym/num/neg/add/mul/frac/pow/fn` (n-ary add/mul; sub = `add[a, neg b]`).
- [x] **Stage 1 (Lift)** `Lift.lean`: `liftExpr : Expr → MetaM MathTerm`, defensive/total; matches PKC alphabet by head (`Quantity.mul/div/add/sub/exp/log/…/mk`, `HAdd/HSub/HMul/HDiv/HPow/Neg`, `OfNat`), drops witnesses/instances via **last-N args** + `getFunInfo` explicit-filter for unknown heads; flattens assoc. Imports `PropertyKindCalculus` (uses `` `` ``-checked names).
- [x] **Stage 2 (Normalize)** `Normalize.lean`: faithful — flatten, integer fold (`2·3→6`, `2+3→5`), drop `1·`/`+0`, `−1·x→−x`, double-neg, adjacent `x·x→x²`, scalar-first product sort (sum order preserved). (Structural `@[pkc_math_rule]` shape-rules = documented future; named-operator recognition is the registry, below.)
- [x] **Stage 3 (Pretty)** `Pretty.lean`: precedence printer (sum 10 < neg 15 < mul 20 < pow 30 < atom 40); `e^{…}`, `\sin/\cos/\log/\arcsin…`, `\frac`, sign-aware sums (`a − b`); takes a `resolve : String→String` closure (pure/testable).
- [x] Symbol table + registry `Registry.lean`: `@[pkc_math_symbol "…"]` per-decl LaTeX override (the practical recognition registry) + `builtinSymbol` heuristic (Greek, `s0→s_{0}`, `ndvi→\mathrm{NDVI}`, single-letter italic, multi-letter `\mathrm`). `resolveToken env` = override-then-heuristic.
- [x] `@[pkc_math]` attribute `Attr.lean`: `quantityToLatex declName : MetaM String` (lambdaTelescope value → lift → normalize → pretty; LHS via `resolveToken`), `@[pkc_math]` / `@[pkc_math "…literal…"]`. **(v2, 2026-08-04)** — no longer `addDeclMath`; instead runs at `applicationTime := .afterCompilation` and writes into the declaration's **own docstring** via `Lean.addDocStringCore`, appending both the `$$…$$` and (new) the **definition's Lean source** as a ```` ```lean ```` block (`defSource?` = `ppSignature` + delaborated body, decl name shortened to its base). `afterCompilation` is required so the authored `/-- … -/` docstring is already attached and preserved (at the default `afterTypeChecking` it is not yet present and would clobber ours — verified empirically). **No doc-gen4 import.**
- [x] `Demo.lean`: dimensionless-kind demo; `@[pkc_math_symbol "\\sigma^0", pkc_math] def avsForward` renders `\sigma^0 = a\,\mathrm{NDVI} + e^{-2\,b\,\mathrm{NDVI}}\,c\,r + d`; **(v2)** now 5 `#guard_msgs` pins (3 pure-stage + 1 `quantityToLatex` + 1 docstring read-back on `noted` asserting prose + `$$…$$` + the ```` ```lean ```` source) — all green.
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
- [ ] Register SMM/EM named helpers + apply `@[pkc_math]` to the *downstream* SMM `lavsForwardQ` and
  Xiaolan's models (in `soil-moisture-model`, not the PKC example mirror).

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
- **Per-decl `@[pkc_math ...]`**: hints/overrides only (symbol choice, forced grouping, literal-LaTeX
  escape hatch). Not a full rewrite language. *(open decision #2: exact attribute surface syntax)*

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
2. `@[pkc_math]` attribute surface syntax — **DONE**: `@[pkc_math]` (auto) / `@[pkc_math "…literal…"]`
   (override); named-operator notation via `@[pkc_math_symbol "…"]`. Structural `@[pkc_math_rule]`
   shape-recognition DSL = deferred (documented future extension in §5; named-operator recognition
   already covered by `@[pkc_math_symbol]`).
3. Build strategy — **RESOLVED**: neither (a) nor (b). `DocGenMath` compiles only core + the Lean-only
   `DeclMath`, so the heavy deps are merely *resolved*, never built; the clone's own `.lake/packages`
   sufficed. `lake update doc-gen4` once to activate the local override. (§7's 9.3G problem was moot.)
4. doc-gen4 PR transport: env-extension hook (§6, preferred) — **shipped as Phase P**; docstring-append
   variant chosen (mirrors `getRecommendedSpellingText`). Verified end-to-end this session.

---

## Session log
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
