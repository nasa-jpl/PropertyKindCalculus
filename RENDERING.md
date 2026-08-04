# PKC ↔ doc-gen4 Math Rendering — Cross-Session Plan

**Status:** 2026-08-03 — Phase 0 (setup) **DONE**; **Phase P (doc-gen4 hook) DONE + green, uncommitted**;
design frozen (IR-based B; option C dropped); Phases B/V/S not started.
**This file is the durable, multi-session tracker.** Update the checkboxes and the "Session log"
at the bottom every time you make progress. A fresh session should read §2 (repo map) and §4
(checklist) first.

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
  presentation-rewrite/recognition registry. **Imports doc-gen4** (for the Phase-P hook API) + PKC core.
  Docs-only; never imported by the core spine.
- demo/tests under `examples/`/`tests/`: `#eval`/`#guard_msgs` pins for the LaTeX of demo defs, plus a
  demo def rendered end-to-end.

---

## 4. Phased checklist

### Phase 0 — Setup ✅ DONE (2026-08-03)
- [x] Fetch upstream doc-gen4; `main` ff'd to `feb58b8` (v4.33.0-rc2).
- [x] doc-gen4 dev branch `pkc-math-hook` off tag `v4.32.0`; **builds green** (194 jobs, exe produced).
- [x] Clone PKC → `/home/nfr/projects/lean/PKC`; remotes repointed (`origin`=JPL, `maap`, `local`=sibling); branch `feat/pkc-math-rendering`.
- [x] Plan written; option C dropped; IR design folded in (§5).

### Phase P — doc-gen4 hook PR (see §6) — ✅ DONE 2026-08-03 (uncommitted)
- [x] New `DocGen4/Process/DeclMath.lean`: `declMathExt` (`SimplePersistentEnvExtension (Name×String) (NameMap String)`) + `addDeclMath declName markdown` (downstream API) + `getDeclMath? env declName` (reader).
- [x] `getDocString?` (`DocGen4/Process/NameInfo.lean`) appends the attached markdown to the docstring (none/`.inl`/`.inr`) → renders through the existing **MathJax-processed** docstring path. **No new `Info` field, no Output change, no DB-schema change.** Mirrors the `getRecommendedSpellingText` precedent.
- [x] Wired into `DocGen4/Process.lean`; `lake build` **green (196 jobs)**.
- [ ] Commit on `pkc-math-hook` (awaiting user OK). Do NOT push until Phase V green (Phase S).

### Phase B — IR + Expr→LaTeX + `@[pkc_math]` (see §5) — the core
- [ ] **Stage 1 (Lift):** `Expr → MathTerm` (n-ary `Mul`/`Add`, `Neg`, `Pow`, `Exp`, `App`, `Sym`, `Lit`); drop `ProductKind`/`TranscendentalKind` Props, instances, mdata; **flatten associativity**.
- [ ] **Stage 2 (Normalize/Recognize):** faithful normalizer (sort, numeral-fold, `x·x→x²`, `exp→e^`, `a+(−b)→a−b`, CSE→`where`) + a **recognition registry** (`@[pkc_math_rule]`) for named operators.
- [ ] **Stage 3 (Pretty):** `MathTerm → LaTeX` precedence printer (owns all parens/spacing).
- [ ] Name→LaTeX symbol table (`ndvi→\mathrm{NDVI}`, `s0→s_0`, …); extensible registry for named helpers (e.g. SMM `attenuationQ`, EM `curl`).
- [ ] `@[pkc_math]` attribute: compute LaTeX from the def value → Phase-P `addDeclMath`. Support literal override `@[pkc_math "…"]` (escape hatch).
- [ ] `#eval`/`#guard_msgs` pins for demo defs. Wire `lean_lib «DocGenMath»` into `lakefile.lean`.

### Phase V — verification / end-to-end (see §7)
- [ ] `require «doc-gen4» from "/home/nfr/projects/lean/doc-gen4"` (local override) in the PKC clone lakefile.
- [ ] Resolve build strategy (§7): get PKC + deps built in the clone (rebase to `49ab475` first).
- [ ] Run doc-gen4 over the demo module; grep the HTML for the `$$…$$` block; open in a browser to confirm MathJax typesets it.

### Phase S — submit PR
- [ ] Rebase the Phase-P diff from `pkc-math-hook` onto doc-gen4 `main` (v4.33); fix any drift.
- [ ] Push to `origin` (NicolasRouquette/doc-gen4); open PR against `leanprover/doc-gen4`. **Only after B verified against the local hook (Phase V green).**

### Follow-on (not in scope)
- [ ] Register SMM/EM named helpers + apply `@[pkc_math]` to `lavsForwardQ` etc. and Xiaolan's models.

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

**Chosen default (revisit if needed): F on by default, E opt-in per decl; P and the sibling-def path
(below) documented as advanced.** F is most of the win and keeps the doc faithful. Escalate to P as the
flagship only if we decide certified-pretty-math is a headline feature. *(open decision #1)*

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

## 6. Design — the doc-gen4 PR (Phase P) — IMPLEMENTED

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
1. Rendering philosophy default: **F** (chosen) vs F+E vs P-as-flagship (§5). — *confirm with user.*
2. `@[pkc_math]` attribute surface syntax + the `@[pkc_math_rule]` DSL shape (§5). — *TBD during Phase B.*
3. Build strategy: (a) clean vs (b) reuse deps (§7). — *leaning (a).*
4. doc-gen4 PR transport: env-extension hook (§6, preferred) vs docstring injection (fallback).

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
