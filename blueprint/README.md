# PropertyKindCalculus Blueprint

A [Verso](https://github.com/leanprover/verso) /
[verso-blueprint](https://github.com/leanprover/verso-blueprint) design document
for [PropertyKindCalculus](../). It records the **proved spine** — each node linked to
a real, sorry-free declaration in the core library — with a dependency graph and a
status summary generated from the linked Lean code.

## What it documents

27 chapters carrying **154 nodes, 34 of them capstones — every one of them
`proved`**, each linking a real, sorry-free declaration through its `(lean := …)` field.
The status summary and the dependency graph are therefore read off the checked source
rather than asserted here; `scripts/check-doc-pins.py` gates these counts and the chapter
list below against the chapter sources, so a new or renamed chapter fails the gate rather
than quietly going unlisted.

| Group | Chapters |
|---|---|
| The foundation | Foundations: system, part, and the ontological square |
| The spine | The Proved Spine · Write Once, Correctly · Metrological modularity · Using the library: annotations and generated indexes · External Cross-References |
| The kind layer | The object type · Dedicated kinds-of-property · Extensivity · The Interaction Algebra (Flater Appendix C) · The Function Calculus and Complex-Valued Carriers (R12) |
| Units and dimension | Units and the Dimension-1 Problem · Dimension as a Forgetful Functor · Scale-spanning units — a third unit category (R13) |
| Uncertainty | Uncertainty quantification and numerical adequacy |
| The standards catalogue | ISO/IEC 80000 — The Standards Catalogue, and one chapter per part: ISO 80000-3 — Space and Time · ISO 80000-4 — Mechanics · ISO 80000-5 — Thermodynamics · IEC 80000-6 — Electromagnetism · ISO 80000-7 — Light and radiation · ISO 80000-8 — Acoustics · ISO 80000-9 — Physical chemistry and molecular physics · ISO 80000-10 — Atomic and nuclear physics · ISO 80000-11 — Characteristic numbers · ISO 80000-12 — Condensed matter physics · IEC 80000-13 — Information science and technology |

Capstone theorems are tagged `capstone` and proved nodes are tagged `proved`. A node
tagged `planned` carries an informal statement and a proof sketch only, and shows as an
in-progress goal in the graph until a `(lean := …)` declaration or checked code block is
attached.

## Prerequisites

* **Lean** — via [elan](https://github.com/leanprover/elan); the pinned toolchain
  (`lean-toolchain`, currently `v4.33.0`) is fetched automatically by Lake.
* **[pixi](https://pixi.prefix.dev/latest/#installation)** — required to run the
  blueprint's **Python** steps: the WeasyPrint **PDF render** and the small
  `file-links.py` post-pass. The scripts and CI invoke Python through `pixi run`,
  which supplies a *pinned* Python + WeasyPrint from `pyproject.toml` + `pixi.lock`
  — so the host's system `python3` is never used and never has to match (an old
  system WeasyPrint will not render this document). Install pixi once, per
  <https://pixi.prefix.dev/latest/#installation>:

  ```bash
  curl -fsSL https://pixi.sh/install.sh | bash
  ```

  The first `pixi run` (or an explicit `pixi install`) materializes the locked
  environment under `blueprint/.pixi/` (git-ignored). Without pixi the HTML still
  builds; only the PDF is skipped.

## Build

This is a **separate Lake package** from the core library: it depends on Verso,
verso-blueprint, and (by path) on the parent `PropertyKindCalculus` package, so it does
not weigh down a plain `import PropertyKindCalculus`.

```bash
cd blueprint
lake update          # fetch verso + verso-blueprint (first time only)
lake build           # type-check the document and its Lean links
lake exe blueprint-gen --output _out/blueprint --with-html-single   # render static HTML
```

Or run `./scripts/ci-pages.sh`, which does the render **and** the
`file-links.py` pass that makes `html-multi` navigable over `file://` (see
[Viewing](#viewing-the-rendered-output) below), then prints absolute paths for
both outputs.

The rendered site lands in `blueprint/_out/blueprint/` (git-ignored). Because the
proved nodes link real declarations, `lake build` re-checks that those links
still resolve to sorry-free proofs — the blueprint cannot silently drift from the
library.

## Viewing the rendered output

Two outputs are produced; both can be opened directly as files.

* **Single page** — `_out/blueprint/html-single/index.html`. One self-contained
  page (all chapters, its own KaTeX/CSS); every link is an in-page `#anchor`.
* **Multi page** — `_out/blueprint/html-multi/index.html`. The full site (one page
  per chapter, search, dependency graph). Verso writes its cross-page links as
  *directory* URLs (`Chapter/`, no `index.html`); a browser opening such a
  `file://` directory shows the folder instead of its page. The build's
  `scripts/file-links.py` pass (run automatically by `ci-pages.sh`) rewrites those
  links to spell out `index.html`, so chapter navigation works over `file://`
  too. Search and the dependency graph fetch data at runtime and still need an
  HTTP server:

  ```bash
  python3 -m http.server 8000 -d "$PWD/_out/blueprint/html-multi"   # then http://localhost:8000/
  ```

  Pass the directory as an **absolute** path (as above): `http.server -d` does not
  validate the directory at startup, so a wrong relative path silently 404s every
  request instead of erroring.

## Conventions

* Every node has a stable label; `{uses "label"}` edges drive the dependency
  graph.
* Proved nodes use `(lean := "PropertyKindCalculus.…")`; their proved/`sorry` status is
  read from the checked library, not asserted in prose.
* Planned nodes carry an informal statement and a proof *sketch* only.
* Source citations follow the core library: Dybkær by `§x.y`, Flater by section.

## Build scripts

Three scripts under `scripts/` automate the render-and-publish pipeline; all are
idempotent and print absolute paths when they finish. The two that run Python
(`ci-pages.sh`'s `file-links.py` pass and `render-pdf.sh`) go through `pixi run`,
so they need [pixi](https://pixi.prefix.dev/latest/#installation) (see
[Prerequisites](#prerequisites)).

* **`scripts/ci-pages.sh`** — the full local/CI render. It runs `lake update`,
  then `lake exe blueprint-gen --output _out/blueprint --with-html-single` (which
  builds the document and emits both `html-multi/` and a self-contained
  `html-single/`), then the `file-links.py` pass that makes `html-multi` navigable
  over `file://`, then `render-pdf.sh` (skipped with a note if pixi is not
  installed), and finally calls `stage-docs.sh`.

  ```bash
  cd blueprint
  ./scripts/ci-pages.sh
  ```

* **`scripts/render-pdf.sh`** — renders `PropertyKindCalculus-Blueprint.pdf` from
  the single page (via WeasyPrint in the pinned pixi env) and copies it into both
  `html-single/` and `html-multi/` so the "download the PDF" link resolves in each
  and `stage-docs.sh` publishes it. Run it *after* a render (it needs
  `_out/blueprint/html-single/` to exist); `ci-pages.sh` and CI both call it, so
  you only invoke it directly to re-make the PDF from an existing build. Also
  available as the pixi task `pixi run render-pdf`.

  ```bash
  cd blueprint
  ./scripts/render-pdf.sh   # requires pixi; requires _out/blueprint/html-single to exist
  ```

* **`scripts/stage-docs.sh`** — copies the already-rendered
  `_out/blueprint/html-multi` (and `html-single/`) into the repo-root `docs/`
  folder for GitHub Pages (served from `main` at `/docs`), and drops a
  `.nojekyll` so Verso's `-verso-data/` assets are served verbatim. Run it *after*
  a render; `ci-pages.sh` already calls it as its last step, so you only invoke it
  directly when re-staging an existing build.

  ```bash
  cd blueprint
  ./scripts/stage-docs.sh   # requires _out/blueprint/html-multi to exist
  ```

The item-index tables (parts 3–13) and the front-page per-part tally are
**generated from the Lean catalogues at build time** (see `ItemIndex.lean` and
`Iso80000/Catalogue.lean`), so they cannot drift from the formalized standard;
there is no separate generation step to run.

## Why the root build is slow (and how to speed CI up)

A cold `lake build` (or `ci-pages.sh`) spends almost all of its wall-clock time
in **one** step: elaborating the root `Blueprint.lean` `#doc`, which inlines every
chapter and then computes the dependency graph and status summary over the whole
node set. Everything else (the per-chapter `.olean`s) builds in ~10–15 s each.

The cost is structural to Verso, not to anything catalogue-derived. A
`set_option profiler true` run of the root puts essentially all of the time under
`interpretation`, against ~**23 ms** of actual term `elaboration`; evaluating all
~700 catalogue entries to build the eleven item-index tables *and* the tally is
~**40 ms** of that. The reason:

* Verso's document-elaboration code runs in the Lean **interpreter**, not as
  compiled native code — both `verso` and `verso-blueprint` ship with
  `precompileModules := false` (Verso disabled it to dodge a toolchain bug).
  Interpreted, monad-transformer-heavy elaboration is one to two orders of
  magnitude slower than native, and the root runs it across the entire assembled
  document.
* The single most expensive interpreted operation is a markup `:::table`: its
  generic directive expander calls `elabBlock` on **every cell**, which recurses
  into the interpreted inline elaborators (code spans, roles, …). Two large
  hand-written `:::table`s in `Blueprint.lean` alone cost ≈ **672 s** of a
  ~16-minute cold build.

**This was addressed.** All the blueprint's data tables are now *term-built* via
the `iso_doc_table` directive (`ItemIndex.lean`): the directive constructs the
whole `Block.table` as one term and Verso elaborates it once, bypassing the
per-cell interpreted path. The eleven catalogue item indexes use it directly; the
two prose comparison tables on the front page use the `mdTable` helper, whose
`md` cells carry a tiny inline grammar (text, `` `code` ``, `*emph*`) parsed at
build time. Converting those two tables cut the cold root elaboration from
≈ **948 s to ≈ 214 s** (~4×). Prefer `iso_doc_table`/`mdTable` over a markup
`:::table` for any non-trivial table.

It can still look like a sudden regression even so: local edit/rebuild cycles are
*incremental* — `Blueprint.olean` is cached and only re-elaborated when a chapter
or the root changes, so it returns in seconds. The full cold cost only appears on
a **clean** build (fresh checkout, cleared `.lake`, or CI).

What helps further, in order of payoff vs. effort:

1. **Cache `.lake/build` in CI.** Key the cache on the Lean sources (toolchain +
   `lake-manifest.json` + the `*.lean` tree). Runs that don't touch the blueprint
   get a cache hit and skip the root elaboration entirely; only an actual
   chapter/root edit re-elaborates it. Biggest remaining CI win, no code change.
2. **Separate "check" from "publish" in CI.** Type-checking the chapters (which
   verifies every `(lean := …)` link) does not require rendering HTML; only the
   Pages job needs the full root render + `blueprint-gen`. Splitting them keeps PR
   feedback fast and pays the cold-root cost only on publish.
3. **Verso precompilation — not currently available.** Setting
   `precompileModules := true` for `verso`/`verso-blueprint` would make their
   elaborators load as a native shared library and remove the interpreted cost
   wholesale. Measured at toolchain `v4.30.0` it **fails**: the native build
   reports `build cycle detected` and the generated dynlibs hit
   `undefined symbol: initialize_subverso_SubVerso_Module` (Lean exits 127) — the
   same issue for which Verso disabled it upstream. That measurement has not been
   repeated at the current pin, so it dates the failure rather than establishing it
   today; repeat it before relying on either outcome.

The `blueprint-gen` render and `--with-html-single` add time *on top of* the
`.olean` elaboration, but the elaboration of the root document is the dominant
cost.

## License

PropertyKindCalculus and this blueprint are licensed under **Apache-2.0** (see
[`../LICENSE`](../LICENSE)). Copyright (c) 2026 California Institute of Technology
(Caltech). U.S. Government sponsorship acknowledged.
