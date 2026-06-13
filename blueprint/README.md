# PropertyKindCalculus Blueprint

A [Verso](https://github.com/leanprover/verso) /
[verso-blueprint](https://github.com/leanprover/verso-blueprint) design document
for [PropertyKindCalculus](../). It records the **proved spine** (each node linked to a
real, sorry-free declaration in the core library) and the **capstone theorems we
plan to provide**, with a dependency graph and a status summary generated from
the linked Lean code.

## What it documents

| Chapter | Status | Highlights |
|---|---|---|
| The Proved Spine | ✅ linked to real decls | scale linear order, **operator-availability monotonicity**, **specialization is a preorder**, mutual comparability |
| Units and the Dimension-1 Problem | 🚧 planned | quantity/unit indexed by kind, **conversion round-trip**, **the dimension-1 disambiguation** (`vwc ≠ gwc` yet same dimension) |
| Dimension as a Forgetful Functor | 🚧 planned | `dim` map, **`dim` is a homomorphism** (dimensional coherence) |
| The Interaction Algebra (Flater App. C) | 🚧 planned | `KMul`/`KDiv`, **multiplication/division inverse on kinds**, torque × angle = energy |
| Extensivity | 🚧 planned | **extensive aggregation** ∀-theorem, ethanol+water counterexample |

Capstone theorems are tagged `capstone`; proved nodes are tagged `proved`;
not-yet-formalized nodes are tagged `planned` and show as in-progress goals in
the graph until a `(lean := …)` declaration or a checked code block is attached.

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
