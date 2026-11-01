# The tools in Lean: every checker, gate and generator of this package a Lean program, its claims proved

*Concept note. Nothing converted yet; §5 is the order of work, §6 the open questions (answer by
number; defaults in bold).* The rule and its reasons are
engineering-foundation-architecture's `docs/architecture/tools-in-lean.md`, whose first tool
(`hcp-gate`, Lean) this package already runs (`scripts/hcp-assurance.sh`); this note applies the
rule to the tools that live *here*.

This package's gates and generators outside Lean are Python scripts, about 4,500 lines across
twelve files (§2). Each one decides something a reader is then asked to trust: that an HCP
chapter's synopsis names only vocabulary that exists, that the pinned toolchain is the one the
prose claims, that a committed probe is the census's output, that a figure is its generator's.
A Python script carries that decision with nothing but the reader's confidence in its author,
and nothing in `lake build` notices when it is wrong. The rest of this package does not work that
way: a requirement is a theorem or a `#guard`, a census is a command whose output is pinned, a
rendering is a function whose faithfulness is proved. The rule, from here on: **every tool is a
Lean program, and the properties its verdict rests on are theorems.** Python is not a tool
language in this package; shell is glue around `lake`, `git` and `pixi`, nothing more.

Terms, for readers who do not maintain these tools:

- A **gate** is a program CI runs that exits 0 or fails; what it decides is a *claim* the package
  makes (the prose names the pinned version; the HCP chapters are consistent; the figures are
  current).
- A **generator** writes an artifact (a probe file, a figure, an HTML page) from inputs a reader
  can inspect; its claim is that the artifact says what the inputs say — and, when the artifact
  is committed, that regenerating it is a no-op.
- A **property** is a statement about the program a theorem establishes: a predicate is decidable
  and the gate evaluates the decision; a generator is deterministic; a check is complete over a
  closed enumeration rather than a regular expression's reach.
- The **trusted computing base** is what remains unproved: Lean's kernel and compiler, Lake, the
  operating system, and the I/O a tool performs. It is named once (§4) and the same for every tool.

## 1. What a Lean tool buys here, and what it does not

- **Elaboration instead of regular expressions.** Four of the twelve scripts read Lean source
  with regexes — `^module` headers, `#doc (Manual) "…"` titles, `(tags := "…")` lists, `-- example`
  probe lines, `%%% tag := "…" %%%` metadata — and each docstring records a case where the regex
  matched prose it should not have (`module-census.py`: 23 false `module` lines in a package whose
  true count was 0). A Lean tool runs in `lake env` and *asks the environment*: `ModuleData.isModule`
  for adoption, the `Verso` document tree for chapters and their tags, `Lean.Elab.Command` for
  whether a probe elaborates. Nothing is matched; what does not elaborate is an error, not a miss.
- **Closed enumerations instead of counted sentences.** `check-doc-pins.py`'s checks 2, 4, 5 and 6
  each count occurrences of a sentence because "a grep that finds nothing proves nothing". In Lean
  the sites are a `List Site` the bumper and the gate *share* (one definition), the version is read
  from `lean-toolchain` once, and completeness — every requirement glossed, every chapter listed —
  is `∀ r ∈ catalogue, r ∈ glossed`, decided over the catalogue the `Requirements` library already
  exports as data.
- **The census is the generator.** `gen-iso80000-coverage.py` writes a driver, runs `lake env lean`,
  splits its stdout into messages and re-emits them as `#guard_msgs` pins. In Lean the two censuses
  are `CommandElabM` functions the probe already calls; the generator *is* a Lean script calling the
  same functions and printing the probe — no stdout parsing, and determinism (same catalogue, same
  bytes) is a theorem about a pure function of the catalogue, not an observation about a run.
- **Figures as data.** The three SVG generators are deterministic drawings from literal
  coordinates; a Lean emitter over an `Svg` inductive gives the same bytes, and `make-figures.sh
  --check` becomes `decEq` on the committed file.
- **One trusted base.** `IO.FS` for bytes, L4YAML for YAML (the HCP front matter is YAML the script
  parses by hand today, 150 lines of it), `git`, `lake` and `pixi run weasyprint` as subprocesses
  whose exit codes are checked and whose output is data, never a verdict.

It does not buy: correctness of a specification (a wrong required-sections list is wrong in Lean
too), properties of the world outside the process (WeasyPrint's PDF is rendered by WeasyPrint),
or speed (the tools that elaborate pay the imports they elaborate against; CI already pays them).

## 2. The inventory: each Python tool, what it claims, the property its Lean form proves

| tool (lines) | claim today | consumers | Lean form | property to prove |
|---|---|---|---|---|
| `HCP/check-hcp.py` (1171): the HCP chapter gate | every `L*.lean` chapter has the `REQUIRED` front-matter fields, its `id` equals its `%%% tag`, the required sections in order; every synopsis bullet names a vocabulary term that is declared (dot-notation members in their namespace); the blueprint's anchor excerpts are byte-equal to the lesson sources (`--fix-excerpts`); every worksheet has its exercises, TODOs, no `#guard_msgs`, and the learning-path lines; `--sbvr`: the ladder's SBVR chain checks clean and `HCP/sbvr/rendered/*.md` is its rendering (`--fix-sbvr`); commented probes are real declarations | CI (`Check HCP blueprint excerpts and the ladder in SBVR`), the chapters' `tools:` lines, `HCP/sbvr/rendered/*.md` headers | `lake exe hcp-check [--fix-excerpts] [--fix-sbvr]` in `tools/`; front matter through L4YAML; chapters and tags from the `Verso` tree, not regexes; declarations by `Environment.contains` after importing `HCP`; the SBVR chain checked **in process** by `require SBVR` at the pin `scripts/sbvr-check.sh` names today (`SBVR.Record`/`ChainFile.run`, the renderer `SBVR.render`), no clone, no `sbvr-check` subprocess | the required sections a closed `List String` with `∀ s ∈ required, s ∈ sections chapter` decided; `excerpt = source[anchor]` by `decEq`, `fixExcerpts` idempotent (`fix (fix c) = fix c`); `rendered = SBVR.render chain view` by `decEq` with SBVR.lean's determinism theorem; vocabulary-name resolution a lookup in the elaborated environment (no `contains_identifier` substring test) |
| `scripts/check-doc-pins.py` (750): the pin and status gate | 1 `blueprint/lean-toolchain = lean-toolchain` and every `vX.Y.Z` `inputRev` the pin; 2 each curated site states the version exactly *n* times; 3 every other versioned line classified (EXEMPT) or failed; 4 `blueprint/README.md` lists every chapter, its counts equal the parsed ones, no `_planned_`/🚧/⬜ left; 5 every package-version site declares the same version once, the site list the bumper's; 6 every requirement glossed in the introduction, the count the catalogue's; 7 each application-template chapter glosses every rubric of its template and cites no other; 8 every dictionary term defined once, no retired phrasing where the gate reads | CI (`Check version and blueprint-status claims`, before Elan), `scripts/bump-version.sh` | `lake exe doc-pins` in the **core** package (no Mathlib: it must run before the cache), reading `lean-toolchain`, both `lake-manifest.json` (L4YAML reads JSON), the sites; chapters and their `tags` from the blueprint sources by the same `Verso` reader `hcp-check` uses; the requirement ids from the `Requirements` library's catalogue, not a regex over `README.md`; the site list one `def sites : List Site` the bumper (`bump-version.sh` → `lake exe doc-pins --bump V`) and the gate share | the eight checks as eight `Decidable` propositions over the read data with `theorem gate_iff : gate d = true ↔ C1 d ∧ … ∧ C8 d`; `bump` and `check` the same `sites` (`C5 (bump v d) v` as a theorem: a bump always passes the package-version check it rewrites for, the only one a bump touches); checks 6 and 7 the two-sided `∀ r ∈ catalogue, r ∈ glossed` and `∀ r ∈ glossed, r ∈ catalogue`; check 8 `∀ t ∈ dictionary, count defs t = 1` and `retired ∩ gated = ∅` |
| `scripts/gen-iso80000-coverage.py` (268): the coverage probe generator | `tests/…/Iso80000/Coverage.lean` is the two censuses' output over every ISO 80000 part, the `_clean` gate pinned exactly where the part's report ends `clean`; `--check` shows the drift's direction | a maintainer after a catalogue change (CI builds `Tests`, where a stale pin fails) | `lake env lean scripts/gen-iso80000-coverage.lean [--check]`: calls `kindExaminationCoverage`/`kindDimensionalCoverage` (the census functions, factored out of the commands) per part and prints the probe; no driver file, no stdout split | `probe catalogue` a pure function (determinism by definition); `cleanGate p ∈ probe ↔ report p ends clean` as a theorem over the emitted list (the "never bless a violation" rule as a property of the emitter) |
| `scripts/import-layers.py` (155), `scripts/module-census.py` (98): the module-system censuses, `MODULARITY.md` | per `lean_lib`, which files are `module`, their depth and dependents, the files no lib covers; the loaded closure's `isModule` per olean | a maintainer migrating bottom-up; `MODULARITY.md`'s numbers | `lake exe module-census [--tree\|--closure] [--tsv]`: libs and their globs from the Lake workspace (`Lake.Workspace` loaded in process, not a hand parser of `lakefile.lean`), headers by `Lean.Parser.parseHeader`, closure by importing the sinks and reading `ModuleData.isModule` | every tracked `.lean` file attributed to exactly one lib or reported (`partition` total over the file list); `depth` the longest path in the import DAG (a `theorem` over the fold); the comment-aware `module` count equal to the parser's verdict, by construction |
| `scripts/inject-index-docs.py` (133): the API-site post-pass | each per-declaration index block (`emit-index-json.lean`) is spliced into the doc-gen4 page of the declaration it names, once | `scripts/build-api-docs.sh` | the rest of `scripts/emit-index-json.lean`: the Lean script that writes the blocks also splices them (`lake env lean scripts/inject-index-docs.lean SITE`), HTML as text with the insertion point located by the declaration's anchor id | `∀ b ∈ blocks, b.page ∈ site → count (inject site b) b.anchor = 1`; a block whose page is not on the site is reported and skipped, as today — the API site publishes the Mathlib-free tier only, so a kind outside it has no page (the skip stays a count in the output, never silent) |
| `blueprint/scripts/file-links.py` (86): the `file://` link pass | every Verso directory link in `html-multi` names `index.html`; nothing else changes | `blueprint/scripts/ci-pages.sh` | a Verso output pass in `PropertyKindCalculusBlueprint` (the blueprint is Lean already) or `lake exe blueprint-links OUT`; the four rewrite rules a total function on `href` values | the rewrite idempotent and every rewritten target a file that exists in `OUT` (decided by the tool, a theorem that the index of written pages lists it) |
| `blueprint/scripts/figures/*.py` (1334): the three schematics and the shared icon | `blueprint/figures/*.svg` are what the generators emit (`make-figures.sh --check`) | `make-figures.sh`, `Figures.lean` (`include_str`), the deck's copies (`--out`, `--audience deck`) | `lake exe blueprint-figures [--check] [--out DIR] [--audience deck]`: an `Svg` inductive and a serializer; each figure a `def : Svg` | `serialize` deterministic by definition; `--check` is `decEq` on bytes; the two audiences' cakes differ only where `audience` is read (a theorem over the figure definition) |
| `blueprint/scripts/html-to-pdf.py` (478): the PDF | `_out/blueprint/html-single/index.html` merged and paginated into one PDF | `blueprint/scripts/render-pdf.sh` (through `pixi run`) | **stays at the edge**: everything before the render — the merge of the multi-page fallback, the `-verso-*` skipping, heading renumbering and nesting check, bookmark cleanup, the print CSS — moves into a Lean print pass (`blueprint-print`, text → text) that writes the page WeasyPrint is then given by shell; the PDF must not change, so the pass is checked by diffing its HTML against the Python pipeline's on the committed blueprint before the Python goes. The PDF is a rendering, not a claim | the print pass is a pure function of the HTML (idempotent: `print (print h) = print h`; heading nesting of its output well-formed); WeasyPrint is the trusted base's edge (§4) |
| `scripts/*.sh` (`sbvr-check.sh`, `hcp-assurance.sh`, `foundation-vocabulary.sh`, `build-api-docs.sh`, `make-figures.sh`, `ci-pages.sh`, `render-pdf.sh`, …) | fetch pinned snapshots, build, run the tools | CI, maintainers | **stay shell**: glue around `git`, `lake` and `pixi` with exit codes checked; no decision is made there (`sbvr-check.sh` goes once the chain is checked in process) | none |

## 3. The package

The tools live in this package, not a sibling: they import what they check.

```
lakefile.lean                 require SBVR (pinned; private, fetched with OPEN_MBEE_READ_TOKEN as hcp-gate's pins are), L4YAML
tools/Tools/DocPins.lean      §2 row 2 — Mathlib-free, in the core's dependency closure
tools/Tools/HcpCheck.lean     §2 row 1 — imports HCP, SBVR, the Verso reader
tools/Tools/ModuleCensus.lean §2 row 4 — Lake.Workspace in process
tools/Tools/Verso.lean        the chapter/tag reader hcp-check and doc-pins share
tools/Tools/Svg.lean          §2 row 7
scripts/*.lean                the generators that already are Lean scripts (emit-*, roundtrip-*, gen-iso80000-coverage, inject-index-docs)
blueprint/…/Links.lean        §2 row 6, in the blueprint's own package
```

`lean_exe doc-pins`, `hcp-check`, `module-census`, `blueprint-figures` with `srcDir := "tools"`, as
the parity harnesses already are under `apps/`. Toolchain the package's (`lean-toolchain`); module
system on in every new file (`MODULARITY.md`'s bottom-up rule: the tools import the libraries, so
they come last). CI's steps keep their names; each `python3 …` becomes `lake exe …` or `lake env lean …`.

## 4. The trusted base, named once

- Lean 4 (kernel, compiler), Lake, Verso, doc-gen4, the operating system.
- **Files**: `IO.FS` for bytes; L4YAML for YAML and JSON (`lake-manifest.json`, the index blocks);
  a document that does not parse is an error, never a default.
- **Processes**: `git` (`rev-parse`, `fetch`, `checkout`, `show`), `lake`, and `pixi run` for
  WeasyPrint. Each call's exit code is checked and its output is data, never interpreted as a
  verdict; the verdict is computed in process from what was read.
- **No clock, no randomness, no environment-dependent paths** in anything that produces a committed
  artifact (the probe, the figures, the renderings).

Anything a tool does outside this list is a defect of the tool, not an extension of the base.

## 5. Order of work

1. **`doc-pins`**: the smallest and the one that runs first in CI; it fixes the shared `Verso`
   chapter reader and the shared `sites` definition with the bumper. *Shipped*:
   `tools/Tools/DocPins.lean` (Q3 resolved for it: textual chapter readers, because it runs before
   the blueprint builds).
2. **`hcp-check`**: the largest; `require SBVR` lands here and retires `scripts/sbvr-check.sh`'s
   clone-and-build (the pin becomes Lake's, `lake-manifest.json`, as `hcp-gate`'s already is).
   *Shipped*: `tools/Tools/HcpCheck.lean`, with `--sbvr SBVR_CHECK` still the pinned binary run as
   a subprocess whose output is data (Q1: a private `require` in this package's lakefile would
   break every pull-request build, which has no token; the in-process form waits for a tools
   sub-package with its own lakefile).
3. **`gen-iso80000-coverage.lean`** and **`inject-index-docs.lean`**: generators that join the Lean
   scripts already in `scripts/`.
   *Shipped (first half)*: `scripts/gen-iso80000-coverage.lean`, `lake env lean --run … [--check]`;
   the censuses called in process (`examinationRows`, `coverageRows`), the probe byte-identical to
   the Python's but for its header; `PartBlock.gate_iff_clean` is the never-bless-a-violation rule.
4. **`module-census`**: the two censuses in one executable; `MODULARITY.md`'s numbers regenerated.
5. **`blueprint-figures`** and the **link pass**; `make-figures.sh` and `ci-pages.sh` call them.
6. **`blueprint-print`**: the print pass of `html-to-pdf.py` (merge of the multi-page fallback,
   `-verso-*` skipping, heading renumbering and nesting check, bookmark cleanup, print CSS) as a
   Lean text pass, its HTML diffed against the Python pipeline's on the committed blueprint before
   the Python goes.
7. Delete `scripts/*.py`, `HCP/check-hcp.py`, `blueprint/scripts/**/*.py` except `html-to-pdf.py`'s
   WeasyPrint call, which shrinks to rendering the page `blueprint-print` wrote; `blueprint/pyproject.toml`
   keeps only WeasyPrint.

Each step is one PR off `main`, replacing one Python tool and its CI step, byte-identical outputs
where an artifact is committed (the probe, the figures, the renderings, the excerpts) so the switch
is visible as a no-op diff of the artifacts.

## 6. Open questions

1. **Where the SBVR pin lives.** `require SBVR` in this package's lakefile (Lake's pin; Mathlib is
   shared, so the cost is SBVR.lean's own modules) or keep `scripts/sbvr-check.sh`'s clone and call
   the binary. **Default: `require SBVR`**; `HCP/assurance/manifest.yaml`'s `tools.sbvr_lean` stays
   hcp-gate's pin (the record's kernel) and may differ from this package's, as it does today.
2. **`doc-pins` before the Mathlib cache.** It must run in seconds on a bare checkout. **Default: a
   core-only executable** (`lean_exe doc-pins` whose imports are `Init`, `Lean`, L4YAML), built by
   `lake build doc-pins` before `lake exe cache get`; Elan is installed first, which moves the step
   after Phase 0's toolchain install (about a minute).
3. **Verso as a dependency of the tools.** Reading chapters and tags through Verso's own document
   tree needs the blueprint package's imports (Verso, the manual genre). **Default: the chapter
   reader is a Lean script in the blueprint package** (`lake env lean`, where Verso is already a
   dependency), emitting the chapter list as JSON that `doc-pins` and `hcp-check` read through
   L4YAML — one reader, two consumers, no Verso in the core.
4. **WeasyPrint.** Stay (a rendering is not a claim) or replace with a Lean PDF writer. **Default:
   stay**, invoked on the one page `blueprint-print` (step 6) writes; the merge and the print
   preprocessing move into that Lean pass, nothing of them is dropped.
5. **Figures: port or freeze.** The three schematics change rarely; porting 1,334 lines of drawing
   code buys determinism the committed SVGs already exhibit. **Default: port**, because
   `make-figures.sh --check` is a gate and the rule has no exception for rarely-run gates;
   alternative: freeze the SVGs as the source of truth and delete the generators.
6. **What of the properties is `Decidable` and what is `theorem`.** **Default:** every gate
   predicate is a `def` + `instance : Decidable` + `theorem sound`; no gate evaluates a `Bool`
   function that has no definition it is proved to decide (engineering-foundation-architecture's
   rule, Q6 there).
7. **The order.** `doc-pins` first because it is small and CI runs it first; `hcp-check` second
   because it carries the SBVR pin. *Alternative:* `hcp-check` first, since it is the gate the HCP
   chapters cite in their `tools:` lines. **Default: as §5.**
