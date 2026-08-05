#!/usr/bin/env bash
# Generate the doc-gen4 API documentation and stage it under docs/api/, next to the Verso
# blueprint that blueprint/scripts/stage-docs.sh puts at the docs/ root. The publish step
# (scripts/publish-pages.sh) then commits the whole docs/ tree to the orphan gh-pages branch.
#
#   bash scripts/build-api-docs.sh
#
# Shared by the CI workflow and any local render, so the API-site scope and layout are defined
# in exactly one place (the same principle stage-docs.sh states for the blueprint layout).
#
# ORDER MATTERS: run this AFTER blueprint/scripts/stage-docs.sh, which does `rm -rf docs/` before
# copying the blueprint in. Running it first would delete docs/api again.
#
# WHY THIS EXISTS AT ALL: `@[pkc_math]` (see RENDERING.md) writes a `$$…$$` equation and the
# definition's Lean source into each annotated declaration's docstring. doc-gen4's page is the only
# fully-styled surface that typesets it — MathJax is loaded there and `$$…$$` is display math. Without
# a published API site the rendered math is visible only in an editor's InfoView hover.
set -euo pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$ROOT"

# --- Scope -------------------------------------------------------------------------------------
#
# The **Mathlib-free tier only**. doc-gen4's `module_facet docInfo` recurses into a module's
# transitive imports, and `fromDb` generates HTML for the transitive closure of the roots — so
# adding a Mathlib-backed library here (`Dimension`, `Uncertainty`, `UncertaintyRigor`, `Torch`,
# `UncertaintyExamples`, `DimensionExamples`, `Tests`) would pull all of Mathlib into both passes:
# hours of generation and multiple GB of HTML. That is a deliberate, revisitable trade — its cost is
# that the two `@[pkc_math]` models living in `UncertaintyExamples` (`wcmForwardQ`, `fictiveModelQ`)
# are absent from the site.
#
# GOTCHA before adding a library: `library_facet docs` renders `lib.rootModules`, and Lake defaults
# `roots := #[<target name>]`, NOT the glob prefix. A library that sets only `globs` therefore has a
# non-existent root and `lake build <lib>:docs` **silently succeeds while generating nothing**
# ("0 root modules"). Declare `roots` in lakefile.lean first — and check the log line below.
DOC_TARGETS=(
  "PropertyKindCalculus:docs"   # the exportable core spine
  "Examples:docs"               # worked examples: AvsForward + DocGenMathDemo carry the rendered math
  "DocGenMath:docs"             # the rendering pipeline itself
)

# --- Force the HTML assembly to re-run ----------------------------------------------------------
#
# doc-gen4's HTML-assembly steps (`fromDb`, `headerData`) are guarded by `*_built` marker files
# whose traces do NOT change when a module's own `docInfo` marker does. Observed directly: editing a
# docstring rebuilds `doc-data/<Module>.doc` (the database row) while `doc/<Module>.html` keeps its
# old timestamp and old content — so a CI run would publish documentation that does not match the
# source. Clearing the markers forces the assembly to re-run and overwrite the pages in place.
#
# Clear ONLY the markers. Two things must survive:
#   * `doc-data/<Module>.doc` and `core-*.doc` — the per-module and Lean-core database markers, so the
#     expensive `genCore` and `single` passes are reused and only the assembly repeats;
#   * the `doc/` tree's static files — because `generateHtmlDocs` ends by tracing a fixed list that
#     includes `references.bib`, which doc-gen4 does *not* emit when the bibliography is disabled
#     (this repo has no `docs/references.bib`; its bibliography lives in the Verso blueprint). Wiping
#     `doc/` therefore fails the build on a missing file that will never be produced.
rm -f "$ROOT"/.lake/build/doc-data/*_built*

# doc-gen4 ends `generateHtmlDocs` by tracing a fixed list of static files that includes
# `doc/references.bib` — but it only *emits* that file when a bibliography is configured. This repo
# has none (`INFO: reference page disabled`; the bibliography lives in the Verso blueprint), so on a
# build tree that does not already carry the file the trace step fails with a bare
# "no such file or directory". That includes a fresh CI runner. Pre-create it empty; a real
# bibliography, if one is ever added, overwrites it.
mkdir -p "$ROOT/.lake/build/doc"
[ -e "$ROOT/.lake/build/doc/references.bib" ] || : > "$ROOT/.lake/build/doc/references.bib"

echo "Building doc-gen4 API documentation for: ${DOC_TARGETS[*]}"
# Capture the log so the "(N root modules)" line can be checked: N == 0 is the silent-no-op failure
# described above, which Lake reports as success.
LOG="$(mktemp -t pkc-api-docs.XXXXXX)"
trap 'rm -f "$LOG"' EXIT
lake build "${DOC_TARGETS[@]}" 2>&1 | tee "$LOG"

if grep -q "(0 root modules)" "$LOG"; then
  echo "error: a docs target generated nothing (\"0 root modules\") — its library is missing an" >&2
  echo "       explicit \`roots\` in lakefile.lean. See the GOTCHA above." >&2
  grep -n "root modules" "$LOG" >&2
  exit 1
fi

GENERATED="$ROOT/.lake/build/doc"
if [ ! -d "$GENERATED" ]; then
  echo "error: $GENERATED not found — doc-gen4 produced no output." >&2
  exit 1
fi

DOCS="$ROOT/docs"
mkdir -p "$DOCS"
rm -rf "$DOCS/api"
cp -r "$GENERATED" "$DOCS/api"
# The blueprint's stage-docs.sh drops a .nojekyll at the docs/ root, which covers the whole tree;
# repeat it here so this script also works standalone (API site without a blueprint render).
touch "$DOCS/.nojekyll"

echo "Staged $(find "$DOCS/api" -type f | wc -l) files into $DOCS/api/ (entry point: docs/api/index.html)"
