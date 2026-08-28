#!/usr/bin/env bash
# Build the PropertyKindCalculus blueprint into static HTML under blueprint/_out/.
set -euo pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$ROOT"
OUT="$ROOT/_out/blueprint"

# --no-pdf / SKIP_PDF: skip the (slow, ~5 min) WeasyPrint PDF render for a fast
# HTML-only preview loop (the HTML render is ~30 s, so the PDF is ~90% of the wall
# clock). The HTML outputs are byte-identical either way; only the downloadable PDF
# — and the target of the in-doc "download the PDF" link — is omitted. Set the env
# var (`SKIP_PDF=1 ./scripts/ci-pages.sh`) or pass the flag (`--no-pdf`).
SKIP_PDF="${SKIP_PDF:-}"
# --no-api / SKIP_API: skip the doc-gen4 API render staged under docs/api/. The first run builds
# doc-gen4 itself and generates HTML for Lean core, so it is the other slow leg of a full render.
SKIP_API="${SKIP_API:-}"
for arg in "$@"; do
  case "$arg" in
    --no-pdf) SKIP_PDF=1 ;;
    --no-api) SKIP_API=1 ;;
    -h|--help)
      echo "usage: ci-pages.sh [--no-pdf] [--no-api]   (or SKIP_PDF=1 / SKIP_API=1)"
      echo "  --no-pdf  skip the ~5 min WeasyPrint PDF render"
      echo "  --no-api  skip the doc-gen4 API render staged under docs/api/"
      echo "  (env: LAKE_UPDATE=1 also runs lake update; off by default)"
      exit 0 ;;
    *) echo "error: unknown argument '$arg' (try --no-pdf or --no-api)" >&2; exit 2 ;;
  esac
done

# `lake update` re-resolves every dependency against the refs its lakefile NAMES, which for a
# ref that is a moving branch means the workspace can silently land on revisions the committed
# manifest does not record — and, if the new tip carries a different `lean-toolchain`, past the
# toolchain Mathlib's cache is built for. A render does not need it: `lake build` fetches and
# builds straight from the manifest, including on a clean CI checkout. So updating is opt-in.
if [ "${LAKE_UPDATE:-0}" = "1" ]; then
  lake update
fi
# Render into a CLEAN output dir: blueprint-gen never prunes superseded,
# content-hashed `searchIndex_N.<hash>.js` search shards, so a reused
# _out/blueprint accumulates stale shard sets that stage-docs.sh then copies
# into docs/ (and thus into the published site). Wiping it first guarantees a
# single, current shard set.
rm -rf "$OUT"
# `--with-html-single` also emits a one-page `html-single/index.html` (multi-page
# stays on by default). The single page is self-contained and openable directly
# as a file.
lake exe blueprint-gen --output _out/blueprint --with-html-single

# Verso writes multi-page links as directory URLs (`Chapter/#anchor`); a browser
# opening a file:// directory shows the folder instead of its `index.html`. This
# pass spells out `index.html` in those links so html-multi is navigable over
# file:// too. It is a no-op for the served site (HTTP maps `Chapter/` to the
# same file) and for html-single (no inter-page links). Python comes from pixi
# (pyproject.toml + pixi.lock), the pinned env shared with the PDF render and CI.
pixi run python "$ROOT/scripts/file-links.py" "$OUT/html-multi"

# Render a beautifully paginated PDF from the self-contained single page (which
# Verso emits in document order), via the shared scripts/render-pdf.sh — the same
# script the CI workflow calls, so the PDF name and placement live in one place.
# render-pdf.sh invokes WeasyPrint through the same pixi env. Best-effort here: if
# pixi is not installed the HTML outputs are still produced and only the PDF is skipped.
PDF_NAME="PropertyKindCalculus-Blueprint.pdf"
PDF="$OUT/$PDF_NAME"
if [ -n "$SKIP_PDF" ]; then
  echo "note: --no-pdf/SKIP_PDF set — skipping the WeasyPrint PDF render (~5 min). HTML outputs are complete; the in-doc 'download the PDF' link will 404 until a full run." >&2
  PDF=""
elif command -v pixi >/dev/null 2>&1; then
  "$ROOT/scripts/render-pdf.sh"
else
  echo "note: pixi not installed — skipping PDF (see blueprint/pyproject.toml; install pixi from https://pixi.sh)." >&2
  PDF=""
fi

# Stage the rendered HTML (and the PDF, if built) into the repo-root docs/.
# Publish it with scripts/publish-pages.sh (orphan gh-pages branch); docs/ is
# gitignored — a build artifact, never committed on main.
"$ROOT/scripts/stage-docs.sh"

# Add the doc-gen4 API site under docs/api/, the same way the CI workflow does (Phase 4b).
# MUST come after stage-docs.sh, which wipes docs/ before copying the blueprint in. Skippable
# with --no-api/SKIP_API for a blueprint-only preview loop; the in-doc "browse the API
# documentation" link then 404s until a full run, exactly as --no-pdf does for the PDF.
if [ -n "$SKIP_API" ]; then
  echo "note: --no-api/SKIP_API set — skipping the doc-gen4 API render. The in-doc 'browse the API documentation' link will 404 until a full run." >&2
else
  bash "$ROOT/../scripts/build-api-docs.sh"
fi

# Point every hint at the staged docs/ tree rather than at _out/. docs/ is the exact layout that
# publish-pages.sh commits to gh-pages — the multi-page site at the root, html-single/ and api/
# beneath it — so a link that resolves here resolves on the published site. The _out/ trees hold the
# blueprint alone: the API site is never staged into them, so the in-doc "browse the API
# documentation" link 404s when _out/blueprint/html-multi is served directly.
DOCS="$(cd "$ROOT/.." && pwd)/docs"
echo
echo "Rendered and staged at repo-root docs/ — the exact layout publish-pages.sh commits to gh-pages."
echo "Open any of these directly as a file:"
echo "  • multi page:   file://$DOCS/index.html"
echo "  • single page:  file://$DOCS/html-single/index.html"
[ -n "$PDF" ] && echo "  • PDF:          file://$DOCS/$PDF_NAME"
[ -z "$SKIP_API" ] && echo "  • API docs:     file://$DOCS/api/index.html"
echo "  • publish to gh-pages with: scripts/publish-pages.sh (add PAGES_PUSH=1 to push)"
echo
echo "Or serve the whole staged site over HTTP (search + dependency graph need this; serving docs/"
echo "rather than _out/ is what makes the in-doc API link resolve. The -d path is absolute so it"
echo "works from any directory):"
echo "  python3 -m http.server 8000 -d \"$DOCS\"   # then http://localhost:8000/"
