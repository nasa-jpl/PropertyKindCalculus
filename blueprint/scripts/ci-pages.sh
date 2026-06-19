#!/usr/bin/env bash
# Build the PropertyKindCalculus blueprint into static HTML under blueprint/_out/.
set -euo pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$ROOT"
OUT="$ROOT/_out/blueprint"

lake update
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
if command -v pixi >/dev/null 2>&1; then
  "$ROOT/scripts/render-pdf.sh"
else
  echo "note: pixi not installed — skipping PDF (see blueprint/pyproject.toml; install pixi from https://pixi.sh)." >&2
  PDF=""
fi

# Stage the rendered HTML (and the PDF, if built) into the repo-root docs/ for
# GitHub Pages (main /docs).
"$ROOT/scripts/stage-docs.sh"

echo
echo "Rendered. Open either output directly as a file:"
echo "  • single page:  file://$OUT/html-single/index.html"
echo "  • multi page:   file://$OUT/html-multi/index.html"
[ -n "$PDF" ] && echo "  • PDF:          file://$PDF"
echo "  • staged for Pages at repo-root docs/ (commit + push, then enable Pages on main /docs)"
echo
echo "Or serve the multi-page site over HTTP (search + dependency graph need this;"
echo "the -d path is absolute so it works from any directory):"
echo "  python3 -m http.server 8000 -d \"$OUT/html-multi\"   # then http://localhost:8000/"
