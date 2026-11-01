#!/usr/bin/env bash
# Render the blueprint's PDF from the self-contained single page Verso emitted
# (_out/blueprint/html-single/index.html), and copy it into html-single/ and html-multi/
# so stage-docs.sh publishes it. Two steps:
#
#   1. `lake exe blueprint-print` (tools/Tools/BlueprintPrint.lean, Lean, TOOLS.md §5 step 6)
#      writes the print page beside the source: the chrome pruned, the heading outline
#      checked and renumbered, the print CSS added — everything the PDF needs decided.
#   2. WeasyPrint renders that page. It runs through the pinned pixi env
#      (blueprint/pyproject.toml + pixi.lock), the one step that needs Python at all; its
#      base URL defaults to the page's directory, which is where the page's assets are.
#
# Requires pixi (https://pixi.sh); the HTML must already be rendered (ci-pages.sh, or
# `lake exe blueprint-gen --with-html-single`).
set -euo pipefail
ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"   # blueprint/
REPO="$(cd "$ROOT/.." && pwd)"
OUT="$ROOT/_out/blueprint"
PDF_NAME="PropertyKindCalculus-Blueprint.pdf"
PDF="$OUT/$PDF_NAME"

if [ ! -f "$OUT/html-single/index.html" ]; then
  echo "error: $OUT/html-single/index.html not found — render the blueprint first" >&2
  echo "       (e.g. run blueprint/scripts/ci-pages.sh, or lake exe blueprint-gen --with-html-single)" >&2
  exit 1
fi

if [ -n "${PIXI_PROJECT_ROOT:-}" ]; then
  WEASY=(weasyprint)
elif command -v pixi >/dev/null 2>&1; then
  WEASY=(pixi run --manifest-path "$ROOT/pyproject.toml" weasyprint)
else
  echo "error: pixi not found — the PDF render uses the pinned Python + WeasyPrint env" >&2
  echo "       in blueprint/pyproject.toml. Install pixi from https://pixi.sh and retry." >&2
  exit 1
fi

MERGED="$OUT/html-single/_merged_for_pdf.html"
trap 'rm -f "$MERGED"' EXIT
(cd "$REPO" && lake exe blueprint-print "$OUT/html-single/index.html" "$MERGED")
echo "Generating PDF: $PDF"
mkdir -p "$(dirname "$PDF")"
"${WEASY[@]}" "$MERGED" "$PDF"
echo "PDF generated: $PDF ($(( $(wc -c < "$PDF") / 1024 )) KB)"

cp "$PDF" "$OUT/html-single/$PDF_NAME"
cp "$PDF" "$OUT/html-multi/$PDF_NAME"
echo "Rendered PDF: $PDF (copied into html-single/ and html-multi/)"
