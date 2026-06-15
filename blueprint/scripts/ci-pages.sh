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
# same file) and for html-single (no inter-page links).
python3 "$ROOT/scripts/file-links.py" "$OUT/html-multi"

# Render a beautifully paginated PDF from the self-contained single page (which
# Verso emits in document order). Best-effort: if WeasyPrint is not installed the
# render still succeeds and the HTML outputs are produced as usual. The PDF is
# placed inside both site directories so the root "download the PDF" link resolves
# locally and after staging (stage-docs.sh copies the site dirs verbatim).
PDF_NAME="PropertyKindCalculus-Blueprint.pdf"
PDF="$OUT/$PDF_NAME"
if python3 -c 'import weasyprint' 2>/dev/null; then
  python3 "$ROOT/scripts/html-to-pdf.py" "$OUT/html-single/index.html" "$PDF"
  cp "$PDF" "$OUT/html-single/$PDF_NAME"
  cp "$PDF" "$OUT/html-multi/$PDF_NAME"
else
  echo "note: WeasyPrint not installed — skipping PDF (pip3 install weasyprint to enable)." >&2
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
