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

# Stage the rendered HTML into the repo-root docs/ for GitHub Pages (main /docs).
"$ROOT/scripts/stage-docs.sh"

echo
echo "Rendered. Open either output directly as a file:"
echo "  • single page:  file://$OUT/html-single/index.html"
echo "  • multi page:   file://$OUT/html-multi/index.html"
echo "  • staged for Pages at repo-root docs/ (commit + push, then enable Pages on main /docs)"
echo
echo "Or serve the multi-page site over HTTP (search + dependency graph need this;"
echo "the -d path is absolute so it works from any directory):"
echo "  python3 -m http.server 8000 -d \"$OUT/html-multi\"   # then http://localhost:8000/"
