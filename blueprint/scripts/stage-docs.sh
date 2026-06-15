#!/usr/bin/env bash
# Stage the rendered blueprint HTML into the repo-root docs/ folder for GitHub
# Pages (configured to serve from the main branch at /docs).
#
# Run AFTER the blueprint has been rendered into blueprint/_out/blueprint/
# (e.g. by blueprint/scripts/ci-pages.sh, or the CI render step). Shared by both
# the local script and the GitHub Actions workflow so the published layout is
# defined in exactly one place.
set -euo pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"   # blueprint/
REPO="$(cd "$ROOT/.." && pwd)"                            # repo root
OUT="$ROOT/_out/blueprint"
DOCS="$REPO/docs"

if [ ! -d "$OUT/html-multi" ]; then
  echo "error: $OUT/html-multi not found — render the blueprint first" >&2
  echo "       (e.g. run blueprint/scripts/ci-pages.sh)" >&2
  exit 1
fi

rm -rf "$DOCS"
# Multi-page site at the docs/ root — this is the Pages entry point (docs/index.html).
# If the PDF was rendered, ci-pages.sh placed a copy inside html-multi/ and
# html-single/, so these recursive copies publish it next to each entry point and
# the root "download the PDF" link resolves on both.
cp -r "$OUT/html-multi" "$DOCS"
# Keep the self-contained single page available too, under docs/html-single/.
cp -r "$OUT/html-single" "$DOCS/html-single"
# Disable Jekyll so Pages serves Verso's `-verso-data/` assets (leading hyphen) verbatim.
touch "$DOCS/.nojekyll"

echo "Staged $(find "$DOCS" -type f | wc -l) files into $DOCS/ (entry point: docs/index.html)"
