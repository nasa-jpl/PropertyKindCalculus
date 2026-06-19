#!/usr/bin/env bash
# Render the single-page blueprint HTML into a paginated PDF and place a copy inside
# BOTH site directories, so the root "download the PDF" link resolves locally and
# after staging (stage-docs.sh copies html-multi/ and html-single/ verbatim into
# docs/, carrying the PDF with them).
#
# Run AFTER the blueprint has been rendered into blueprint/_out/blueprint/ (e.g. by
# blueprint/scripts/ci-pages.sh, or the CI render step). Shared by the local render
# and the CI workflow so the PDF name and placement live in one place.
#
# Python comes from pixi (blueprint/pyproject.toml + pixi.lock) — an exact, pinned
# Python + WeasyPrint, so the render is reproducible regardless of whatever
# `python3` the host happens to ship. When this script is already running inside a
# `pixi run` shell (PIXI_PROJECT_ROOT set) the env's `python` is used directly;
# otherwise it self-wraps with `pixi run`.
set -euo pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"   # blueprint/
OUT="$ROOT/_out/blueprint"
PDF_NAME="PropertyKindCalculus-Blueprint.pdf"
PDF="$OUT/$PDF_NAME"

if [ ! -f "$OUT/html-single/index.html" ]; then
  echo "error: $OUT/html-single/index.html not found — render the blueprint first" >&2
  echo "       (e.g. run blueprint/scripts/ci-pages.sh, or lake exe blueprint-gen --with-html-single)" >&2
  exit 1
fi

# Choose how to invoke Python: inside an active pixi env use it directly; else
# wrap with pixi so the pinned env is used; error clearly if pixi is missing.
if [ -n "${PIXI_PROJECT_ROOT:-}" ]; then
  PY=(python)
elif command -v pixi >/dev/null 2>&1; then
  PY=(pixi run --manifest-path "$ROOT/pyproject.toml" python)
else
  echo "error: pixi not found — the PDF render uses the pinned Python + WeasyPrint env" >&2
  echo "       in blueprint/pyproject.toml. Install pixi from https://pixi.sh and retry." >&2
  exit 1
fi

"${PY[@]}" "$ROOT/scripts/html-to-pdf.py" "$OUT/html-single/index.html" "$PDF"
cp "$PDF" "$OUT/html-single/$PDF_NAME"
cp "$PDF" "$OUT/html-multi/$PDF_NAME"

echo "Rendered PDF: $PDF (copied into html-single/ and html-multi/)"
