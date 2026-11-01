#!/usr/bin/env bash
# Regenerate the blueprint's hand-authored schematics — figures/*.svg — from their
# generator, `lake exe blueprint-figures` (tools/Tools/Figures/*.lean, TOOLS.md §5 step 5),
# or, with --check, verify that the committed SVGs are what it emits, so a generator edit
# cannot land without its figure.
#
#   scripts/make-figures.sh            # rewrite figures/*.svg
#   scripts/make-figures.sh --check    # exit 1 and name each figure that differs
#
# The figures are read into `PropertyKindCalculusBlueprint/Figures.lean` by `include_str`
# at compile time, and Lake's trace does not see that file dependency: a regenerated
# figure alone does not rebuild the module. So after writing a figure that changed, this
# script removes the module's build products, and the next `lake build` rebuilds it and
# every chapter that inlines a figure.
#
# The deck's copy of the cake (research-presentations) is not covered here:
#   lake exe blueprint-figures --audience deck --out DIR
# writes it (Tools/Figures/Cake.lean says how the two audiences differ).
#
# The generator imports nothing beyond the core toolchain; `lake exe` builds it in seconds
# once the root package's dependencies are materialized (CI's `lake build` has done so).
set -euo pipefail
ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"   # blueprint/
REPO="$(cd "$ROOT/.." && pwd)"
FIG="$ROOT/figures"
FIGURES_MODULE="$ROOT/.lake/build/lib/lean/PropertyKindCalculusBlueprint/Figures"

MODE="${1:-write}"
case "$MODE" in
  write) FLAGS=() ;;
  --check) FLAGS=(--check) ;;
  *) echo "usage: make-figures.sh [--check]" >&2; exit 2 ;;
esac

before="$(cd "$FIG" && cksum ./*.svg)"
(cd "$REPO" && lake exe blueprint-figures "${FLAGS[@]}" --out "$FIG")
after="$(cd "$FIG" && cksum ./*.svg)"

if [ "$MODE" = write ] && [ "$before" != "$after" ]; then
  rm -f "$FIGURES_MODULE".* "$FIGURES_MODULE"/*.* 2>/dev/null || true
  echo "Figures.lean build products removed so the next lake build re-reads the rewritten figure(s)"
fi
