#!/usr/bin/env bash
# CI: clean the checkout but keep the `.lake` directories between runs, pruned of what is unused.
# CLEAN_LEAN_CACHE=true deletes them too, for a build from scratch.
set -euo pipefail
cd "$(dirname "$0")/.."

if [ "${CLEAN_LEAN_CACHE:-false}" = true ]; then
  git clean -ffdx
  exit 0
fi
git clean -ffdx -e .lake

for pkg in . blueprint; do
  # A run that stopped between two `lake build -R` leaves its `-K` options configured.
  rm -rf "$pkg/.lake/config"
  [ -d "$pkg/.lake/packages" ] || continue
  names="$(grep -o '"name": *"[^"]*"' "$pkg/lake-manifest.json" | sed 's/.*: *"//; s/"$//; s/[«»]//g')"
  for dir in "$pkg"/.lake/packages/*/; do
    name="$(basename "$dir")"
    if ! grep -qxF "$name" <<<"$names"; then
      echo "pruning $dir: not in $pkg/lake-manifest.json"
      rm -rf "$dir"
    fi
  done
done

# Mathlib's download cache is shared by every Lean project of the account: prune by age only.
cache="${MATHLIB_CACHE_DIR:-${XDG_CACHE_HOME:-$HOME/.cache}/mathlib}"
if [ -d "$cache" ]; then
  find "$cache" -type f -name '*.ltar' -atime +30 -print -delete | wc -l | sed 's/$/ Mathlib cache file(s) pruned/'
fi
