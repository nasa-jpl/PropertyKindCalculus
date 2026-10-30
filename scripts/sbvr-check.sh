#!/usr/bin/env bash
# A pinned `sbvr-check` (SBVR.lean) for `python3 HCP/check-hcp.py --sbvr`: clones SBVR.lean at
# SBVR_LEAN_REV into .lake/sbvr-lean (or reuses SBVR_LEAN_DIR, an existing checkout — then the
# revision is not pinned), fetches Mathlib's oleans and builds the executable; prints its path.
# The pin moves deliberately, with the renderings in HCP/sbvr/rendered/ regenerated at the new
# revision (the rendering format is the tool's).
set -euo pipefail
cd "$(dirname "$0")/.."
SBVR_LEAN_REV="${SBVR_LEAN_REV:-919862b99d9e301e49664b4e1a7b1002c2de3705}"
dir="${SBVR_LEAN_DIR:-.lake/sbvr-lean}"
if [[ -z "${SBVR_LEAN_DIR:-}" ]]; then
  if [[ ! -d "$dir/.git" ]]; then
    git clone -q https://github.com/Open-MBEE/SBVR.lean "$dir" >&2
  fi
  git -C "$dir" fetch -q origin "$SBVR_LEAN_REV" >&2
  git -C "$dir" checkout -q "$SBVR_LEAN_REV" >&2
fi
( cd "$dir" && lake exe cache get >&2 && lake build sbvr-check >&2 )
echo "$dir/.lake/build/bin/sbvr-check"
