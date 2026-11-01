#!/usr/bin/env bash
# A pinned `sbvr-check` (SBVR.lean) for `python3 HCP/check-hcp.py --sbvr`: clones SBVR.lean at
# SBVR_LEAN_REV into .lake/sbvr-lean (or reuses SBVR_LEAN_DIR, an existing checkout — then the
# revision is not pinned), fetches Mathlib's oleans and builds the executable — and prov.lean's
# `prov-check`, which the HCP assurance gate (scripts/hcp-assurance.sh) validates records with; prints
# sbvr-check's path. HCP/assurance/manifest.yaml names the same revision; move both together.
# The pin moves deliberately, with the renderings in HCP/sbvr/rendered/ regenerated at the new
# revision (the rendering format is the tool's).
set -euo pipefail
cd "$(dirname "$0")/.."
SBVR_LEAN_REV="${SBVR_LEAN_REV:-015db27cee2758bfeeaa74233b3c64b491042d87}"
dir="${SBVR_LEAN_DIR:-.lake/sbvr-lean}"
if [[ -z "${SBVR_LEAN_DIR:-}" ]]; then
  if [[ ! -d "$dir/.git" ]]; then
    git clone -q https://github.com/Open-MBEE/SBVR.lean "$dir" >&2
  fi
  git -C "$dir" fetch -q origin "$SBVR_LEAN_REV" >&2
  git -C "$dir" checkout -q "$SBVR_LEAN_REV" >&2
fi
( cd "$dir" && lake exe cache get >&2 && lake build sbvr-check prov-check >&2 )
echo "$dir/.lake/build/bin/sbvr-check"
