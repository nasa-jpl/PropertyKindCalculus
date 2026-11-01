#!/usr/bin/env bash
# A pinned `face-eval` (face.lean) for the HCP assurance gate (scripts/hcp-assurance.sh): clones
# face.lean at FACE_LEAN_REV into .lake/face-lean (or reuses FACE_LEAN_DIR, an existing checkout —
# then the revision is not pinned), fetches Mathlib's oleans and builds the executable; prints the
# checkout's path. HCP/assurance/manifest.yaml names the same revision; move both together.
set -euo pipefail
cd "$(dirname "$0")/.."
FACE_LEAN_REV="${FACE_LEAN_REV:-cefb034619704f985fb306ae9bde5df7ee6124be}"
dir="${FACE_LEAN_DIR:-.lake/face-lean}"
if [[ -z "${FACE_LEAN_DIR:-}" ]]; then
  if [[ ! -d "$dir/.git" ]]; then
    git clone -q https://github.com/Open-MBEE/face.lean "$dir" >&2
  fi
  git -C "$dir" fetch -q origin "$FACE_LEAN_REV" >&2
  git -C "$dir" checkout -q "$FACE_LEAN_REV" >&2
fi
( cd "$dir" && lake exe cache get >&2 && lake build face-eval >&2 )
echo "$dir"
