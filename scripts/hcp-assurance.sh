#!/usr/bin/env bash
# The ladder's assurance case (HCP/assurance/): engineering-foundation-architecture's HCP gate, `hcp-gate`
# (Lean, Efa.Hcp.Gate) at the pinned EFA_COMMIT (scripts/efa-pin.sh), built in .lake/efa and run over
# HCP/assurance/manifest.yaml — the chain's verdict recorded as PROV (prov/physlib-contributor.nq) by the
# SBVR.lean kernel the gate is built with, cited by the FACE case case.face.yaml, valuated by face.lean's
# support semantics, the gate's own run recorded (prov/gate.nq). The manifest's `tools` must be the gate's
# own pins (its lake-manifest.json). The checkout and Lake's fetch of those pins (all private) use
# OPEN_MBEE_READ_TOKEN when set (CI pushes), else git's ambient credentials; the token stays in this process.
#
#   scripts/hcp-assurance.sh [--fix] [--out DIR]      # --fix regenerates a stale record; --out writes the page
set -euo pipefail
cd "$(dirname "$0")/.."
# shellcheck source=scripts/efa-pin.sh
source scripts/efa-pin.sh
if [[ -n "${OPEN_MBEE_READ_TOKEN:-}" ]]; then
  export GIT_CONFIG_COUNT=1
  export GIT_CONFIG_KEY_0="url.https://x-access-token:${OPEN_MBEE_READ_TOKEN}@github.com/Open-MBEE/.insteadOf"
  export GIT_CONFIG_VALUE_0="https://github.com/Open-MBEE/"
fi
export GIT_TERMINAL_PROMPT=0
dir=.lake/efa
if [[ ! -d "$dir/.git" ]]; then
  mkdir -p "$dir"; git -C "$dir" init -q; git -C "$dir" remote add origin "$EFA_REPO"
fi
if [[ "$(git -C "$dir" rev-parse HEAD 2>/dev/null || true)" != "$EFA_COMMIT" ]]; then
  git -C "$dir" fetch -q --depth 1 origin "$EFA_COMMIT" >&2
  git -C "$dir" checkout -q "$EFA_COMMIT" >&2
fi
( cd "$dir" && lake exe cache get >&2 && lake build hcp-gate >&2 )
"$dir/.lake/build/bin/hcp-gate" HCP/assurance/manifest.yaml "$@"
