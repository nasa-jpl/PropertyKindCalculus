#!/usr/bin/env bash
# The ladder's assurance case (HCP/assurance/): engineering-foundation-architecture's HCP gate,
# tools/hcp_assurance.py at the pinned EFA_COMMIT (scripts/efa-pin.sh), over HCP/assurance/manifest.yaml —
# the chain's sbvr-check verdict recorded as PROV (HCP/assurance/prov/physlib-contributor.nq), cited by the
# FACE case HCP/assurance/case.face.yaml, valued by face-eval, the gate's own run recorded (prov/gate.nq).
# Needs sbvr-check and prov-check (scripts/sbvr-check.sh) and face-eval (scripts/face-eval.sh) at the
# revisions the manifest names; both scripts clone and build them when SBVR_LEAN / FACE_LEAN are unset.
#
#   scripts/hcp-assurance.sh [--fix] [--out DIR]      # --fix regenerates a stale record; --out writes the page
set -euo pipefail
cd "$(dirname "$0")/.."
# shellcheck source=scripts/efa-pin.sh
source scripts/efa-pin.sh
dir=.lake/efa
if [[ ! -d "$dir/.git" ]]; then git clone -q --filter=blob:none --no-checkout "$EFA_REPO" "$dir" >&2; fi
if ! git -C "$dir" cat-file -e "$EFA_COMMIT^{commit}" 2>/dev/null; then
  git -C "$dir" fetch -q origin "$EFA_COMMIT" >&2 2>/dev/null || git -C "$dir" fetch -q origin >&2
fi
gate=.lake/hcp_assurance.py
git -C "$dir" show "$EFA_COMMIT:tools/hcp_assurance.py" > "$gate"
if [[ -z "${SBVR_LEAN:-}" ]]; then SBVR_LEAN="$(dirname "$(dirname "$(dirname "$(dirname "$(scripts/sbvr-check.sh)")")")")"; fi
if [[ -z "${FACE_LEAN:-}" ]]; then FACE_LEAN="$(scripts/face-eval.sh)"; fi
SBVR_LEAN="$SBVR_LEAN" FACE_LEAN="$FACE_LEAN" python3 "$gate" HCP/assurance/manifest.yaml "$@"
