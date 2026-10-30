#!/usr/bin/env bash
# HCP/sbvr/foundation.yaml is the Foundation root vocabulary of Open-MBEE/engineering-foundation-architecture
# (docs/hcp/foundation.yaml) at a pinned commit, vendored so that the ladder's `PKC ⊂ Foundation`
# checks without a network. This script fetches the pinned file and fails when the copy differs;
# bump EFA_COMMIT and re-run with --update to take a newer Foundation.
set -euo pipefail
cd "$(dirname "$0")/.."
EFA_COMMIT="${EFA_COMMIT:-2289044e0c1ee1733457b351d4435286b5d69d51}"
EFA_REPO=https://github.com/Open-MBEE/engineering-foundation-architecture
copy=HCP/sbvr/foundation.yaml
dir=.lake/efa
if [[ ! -d "$dir/.git" ]]; then git clone -q --filter=blob:none --no-checkout "$EFA_REPO" "$dir" >&2; fi
git -C "$dir" fetch -q origin "$EFA_COMMIT" >&2 2>/dev/null || git -C "$dir" fetch -q origin >&2
fetched=$(mktemp)
trap 'rm -f "$fetched"' EXIT
git -C "$dir" show "$EFA_COMMIT:docs/hcp/foundation.yaml" > "$fetched"
if [[ "${1:-}" == "--update" ]]; then
  cp "$fetched" "$copy"; echo "wrote $copy from engineering-foundation-architecture@$EFA_COMMIT"; exit 0
fi
diff "$fetched" "$copy" || { echo "FAIL: $copy differs from engineering-foundation-architecture@$EFA_COMMIT docs/hcp/foundation.yaml (run scripts/foundation-vocabulary.sh --update)"; exit 1; }
echo "ok   $copy is engineering-foundation-architecture@${EFA_COMMIT:0:8} docs/hcp/foundation.yaml"
