#!/usr/bin/env bash
# `hcp-check` with SBVR.lean in process (tools/sbvr/, TOOLS.md §6 Q1): builds the sub-package — Lake
# fetches SBVR.lean at the pin in tools/sbvr/lakefile.lean with the ambient git credentials (the
# self-hosted runner's, a maintainer's) — and runs `hcp-check-sbvr` from the root. The pin moves
# deliberately, with the renderings in HCP/sbvr/rendered/ regenerated at the new revision:
#
#   scripts/hcp-check-sbvr.sh [--fix-excerpts] [--fix-sbvr]
set -euo pipefail
cd "$(dirname "$0")/.."
( cd tools/sbvr && lake exe cache get >&2 && lake build >&2 )
exec tools/sbvr/.lake/build/bin/hcp-check-sbvr "$@"
