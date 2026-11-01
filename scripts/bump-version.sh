#!/usr/bin/env bash
# Show or bump the PropertyKindCalculus package version.
#
#   scripts/bump-version.sh            # print the current version
#   scripts/bump-version.sh +p         # bump patch  (X.Y.Z   -> X.Y.(Z+1))
#   scripts/bump-version.sh +m         # bump minor  (X.Y.Z   -> X.(Y+1).0)
#   scripts/bump-version.sh +M         # bump major  (X.Y.Z   -> (X+1).0.0)
#
# The version is declared once, in the Lean package (lakefile.lean's `version := v!"X.Y.Z"`) — the
# single source of truth — and mirrored into the blueprint's `{version}[]` role, whose Lean literal
# is the only channel Lake's module trace watches (see that file's header). The sites are
# `Tools.DocPins.pkgSites` (tools/Tools/DocPins.lean): the same list the doc-pins gate reads back in
# CI, so the bumper cannot write a file the gate does not check. This script is the command line;
# the bump refuses to move while the sites disagree.
#
# After a bump: commit, then `git tag vX.Y.Z` to cut the release.
set -euo pipefail
cd "$(dirname "${BASH_SOURCE[0]}")/.."
case "${1:-}" in
  '')         exec lean --run tools/Tools/DocPins.lean --version ;;
  -h|--help)  awk 'NR==1 {next} /^#/ {sub(/^# ?/, ""); print; next} {exit}' "$0"; exit 0 ;;
  +M|+m|+p)   exec lean --run tools/Tools/DocPins.lean --bump "$1" ;;
  *)          echo "error: unknown argument '$1' (use +p, +m, +M, or no args)" >&2; exit 2 ;;
esac
