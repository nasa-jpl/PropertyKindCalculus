#!/usr/bin/env bash
# Build every library and example target this package declares — the one command that says
# "the whole package still compiles", shared by CI and any local check so the scope is defined
# in exactly one place (the same principle scripts/build-api-docs.sh states for the API site).
#
#   bash scripts/build-all-libs-examples.sh
#
# WHY THIS EXISTS AT ALL: a bare `lake build` at this root covers ONLY the default target —
# the `PropertyKindCalculus` core-spine library, ~44 jobs — and reports success. None of the
# other libraries (`ForPhysLib`, `Iso80000`, `Tests`, the examples, the uncertainty stack, …)
# is touched, so "lake build was green" is not evidence that a change outside the core spine
# still compiles. Every library's lakefile docstring ends "Build with `lake build <Name>`";
# this script is those commands, all of them.
#
# THE TARGET LIST IS DERIVED, NOT COPIED. The `lean_lib «Name»` / `lean_exe «name»`
# declarations in lakefile.lean are the single source of truth; the list is parsed out of it
# here so a newly added library is swept in without editing this script — a hand-maintained
# second copy would drift exactly the way the hand-copied dimension strings in
# Iso80000/Catalogue.lean once did. (`lakefile.lean` spells every target with the «» guillemet
# form; the parse relies on that.)
#
# WHAT "BUILT" MEANS PER TARGET — three caveats the green tick does not carry:
#   * `UncertaintyBatch` is only TYPECHECKED: its `CudaT` device ops are `@[extern]` FFI with
#     no interpreter fallback. A batched result is *run* only by the parity executables —
#     which this script LINKS (a build check that catches missing symbols) but does not
#     execute. CI runs them; locally, run them separately:
#       lake exe ssprc_batched_parity   # batched SSPRC vs the scalar Ssprc.run
#       lake exe mcm_batched_parity     # batched MCM   vs the scalar Mcm.run
#   * The default build uses the portable CPU stub for the batch carrier. A `-K cuda=true`
#     container build is a different artifact with its own verification story (see the memory
#     notes on stub linking); nothing here checks the device path.
#   * The doc-gen4 `:docs` facets are NOT built here — that is scripts/build-api-docs.sh,
#     which also owns the marker-clearing and staging those facets need.
set -euo pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$ROOT"

# --- Derive the target list from lakefile.lean --------------------------------------------------
mapfile -t TARGETS < <(grep -oP '^lean_(lib|exe) «\K[^»]+' lakefile.lean)

if [ "${#TARGETS[@]}" -lt 2 ]; then
  echo "error: parsed only ${#TARGETS[@]} target(s) from lakefile.lean — the «Name» parse" >&2
  echo "       no longer matches how targets are declared. Fix the grep above." >&2
  exit 1
fi

echo "Building ${#TARGETS[@]} targets derived from lakefile.lean:"
printf '  %s\n' "${TARGETS[@]}"

# --- Build --------------------------------------------------------------------------------------
#
# One `lake build` invocation, not a loop: Lake schedules the shared prefix (Mathlib, PhysLib,
# TorchLean, the core spine) once and parallelizes across targets, where a per-target loop
# would re-walk the whole dependency graph N times.
#
# The log is captured so the job count can be echoed back: the count is the evidence that this
# ran wider than the default target (compare the ~44 jobs of a bare `lake build`).
LOG="$(mktemp -t pkc-all-libs.XXXXXX)"
trap 'rm -f "$LOG"' EXIT
lake build "${TARGETS[@]}" 2>&1 | tee "$LOG"

SUMMARY="$(grep -E 'Build completed successfully' "$LOG" | tail -1 || true)"
if [ -z "$SUMMARY" ]; then
  echo "error: lake exited 0 but printed no 'Build completed successfully' line — inspect the log." >&2
  exit 1
fi
echo "All ${#TARGETS[@]} targets: $SUMMARY"
