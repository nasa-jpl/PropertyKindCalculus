#!/usr/bin/env bash
# Generate a Lake `package-overrides.json` so a second package in this repo reuses the
# root package's already-built dependency checkouts instead of cloning and building its
# own.
#
# ## The problem
#
# `blueprint/` is a separate Lake package. It requires the root by path (`path = ".."`),
# but Lake materializes the whole *transitive git* closure under the workspace root's
# `packagesDir` — which for a blueprint build is `blueprint/.lake/packages/`. So the
# repo ends up with two Mathlib checkouts, two Batteries, two Physlib, two TorchLean…
# and the second set has to be downloaded and built from scratch. Mathlib alone is
# thousands of modules; a cold blueprint render pays for all of it a second time.
#
# ## The fix
#
# `lake --packages=FILE` (a Lake *global* option) takes a JSON file of package entries
# that override the manifest, each redirecting a package name to a `type: path`
# directory. Point them at the root's `.lake/packages/<name>` and Lake resolves — and
# reuses the build artifacts of — the single copy. Lake also reads
# `<package>/.lake/package-overrides.json` automatically during resolution, so writing
# the file there makes every plain `lake build` in that package pick it up with no flag
# and no lakefile edit.
#
# The technique is lifted from the author's `torchlean-development-slim`
# `scripts/lean-store-sync.sh`, which uses it to collapse a multi-repo Lean store to one
# copy of each shared dependency. This is the same mechanism at one repo's scale.
#
# ## Safety
#
# A `type: path` override tells Lake "trust me, this directory is that package" — Lake
# does **not** verify the revision. So this script does: it reads both manifests and
# emits an override only when the source and target pin the *same* rev, reporting any
# package where they disagree instead of silently wiring up a mismatch. Re-run it after
# any `lake update` on either side.
#
# Usage:
#   scripts/gen-package-overrides.sh [--source DIR] [--target DIR]
#                                    [--output FILE] [--exclude NAME]...
#
#   --source   package whose .lake/packages holds the copies to reuse (default: repo root)
#   --target   package that should reuse them; enables the rev cross-check and restricts
#              output to packages the target actually requires (default: none — emit all)
#   --output   where to write the JSON (default: <target>/.lake/package-overrides.json,
#              or ./package-overrides.json when no --target is given)
#   --exclude  package name to omit (repeatable)
#   --reclaim  after writing the overrides, DELETE the target's now-redundant local
#              checkouts of the redirected packages. Opt-in, because it is a deletion:
#              the overrides alone already make Lake ignore those copies, so reclaiming
#              is purely about disk. Anything Lake still resolves locally (packages the
#              target requires and the source does not) is left untouched, and a
#              re-`lake build` re-fetches anything removed in error at its pinned rev.
#
set -euo pipefail

REPO_ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
SOURCE="$REPO_ROOT"
TARGET=""
OUTPUT=""
RECLAIM=""
EXCLUDES=()

while [ $# -gt 0 ]; do
  case "$1" in
    --source)  SOURCE="$2"; shift 2 ;;
    --target)  TARGET="$2"; shift 2 ;;
    --output)  OUTPUT="$2"; shift 2 ;;
    --exclude) EXCLUDES+=("$2"); shift 2 ;;
    --reclaim) RECLAIM=1; shift ;;
    -h|--help) sed -n '2,/^set -euo/p' "${BASH_SOURCE[0]}" | sed '$d; s/^# \{0,1\}//'; exit 0 ;;
    *) echo "error: unknown argument '$1' (try --help)" >&2; exit 2 ;;
  esac
done

SOURCE="$(cd "$SOURCE" && pwd)"
[ -f "$SOURCE/lake-manifest.json" ] || {
  echo "error: no lake-manifest.json in source '$SOURCE' — build it once first" >&2; exit 1; }

if [ -n "$TARGET" ]; then
  TARGET="$(cd "$TARGET" && pwd)"
  [ -f "$TARGET/lake-manifest.json" ] || {
    echo "error: no lake-manifest.json in target '$TARGET' — build it once first" >&2; exit 1; }
fi

if [ -z "$OUTPUT" ]; then
  if [ -n "$TARGET" ]; then OUTPUT="$TARGET/.lake/package-overrides.json"
  else OUTPUT="package-overrides.json"; fi
fi

# `dir` must be a path the *native* Lake binary understands. Under Git Bash / MSYS the
# shell's own `/c/...` form is not one, so convert when cygpath is available; forward
# slashes are used throughout because they need no escaping in JSON and Windows accepts
# them. On Linux and macOS cygpath is absent and the path is already native.
native_path() {
  if command -v cygpath >/dev/null 2>&1; then cygpath -m "$1"; else printf '%s' "$1"; fi
}

# One `name|rev|configFile|manifestFile|scope|inherited` record per manifest entry.
# Written as awk rather than a JSON parser because this repo has no committed Python
# dependency and the manifest's shape is fixed by Lake.
#
# The delimiter is `|`, not a tab, and that matters: a tab is an IFS *whitespace*
# character, so `IFS=$'\t' read` collapses runs of them and drops empty fields — which
# silently shifts every column right of an empty `scope`. `|` is non-whitespace, so
# empty fields survive. No Lake package name, revision or config filename contains one.
read_manifest() {
  awk '
    /"name":/         { v=$0; sub(/.*"name": *"/,"",v);         sub(/".*/,"",v); name=v }
    /"rev":/          { v=$0; sub(/.*"rev": *"/,"",v);          sub(/".*/,"",v); rev=v }
    /"scope":/        { v=$0; sub(/.*"scope": *"/,"",v);        sub(/".*/,"",v); scope=v }
    /"inherited":/    { v=$0; sub(/.*"inherited": */,"",v);     sub(/[,}].*/,"",v); inh=v }
    /"manifestFile":/ { v=$0; sub(/.*"manifestFile": *"/,"",v); sub(/".*/,"",v); mf=v }
    /"configFile":/   {
      v=$0; sub(/.*"configFile": *"/,"",v); sub(/".*/,"",v); cf=v
      if (name != "") {
        printf "%s|%s|%s|%s|%s|%s\n", name, rev, cf, (mf=="" ? "lake-manifest.json" : mf),
               scope, (inh=="" ? "true" : inh)
        name=""; rev=""; cf=""; mf=""; scope=""; inh=""
      }
    }
  ' "$1"
}

SRC_PKGS="$(read_manifest "$SOURCE/lake-manifest.json")"
TGT_REVS=""
[ -n "$TARGET" ] && TGT_REVS="$(read_manifest "$TARGET/lake-manifest.json" | cut -d"|" -f1,2)"

is_excluded() {
  local n="$1" e
  for e in ${EXCLUDES[@]+"${EXCLUDES[@]}"}; do [ "$n" = "$e" ] && return 0; done
  return 1
}

VERSION="$(grep -oE '"version": *"[^"]*"' "$SOURCE/lake-manifest.json" | head -1 \
            | sed 's/.*: *"//; s/"//')"

emitted=0
skipped_missing=0
mismatches=()
entries=""

while IFS='|' read -r name rev cfg mfst scope inherited; do
  [ -n "$name" ] || continue
  is_excluded "$name" && continue

  # Lake stores a package under its UNESCAPED name (`«doc-gen4»` lives at `doc-gen4`).
  dir=""
  for cand in "$(printf '%s' "$name" | tr -d '«»')" "$name"; do
    if [ -d "$SOURCE/.lake/packages/$cand" ]; then dir="$SOURCE/.lake/packages/$cand"; break; fi
  done
  if [ -z "$dir" ]; then
    skipped_missing=$((skipped_missing + 1))
    continue
  fi

  # With a target: only redirect what the target actually requires, and only at a
  # matching rev — a path override is unverified by Lake, so this is the whole safety net.
  if [ -n "$TARGET" ]; then
    tgt_rev="$(printf '%s\n' "$TGT_REVS" | awk -F'|' -v n="$name" '$1==n {print $2; exit}')"
    [ -n "$tgt_rev" ] || continue
    if [ "$tgt_rev" != "$rev" ]; then
      mismatches+=("$name (source ${rev:0:12} vs target ${tgt_rev:0:12})")
      continue
    fi
  fi

  [ -n "$entries" ] && entries="$entries,"
  entries="$entries
    {
      \"name\": \"$name\",
      \"scope\": \"$scope\",
      \"inherited\": $inherited,
      \"configFile\": \"$cfg\",
      \"manifestFile\": \"$mfst\",
      \"type\": \"path\",
      \"dir\": \"$(native_path "$dir")\"
    }"
  emitted=$((emitted + 1))
done <<< "$SRC_PKGS"

mkdir -p "$(dirname "$OUTPUT")"
cat > "$OUTPUT" <<EOF
{
  "version": "$VERSION",
  "packages": [$entries
  ]
}
EOF

echo ">> wrote $OUTPUT"
echo "   $emitted override(s) pointing into $SOURCE/.lake/packages"
[ "$skipped_missing" -gt 0 ] && \
  echo "   $skipped_missing manifest entry/entries had no checkout in the source (not built yet?)"
if [ "${#mismatches[@]}" -gt 0 ]; then
  echo "!! NOT overridden — the two packages pin different revisions:" >&2
  for m in "${mismatches[@]}"; do echo "     $m" >&2; done
  echo "   Reconcile the pins (or accept the duplicate for those packages) and re-run." >&2
fi

# --- optional: drop the target's now-dead duplicate checkouts ---------------------
if [ -n "$RECLAIM" ]; then
  [ -n "$TARGET" ] || { echo "error: --reclaim needs --target" >&2; exit 2; }
  if [ ! -d "$TARGET/.lake/packages" ]; then
    echo ">> nothing to reclaim (no $TARGET/.lake/packages)"
    exit 0
  fi
  reclaimed=0
  for pkgdir in "$TARGET"/.lake/packages/*; do
    # A dangling symlink satisfies neither -e nor -d, so test -L too.
    { [ -e "$pkgdir" ] || [ -L "$pkgdir" ]; } || continue
    pkg="$(basename "$pkgdir")"
    # Reclaim only what the override actually redirects.
    grep -q "\"dir\": \".*/packages/$pkg\"" "$OUTPUT" || continue
    echo "   reclaim: $TARGET/.lake/packages/$pkg"
    # NOTE the missing trailing slash, and keep it missing. `rm -rf foo/` where `foo`
    # is a symlink to a directory dereferences the link and empties the TARGET — which
    # here would be the canonical copy in the source package. Without the slash, `rm`
    # removes the link itself. (Inherited verbatim from lean-store-sync.sh, where the
    # same footgun was found the hard way.)
    rm -rf -- "$pkgdir"
    reclaimed=$((reclaimed + 1))
  done
  echo ">> reclaimed $reclaimed redirected checkout(s) from $TARGET/.lake/packages"
fi
exit 0
