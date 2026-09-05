#!/usr/bin/env python3
"""Gate every version claim in this package against `lean-toolchain`.

The bug this exists to catch: `lean-toolchain` moves at a bump, and the prose that
names the pin does not. Three READMEs and a CI comment drifted two minor versions
behind the pin before anyone read them side by side, and nothing in the build could
notice — a stale sentence still compiles.

Three checks, in increasing order of how easy they are to fool:

1. **Machine pins (hard).** `blueprint/lean-toolchain` must equal `lean-toolchain`,
   and every `inputRev` in either `lake-manifest.json` that is shaped like a Lean
   release tag (`vX.Y.Z`) must name the pinned version.

2. **Curated prose sites (hard, with counts).** Each entry below is a file, an exact
   sentence with `{VER}` standing for the pinned version, and how many times it must
   occur. The count is the point: a grep that finds nothing proves nothing, so a
   claim that is silently deleted or reworded out of the pattern's reach fails the
   gate exactly as loudly as one left stale.

3. **Discovery (report-only).** Every other line in a tracked text file that names a
   `vX.Y.Z` alongside a pin word. These are reported, never failed, because some are
   deliberately not the current pin — a dated measurement of a failure mode, the
   recorded state of a checkout outside this repository, or an upstream PR named by
   the version it bumped to. Each such file is listed in EXEMPT with the reason its
   claims are allowed to differ; a line in a file that is in neither EXEMPT nor
   SITES is a new claim nobody has classified yet, and it fails the gate.

What this does not catch, stated plainly: EXEMPT is per *file*, not per line, so a
newly stale claim written into an exempt file is reported and not failed. The two
exempt files that also carry load-bearing pins (`lakefile.lean`,
`blueprint/lakefile.toml`) have those pins in SITES, where they are gated hard — but
a fourth claim added to either would only be noted. Read the notes.

Usage: `python3 scripts/check-doc-pins.py [--quiet]`; exits non-zero on any hard
failure. Wired into `.github/workflows/blueprint.yml` ahead of the Lean build.
"""

from __future__ import annotations

import json
import re
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent

# --- 2. Curated prose sites: (file, sentence with {VER}, required occurrences) ----
SITES: list[tuple[str, str, int]] = [
    ("README.md", "`leanprover/lean4:v{VER}`", 1),
    ("UNCERTAINTY.md", "PKC is pinned `v{VER}` (Mathlib v{VER}, TorchLean `combined`)", 1),
    ("lakefile.lean", "Mathlib `v{VER}` pin", 1),
    ("lakefile.lean", "doc-gen4 v{VER}", 1),
    ("blueprint/lakefile.toml", "on the v{VER} toolchain", 1),
    ("blueprint/lakefile.toml", "`v{VER}`-branch commit that still pins toolchain v{VER}", 1),
    ("RENDERING.md", "transitively (`v{VER}`, `", 1),
]

# --- 3. Discovery exemptions: version claims allowed to differ, and why ----------
EXEMPT: dict[str, str] = {
    "blueprint/README.md": (
        "dates a measurement of the Verso precompilation failure at the toolchain it "
        "was taken on; naming the current pin there would claim a run nobody made"
    ),
    "RENDERING.md": (
        "records the environment of checkouts outside this repository, and a session "
        "log whose entries are dated records of what was true when written"
    ),
    "blueprint/lakefile.toml": (
        "names the toolchain the verso-blueprint branch tip moved onto — the version "
        "this package deliberately does not take, which is why the pin is a SHA"
    ),
    "lakefile.lean": (
        "names the upstream PhysLib toolchain-bump PR by the version it bumped to"
    ),
    "dimension/PropertyKindCalculus/Dimension.lean": (
        "names the same upstream PhysLib toolchain-bump PR by the version it bumped to"
    ),
}

PIN_WORDS = re.compile(r"\bpin(s|ned|ning)?\b|\btoolchain\b", re.IGNORECASE)
VERSION_TOKEN = re.compile(r"\bv(\d+\.\d+\.\d+)\b")
RELEASE_TAG = re.compile(r"^v\d+\.\d+\.\d+$")
SCAN_SUFFIXES = {".md", ".lean", ".toml", ".yml", ".yaml", ".sh", ".py"}
SKIP_DIRS = {".lake", ".git", "_out", "docs", "Scratch", ".pixi"}


def read(rel: str) -> str:
    return (ROOT / rel).read_text(encoding="utf-8")


def main() -> int:
    quiet = "--quiet" in sys.argv
    failures: list[str] = []

    toolchain = read("lean-toolchain").strip()
    m = re.fullmatch(r"leanprover/lean4:v(\d+\.\d+\.\d+)", toolchain)
    if not m:
        print(f"FAIL  lean-toolchain is not a pinned release: {toolchain!r}")
        return 1
    ver = m.group(1)
    print(f"lean-toolchain: {toolchain}  (version {ver})")

    # 1. Machine pins.
    bp = read("blueprint/lean-toolchain").strip()
    if bp != toolchain:
        failures.append(f"blueprint/lean-toolchain is {bp!r}, root is {toolchain!r}")

    for manifest in ("lake-manifest.json", "blueprint/lake-manifest.json"):
        data = json.loads(read(manifest))
        for pkg in data.get("packages", []):
            rev = pkg.get("inputRev") or ""
            if RELEASE_TAG.match(rev) and rev != f"v{ver}":
                failures.append(
                    f"{manifest}: {pkg.get('name')} pins inputRev {rev}, expected v{ver}"
                )

    # 2. Curated prose sites.
    for rel, template, want in SITES:
        sentence = template.replace("{VER}", ver)
        got = read(rel).count(sentence)
        if got != want:
            failures.append(
                f"{rel}: expected {want} occurrence(s) of {sentence!r}, found {got}"
            )
        elif not quiet:
            print(f"ok    {rel}: {sentence}")

    # 3. Discovery.
    unclassified: list[str] = []
    for path in sorted(ROOT.rglob("*")):
        if not path.is_file() or path.suffix not in SCAN_SUFFIXES:
            continue
        rel = path.relative_to(ROOT).as_posix()
        if any(part in SKIP_DIRS for part in path.relative_to(ROOT).parts):
            continue
        try:
            lines = path.read_text(encoding="utf-8").splitlines()
        except UnicodeDecodeError:
            continue
        for n, line in enumerate(lines, 1):
            if not PIN_WORDS.search(line):
                continue
            stale = [t for t in VERSION_TOKEN.findall(line) if t != ver]
            if not stale:
                continue
            entry = f"{rel}:{n}: names v{', v'.join(stale)} — {line.strip()[:96]}"
            # A file can be both gated and exempt: SITES pins the claims that must
            # track the toolchain, EXEMPT covers the dated ones in the same file.
            if rel in EXEMPT:
                if not quiet:
                    print(f"note  {entry}")
            else:
                unclassified.append(entry)

    if unclassified:
        print("\nUnclassified version claims (add to SITES if they must track the pin,")
        print("or to EXEMPT with the reason they are allowed to differ):")
        for entry in unclassified:
            print(f"  {entry}")
        failures.append(f"{len(unclassified)} unclassified version claim(s)")

    for rel, reason in EXEMPT.items():
        if not quiet:
            print(f"exempt {rel}: {reason}")

    if failures:
        print("\nFAILED:")
        for f in failures:
            print(f"  {f}")
        return 1
    print("\nAll version claims agree with lean-toolchain.")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
