#!/usr/bin/env python3
"""Gate this package's version claims against `lean-toolchain`, its blueprint-status
claims against the blueprint source, and its package-version declarations against
each other.

The bug this exists to catch: an artifact moves and the prose that describes it does
not. `lean-toolchain` moves at a bump; three READMEs and a CI comment drifted two
minor versions behind the pin before anyone read them side by side. A chapter gets
written and proved; the table that called it "planned" keeps saying so. Nothing in the
build can notice either — a stale sentence still compiles.

Five checks, the first four in increasing order of how easy they are to fool:

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

4. **Blueprint status claims (hard, with counts).** `blueprint/README.md` describes a
   document whose real status lives in the chapter sources: one `#doc (Manual) "…"`
   title per chapter file, and one `(tags := "…")` list per node. So the README's
   chapter list must name every chapter, its headline counts must equal the parsed
   ones, and — while every node parses as `proved` — no chapter source may carry the
   `_planned_` status italic and the README may carry no `🚧`/`⬜` marker. A count is
   the point here for the same reason it is in check 2: a chapter added and never
   listed, or a status glyph left behind after the node was proved, is exactly the
   drift that a table nobody re-reads will keep.

5. **Package-version sites (hard, with counts).** The package version is declared in
   `lakefile.lean` and mirrored into the blueprint's `{version}[]` literal, because
   Lake's module trace watches a module's source text and not a file its elaborator
   reads. Every site must declare the same version exactly once, and the site list
   must be the one `scripts/bump-version.sh` writes — a site added to the bumper and
   not to the gate is itself a failure.

What this does not catch, stated plainly: EXEMPT is per *file*, not per line, so a
newly stale claim written into an exempt file is reported and not failed. The two
exempt files that also carry load-bearing pins (`lakefile.lean`,
`blueprint/lakefile.toml`) have those pins in SITES, where they are gated hard — but
a fourth claim added to either would only be noted. And check 4 gates the chapter
*inventory* and the counts, not the prose *about* a chapter: a paragraph that
misdescribes a node it correctly lists still passes. Read the notes.

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
    "MODULARITY.md": (
        "a staged plan whose status ledger records the version each stage landed at — "
        "dated records of what was true when a stage shipped, not claims about the "
        "current version"
    ),
    "blueprint/PropertyKindCalculusBlueprintMain.lean": (
        "names the toolchain an upstream verso commit's own lean-toolchain declares — "
        "the version this package deliberately does not take, recorded to explain why "
        "the fix is a backport rather than a pin bump"
    ),
}

# --- 5. Package-version sites: the lakefile declaration and its Lean mirror ------
# The package version is declared in `lakefile.lean` and mirrored into the blueprint's
# `{version}[]` literal. The mirror is not redundancy for its own sake: Lake's module
# trace is the module's source, its imports, the toolchain, the platform and the
# library's `leanOptions`, so a version the *elaborator* reads out of the lakefile is
# invisible to it and the `.olean` keeps the value it was first built with. Source text
# is tracked; a literal is therefore the cheapest correct channel (see that module's
# header for the `leanOptions` alternative and why it costs a full re-elaboration).
#
# Each entry is (file, text before the version, text after) — the triple shape
# `scripts/bump-version.sh` bumps. Both must be anchored to the start of a line, and
# both lists must name the same sites; the check below enforces that too, so a site
# added to the bumper and not here cannot drift unnoticed.
PKG_VERSION_SITES: list[tuple[str, str, str]] = [
    ("lakefile.lean", '  version := v!"', '"'),
    ("blueprint/PropertyKindCalculusBlueprint/Version.lean",
     'def versionStr : String := "', '"'),
]
BUMPER = "scripts/bump-version.sh"
BUMPER_SITES = re.compile(r"^SITES=\((.*?)^\)", re.DOTALL | re.MULTILINE)

# --- 4. Blueprint status: where the real status lives, and the claim that mirrors it -
BP_CHAPTERS = "blueprint/PropertyKindCalculusBlueprint/Chapters"
BP_SOURCE = "blueprint/PropertyKindCalculusBlueprint"
BP_README = "blueprint/README.md"

# The headline sentence in BP_README, with the parsed counts substituted. Written as a
# template for the same reason SITES entries are: the gate fails on a reworded claim as
# loudly as on a stale one.
BP_HEADLINE = "{CHAPTERS} chapters carrying **{NODES} nodes, {CAPSTONES} of them capstones"

# Curated status sites in the blueprint prose: (file, sentence with {NWORD}, occurrences).
# `{NWORD}` is the number of entries in `Iso80000.catalogue`, spelled as the prose spells it.
# Same discipline as SITES: the count is the point, so a reworded claim fails as loudly as a
# stale one.
BP_CATALOGUE_REFS = "iso80000/PropertyKindCalculus/Iso80000/References.lean"
BP_CATALOGUE_SITES: list[tuple[str, str, int]] = [
    ("blueprint/PropertyKindCalculusBlueprint/Chapters/Iso80000.lean",
     "catalogues {NWORD} of its", 1),
    ("blueprint/PropertyKindCalculusBlueprint/Chapters/Iso80000.lean",
     "the list of the {NWORD} catalogued parts", 1),
    ("blueprint/PropertyKindCalculusBlueprint/Chapters/Iso80000.lean",
     "the {NWORD} definitions", 1),
]
NUMBER_WORDS = ["zero", "one", "two", "three", "four", "five", "six", "seven", "eight",
                "nine", "ten", "eleven", "twelve", "thirteen", "fourteen", "fifteen",
                "sixteen", "seventeen", "eighteen", "nineteen", "twenty"]
CATALOGUE_LIST = re.compile(r"def catalogue : List StandardRef :=\s*\[(.*?)\]", re.DOTALL)

CHAPTER_TITLE = re.compile(r'#doc \(Manual\) "([^"]+)" =>')
NODE_TAGS = re.compile(r'\(tags := "([^"]*)"\)')
# The blueprint's own status vocabulary, in the italic form its prose uses.
PLANNED_ITALIC = "_planned_"
STATUS_GLYPHS = ("\U0001f6a7", "\u2b1c")  # 🚧 in-progress, ⬜ planned

PIN_WORDS = re.compile(r"\bpin(s|ned|ning)?\b|\btoolchain\b", re.IGNORECASE)
VERSION_TOKEN = re.compile(r"\bv(\d+\.\d+\.\d+)\b")
RELEASE_TAG = re.compile(r"^v\d+\.\d+\.\d+$")
SCAN_SUFFIXES = {".md", ".lean", ".toml", ".yml", ".yaml", ".sh", ".py"}
SKIP_DIRS = {".lake", ".git", "_out", "docs", "Scratch", ".pixi"}


def read(rel: str) -> str:
    return (ROOT / rel).read_text(encoding="utf-8")


def check_package_version(quiet: bool) -> list[str]:
    """Check 5: every package-version site declares the same version, exactly once.

    Two writers of one value — `scripts/bump-version.sh` writes both sites, this reads
    both back — so the gate is what makes the pair a mirror rather than two versions.
    The occurrence count matters for the reason it does in check 2: a declaration
    reworded out of the pattern's reach would otherwise pass by matching nothing.
    """
    failures: list[str] = []
    found: dict[str, str] = {}

    for rel, before, after in PKG_VERSION_SITES:
        pat = re.compile("^" + re.escape(before) + r"(\d+\.\d+\.\d+)" + re.escape(after),
                         re.MULTILINE)
        hits = pat.findall(read(rel))
        if len(hits) != 1:
            failures.append(
                f"{rel}: expected 1 version declaration matching "
                f"{before + 'X.Y.Z' + after!r} at the start of a line, found {len(hits)}"
            )
        else:
            found[rel] = hits[0]

    versions = set(found.values())
    if len(versions) > 1:
        failures.append(
            "package-version declarations disagree: "
            + "; ".join(f"{rel} says {v}" for rel, v in sorted(found.items()))
        )
    elif versions and not quiet:
        for rel in sorted(found):
            print(f"ok    {rel}: package version {found[rel]}")

    # The bumper and this gate must know the same sites, or one of them is writing a
    # file nobody checks (or checking a file nobody writes).
    m = BUMPER_SITES.search(read(BUMPER))
    if not m:
        failures.append(f"{BUMPER}: could not parse its `SITES=(…)` array")
    else:
        bumped = {line.strip().strip("'").split("|")[0]
                  for line in m.group(1).splitlines() if line.strip().startswith("'")}
        gated = {rel for rel, _, _ in PKG_VERSION_SITES}
        if bumped != gated:
            failures.append(
                f"{BUMPER} bumps {sorted(bumped)} but this gate checks {sorted(gated)}"
            )
        elif not quiet:
            print(f"ok    {BUMPER}: bumps the same {len(gated)} site(s) this gate checks")

    return failures


def check_blueprint_status(quiet: bool) -> list[str]:
    """Check 4: the blueprint README's inventory and counts against the chapter sources.

    Returns the failures; prints what it verified. The parse is deliberately the same
    one a reader would do by hand — one title per chapter file, one tag list per node —
    so what the gate believes and what the source says cannot come apart.
    """
    failures: list[str] = []

    titles: dict[str, str] = {}
    for path in sorted((ROOT / BP_CHAPTERS).glob("*.lean")):
        m = CHAPTER_TITLE.search(path.read_text(encoding="utf-8"))
        if m:
            titles[path.stem] = m.group(1)
    if not titles:
        return [f"{BP_CHAPTERS}: parsed no chapter titles — the `#doc (Manual)` "
                "pattern no longer matches how chapters are declared"]

    tags = [t for path in sorted((ROOT / BP_SOURCE).rglob("*.lean"))
            for t in NODE_TAGS.findall(path.read_text(encoding="utf-8"))]
    nodes = len(tags)
    proved = sum("proved" in t for t in tags)
    capstones = sum("capstone" in t for t in tags)

    readme = read(BP_README)

    headline = (BP_HEADLINE
                .replace("{CHAPTERS}", str(len(titles)))
                .replace("{NODES}", str(nodes))
                .replace("{CAPSTONES}", str(capstones)))
    got = readme.count(headline)
    if got != 1:
        failures.append(f"{BP_README}: expected 1 occurrence of {headline!r}, found {got}")
    elif not quiet:
        print(f"ok    {BP_README}: {headline}")

    unlisted = sorted(t for t in titles.values() if t not in readme)
    if unlisted:
        failures.append(
            f"{BP_README}: {len(unlisted)} chapter(s) not named in it: "
            + "; ".join(unlisted)
        )
    elif not quiet:
        print(f"ok    {BP_README}: names all {len(titles)} chapters")

    if proved == nodes:
        for glyph in STATUS_GLYPHS:
            if glyph in readme:
                failures.append(
                    f"{BP_README}: carries the {glyph!r} status marker while all "
                    f"{nodes} nodes parse as proved"
                )
        for path in sorted((ROOT / BP_CHAPTERS).glob("*.lean")):
            if PLANNED_ITALIC in path.read_text(encoding="utf-8"):
                rel = path.relative_to(ROOT).as_posix()
                failures.append(
                    f"{rel}: calls a node {PLANNED_ITALIC} while all {nodes} nodes "
                    "parse as proved"
                )
        if not quiet:
            print(f"ok    blueprint: all {nodes} nodes proved, no stale status marker")
    else:
        # The honest branch: unproved nodes are legitimate, but the README has to say so.
        claim = f"{nodes - proved} not yet proved"
        if claim not in readme:
            failures.append(
                f"{BP_README}: {nodes - proved} node(s) are not tagged proved, but it "
                f"does not say so — expected the phrase {claim!r}"
            )
        elif not quiet:
            print(f"ok    {BP_README}: {claim}")

    # The catalogued-parts count, named in the standards chapter's prose.
    m = CATALOGUE_LIST.search(read(BP_CATALOGUE_REFS))
    if not m:
        failures.append(f"{BP_CATALOGUE_REFS}: could not parse `catalogue : List StandardRef`")
    else:
        n = len([e for e in m.group(1).replace("\n", " ").split(",") if e.strip()])
        if n >= len(NUMBER_WORDS):
            failures.append(f"{BP_CATALOGUE_REFS}: {n} parts, beyond the spelled-out range")
        else:
            word = NUMBER_WORDS[n]
            for rel, template, want in BP_CATALOGUE_SITES:
                sentence = template.replace("{NWORD}", word)
                got = read(rel).count(sentence)
                if got != want:
                    failures.append(
                        f"{rel}: expected {want} occurrence(s) of {sentence!r} "
                        f"({n} parts in the catalogue), found {got}"
                    )
                elif not quiet:
                    print(f"ok    {rel}: {sentence}")

    return failures


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

    # 4. Blueprint status claims.
    failures.extend(check_blueprint_status(quiet))

    # 5. Package-version sites.
    failures.extend(check_package_version(quiet))

    for rel, reason in EXEMPT.items():
        if not quiet:
            print(f"exempt {rel}: {reason}")

    if failures:
        print("\nFAILED:")
        for f in failures:
            print(f"  {f}")
        return 1
    print("\nAll version claims agree with lean-toolchain; all blueprint status")
    print("claims agree with the chapter sources; all package-version sites agree.")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
