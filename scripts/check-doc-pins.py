#!/usr/bin/env python3
"""Gate this package's version claims against `lean-toolchain`, its blueprint-status
claims against the blueprint source, its package-version declarations against each
other, and its plain-language gloss of the requirements against the catalogue.

The bug this exists to catch: an artifact moves and the prose that describes it does
not. `lean-toolchain` moves at a bump; three READMEs and a CI comment drifted two
minor versions behind the pin before anyone read them side by side. A chapter gets
written and proved; the table that called it "planned" keeps saying so. Nothing in the
build can notice either — a stale sentence still compiles.

Six checks, the first four in increasing order of how easy they are to fool:

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

6. **Plain-terms coverage (hard, with counts).** The introduction glosses each
   requirement in one bullet of a hand-written list, and closes by claiming the list
   names all of them. So every id the bullets cite must exist in the requirement
   catalogue, every catalogued id must be cited, and the spelled-out count in that
   closing sentence must be the catalogue's. A requirement added and never glossed is
   the drift here, and the completeness claim is what makes it checkable at all.

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
    # Only the branch NAME tracks the pin here: the commit it names declares
    # `v4.34.0-rc2` in its own `lean-toolchain`, so a claim that it "still pins
    # toolchain {VER}" would be false of the very commit this file pins.
    ("blueprint/lakefile.toml", "is the `v{VER}`-branch commit", 1),
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
                "sixteen", "seventeen", "eighteen", "nineteen", "twenty"] + [
                f"twenty-{u}" for u in
                ("one", "two", "three", "four", "five", "six", "seven", "eight", "nine")
                ] + ["thirty"]
CATALOGUE_LIST = re.compile(r"def catalogue : List StandardRef :=\s*\[(.*?)\]", re.DOTALL)

# Check 6: the introduction's plain-language gloss of the requirements. Its bullets
# each end with the requirement ids they gloss, and the sentence that closes the list
# claims the bullets name all of them.
REQ_CATALOGUE = "requirements/PropertyKindCalculus/Requirements/Catalogue.lean"
PLAIN_TERMS_FILE = "blueprint/PropertyKindCalculusBlueprint/Blueprint.lean"
PLAIN_TERMS_OPEN = "In plain terms, _rigorous metrology_ here means:"
PLAIN_TERMS_CLOSE = "Between them these bullets name all {NWORD} requirements"
REQ_ID = re.compile(r'id := "R(\d+)"')
PLAIN_TERMS_REF = re.compile(r"\bR(\d+)\b")

# Check 7 — the application-template chapters against the rubric catalogue. Each
# chapter renders its template as a *generated* table, so the table cannot drift; what
# can drift is the prose that argues each rubric, which is written by hand beside a
# catalogue that grows. The pairing below is (catalogue prefix, chapter file).
RUBRIC_CATALOGUE = "rubrics/PropertyKindCalculus/Rubrics/Catalogue.lean"
RUBRIC_CHAPTERS = [
    ("M", "blueprint/PropertyKindCalculusBlueprint/Chapters/ModelTemplate.lean"),
    ("D", "blueprint/PropertyKindCalculusBlueprint/Chapters/DeploymentTemplate.lean"),
]

# Check 8 — the terminological dictionary against the blueprint, the root documents, and
# the library. One name per concept: each term has exactly one `{deftech}` in the blueprint,
# under the section the dictionary names; a retired phrasing is refused wherever the gate
# reads and counted in the library against a ratchet pin.
TERM_DICTIONARY = "terminology/PropertyKindCalculus/Terminology/Dictionary.lean"
# Root documents where a retired phrasing is refused outright (the blueprint chapters and
# root are always in this set).
TERM_GATED_DOCS = ["README.md", "MODULARITY.md", "UNCERTAINTY.md", "METHODOLOGY_TEMPLATES.md",
                   "RENDERING.md", "blueprint/README.md"]
# Library source roots where a retired phrasing is counted against `libraryRetiredSites`.
TERM_LIBRARY_DIRS = ["PropertyKindCalculus", "graph", "torch", "dimension", "uncertainty",
                     "index", "crossrefs", "iso80000", "ForPhysLib", "examples", "tests",
                     "requirements", "rubrics", "docgen", "apps"]
TERM_DEFTECH = re.compile(r"\{deftech\}\[([^\]]+)\]")
TERM_TAG = re.compile(r'tag := "([^"]+)"')
TERM_RATCHET = re.compile(r"def libraryRetiredSites : Nat := (\d+)")

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


def check_plain_terms(quiet: bool) -> list[str]:
    """Check 6: the introduction's plain-terms bullets name every catalogued requirement.

    The list is prose written by hand against a catalogue that grows, and it makes a
    completeness claim in its closing sentence. Both halves fail here: an id cited that
    the catalogue does not have (a typo, or a requirement renumbered out from under the
    prose), and a catalogued id no bullet glosses. The spelled-out count in the closing
    sentence is checked against the catalogue for the same reason check 2 counts its
    sites — a sentence reworded out of the pattern's reach would otherwise pass by
    matching nothing.
    """
    failures: list[str] = []

    catalogued = sorted({int(n) for n in REQ_ID.findall(read(REQ_CATALOGUE))})
    if not catalogued:
        return [f"{REQ_CATALOGUE}: parsed no requirement ids — the `id := \"R…\"` "
                "pattern no longer matches how requirements are declared"]

    doc = read(PLAIN_TERMS_FILE)
    if doc.count(PLAIN_TERMS_OPEN) != 1:
        return [f"{PLAIN_TERMS_FILE}: expected 1 occurrence of {PLAIN_TERMS_OPEN!r}, "
                f"found {doc.count(PLAIN_TERMS_OPEN)}"]

    if len(catalogued) >= len(NUMBER_WORDS):
        closing = None
        failures.append(f"{REQ_CATALOGUE}: {len(catalogued)} requirements, beyond the "
                        "spelled-out range check 6 can state")
    else:
        closing = PLAIN_TERMS_CLOSE.replace("{NWORD}", NUMBER_WORDS[len(catalogued)])
        if doc.count(closing) != 1:
            failures.append(
                f"{PLAIN_TERMS_FILE}: expected 1 occurrence of {closing!r} "
                f"({len(catalogued)} requirements in the catalogue), "
                f"found {doc.count(closing)}"
            )

    start = doc.index(PLAIN_TERMS_OPEN)
    end = doc.index(closing, start) if closing and closing in doc[start:] else -1
    if end < 0:
        return failures + [f"{PLAIN_TERMS_FILE}: cannot delimit the plain-terms list — "
                           "its closing sentence was not found after the opening one"]

    cited = sorted({int(n) for n in PLAIN_TERMS_REF.findall(doc[start:end])})
    unknown = [n for n in cited if n not in catalogued]
    missing = [n for n in catalogued if n not in cited]
    if unknown:
        failures.append(f"{PLAIN_TERMS_FILE}: plain-terms bullets cite "
                        + ", ".join(f"R{n}" for n in unknown)
                        + f", which {REQ_CATALOGUE} does not define")
    if missing:
        failures.append(f"{PLAIN_TERMS_FILE}: no plain-terms bullet glosses "
                        + ", ".join(f"R{n}" for n in missing)
                        + " — either add one or drop the list's completeness claim")
    if not failures and not quiet:
        print(f"ok    {PLAIN_TERMS_FILE}: plain-terms bullets name all "
              f"{len(catalogued)} catalogued requirements")

    return failures


def check_rubric_chapters(quiet: bool) -> list[str]:
    """Check 7: each application-template chapter glosses every rubric of its template.

    The template *tables* are generated from the catalogue and need no gate. The prose
    around them is not: a rubric added to the catalogue appears in the table with no
    paragraph arguing it, and one removed leaves a paragraph arguing something the
    document no longer asks for. Both are caught here, in the two directions check 6
    catches for the requirement catalogue.

    The parse is asserted non-empty for the reason every check in this file is: a
    pattern that stops matching how rubrics are declared would otherwise report a
    catalogue of zero rubrics as fully glossed.
    """
    failures: list[str] = []
    catalogue = read(RUBRIC_CATALOGUE)

    for prefix, chapter in RUBRIC_CHAPTERS:
        ids = re.findall(rf'id := "({prefix}\d+)"', catalogue)
        if not ids:
            failures.append(
                f"{RUBRIC_CATALOGUE}: parsed no {prefix}-rubric ids — the "
                f'`id := "{prefix}…"` pattern no longer matches how rubrics are declared'
            )
            continue
        text = read(chapter)
        cited = set(re.findall(rf"\b{prefix}\d+\b", text))
        unknown = sorted(cited - set(ids), key=lambda i: int(i[1:]))
        missing = [i for i in ids if i not in cited]
        if unknown:
            failures.append(f"{chapter}: cites " + ", ".join(unknown)
                            + f", which {RUBRIC_CATALOGUE} does not define")
        if missing:
            failures.append(f"{chapter}: no paragraph glosses " + ", ".join(missing)
                            + " — either add one or drop the rubric from the template")
        if not unknown and not missing and not quiet:
            print(f"ok    {chapter}: glosses all {len(ids)} rubrics of its template")

    return failures


def term_normalize(s: str) -> str:
    """Verso's `deftech`/`tech` key normalization, reproduced: lowercase, a trailing `ies`
    becomes `y`, and every run of whitespace or hyphens becomes one space."""
    s = s.strip().lower()
    if s.endswith("ies"):
        s = s[:-3] + "y"
    return re.sub(r"[\s-]+", " ", s)


def parse_dictionary(text: str) -> list[dict]:
    """The dictionary entries, read the way a reader would: one `{ key := … }` per entry
    inside `def dictionary`, with the fields the gate needs — key, definedIn, avoid."""
    block = re.search(r"def dictionary : List Term :=\n(.*?)\n  \]\n", text, re.S)
    if not block:
        return []
    entries: list[dict] = []
    for chunk in re.split(r"\n  [\[,] \{", "\n" + block.group(1))[1:]:
        key = re.search(r'key := "([^"]*)"', chunk)
        if not key:
            continue
        defined = re.search(r'definedIn := "([^"]*)"', chunk)
        avoid_m = re.search(r"avoid := \[(.*?)\]", chunk, re.S)
        entries.append({
            "key": key.group(1),
            "definedIn": defined.group(1) if defined else "",
            "avoid": re.findall(r'"([^"]*)"', avoid_m.group(1)) if avoid_m else [],
        })
    return entries


def check_terminology(quiet: bool) -> list[str]:
    """Check 8: the terminological dictionary against the documents.

    Three claims, each read from the sources the way a reader would. (a) Every term has
    exactly one `{deftech}` in the blueprint, and it sits under the section tag the
    dictionary names — so the *Defined in* link in the rendered table reaches the prose
    that explains the term, and a term explained in two places fails. (b) A `{deftech}`
    the dictionary does not carry fails: the entry comes first. (c) No retired phrasing
    survives in a blueprint chapter, the blueprint root, or a root plan document; in the
    library's own docstrings the count is held by a ratchet pin, so it moves only by a
    conscious edit — a rise is a regression, a fall asks for the pin to be lowered.
    """
    failures: list[str] = []
    dict_text = read(TERM_DICTIONARY)
    entries = parse_dictionary(dict_text)
    if not entries:
        return [f"{TERM_DICTIONARY}: parsed no dictionary entries — the `def dictionary` "
                "layout no longer matches what this gate reads"]

    bp_files = sorted((ROOT / BP_CHAPTERS).rglob("*.lean")) + [ROOT / BP_SOURCE / "Blueprint.lean"]
    deftechs: dict[str, list[tuple[str, int, str | None]]] = {}
    tags_all: set[str] = set()
    for path in bp_files:
        src = path.read_text(encoding="utf-8")
        rel = path.relative_to(ROOT).as_posix()
        tag_positions = [(m.start(), m.group(1)) for m in TERM_TAG.finditer(src)]
        tags_all.update(t for _, t in tag_positions)
        # Verso does not traverse a `:::group` body for term definitions (measured
        # 2026-09-28: a `{deftech}` inside one renders, but every `{tech}` pointing at it
        # fails with "No term def with key"), so a definition there is refused here rather
        # than discovered at render time.
        group_lines: set[int] = set()
        in_group = False
        for n, line in enumerate(src.splitlines(), 1):
            if line.startswith(":::group"):
                in_group = True
            elif in_group and line.strip() == ":::":
                in_group = False
            if in_group:
                group_lines.add(n)
        for m in TERM_DEFTECH.finditer(src):
            enclosing = None
            for pos, t in tag_positions:
                if pos < m.start():
                    enclosing = t
                else:
                    break
            line = src.count("\n", 0, m.start()) + 1
            if line in group_lines:
                failures.append(
                    f"{rel}:{line}: {{deftech}} for {m.group(1)!r} sits inside a `:::group` "
                    "block, which Verso does not traverse for term definitions — define it "
                    "in prose or in a definition or theorem node"
                )
            deftechs.setdefault(term_normalize(m.group(1)), []).append((rel, line, enclosing))

    known: set[str] = set()
    for e in entries:
        k = term_normalize(e["key"])
        known.add(k)
        sites = deftechs.get(k, [])
        if len(sites) != 1:
            where = "; ".join(f"{r}:{l}" for r, l, _ in sites)
            failures.append(
                f"{TERM_DICTIONARY}: term {e['key']!r} needs exactly one {{deftech}} in the "
                f"blueprint, found {len(sites)}" + (f" ({where})" if where else "")
            )
        else:
            rel, line, enclosing = sites[0]
            if enclosing != e["definedIn"]:
                failures.append(
                    f"{rel}:{line}: {{deftech}} for {e['key']!r} sits under tag "
                    f"{enclosing!r}; the dictionary says {e['definedIn']!r}"
                )
        if e["definedIn"] not in tags_all:
            failures.append(
                f"{TERM_DICTIONARY}: term {e['key']!r} names section tag "
                f"{e['definedIn']!r}, which no blueprint section carries"
            )
    for k, sites in deftechs.items():
        if k not in known:
            for rel, line, _ in sites:
                failures.append(
                    f"{rel}:{line}: {{deftech}} defines {k!r}, which the dictionary does "
                    "not carry — add the entry first"
                )

    retired = [(a, e["key"]) for e in entries for a in e["avoid"]]
    gated = [p for p in bp_files if p.name != "Terminology.lean"] + \
        [ROOT / d for d in TERM_GATED_DOCS]
    for path in gated:
        if not path.exists():
            continue
        rel = path.relative_to(ROOT).as_posix()
        for n, line in enumerate(path.read_text(encoding="utf-8").splitlines(), 1):
            low = line.lower()
            for phrase, canonical in retired:
                if phrase.lower() in low:
                    failures.append(
                        f"{rel}:{n}: retired phrasing {phrase!r} — the dictionary's term "
                        f"is {canonical!r}"
                    )

    # The library: counted against the ratchet, not refused.
    hits: dict[str, int] = {}
    for d in TERM_LIBRARY_DIRS:
        base = ROOT / d
        if not base.is_dir():
            continue
        for path in sorted(base.rglob("*.lean")):
            if ".lake" in path.parts:
                continue
            try:
                low = path.read_text(encoding="utf-8").lower()
            except UnicodeDecodeError:
                continue
            n = sum(low.count(phrase.lower()) for phrase, _ in retired)
            if n:
                hits[path.relative_to(ROOT).as_posix()] = n
    total = sum(hits.values())
    pin_m = TERM_RATCHET.search(dict_text)
    if not pin_m:
        failures.append(f"{TERM_DICTIONARY}: could not parse `libraryRetiredSites`")
    else:
        pin = int(pin_m.group(1))
        if total != pin:
            top = ", ".join(f"{r} ({c})" for r, c in
                            sorted(hits.items(), key=lambda kv: -kv[1])[:6])
            verdict = "a regression" if total > pin else "lower the pin to match"
            failures.append(
                f"{TERM_DICTIONARY}: `libraryRetiredSites := {pin}`, but the library carries "
                f"{total} retired-phrasing site(s) — {verdict}; top files: {top}"
            )
        elif not quiet:
            print(f"ok    {TERM_DICTIONARY}: library retired-phrasing sites = {total}, "
                  "at the ratchet pin")
    if not failures and not quiet:
        print(f"ok    {TERM_DICTIONARY}: {len(entries)} terms, each defined once under its "
              "section; no retired phrasing in the blueprint or the root documents")
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

    # 6. The introduction's plain-terms gloss of the requirement catalogue.
    failures.extend(check_plain_terms(quiet))

    # 7. The application-template chapters against the rubric catalogue.
    failures.extend(check_rubric_chapters(quiet))

    # 8. The terminological dictionary against the blueprint, the root documents, and
    # the library's ratchet.
    failures.extend(check_terminology(quiet))

    for rel, reason in EXEMPT.items():
        if not quiet:
            print(f"exempt {rel}: {reason}")

    if failures:
        print("\nFAILED:")
        for f in failures:
            print(f"  {f}")
        return 1
    print("\nAll version claims agree with lean-toolchain; all blueprint status")
    print("claims agree with the chapter sources; all package-version sites agree;")
    print("the plain-terms bullets name every catalogued requirement; the")
    print("application-template chapters gloss every catalogued rubric; every")
    print("dictionary term is defined once and no retired phrasing survives where")
    print("the gate reads.")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
