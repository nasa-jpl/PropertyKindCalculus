#!/usr/bin/env python3
"""Regenerate `tests/PropertyKindCalculus/Tests/Iso80000/Coverage.lean` from the compiler.

That probe pins the two Dimension-library censuses — `#kind_examination_coverage` (the
model template's M6) and `#kind_dimensional_coverage` (M10) — over every part of ISO 80000
as `#guard_msgs` records, and pins the matching `_clean` gate over a part exactly when the
part's own report says it passes. The pins are the commands' output, not prose about it;
this script is how they are produced, so that a catalogue change is re-pinned by running
the census again rather than by editing a message until the build goes green.

What it does, in order:

1. `lake build` the two imports the driver needs (skip with `--no-build`).
2. Write a driver — one command per (census, part), in a fixed order, under *no* namespace,
   because the dimensional rows pretty-print kind names relative to the current namespace
   and the probe declares nothing — and run it with `lake env lean`.
3. Split the output into one message per command, refuse any `error`, and refuse a message
   that would close the doc-comment it is pinned in (`-/`).
4. Emit the probe: a fixed header, a summary block *derived from the messages* (no dates,
   no hand-typed counts, so a regeneration with an unchanged catalogue is byte-identical),
   then per part the record and — only where the report ends `clean` or is empty — the gate.

Modes:

    python3 scripts/gen-iso80000-coverage.py            # regenerate the probe in place
    python3 scripts/gen-iso80000-coverage.py --check    # diff against the probe; 1 on drift
    python3 scripts/gen-iso80000-coverage.py --from-output FILE  # reuse a captured run

`--check` is for a human after a catalogue change, not for CI: CI builds `Tests`, and a
stale pin already fails that build. What `--check` adds is the *direction* of the drift —
which part's report moved and how — before anyone decides whether to accept it.

The gate rule is the library's own (`#kind_dimensional_clean`'s docstring): a violation is
recorded, never gated on. Re-pinning a report whose summary says `violation` is a finding
awaiting a maintainer's decision; pinning `_clean` over it would be a blessing, and the
generator will not write one.
"""
from __future__ import annotations

import argparse
import difflib
import re
import subprocess
import sys
import tempfile
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
PROBE = ROOT / "tests" / "PropertyKindCalculus" / "Tests" / "Iso80000" / "Coverage.lean"

CATALOGUE_ROOT = "PropertyKindCalculus.Iso80000"
PARTS = [f"Part{i}" for i in range(1, 14)]
IMPORTS = ["PropertyKindCalculus.Iso80000", "PropertyKindCalculus.ExaminationCoverage"]

# One census: the record command, its gate, the first words of its messages, the rubric it
# serves, and the comment written above a gate.
CENSUSES = [
    {
        "record": "#kind_examination_coverage",
        "gate": "#kind_examination_clean",
        "prefix": "examination coverage",
        "rubric": "M6",
        "gate_note": "the census as an invariant, with no message to re-bless",
    },
    {
        "record": "#kind_dimensional_coverage",
        "gate": "#kind_dimensional_clean",
        "prefix": "dimensional coverage",
        "rubric": "M10",
        "gate_note": "the coverage invariant, with no message to re-bless",
    },
]

# A `lake env lean` message line may or may not carry a `file:line:col: severity: ` prefix
# depending on the toolchain; strip it either way.
PREFIX_RE = re.compile(r"^(?:\S+:\d+:\d+: )?(?:info|warning|error): ")

HEADER = """/-
`Tests.Iso80000.Coverage` — the two Dimension-library censuses over every part of ISO 80000.

**Generated. Do not edit by hand** — regenerate with `scripts/gen-iso80000-coverage.py`,
which runs the censuses and writes this file from their output.

**Records, generated from the compiler.** Every pin below is the command's own output, captured
by a driver (`lake env lean`) over the catalogue's root import and written here verbatim — not
typed. A change in what a part individuates, or in how it dimensions a kind, is therefore a
visible diff in this file; a part's report is re-pinned only when the change it records has
been read and accepted.

**Gates, only where they pass.** A `_clean` command is pinned over a part exactly when that
part's report ends `clean` (or is empty). Where the report records a violation, there is no
gate, and the record is a *finding awaiting a maintainer's decision*, not a blessing of it —
pinning a violation and gating on it are different acts, and the second is what the library's
`_clean` discipline exists to prevent (`#kind_dimensional_clean`'s docstring). What the current
findings mean, and what decisions they wait on, is `METHODOLOGY_TEMPLATES.md` §5 — not this
header, which the generator overwrites.

Summary of the records below, derived from them by the generator:

{summary}
Both commands record `AuditReceipt`s (`PropertyKindCalculus.AuditReceipt`) over each part.
-/
"""

PREAMBLE = """
-- No namespace: the dimensional rows pretty-print kinds relative to the current namespace,
-- and the driver that produced these pins ran with none. Nothing here is declared.
"""


def die(msg: str):
    print(f"gen-iso80000-coverage: {msg}", file=sys.stderr)
    sys.exit(2)


def driver_source() -> str:
    lines = [f"import {m}" for m in IMPORTS] + [""]
    for c in CENSUSES:
        lines += [f"{c['record']} {CATALOGUE_ROOT}.{p}" for p in PARTS]
    return "\n".join(lines) + "\n"


def run_driver(build: bool) -> str:
    if build:
        r = subprocess.run(["lake", "build", *IMPORTS], cwd=ROOT, text=True,
                           capture_output=True)
        if r.returncode != 0:
            die(f"`lake build {' '.join(IMPORTS)}` failed:\n{r.stdout}\n{r.stderr}")
    with tempfile.TemporaryDirectory(prefix="iso80000-coverage-") as td:
        drv = Path(td) / "Driver.lean"
        drv.write_text(driver_source())
        r = subprocess.run(["lake", "env", "lean", str(drv)], cwd=ROOT, text=True,
                           capture_output=True)
        out = r.stdout + r.stderr
        if r.returncode != 0:
            die(f"`lake env lean` exited {r.returncode}; output follows.\n{out}")
        return out


def split_messages(raw: str) -> list[str]:
    """One string per command message, in driver order."""
    lines = [PREFIX_RE.sub("", l) for l in raw.rstrip("\n").split("\n")]
    for l in lines:
        if l.startswith("error") or ": error:" in l:
            die(f"the driver reported an error; nothing pinned.\n{raw}")
    prefixes = tuple(c["prefix"] for c in CENSUSES)
    starts = [i for i, l in enumerate(lines) if l.startswith(prefixes)]
    if not starts:
        die(f"no census message found in the driver output.\n{raw}")
    # Lines before the first message are noise (build chatter); after it, everything belongs
    # to some message.
    bounds = zip(starts, starts[1:] + [len(lines)])
    msgs = ["\n".join(lines[a:b]).rstrip("\n") for a, b in bounds]
    want = len(CENSUSES) * len(PARTS)
    if len(msgs) != want:
        die(f"expected {want} messages ({len(CENSUSES)} censuses × {len(PARTS)} parts), "
            f"found {len(msgs)}.\n{raw}")
    for m in msgs:
        if "-/" in m or "/-" in m:
            die(f"a message contains a doc-comment delimiter and cannot be pinned:\n{m}")
    return msgs


def is_clean(msg: str, prefix: str) -> bool:
    last = msg.split("\n")[-1]
    return last.endswith("— clean") or msg.startswith(f"{prefix} — no ")


def summary_line(msg: str, prefix: str) -> str:
    """The report's last line — or, for an empty report, its one line minus the prefix."""
    if msg.startswith(f"{prefix} — "):
        return msg[len(prefix) + len(" — "):]
    return msg.split("\n")[-1]


MARKER_RE = re.compile(r"^(\[[a-z]+\]|⚠ [A-Z]+|⊘ [a-z]+)")


def totals(msgs: list[str]) -> dict[str, int]:
    t: dict[str, int] = {}
    for m in msgs:
        for l in m.split("\n"):
            mk = MARKER_RE.match(l)
            if mk:
                t[mk.group(1)] = t.get(mk.group(1), 0) + 1
    return t


def build_summary(per_census: list[list[str]]) -> str:
    out: list[str] = []
    for c, msgs in zip(CENSUSES, per_census):
        gated = [p for p, m in zip(PARTS, msgs) if is_clean(m, c["prefix"])]
        out.append(f"  * `{c['record']}` ({c['rubric']}):")
        for p, m in zip(PARTS, msgs):
            out.append(f"      {p:<7}{summary_line(m, c['prefix'])}")
        tot = ", ".join(f"{n} {k}" for k, n in sorted(totals(msgs).items()))
        out.append(f"    totals: {tot or 'no rows'}")
        gl = ", ".join(gated) if gated else "no part"
        out.append(f"    gated (`{c['gate']}`): {gl}")
    return "\n".join(out) + "\n"


def by_census(msgs: list[str]) -> list[list[str]]:
    n = len(PARTS)
    return [msgs[i * n:(i + 1) * n] for i in range(len(CENSUSES))]


def render(msgs: list[str]) -> str:
    per_census = by_census(msgs)
    out = [HEADER.format(summary=build_summary(per_census))]
    out += [f"import {m}" for m in IMPORTS]
    out.append(PREAMBLE)
    for c, cmsgs in zip(CENSUSES, per_census):
        out.append(f"/-! ## `{c['record']}` — {c['rubric']}, part by part -/\n")
        for p, m in zip(PARTS, cmsgs):
            out.append(f"/--\ninfo: {m}\n-/\n#guard_msgs (whitespace := lax) in\n"
                       f"{c['record']} {CATALOGUE_ROOT}.{p}\n")
            if is_clean(m, c["prefix"]):
                out.append(f"-- {p} is clean: {c['gate_note']}\n#guard_msgs in\n"
                           f"{c['gate']} {CATALOGUE_ROOT}.{p}\n")
    return "\n".join(out)


def main() -> int:
    ap = argparse.ArgumentParser(description=__doc__.split("\n\n")[0])
    ap.add_argument("--check", action="store_true",
                    help="regenerate to memory and diff against the probe; exit 1 on drift")
    ap.add_argument("--no-build", action="store_true",
                    help="skip `lake build` of the driver's imports")
    ap.add_argument("--from-output", metavar="FILE",
                    help="parse a captured `lake env lean` output instead of running "
                         "the driver")
    ap.add_argument("--save-output", metavar="FILE",
                    help="keep the driver's raw output here (for --from-output later)")
    args = ap.parse_args()

    if args.from_output:
        raw = Path(args.from_output).read_text()
    else:
        raw = run_driver(not args.no_build)
    if args.save_output:
        Path(args.save_output).write_text(raw)
    msgs = split_messages(raw)
    text = render(msgs)

    if args.check:
        current = PROBE.read_text() if PROBE.exists() else ""
        if current == text:
            print(f"{PROBE.relative_to(ROOT)}: up to date")
            return 0
        sys.stdout.writelines(difflib.unified_diff(
            current.splitlines(True), text.splitlines(True),
            fromfile=str(PROBE.relative_to(ROOT)), tofile="regenerated"))
        print(f"\n{PROBE.relative_to(ROOT)}: DRIFT — the censuses' output differs "
              "from the pins")
        return 1

    PROBE.write_text(text)
    for c, cm in zip(CENSUSES, by_census(msgs)):
        gated = sum(is_clean(m, c["prefix"]) for m in cm)
        print(f"{c['record']}: {len(cm)} records, {gated} gates; "
              + ", ".join(f"{n} {k}" for k, n in sorted(totals(cm).items())))
    print(f"wrote {PROBE.relative_to(ROOT)}")
    return 0


if __name__ == "__main__":
    sys.exit(main())
