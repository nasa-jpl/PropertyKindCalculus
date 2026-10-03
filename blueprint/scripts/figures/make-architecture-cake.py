#!/usr/bin/env python3
"""Emit the architecture-cake schematic: the stack a model's trust traces down through.

The figure answers *after everything derived, what is still trusted?* by drawing the
libraries a model written in the calculus requires, top to bottom, and saying at each
band what kind of vouching that band costs a reviewer. It is a picture of a dependency
graph and carries no measured claim of its own. What it *does* assert — who requires
whom — is checkable, and was checked against `lakefile.lean` and `lake-manifest.json`
of PropertyKindCalculus, the vendored TorchLean (rev 458f2a7a), cslib (rev 990e65a6)
and physlib on 2026-10-03:

    PropertyKindCalculus -> Physlib   -> mathlib
    PropertyKindCalculus -> cslib     -> mathlib
    PropertyKindCalculus -> TorchLean -> floatlib, mathlib

PhysLib and cslib are peers: each requires Mathlib and nothing else of the stack, and
PhysLib is drawn beside cslib for that reason. TorchLean is likewise on Mathlib
directly; it is drawn as its own band because FloatLib rides under it —
`lakefile.lean` records why: "TorchLean brings `FloatLib` transitively, which is where
the executable binary32 word (`ExecFloat.Binary 8 23`) and the Flocq rounding theory
live." cslib and Mathlib are at one revision: cslib's own manifest pins Mathlib
`v4.34.0` at the commit PKC resolves to.

Two audiences read the figure, and the bands above the calculus differ between them:

  blueprint   (the default) one band above the calculus — *a domain model written in
              the calculus* — and a TorchLean chip stating the three-carrier
              architecture the blueprint's own text states. Every chip is a property
              of the library or the build; nothing on the figure is measured
              downstream. Written to `figures/architecture-cake.svg`, which the
              blueprint inlines (`PropertyKindCalculusBlueprint/Figures.lean`).
  deck        the JPL Gen-AI two-arcs deck: two mission bands above the calculus (the
              operational data product; the science algorithm as configured for a
              run) and the TorchLean chip that cites the deck's own CPU/GPU
              measurements. The deck's conventions are in force — ■ measured ·
              ◪ partly · □ designed — and its copy is written with `--out` into
              research-presentations, which commits it beside the deck.

The PKC band carries the wordless mark of Lowe's square, drawn by the shared `pkc_icon`
module so that it and the explanatory square (`make-lowe-square-pkc.py`) cannot drift
apart.

Logo provenance — the sources under `figures/logos/` are downscaled copies of:
  lean            the Lean 4 brand mark, redrawn inline as paths (no file)
  torchlean       github.com/lean-dojo/TorchLean home_page/assets/media/brand/
  floatlib        github.com/lean-dojo/FloatLib site/content/assets/
  physlib         leanprover-community/physlib docs/Physlib-logo.jpeg — cropped
                  to its non-white bounding box, (75, 373, 1873, 872) of the
                  1920x1080 original, then resized to 360 px wide
  arena banner    arena.lean-lang.org/round/2026-09/static/

Mathlib and cslib are set as wordmarks rather than logos on purpose: neither library
ships a mark of its own, and the leanprover-community logo — the obvious stand-in —
is a variation on the Lean mark, so the bands would read as the same layer twice.

The SVG root carries a `viewBox` and no fixed size, so the same file scales to its
container both inlined in the blueprint and as the deck's `<img>`.

Usage:  python3 scripts/figures/make-architecture-cake.py
        python3 scripts/figures/make-architecture-cake.py --audience deck --out <deck>/architecture-cake.svg
"""

from __future__ import annotations

import argparse
import base64
import mimetypes
import pathlib
import sys
from xml.sax.saxutils import escape

import pkc_icon

HERE = pathlib.Path(__file__).resolve().parent      # blueprint/scripts/figures
BLUEPRINT = HERE.parent.parent                       # blueprint/
FIGURES = BLUEPRINT / "figures"
LOGOS = FIGURES / "logos"

# ── canvas ────────────────────────────────────────────────────────────────
# The deck renders the figure by `section.figure img { width: 100%; max-height: 67vh }`
# into a 1280x720 slide with 55px side padding: 1170 CSS px wide, 482 px tall. A
# viewBox 1200 wide therefore renders at ~0.975 scale, so nominal font sizes here are
# very close to rendered CSS pixels. The height is computed from the bands; if it
# exceeds 494 the deck's height binds instead and the bands shrink a little.
W = 1200

RAIL_X = 26  # the "traces down" arrow
BAND_X0, BAND_X1 = 54, 772
LOGO_X0, LOGO_W = 66, 180
TEXT_X = 262
CHIP_X = 790
PEER_GAP = 8          # between the two peer bands of one row
PEER_LOGO_W = 100     # a peer's logo slot is narrower than a full band's
PEER_TEXT_DX = 124    # a peer's text starts here, from the peer band's left edge

RED = "#E4002B"
BLACK = "#000000"
GRAY5 = "#767676"
GRAY3 = "#D5D5D5"
GRAY1 = "#F9F9F9"
TINT = "#FDF2F4"
MONO = "SF Mono, Menlo, Consolas, monospace"

# ── the layers, top to bottom ─────────────────────────────────────────────
# `chip` is what that layer costs a reviewer in trust. A chip line is a string, or a
# (bold head, rest) pair when a row holds two peers and each line must say whose it is.
MISSION = "mission"
BASE = "base"
FLOOR = "floor"

# Above the calculus, for the deck: the mission stack, in the deck's own conventions.
DECK_MISSION_LAYERS = [
    dict(
        kind=MISSION, h=58, logo="pixels",
        name="the operational data product",
        role="values · QC flags · provenance, per pixel",
        chip=["■ the pixel's own conditions travel with it"],
    ),
    dict(
        kind=MISSION, h=64, logo="statement",
        name="a trusted science algorithm, as configured for a run",
        role="the scientist runs what operations runs, aside from the hardware",
        chip=["■ every number's kind is derived, checked, or attested",
              "with a reason — or the build fails",
              "□ release: the scientist accepts every attestation"],
    ),
]

# Above the calculus, for the blueprint: one band, stated in the calculus's own terms.
BLUEPRINT_MODEL_LAYER = dict(
    kind=MISSION, h=64, logo="statement",
    name="a domain model written in the calculus",
    role="its boundaries declared, audited, and decided by the build",
    chip=["■ every number's kind is derived, checked, or attested",
          "with a reason — or the build fails"],
)

# The TorchLean chip is the one base-layer chip that differs: the deck cites its own
# CPU/GPU measurements; the blueprint states the three-carrier architecture.
TORCH_CHIP = {
    "deck": ["CPU ■ same binary, same inputs → same bits",
             "GPU ◪ same bits as CPU where the arithmetic matches;",
             "the iterative fit's run-to-run bits are unmeasured"],
    "blueprint": ["■ one source, three carriers: ℝ to prove, FP32 to bound",
                  "rounding, IEEE32Exec to run — bridged by refinement theorems"],
}


def base_layers(audience: str) -> list[dict]:
    return [
        dict(
            kind=BASE, h=64, logo="pkc",
            name="PropertyKindCalculus",
            role="a quantity carries its kind in its type — what the number is a value <i>of</i>",
            chip=["■ each module declares its inputs → outputs, with kinds",
                  "■ the build proves the code has exactly those",
                  "■ modules compose by contract, across repositories"],
        ),
        dict(
            kind=BASE, h=74,
            peers=[
                dict(logo="physlib-logo.png", name="PhysLib",
                     role=["dimensions and units"]),
                dict(logo="cslib", name="CSLib",
                     role=["labelled transition systems", "and bisimulation"]),
            ],
            chip=[("PhysLib ", "■ dimensions checked at compile time:"),
                  "a dimensionally wrong formula does not build",
                  ("CSLib ", "■ the kind-transporting weak bisimulation is one"),
                  "in the textbook sense — not a local re-definition"],
        ),
        dict(
            kind=BASE, h=64, logo="torchlean+floatlib",
            name="TorchLean + FloatLib",
            role="tensors, CPU and GPU execution · the executable float word, specified",
            chip=TORCH_CHIP[audience],
        ),
        dict(
            kind=BASE, h=56, logo="mathlib",
            name="Mathlib",
            role="the mathematics the proofs cite",
            chip=["proofs: checked by the kernel",
                  "definitions: community peer review before merge"],
        ),
        dict(
            kind=FLOOR, h=92, logo="lean",
            name="the Lean kernel + three classical axioms",
            role="the only thing that must be believed",
            chip=["■ the build prints the axiom profile",
                  "small enough to re-implement — two dozen independent",
                  "checkers compete to reject bad proofs (Kernel Arena)"],
        ),
    ]


def layers_for(audience: str) -> list[dict]:
    top = DECK_MISSION_LAYERS if audience == "deck" else [BLUEPRINT_MODEL_LAYER]
    return top + base_layers(audience)


# The Lean 4 brand mark, as supplied: stroked outline, viewBox 0 0 486 169.
LEAN_MARK = (
    "M206.333 5.67949H105.667M206.333 5.67949L243.25 84.5M206.333 5.67949V84.5"
    "M243.25 84.5H317.549M243.25 84.5L279.667 163.321L280.889 163.318L317.549 84.5"
    "M206.333 84.5V163.321H5V5M206.333 84.5H105.667M317.549 84.5L353 5.67949"
    "M353 5.67949V164M353 5.67949H353.667L480.333 163.454H481V5"
)


def data_uri(path: pathlib.Path) -> str:
    mime, _ = mimetypes.guess_type(path.name)
    if mime is None:
        mime = "application/octet-stream"
    payload = base64.b64encode(path.read_bytes()).decode("ascii")
    return f"data:{mime};base64,{payload}"


def image(path: pathlib.Path, x: float, y: float, w: float, h: float) -> str:
    """An <image> box that letterboxes its content, like object-fit: contain."""
    return (
        f'<image href="{data_uri(path)}" x="{x:.1f}" y="{y:.1f}" '
        f'width="{w:.1f}" height="{h:.1f}" preserveAspectRatio="xMidYMid meet"/>'
    )


def lean_logo(cx: float, cy: float, w: float) -> str:
    """The stroked Lean mark, scaled to width `w` and centered on (cx, cy)."""
    s = w / 486.0
    h = 169.0 * s
    x, y = cx - w / 2.0, cy - h / 2.0
    return (
        f'<g transform="translate({x:.1f},{y:.1f}) scale({s:.4f})" '
        f'fill="none" stroke="{BLACK}" stroke-width="10" '
        f'stroke-linecap="round" stroke-linejoin="round">'
        f'<path d="{LEAN_MARK}"/></g>'
    )


def pixel_grid(cx: float, cy: float) -> str:
    """The product's slot: a raster tile, one cell flagged — per pixel."""
    cols, rows, s, gap = 5, 3, 9.0, 3.0
    w = cols * s + (cols - 1) * gap
    h = rows * s + (rows - 1) * gap
    x0, y0 = cx - w / 2, cy - h / 2
    out = []
    for i in range(cols):
        for j in range(rows):
            hot = (i, j) == (3, 1)
            out.append(
                f'<rect x="{x0 + i * (s + gap):.1f}" y="{y0 + j * (s + gap):.1f}" '
                f'width="{s}" height="{s}" rx="1.5" fill="{RED if hot else "#FFFFFF"}" '
                f'stroke="{RED if hot else GRAY5}" stroke-width="1.1"/>'
            )
    return "".join(out)


def statement(cx: float, cy: float) -> str:
    """The model's slot: a reviewed statement, with its check."""
    w, h = 54.0, 40.0
    x0, y0 = cx - w / 2, cy - h / 2
    out = [
        f'<rect x="{x0:.1f}" y="{y0:.1f}" width="{w}" height="{h}" rx="3" '
        f'fill="#FFFFFF" stroke="{GRAY5}" stroke-width="1.2"/>'
    ]
    for k, frac in enumerate((0.26, 0.46, 0.66)):
        wide = w - 16 if k != 2 else w - 30
        out.append(
            f'<line x1="{x0 + 8:.1f}" y1="{y0 + h * frac:.1f}" x2="{x0 + 8 + wide:.1f}" '
            f'y2="{y0 + h * frac:.1f}" stroke="{GRAY3}" stroke-width="2.4"/>'
        )
    out.append(
        f'<path d="M{x0 + w - 20:.1f} {y0 + h - 12:.1f} l5 6 l10 -13" fill="none" '
        f'stroke="{RED}" stroke-width="2.6" stroke-linecap="round" stroke-linejoin="round"/>'
    )
    return "".join(out)


def wordmark(cx: float, cy: float, text: str) -> str:
    """A library that ships no mark of its own gets its name, set plainly."""
    return (
        f'<text x="{cx:.1f}" y="{cy + 7:.1f}" text-anchor="middle" font-size="26" '
        f'font-weight="700" letter-spacing="-0.4" fill="{BLACK}">{escape(text)}</text>'
    )


def tspans(lines: list, x: float, y: float, size: float, fill: str, lead: float) -> str:
    """A block of chip lines. A line is a string, or a (bold head, rest) pair."""
    out = [f'<text x="{x:.1f}" y="{y:.1f}" font-size="{size}" fill="{fill}">']
    for i, line in enumerate(lines):
        dy = 0 if i == 0 else lead
        if isinstance(line, tuple):
            head, rest = line
            out.append(
                f'<tspan x="{x:.1f}" dy="{dy:.1f}"><tspan font-weight="700" fill="{BLACK}">'
                f'{escape(head)}</tspan>{escape(rest)}</tspan>'
            )
        else:
            out.append(f'<tspan x="{x:.1f}" dy="{dy:.1f}">{escape(line)}</tspan>')
    out.append("</text>")
    return "".join(out)


def role_text(role: str, x: float, y: float) -> str:
    """The role line, honoring a single <i>…</i> emphasis span."""
    if "<i>" not in role:
        return f'<text x="{x:.1f}" y="{y:.1f}" font-size="14" fill="{GRAY5}">{escape(role)}</text>'
    head, rest = role.split("<i>", 1)
    mid, tail = rest.split("</i>", 1)
    return (
        f'<text x="{x:.1f}" y="{y:.1f}" font-size="14" fill="{GRAY5}">{escape(head)}'
        f'<tspan font-style="italic">{escape(mid)}</tspan>{escape(tail)}</text>'
    )


def logo_slot(logo: str, lx: float, lcx: float, cy: float, w: float) -> str:
    """The logo for a band, centered on (lcx, cy) in a slot `w` wide that starts at `lx`."""
    if logo == "lean":
        return lean_logo(lcx, cy, 118)
    if logo == "pkc":
        # The wordless mark, centered in the slot by its true bounding box: the carrier
        # plates hang below and to the right of the square, so centering the square
        # itself would sit the group high and left.
        s = 40.0
        x0, y0, x1, y1 = pkc_icon.extent(s)
        return pkc_icon.icon(lcx - (x0 + x1) / 2, cy - (y0 + y1) / 2, s)
    if logo == "torchlean+floatlib":
        return (image(LOGOS / "torchlean-logo.png", lx + 8, cy - 25, 78, 50) +
                image(LOGOS / "floatlib-logo.png", lx + 98, cy - 25, 78, 50))
    if logo in ("mathlib", "cslib"):
        return wordmark(lcx, cy, logo)
    if logo == "pixels":
        return pixel_grid(lcx, cy)
    if logo == "statement":
        return statement(lcx, cy)
    if logo:
        h = 48 if w >= LOGO_W else 32
        return image(LOGOS / logo, lx, cy - h / 2, w, h)
    return ""


def band_rect(x0: float, x1: float, y: float, h: float, kind: str) -> str:
    if kind == MISSION:
        fill, stroke, sw = TINT, RED, 1.2
    elif kind == FLOOR:
        fill, stroke, sw = "#FFFFFF", BLACK, 2.2
    else:
        fill, stroke, sw = GRAY1, GRAY3, 1.2
    out = [f'<rect x="{x0:.1f}" y="{y:.1f}" width="{x1 - x0:.1f}" height="{h}" '
           f'rx="6" fill="{fill}" stroke="{stroke}" stroke-width="{sw}"/>']
    if kind == MISSION:
        out.append(f'<rect x="{x0:.1f}" y="{y:.1f}" width="5" height="{h}" fill="{RED}"/>')
    return "".join(out)


def peer_band(peer: dict, x0: float, x1: float, y: float, h: float, kind: str) -> str:
    """One of two libraries sharing a row: its own band, logo, name and role lines."""
    cy = y + h / 2.0
    out = [band_rect(x0, x1, y, h, kind)]
    lx = x0 + 10
    out.append(logo_slot(peer["logo"], lx, lx + PEER_LOGO_W / 2.0, cy, PEER_LOGO_W))
    tx = x0 + PEER_TEXT_DX
    roles = peer["role"]
    name_y = cy - 4 if len(roles) == 1 else cy - 12
    out.append(
        f'<text x="{tx:.1f}" y="{name_y:.1f}" font-size="19" font-weight="700" '
        f'fill="{BLACK}">{escape(peer["name"])}</text>'
    )
    for i, role in enumerate(roles):
        out.append(role_text(role, tx, name_y + 21 + 16 * i))
    return "".join(out)


def build(audience: str) -> str:
    layers = layers_for(audience)
    body: list[str] = []

    # ── the layers ────────────────────────────────────────────────────────
    y = 4.0
    floor_cy = None
    for layer in layers:
        h = layer["h"]
        cy = y + h / 2.0
        kind = layer["kind"]
        if kind == FLOOR:
            floor_cy = cy

        if "peers" in layer:
            mid = (BAND_X0 + BAND_X1) / 2.0
            left, right = layer["peers"]
            body.append(peer_band(left, BAND_X0, mid - PEER_GAP / 2.0, y, h, kind))
            body.append(peer_band(right, mid + PEER_GAP / 2.0, BAND_X1, y, h, kind))
        else:
            body.append(band_rect(BAND_X0, BAND_X1, y, h, kind))
            body.append(logo_slot(layer["logo"], LOGO_X0, LOGO_X0 + LOGO_W / 2.0, cy, LOGO_W))
            name_size = 18 if kind == FLOOR else 19
            if kind == FLOOR:
                name_y, role_y = cy - 14, cy + 8
            else:
                name_y, role_y = cy - 4, cy + 17
            body.append(
                f'<text x="{TEXT_X}" y="{name_y:.1f}" font-size="{name_size}" font-weight="700" '
                f'fill="{BLACK}">{escape(layer["name"])}</text>'
            )
            body.append(role_text(layer["role"], TEXT_X, role_y))

        # chip
        chip = layer["chip"]
        first = cy - (len(chip) - 1) * 7.5 + 5
        body.append(tspans(chip, CHIP_X, first, 14, BLACK if kind == FLOOR else GRAY5, 15))

        y += h + 5.0

    bottom = y - 5.0
    height = bottom + 4.0

    # ── the Kernel Arena badge, inside the floor band ─────────────────────
    arena = LOGOS / "kernel-arena-banner.jpg"
    if arena.exists() and floor_cy is not None:
        bw, bh = 132.0, 72.0
        bx, by = BAND_X1 - bw - 14, floor_cy - bh / 2.0
        body.append(
            f'<clipPath id="cake-arenaclip"><rect x="{bx:.1f}" y="{by:.1f}" '
            f'width="{bw}" height="{bh}" rx="5"/></clipPath>'
        )
        body.append(
            f'<image href="{data_uri(arena)}" x="{bx:.1f}" y="{by:.1f}" width="{bw}" '
            f'height="{bh}" preserveAspectRatio="xMidYMid slice" clip-path="url(#cake-arenaclip)"/>'
        )
        body.append(
            f'<rect x="{bx:.1f}" y="{by:.1f}" width="{bw}" height="{bh}" rx="5" '
            f'fill="none" stroke="{GRAY3}" stroke-width="1"/>'
        )

    # ── the traceability rail ─────────────────────────────────────────────
    # Ids are prefixed per figure: the blueprint's single-page build inlines every
    # figure into one document, where a bare `arrow` would collide with another's.
    body.append(
        f'<defs><marker id="cake-arrow" viewBox="0 0 10 10" refX="9" refY="5" '
        f'markerWidth="6" markerHeight="6" orient="auto-start-reverse">'
        f'<path d="M 0 0 L 10 5 L 0 10 z" fill="{RED}"/></marker></defs>'
    )
    body.append(
        f'<line x1="{RAIL_X}" y1="20" x2="{RAIL_X}" y2="{bottom - 8:.1f}" '
        f'stroke="{RED}" stroke-width="2" marker-end="url(#cake-arrow)"/>'
    )
    body.append(
        f'<text transform="translate({RAIL_X - 8},{(bottom / 2):.1f}) rotate(-90)" '
        f'text-anchor="middle" font-size="13" font-weight="700" fill="{RED}" '
        f'letter-spacing="1.6">TRACEABLE DOWN TO</text>'
    )

    head = (
        f'<svg xmlns="http://www.w3.org/2000/svg" xmlns:xlink="http://www.w3.org/1999/xlink" '
        f'viewBox="0 0 {W} {height:.0f}" '
        f'font-family="Helvetica Neue, Helvetica, Arial, sans-serif">'
        f'<rect width="{W}" height="{height:.0f}" fill="#FFFFFF"/>'
    )
    return head + "".join(body) + "</svg>"


def main() -> int:
    ap = argparse.ArgumentParser(description=__doc__,
                                 formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("--audience", choices=("blueprint", "deck"), default="blueprint")
    ap.add_argument("--out", default=None,
                    help="output path (default: figures/architecture-cake.svg; "
                         "required for --audience deck)")
    args = ap.parse_args()

    if args.out is None:
        if args.audience == "deck":
            print("--audience deck needs --out: the deck's copy lives in its own repository",
                  file=sys.stderr)
            return 2
        args.out = str(FIGURES / "architecture-cake.svg")

    missing = [p.name for p in (
        LOGOS / "torchlean-logo.png", LOGOS / "floatlib-logo.png",
        LOGOS / "physlib-logo.png",
    ) if not p.exists()]
    if missing:
        print(f"missing logo sources in {LOGOS}: {', '.join(missing)}", file=sys.stderr)
        return 1

    out = pathlib.Path(args.out)
    out.parent.mkdir(parents=True, exist_ok=True)
    out.write_text(build(args.audience), encoding="utf-8")
    print(f"{out}  {out.stat().st_size:,} bytes")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
