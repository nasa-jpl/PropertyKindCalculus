#!/usr/bin/env python3
"""Splice the per-declaration index blocks into the generated doc-gen4 pages.

    python3 scripts/inject-index-docs.py <site-dir> <blocks.json>

`scripts/build-api-docs.sh` runs this after doc-gen4 has generated the HTML and after
`scripts/emit-index-json.lean` has written the blocks.

WHY THIS IS A POST-PROCESS AND NOT AN ATTRIBUTE
-----------------------------------------------
The obvious design is the one `@[pkc_math]` already uses: append the block to each kind's own
docstring with `Lean.addDocStringCore`, and let doc-gen4 render it like any other docstring. That is
impossible here. `addDocStringCore` refuses a declaration that lives in an *imported* module, and the
facts being reported — which crossings mint this kind, which theorems mention it — are almost always
declared in modules *later* than the kind itself. By the time they are known, the kind is imported.

So the blocks are computed in Lean (`PropertyKindCalculus.Index.declarationBlocks`), which is where
the question "what is this kind's algebra?" belongs, emitted as HTML, and spliced here. This script
knows nothing about the calculus; it only knows where in a doc-gen4 page a declaration's block ends.

IDEMPOTENCE
-----------
Every inserted block carries `class="pkc-index"`, and a declaration that already has one is skipped.
Re-running is therefore safe, which matters because doc-gen4's HTML assembly is skipped when its
`*_built` markers are current, so a rebuild can leave already-injected pages in place.
"""

import json
import re
import sys
from pathlib import Path

MARKER = 'class="pkc-index"'

STYLE = (
    '<style id="pkc-index-style">'
    ".pkc-index{margin-top:.75em;padding:.4em .75em;border-left:3px solid #999}"
    ".pkc-index p{margin:.3em 0}"
    ".pkc-index ul{margin:.2em 0 .5em 1.3em}"
    "</style>"
)

DIV_RE = re.compile(r"<div\b|</div>")


def end_of_decl(html: str, open_start: int, open_end: int):
    """Index of the `</div>` that closes the `<div class="decl" …>` opening at `open_start`.

    Depth-counted rather than matched by a regex, because a declaration's block nests arbitrarily
    (signature, docstring, structure fields, instance lists) and a non-greedy match would stop at
    the first inner close.
    """
    depth = 1
    for m in DIV_RE.finditer(html, open_end):
        if m.group(0) == "</div>":
            depth -= 1
            if depth == 0:
                return m.start()
        else:
            depth += 1
    return None


def inject(html: str, name: str, block: str):
    """Insert `block` at the end of `name`'s declaration div. Returns (html, injected?)."""
    m = re.search(r'<div class="decl" id="%s"[^>]*>' % re.escape(name), html)
    if not m:
        return html, False
    end = end_of_decl(html, m.start(), m.end())
    if end is None:
        return html, False
    if MARKER in html[m.start():end]:
        return html, False  # already injected
    return html[:end] + '<div %s>%s</div>' % (MARKER, block) + html[end:], True


def main(argv):
    if len(argv) != 3:
        print(__doc__.strip().splitlines()[2].strip(), file=sys.stderr)
        return 2
    site, blocks_path = Path(argv[1]), Path(argv[2])
    blocks = json.loads(blocks_path.read_text())

    data_path = site / "declarations" / "declaration-data.bmp"
    if not data_path.exists():
        print("error: %s not found — was the doc-gen4 site generated?" % data_path, file=sys.stderr)
        return 1
    declarations = json.loads(data_path.read_text())["declarations"]

    # Group by page, so each file is read and written once however many declarations it holds.
    by_page = {}
    unresolved = []
    for name in blocks:
        entry = declarations.get(name)
        if not entry:
            unresolved.append(name)
            continue
        # "./PropertyKindCalculus/Kind.html#PropertyKindCalculus.KindOfProperty"
        page = entry["docLink"].split("#", 1)[0].lstrip("./")
        by_page.setdefault(page, []).append(name)

    injected = skipped = 0
    for page, names in sorted(by_page.items()):
        path = site / page
        if not path.exists():
            unresolved.extend(names)
            continue
        html = path.read_text()
        changed = False
        for name in names:
            html, did = inject(html, name, blocks[name])
            if did:
                injected += 1
                changed = True
            else:
                skipped += 1
        if changed:
            if 'id="pkc-index-style"' not in html:
                html = html.replace("</head>", STYLE + "</head>", 1)
            path.write_text(html)

    print("index blocks: %d injected, %d already present or not found on page, %d unresolved"
          % (injected, skipped, len(unresolved)))
    if unresolved:
        # Not an error: the API site is a *subset* of the environment (PKC publishes the
        # Mathlib-free tier only), so a kind outside that subset has no page to inject into.
        print("  not on this site: " + ", ".join(sorted(unresolved)[:8])
              + (" …" if len(unresolved) > 8 else ""))
    return 0


if __name__ == "__main__":
    sys.exit(main(sys.argv))
