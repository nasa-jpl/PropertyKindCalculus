#!/usr/bin/env python3
"""Make Verso `html-multi` output navigable over file://.

Verso writes every internal link as a *directory* URL with a trailing slash
(`Chapter/#anchor`), resolved through a per-page `<base href>`. A web server maps
`Chapter/` to `Chapter/index.html`; a browser opening a `file://` directory URL
does not — it shows the folder instead of the page. That is the only thing that
breaks under file:// (the `<base>` mechanism itself works at every depth).

This pass rewrites the link *targets* to spell out `index.html`:

    Chapter/#anchor            -> Chapter/index.html#anchor
    Chapter/Section/#anchor     -> Chapter/Section/index.html#anchor
    find/?domain=...            -> find/index.html?domain=...
    ./   (root home link)       -> index.html      (base already points to root)
    ./../  (deep home link)     -> index.html

It is safe for the served site too: over HTTP `Chapter/index.html` resolves the
same as `Chapter/`. It deliberately leaves alone: the `<base href>` tag itself,
external/scheme links, pure `#fragment` links, and asset links (.css/.js, which
never end in `/`). Re-running is idempotent.
"""
import re
import sys
from pathlib import Path

# href="..." but NOT the page's <base href="..."> (which must stay a directory).
HREF = re.compile(r'(?<!<base )href="([^"]*)"')
# A path made only of "./" / "../" segments — a home/up link to the site root.
PURE_DOTS = re.compile(r'^(?:\.\.?/)+$')


def fix_href(value: str) -> str:
    if not value or value.startswith("#"):
        return value                      # empty or same-page fragment
    if "://" in value or value.split(":", 1)[0] in ("mailto", "data", "javascript"):
        return value                      # external / non-navigational scheme
    # Split off the #fragment / ?query suffix; only the path part is rewritten.
    m = re.match(r'^([^#?]*)([#?].*)?$', value)
    path, suffix = m.group(1), m.group(2) or ""
    if not path:
        return value                      # bare ?query — leave it
    if PURE_DOTS.match(path):
        # Home/up link: base already resolves to the site root, so point at its index.
        return "index.html" + suffix
    if path.endswith("/"):
        return path + "index.html" + suffix
    return value                          # a real file (asset, .html) — leave it


def fix_file(p: Path) -> bool:
    text = p.read_text(encoding="utf-8")
    new = HREF.sub(lambda mo: f'href="{fix_href(mo.group(1))}"', text)
    if new != text:
        p.write_text(new, encoding="utf-8")
        return True
    return False


def main(argv: list[str]) -> int:
    if len(argv) != 2:
        print("usage: file-links.py <html-multi-dir>", file=sys.stderr)
        return 2
    root = Path(argv[1])
    if not root.is_dir():
        print(f"not a directory: {root}", file=sys.stderr)
        return 1
    changed = sum(fix_file(p) for p in sorted(root.rglob("*.html")))
    print(f"file-links: rewrote directory links in {changed} html file(s) under {root}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main(sys.argv))
