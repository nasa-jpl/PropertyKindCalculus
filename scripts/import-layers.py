#!/usr/bin/env python3
"""Intra-package import graph of this package: module-system adoption, topological depth,
and transitive dependents, over every `lean_lib` at once.

The bug this exists to catch: the module system must be adopted strictly bottom-up (a
`module` file cannot import a non-`module` one), and the import graph ignores the ~20
`lean_lib` boundaries and ~15 `srcDir` roots of this package. A per-lib view under-reports
the frontier; a `grep '^module'` over-reports adoption (prose lines inside docstrings that
begin with "module" matched 23 files whose true count was 0). This script reads only the
import header of each file with comments stripped, attributes every file to the lib whose
`globs`/`roots` cover it, and reports files no lib covers, so a path that drifted out of
every lib's glob is named instead of silently dropped.

Output: a summary on stdout and, with `--tsv PATH`, one row per module:
  depth  module  lib  path  module_header  intra_imports  dependents
where depth 0 = imports nothing in this package, and dependents = modules that rebuild
after a body edit of this one.
"""
import argparse, collections, os, re, sys
sys.dont_write_bytecode = True

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.dirname(HERE)
SKIP_DIRS = {'.lake', 'blueprint', 'Scratch', 'scripts', 'docs', 'References', '__pycache__'}

def strip_comments(s):
    """Drop block/line comments; string literals are skipped so a `--` or `/-` inside a
    string (a docstring's example, a message) cannot open a phantom comment."""
    out, i, n, d = [], 0, len(s), 0
    while i < n:
        if d == 0:
            if s[i] == '"':
                j = i + 1
                while j < n and s[j] != '"':
                    j += 2 if s[j] == '\\' else 1
                out.append(' '); i = j + 1; continue
            if s.startswith('/-', i): d = 1; i += 2; continue
            if s.startswith('--', i):
                j = s.find('\n', i); i = n if j < 0 else j; continue
            out.append(s[i]); i += 1
        else:
            if s.startswith('-/', i): d -= 1; i += 2; continue
            if s.startswith('/-', i): d += 1; i += 2; continue
            i += 1
    return ''.join(out)

def header(path):
    """(imports, has_module_header) from the comment-stripped header of a .lean file."""
    toks = strip_comments(open(path, encoding='utf-8', errors='replace').read()).split()
    imps, is_mod, i = [], False, 0
    if toks and toks[0] == 'module': is_mod, i = True, 1
    while i < len(toks):
        t = toks[i]
        if t in ('public', 'meta', 'private'): i += 1; continue
        if t == 'import':
            i += 1
            if i < len(toks) and toks[i] == 'all': i += 1
            if i < len(toks): imps.append(toks[i].strip('«»')); i += 1
            continue
        break
    return imps, is_mod

def libs_from_lakefile():
    """[(lib, srcDir, [(kind, prefix)], target)] with kind in {'sub','one'} and target in {'lib','exe'}."""
    text = open(os.path.join(ROOT, 'lakefile.lean'), encoding='utf-8').read()
    blocks = re.split(r'^(?=lean_(?:lib|exe)\s)', text, flags=re.M)
    libs = []
    for b in blocks:
        m = re.match(r'lean_(lib|exe)\s+«?([\w.]+)»?', b)
        if not m: continue
        kind, name = m.groups()
        body = b.split('\n\n')[0] if '\n\n' in b else b
        src = re.search(r'srcDir\s*:=\s*"([^"]*)"', body)
        src = src.group(1) if src else '.'
        pats = []
        for g in re.finditer(r'\.andSubmodules\s+`([\w.]+)', body): pats.append(('sub', g.group(1)))
        for g in re.finditer(r'\.one\s+`([\w.]+)', body): pats.append(('one', g.group(1)))
        if not pats:
            r = re.search(r'roots\s*:=\s*#\[\s*`([\w.]+)', body)
            pats.append(('sub', r.group(1) if r else name))
        if kind == 'exe':
            r = re.search(r'root\s*:=\s*`([\w.]+)', body)
            pats = [('one', r.group(1) if r else name)]
        libs.append((name, src, pats, kind))
    return libs

def covered(name, pats):
    return any((k == 'one' and name == p) or (k == 'sub' and (name == p or name.startswith(p + '.'))) for k, p in pats)

def main():
    ap = argparse.ArgumentParser(description=__doc__.split('\n')[0])
    ap.add_argument('--tsv', help='write the per-module table here')
    ap.add_argument('--max-depth', type=int, help='also list the modules at or below this depth')
    args = ap.parse_args()
    libs = libs_from_lakefile()
    mods, orphans = {}, []
    for src in sorted({s for _, s, _, _ in libs}):
        base = os.path.normpath(os.path.join(ROOT, src))
        for dp, dn, fn in os.walk(base):
            dn[:] = [d for d in dn if d not in SKIP_DIRS]
            for f in fn:
                if not f.endswith('.lean') or f == 'lakefile.lean': continue
                p = os.path.join(dp, f)
                name = os.path.relpath(p, base)[:-5].replace('/', '.')
                owners = [l for l, s, pats, _ in libs if s == src and covered(name, pats)]
                if not owners:
                    if src == '.': continue        # the root srcDir holds every other srcDir too
                    orphans.append(os.path.relpath(p, ROOT)); continue
                if name in mods and mods[name][1] != os.path.relpath(p, ROOT):
                    print(f'DUPLICATE module name {name}: {mods[name][1]} and {os.path.relpath(p, ROOT)}', file=sys.stderr)
                mods[name] = (owners[0], os.path.relpath(p, ROOT))
    edges, ismod = {}, {}
    for name, (lib, rel) in mods.items():
        imps, m = header(os.path.join(ROOT, rel))
        edges[name] = [x for x in imps if x in mods]; ismod[name] = m
    sys.setrecursionlimit(20000)
    depth = {}
    def dep(n):
        if n in depth:
            if depth[n] < 0: raise SystemExit(f'import cycle through {n}')
            return depth[n]
        depth[n] = -1
        depth[n] = max([dep(m) + 1 for m in edges[n]], default=0); return depth[n]
    for n in mods: dep(n)
    rev = collections.defaultdict(set)
    for n, ms in edges.items():
        for m in ms: rev[m].add(n)
    tdep = {}
    def td(n):
        if n in tdep: return tdep[n]
        acc = set()
        for k in rev[n]: acc.add(k); acc |= td(k)
        tdep[n] = acc; return acc
    for n in mods: td(n)
    # blocked frontier: non-module files all of whose intra-package imports are modules
    frontier = [n for n in mods if not ismod[n] and all(ismod[m] for m in edges[n])]
    hist = collections.Counter(depth.values())
    print(f'modules {len(mods)}  with module header {sum(ismod.values())}  max depth {max(depth.values())}  '
          f'orphans (no lib covers) {len(orphans)}  migratable-now frontier {len(frontier)}')
    print('layer histogram:', ' '.join(f'{k}:{hist[k]}' for k in sorted(hist)))
    per = collections.defaultdict(lambda: [0, 0])
    for n, (lib, _) in mods.items(): per[lib][0] += 1; per[lib][1] += ismod[n]
    print('per lib (files/module):', ' '.join(f'{l}={v[1]}/{v[0]}' for l, v in sorted(per.items())))
    for o in orphans: print('ORPHAN', o)
    if args.tsv:
        with open(args.tsv, 'w') as f:
            f.write('depth\tmodule\tlib\tpath\tmodule_header\tintra_imports\tdependents\n')
            for n in sorted(mods, key=lambda x: (depth[x], x)):
                f.write(f'{depth[n]}\t{n}\t{mods[n][0]}\t{mods[n][1]}\t{int(ismod[n])}\t{len(edges[n])}\t{len(tdep[n])}\n')
    if args.max_depth is not None:
        for n in sorted(mods, key=lambda x: (depth[x], x)):
            if depth[n] <= args.max_depth: print(f'{depth[n]}\t{n}\t{mods[n][1]}')

if __name__ == '__main__':
    main()
