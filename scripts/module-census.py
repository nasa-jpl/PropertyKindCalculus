#!/usr/bin/env python3
"""Module-system adoption census: what this package's oleans and headers actually say.

Two instruments, because they answer different questions and disagree with `grep`:

  --tree     Count `.lean` files whose FIRST TOKEN outside comments is `module`, per
             directory root given on the command line (default: this package). A plain
             `grep '^module'` matched 23 prose lines inside docstrings in a package whose
             true count was 0; this is the comment-aware count.
  --closure  Import every sink module of this package (the ones nothing else here
             imports) in one `lake env lean` run and read `ModuleData.isModule` from
             every olean in the resulting environment. This measures the closure that is
             actually loaded, dependencies included, and is the precondition for a
             bottom-up migration: a `module` file cannot import a non-`module` one, so
             any dependency module reported here blocks every package module above it.

The bug this exists to catch: a readiness claim made from a file-tree census of the
dependencies' source checkouts (which counts their tests and benchmarks too) instead of
from the modules this package imports.
"""
import argparse, os, subprocess, sys
sys.dont_write_bytecode = True

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.dirname(HERE)
sys.path.insert(0, HERE)
from importlib import import_module
layers = import_module('import-layers')

def tree(roots):
    skip = tuple(f'/{d}/' for d in layers.SKIP_DIRS)   # same exclusions as the layering
    for r in roots:
        tot = mod = 0
        for dp, dn, fn in os.walk(r):
            if any(s in dp + '/' for s in skip): continue
            for f in fn:
                if not f.endswith('.lean') or f == 'lakefile.lean': continue
                tot += 1
                if layers.header(os.path.join(dp, f))[1]: mod += 1
        print(f'{r}: {mod}/{tot} module files')

def closure(names=False):
    libs = layers.libs_from_lakefile()
    mods, exe_only = {}, set()
    for src in sorted({s for _, s, _, _ in libs}):
        base = os.path.normpath(os.path.join(ROOT, src))
        for dp, dn, fn in os.walk(base):
            dn[:] = [d for d in dn if d not in layers.SKIP_DIRS]
            for f in fn:
                if not f.endswith('.lean') or f == 'lakefile.lean': continue
                p = os.path.join(dp, f)
                name = os.path.relpath(p, base)[:-5].replace('/', '.')
                owners = [(l, t) for l, s, pats, t in libs if s == src and layers.covered(name, pats)]
                if owners:
                    mods[name] = p
                    if all(t == 'exe' for _, t in owners): exe_only.add(name)   # two `main`s cannot share one environment
    imported = set()
    for name, p in mods.items():
        imported.update(layers.header(p)[0])
    sinks = sorted(n for n in mods if n not in imported and n not in exe_only)
    probe = ['import ' + n for n in sinks] + ['''
open Lean in
#eval show CoreM Unit from do
  let env ← getEnv
  let names := env.header.moduleNames
  let datas := env.header.moduleData
  IO.println s!"CLOSURE {names.size}"
  for i in [0:names.size] do
    if !datas[i]!.isModule then IO.println s!"NONMOD {names[i]!}"
''']
    os.makedirs(os.path.join(ROOT, 'Scratch'), exist_ok=True)
    path = os.path.join(ROOT, 'Scratch', 'ModuleCensusProbe.lean')
    open(path, 'w').write('\n'.join(probe))
    try:
        r = subprocess.run(['lake', 'env', 'lean', path], cwd=ROOT, capture_output=True, text=True)
    finally:
        os.remove(path)
    if r.returncode != 0:
        sys.stderr.write(r.stdout + r.stderr); raise SystemExit(f'probe failed ({r.returncode})')
    non = [l.split()[1] for l in r.stdout.splitlines() if l.startswith('NONMOD')]
    total = next(int(l.split()[1]) for l in r.stdout.splitlines() if l.startswith('CLOSURE'))
    own = [n for n in non if n in mods]; dep = [n for n in non if n not in mods]
    print(f'sinks imported {len(sinks)}; closure {total} modules; without module flag {len(non)} '
          f'(this package {len(own)}, dependencies {len(dep)})')
    for n in dep: print('DEPENDENCY NON-MODULE', n)
    if names:
        for n in sorted(own): print('OWN NON-MODULE', n)
    return 1 if dep else 0

if __name__ == '__main__':
    ap = argparse.ArgumentParser(description=__doc__.split('\n')[0])
    ap.add_argument('--tree', nargs='*', metavar='DIR', help='header census of these roots (default: this package)')
    ap.add_argument('--closure', action='store_true', help='olean-flag census of the imported closure (runs lake env lean)')
    ap.add_argument('--names', action='store_true', help='with --closure: also list this package\'s unflagged modules by name')
    a = ap.parse_args()
    if a.tree is not None: tree(a.tree or [ROOT])
    if a.closure: raise SystemExit(closure(a.names))
    if a.tree is None and not a.closure: ap.print_help()
