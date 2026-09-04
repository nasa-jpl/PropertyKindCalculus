/-
Copyright (c) 2026 California Institute of Technology. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nicolas Rouquette
-/
import PropertyKindCalculus.Index.Markdown
import PropertyKindCalculus.Examples
import PropertyKindCalculus.DocGenMath

/-!
This module's page is *generated*. Everything below it is written by `#pkc_index_page` at
elaboration time, from the environment, into this module's own module docstring — which is what
doc-gen4 renders at the top of a module's page.

It is a library of its own (`lean_lib IndexPage`) rather than a module of
`PropertyKindCalculus.Index` because it imports the libraries it indexes, and the harvest must stay
importable by anything without dragging the worked examples along.

The scope is the API site's scope: the Mathlib-free tier, which is what
`scripts/build-api-docs.sh` generates. The dimensioned kinds and the uncertainty layers are absent
for that reason and not because the harvest cannot see them — the blueprint, which does import them,
renders their tables.
-/

#pkc_index_page
  "The library's index of itself, generated from the environment when this module was compiled.

Each table below is derived, not maintained: membership is decided by what a declaration *is* (a
constant of the ontology's type, a structure with a carrier-typed field, a definition returning a
carrier) or by the registries the boundary audit already keeps. No annotation exists solely to put
something in an index.

The **Algebra** column of the kind table is the one to read first. A kind's authored edges are the
complete statement of what may be done with it arithmetically, because the calculus infers none of
them — so an empty cell there means the kind supports no arithmetic at all."
  ["annotations", "carriers", "crossings", "kinds", "sorts", "systems", "components",
   "dedicated-kinds", "examinations", "records", "operations", "pkc-math", "pkc-math-symbol",
   "pkc-math-config", "pkc-math-transparent"]
  PropertyKindCalculus
