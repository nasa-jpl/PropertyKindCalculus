/-
Copyright (c) 2026 California Institute of Technology. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nicolas Rouquette
-/

module

public import PropertyKindCalculus.Index.Basic
public import PropertyKindCalculus.KindEdges
public import PropertyKindCalculus.Examination
public import PropertyKindCalculus.DedicatedKind

/-!
# Indexing the ontology — kinds, systems, components, dedicated kinds, examinations

The Dybkær spine is a handful of small structures (`KindOfProperty`, `System`, `Component`,
`DedicatedKind`, the three examination layers), and a model builds its vocabulary by *inhabiting*
them: `def soilWater : System := ⟨"soil water"⟩`. Those inhabitants are ordinary definitions, so
nothing marks them as a family — the criterion is simply "a constant whose type is that structure",
and that is all the harvests below test. No annotation is required, and adding one would be a second
place to forget.

## Why the kind table carries its edges

The kind column that matters is not the identity string; it is **what may be done with the kind
algebraically**. A kind crossing and a kind-algebra edge are both *authored* — the calculus refuses
to infer either — so the set of authored edges mentioning a kind is a closed, checkable statement of
its algebra, in the way `#print axioms` is a closed statement of what a proof rests on. Rendering
that set next to the kind is the point of the index; `#kind_edges` already computes it, and
`KindEdges.edgesByKind` gets it for every kind in one environment walk.
-/

@[expose] public section Blanket

namespace PropertyKindCalculus.Index

open Lean Meta

/-! ## Reading a structure field back out of a definition

An index needs the *values*: `soilWater`'s identity is `"soil water"`, not the expression
`⟨"soil water"⟩`. Since these definitions are closed structure literals, `whnf` on a projection
reduces to the literal — delta-unfold the constant, iota-reduce the projection. Anything that does
not reduce that far (an opaque or parameterized definition) falls back to pretty-printing, so an
unexpected shape degrades to something honest rather than throwing. -/

/-- The value reached from `declName` by applying `chain`'s projections in order, as a string: a
`String` literal read back verbatim, a constructor read back by its final name component, anything
else pretty-printed.

A *chain* rather than a single projection because the layers nest: a `DimensionedKind`'s identity is
`dk.kind.id`, two projections down, and the dimensioned layer is indexed by the same code as the core
one. An empty chain is the declaration's own value. -/
def fieldStringChain (declName : Name) (chain : Array Name) : MetaM String := do
  -- Application *and* reduction share one budget. `mkAppM`, not `mkApp`, because a projection of a
  -- parameterized structure (`DimensionedKind.kind`, whose structure carries a base-dimension
  -- parameter) takes implicit arguments before its subject, so a hand-built application would be
  -- ill-typed rather than merely wrong — but `mkAppM` unifies to find them, and unification is
  -- exactly the work that must not be allowed to run away across a table's worth of cells.
  let r ← bounded do
    let mut e ← mkConstWithLevelParams declName
    for p in chain do
      e ← mkAppM p #[e]
    let v ← Meta.whnf e
    match v with
    | .lit (.strVal s) => return s
    | _ =>
      match v.getAppFn with
      | .const c _ =>
        -- `Option.some "…"` prints as its payload; a bare enum constructor as its own name.
        if c == ``Option.some then
          match ← Meta.whnf (v.getAppArgs[1]!) with
          | .lit (.strVal s) => return s
          | other => return toString (← ppExpr other)
        else if c == ``Option.none then return ""
        else return lastComponent c
      | _ => return toString (← ppExpr v)
  return r.getD (lastComponent declName)

/-- The value of `declName`'s single `field` projection — `fieldStringChain` at length one. -/
def fieldString (declName field : Name) : MetaM String :=
  fieldStringChain declName #[field]

/-- The head constant of the value reached from `declName` by `chain` — the declaration the cell
links to when its rendered value is a constructor (a scale, an enum field). `none` when the value
reduces to anything else (a literal, an `Option` payload, a lambda) or exhausts its reduction
budget: the cell then degrades to unlinked text rather than failing the table. -/
def fieldConstChain? (declName : Name) (chain : Array Name) : MetaM (Option Name) := do
  let r ← bounded do
    let mut e ← mkConstWithLevelParams declName
    for p in chain do
      e ← mkAppM p #[e]
    let v ← Meta.whnf e
    match v.getAppFn with
    | .const c _ =>
      if c == ``Option.some || c == ``Option.none then return (none : Option Name)
      else return some c
    | _ => return (none : Option Name)
  return r.getD none

/-- The `SortOfSystem`/`Component`/`KindOfProperty` a dedicated kind projects to, as the
*declaration* that defines it where one exists — so the cell can link — else as the rendered value.

A `DedicatedKind` is built by `k.dedicatedTo sort comp`, so its fields *are* the very constants the
model declared; recovering them is what lets the dedicated-kind table cross-link to the sort and
component tables instead of repeating their identity strings.

Reducing the *projection* is the wrong move and gives the wrong answer: `whnf (DedicatedKind.sort
vwc)` runs all the way to `SortOfSystem.mk "soil"`, so the constant the author wrote is gone and the
cell can only say `mk`. What is wanted is the argument *as written*. So reduce the declaration's own
value just far enough to expose its constructor application — `waterKind.dedicatedTo soil water`
becomes `DedicatedKind.mk soil water waterKind`, with the arguments still unreduced, because `whnf`
reduces only the head — and read the field out of it positionally. -/
def fieldDecl? (declName proj : Name) : MetaM (Option Name) := do
  let env ← getEnv
  let some pinfo := env.getProjectionFnInfo? proj | return none
  let some info := env.find? declName | return none
  let some val := info.value? | return none
  let some v ← boundedWhnf val | return none
  let .const c _ := v.getAppFn | return none
  unless c == pinfo.ctorName do return none
  let some a := v.getAppArgs[pinfo.numParams + pinfo.i]? | return none
  match a.getAppFn with
  | .const k _ => return if k.isInternal then none else some k
  | _ => return none

/-! ## The tables -/

/-- Which kind layer to index. The calculus has two — the core `KindOfProperty` and the
PhysLib-backed `DimensionedKind` that wraps it — and they carry different fields, so the layer is a
parameter rather than a hard-coded type.

`PropertyKindCalculus.Index` deliberately does not import the dimensioned layer (that would pull
PhysLib and Mathlib into a library whose whole purpose is to be importable everywhere), so the
dimensioned layer's spec is constructed by the document that already imports it. -/
structure KindLayer where
  /-- The table identifier a directive names. -/
  id : String
  /-- The table's title. -/
  title : String
  /-- The type whose inhabitants are the kinds of this layer. -/
  ty : Name
  /-- Projection chain from a kind to its identity string. -/
  identity : Array Name
  /-- An extra descriptive column: its header and the projection chain that fills it. -/
  extra : Option (String × Array Name) := none

/-- The core layer: `KindOfProperty`, described by its identity and its scale type. -/
def KindLayer.core : KindLayer where
  id := "kinds"
  title := "Kinds of property"
  ty := ``PropertyKindCalculus.KindOfProperty
  identity := #[``PropertyKindCalculus.KindOfProperty.id]
  extra := some ("Scale", #[``PropertyKindCalculus.KindOfProperty.scale])

/-- The kinds of `layer` in scope, with their authored kind-algebra edges and the theorems that
mention them.

The **Algebra** column is the one that justifies the table: it lists every authored edge mentioning
the kind, which is the complete statement of what may be done with it — multiplied by what, divided
into what, raised to what power. The edges arrive deduplicated by equation and grouped as
produced / consumed (`KindEdges.groupEdges`), one equation per rendered line. A kind with an empty
Algebra cell is a kind that currently supports no arithmetic at all, and that is a fact worth being
able to see. -/
def kindsTable (layer : KindLayer) (scope : Scope) : MetaM IndexTable := do
  let env ← getEnv
  let headers :=
    #["Kind", "Identity"] ++ (layer.extra.map (fun (h, _) => #[h])).getD #[]
      ++ #["Algebra", "Theorems"]
  let kinds := constantsOfType env layer.ty scope
  if kinds.isEmpty then return IndexTable.empty layer.id layer.title headers
  let edges ← KindEdges.edgesByKind kinds
  let thms := theoremsMentioning env kinds
  let mut rows : Array (Array IndexCell) := #[]
  for k in kinds do
    -- The identity links back to the kind's own declaration, and the extra column (a scale) to
    -- the constructor its value reduces to — so every cell of the row can jump to a definition.
    let extraCell : Array IndexCell ← match layer.extra with
      | some (_, chain) => do
        let txt ← fieldStringChain k chain
        match ← fieldConstChain? k chain with
        | some c => pure #[IndexCell.declText c txt]
        | none   => pure #[.code txt]
      | none            => pure #[]
    rows := rows.push (#[
      IndexCell.decl k (lastComponent k),
      .declText k (← fieldStringChain k layer.identity)] ++ extraCell ++ #[
      .codeGroups (KindEdges.groupEdges (lastComponent k) (edges.getD k #[])),
      .links ((thms.getD k #[]).map fun t => (t, lastComponent t))])
  return { id := layer.id, title := layer.title, headers, rows }

/-- The one-identity ontology values — `SortOfSystem`, `System` and `Component` — with the
dedicated kinds built on them. `ty` is the structure; `dedicatedField?` the `DedicatedKind`
projection that points back here (`DedicatedKind.sort` or `.component`), which is what turns the
table into a two-way index — or `none` for a layer nothing dedicates to (the particular systems:
dedication is to the sort, so their table has no dedicated-kinds column at all rather than an
always-empty one). -/
def identityTable (id title heading : String) (ty : Name) (dedicatedField? : Option Name)
    (scope : Scope) : MetaM IndexTable := do
  let env ← getEnv
  let values := constantsOfType env ty scope
  let headers := match dedicatedField? with
    | some _ => #[heading, "Identity", "Dedicated kinds", "Theorems"]
    | none   => #[heading, "Identity", "Theorems"]
  if values.isEmpty then return IndexTable.empty id title headers
  -- Which dedicated kinds point back at each value.
  let mut back : Std.HashMap Name (Array Name) := {}
  if let some dedicatedField := dedicatedField? then
    let dedicated := constantsOfType env ``PropertyKindCalculus.DedicatedKind scope
    for d in dedicated do
      if let some target ← fieldDecl? d dedicatedField then
        back := back.insert target ((back.getD target #[]).push d)
  let thms := theoremsMentioning env values
  let mut rows : Array (Array IndexCell) := #[]
  for v in values do
    let backCell : Array IndexCell := match dedicatedField? with
      | some _ => #[.links ((back.getD v #[]).map fun d => (d, lastComponent d))]
      | none   => #[]
    rows := rows.push (#[
      IndexCell.decl v (lastComponent v),
      .text (← fieldString v (ty ++ `id))] ++ backCell ++ #[
      .links ((thms.getD v #[]).map fun t => (t, lastComponent t))])
  return { id, title, headers, rows }

/-- Dedicated kinds in scope, as the IUPAC/IFCC `System — Component ; kind-of-property` triple each
one *is*, with the theorems that distinguish them.

The distinctness theorems are the load-bearing column: two dedicated kinds that share a
kind-of-property are held apart only by their sort and component (`boundRelaxTime` vs
`freeRelaxTime`, both relaxation times), and `DedicatedKind.distinct_of_component` is what proves
it. A dedicated kind with no distinctness theorem is a kind nothing yet relies on separating. -/
def dedicatedKindsTable (scope : Scope) : MetaM IndexTable := do
  let env ← getEnv
  let ds := constantsOfType env ``PropertyKindCalculus.DedicatedKind scope
  let headers := #["Dedicated kind", "Sort of system", "Component", "Kind of property", "Theorems"]
  if ds.isEmpty then
    return IndexTable.empty "dedicated-kinds" "Dedicated kinds-of-property" headers
  let thms := theoremsMentioning env ds
  let mut rows : Array (Array IndexCell) := #[]
  for d in ds do
    -- Link to the constant the model declared where there is one; otherwise fall back to the
    -- field's *identity string* (`"soil water"`), never to the raw constructor.
    let cellFor (proj idProj : Name) : MetaM IndexCell := do
      match ← fieldDecl? d proj with
      | some c => return .decl c (lastComponent c)
      | none   => return .text (← fieldStringChain d #[proj, idProj])
    rows := rows.push #[
      .decl d (lastComponent d),
      ← cellFor ``PropertyKindCalculus.DedicatedKind.sort ``PropertyKindCalculus.SortOfSystem.id,
      ← cellFor ``PropertyKindCalculus.DedicatedKind.component ``PropertyKindCalculus.Component.id,
      ← cellFor ``PropertyKindCalculus.DedicatedKind.kind ``PropertyKindCalculus.KindOfProperty.id,
      .links ((thms.getD d #[]).map fun t => (t, lastComponent t))]
  return { id := "dedicated-kinds", title := "Dedicated kinds-of-property", headers, rows }

/-- The examination chain: every principle, method and procedure in scope, with what each is *based
on*.

`BasedOn` is structural rather than authored — a method is based on the principle it cites, a
procedure on the method it cites — so the refinement relation is read straight off the values, and
this table is the `Refines` closure's generating edges. That is why the chain needs no annotation:
`ExaminationMethod.principle` and `ExaminationProcedure.method` *are* the edges. -/
def examinationsTable (scope : Scope) : MetaM IndexTable := do
  let env ← getEnv
  let headers := #["Examination", "Layer", "Based on", "Principle"]
  let principles := constantsOfType env ``PropertyKindCalculus.ExaminationPrinciple scope
  let methods := constantsOfType env ``PropertyKindCalculus.ExaminationMethod scope
  let procedures := constantsOfType env ``PropertyKindCalculus.ExaminationProcedure scope
  if principles.isEmpty && methods.isEmpty && procedures.isEmpty then
    return IndexTable.empty "examinations" "Examinations" headers
  let mut rows : Array (Array IndexCell) := #[]
  for p in principles do
    rows := rows.push #[.decl p (lastComponent p), .text "principle", .text "—",
      .text (← fieldString p ``PropertyKindCalculus.ExaminationPrinciple.id)]
  let basedOnCell (d proj idProj : Name) : MetaM IndexCell := do
    match ← fieldDecl? d proj with
    | some c => return .decl c (lastComponent c)
    | none   => return .text (← fieldStringChain d #[proj, idProj])
  for m in methods do
    rows := rows.push #[.decl m (lastComponent m), .text "method",
      ← basedOnCell m ``PropertyKindCalculus.ExaminationMethod.principle
        ``PropertyKindCalculus.ExaminationPrinciple.id,
      .text (← fieldString m ``PropertyKindCalculus.ExaminationMethod.id)]
  for q in procedures do
    rows := rows.push #[.decl q (lastComponent q), .text "procedure",
      ← basedOnCell q ``PropertyKindCalculus.ExaminationProcedure.method
        ``PropertyKindCalculus.ExaminationMethod.id,
      .text (← fieldString q ``PropertyKindCalculus.ExaminationProcedure.id)]
  return { id := "examinations", title := "Examinations", headers, rows }

end PropertyKindCalculus.Index

end Blanket
