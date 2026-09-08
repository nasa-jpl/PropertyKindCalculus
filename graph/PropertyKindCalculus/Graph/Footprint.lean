import PropertyKindCalculus.Graph.KindGraph
import PropertyKindCalculus.KindIncidence
import PropertyKindCalculus.ModuleCard

/-!
# The SCC footprint of a declared boundary — where a module's guarantee comes from

`#kind_scc` reads the kind vocabulary: which kinds are mutually manufacturable through
licensed derivations alone. A *module* — a declared `Provenance.Contract` — draws its
port and interior kinds from that vocabulary, and how they fall across the components
decides how much checking the kind algebra gives the module for free: the type system
refuses a mis-wiring exactly when the confused kinds have no licensed path between them,
i.e. lie in different components. A boundary whose kinds span many components gets
strong checking for free; one operating inside a single component gets little, and its
guarantee rests on compensations — role kinds, curated quotient targets, `#guard` pins,
goldens — the footprint must surface rather than assume.

`#kind_footprint` is that report, one boundary at a time, and a spanning footprint is
**necessary, not sufficient** — three confusions are invisible to any component
separation, so each has its own section:

  * **same-kind ports** — two ports at one kind swap without any kind graph noticing,
    however separated the components; the groups are listed, because role wrappers and
    named record fields are their compensation and a reader should see what those must
    carry;
  * **crossings and attests** — an authored `@[kindCrossing]` connects kinds *by
    review*, and an attested mint can land anything anywhere, so the report lists the
    crossing declarations the members route through and the attested introductions of
    the assembled graph: the sites where discrimination is review-strength rather than
    type-strength;
  * **the erased region** — beyond a declared exit nothing kinded protects the wires at
    all; the exits are listed as the boundary of that region.

The verdict line answers one question per module — *where does this module's guarantee
actually come from?* — and is `#guard_msgs`-pinnable, so a footprint that silently
collapses into a single component fails a pin instead of passing as prose.
-/

namespace PropertyKindCalculus.KindGraph

open Lean Meta Elab
open PropertyKindCalculus.KindIncidence (contractValueOf assembleContract)

/-- The display form of a kind vertex — its last name component, as the cluster
renderings spell it. -/
private def kindShortName (n : Name) : String :=
  match n with
  | .str _ s => s
  | _ => toString n

/-- Resolve a kind reference against the graph's vertices: a `decl` by its environment
name, exactly. `none` for everything else — a kind param, a signature or tuple, an
out-of-scope declaration — because those denote no single vertex of this graph. -/
def resolveKind (kg : KindGraph) (k : PropertyKindCalculus.Provenance.KindRef) :
    Option Nat :=
  match k with
  | .decl n => kg.kinds.findIdx? (· == n)
  | _ => none

open Elab Command in
/-- `#kind_footprint c ns…` — the SCC footprint of the declared boundary `c` against
the kind graph of the given namespaces (the same graph `#kind_scc ns…` reads): the
component partition of the boundary's port and interior kinds, the same-kind port
groups, the review-strength sites (crossing members, attested introductions, declared
exits), and the verdict naming where the module's guarantee comes from — as a single
`info` message suitable for `#guard_msgs` pinning. -/
elab "#kind_footprint " c:ident nss:ident* : command => liftTermElabM do
  if nss.isEmpty then
    throwError "#kind_footprint expects the namespaces whose kind graph to read, \
      as #kind_scc does"
  let cname ← realizeGlobalConstNoOverload c
  let ctr ← contractValueOf cname
  let a ← assembleContract ctr
  let kg ← kindGraphOf (nss.map (·.getId))
  let clusters := kg.clusters
  let clusterOf : Nat → Nat := fun v =>
    (clusters.findIdx? (·.contains v)).getD 0
  -- the footprint's kinds: every declared port kind, and the interior kinds the
  -- assembled graph introduces beyond them — deduplicated by *graph vertex*, because a
  -- port spells a kind short while an interior introduction from another namespace
  -- spells it qualified, and one kind counted twice would inflate every number below
  let portKinds := (ctr.ports.map (·.kind)).eraseDups
  let interiorKinds := ((a.graph.intros.map (·.kind)).eraseDups.filter
    (!portKinds.contains ·))
  let mut verts : Array Nat := #[]
  let mut unresolved : Array String := #[]
  for k in portKinds ++ interiorKinds do
    match resolveKind kg k with
    | some v => unless verts.contains v do verts := verts.push v
    | none => unless unresolved.contains k.render do unresolved := unresolved.push k.render
  -- the touched components, each with the footprint's vertices it holds
  let mut touched : Array (Nat × Array Nat) := #[]
  for v in verts do
    let ci := clusterOf v
    match touched.findIdx? (·.1 == ci) with
    | some i => touched := touched.set! i (ci, touched[i]!.2.push v)
    | none => touched := touched.push (ci, #[v])
  let rep : Nat → String := fun ci =>
    ((clusters[ci]!.map fun v => kindShortName kg.kinds[v]!).qsort (· < ·)).getD 0 "?"
  let sortedTouched := touched.qsort fun x y => rep x.1 < rep y.1
  let nontrivial := sortedTouched.filter fun (ci, _) => clusters[ci]!.size ≥ 2
  let singletons := sortedTouched.size - nontrivial.size
  let mut lines : Array String := #[]
  lines := lines.push <|
    s!"kind footprint of '{ctr.name}': {verts.size} kind(s) in the graph; \
      {nontrivial.size} derivation cluster(s) of size ≥ 2 touched, \
      {singletons} singleton kind(s)"
      ++ (if unresolved.isEmpty then "" else s!", {unresolved.size} unresolved")
  for (ci, vs) in nontrivial do
    let names := (vs.map fun v => kindShortName kg.kinds[v]!).qsort (· < ·)
    lines := lines.push
      s!"  cluster {rep ci} ({clusters[ci]!.size} kinds): \
        {String.intercalate ", " names.toList}"
  if nontrivial.size == 1 && singletons == 0 && !verts.isEmpty then
    lines := lines.push
      s!"  ⚠ single-cluster footprint: every resolved kind lies in cluster {rep nontrivial[0]!.1}"
  unless unresolved.isEmpty do
    lines := lines.push
      s!"  unresolved (a kind variable, an ambiguous short name, or out of scope): \
        {String.intercalate ", " (unresolved.qsort (· < ·)).toList}"
  -- the same-kind port groups: swappable regardless of component separation. Grouped by
  -- *graph vertex* where the kind resolves — a kind spelled short at one port and
  -- qualified at another is one kind, and splitting the group would hide the swap pair —
  -- and by the authored string where it does not (kind variables group by name)
  let canonical := fun (k : PropertyKindCalculus.Provenance.KindRef) =>
    match resolveKind kg k with
    | some v => kindShortName kg.kinds[v]!
    | none => k.render
  let mut groups : Array (String × Array String) := #[]
  for p in ctr.ports do
    let key := canonical p.kind
    match groups.findIdx? (·.1 == key) with
    | some i =>
      groups := groups.set! i (key, groups[i]!.2.push s!"{p.node.render} ({p.dir.label})")
    | none => groups := groups.push (key, #[s!"{p.node.render} ({p.dir.label})"])
  let sharedGroups := (groups.filter (·.2.size ≥ 2)).qsort fun x y => x.1 < y.1
  lines := lines.push s!"same-kind ports — {sharedGroups.size} group(s):"
  for (k, ns) in sharedGroups do
    lines := lines.push s!"  {k}: {String.intercalate ", " ns.toList}"
  -- the review-strength sites: crossings the members route through, attested
  -- introductions, and the declared exits bounding the erased region
  let env ← getEnv
  let crossingDecls : NameSet :=
    (BoundaryAudit.boundaryTags env).foldl (init := {}) fun s t =>
      if t.tier == .kindCrossing then s.insert t.decl else s
  let mut crossings : Array String := #[]
  for m in ctr.members do
    let mn := m
    if crossingDecls.contains mn && !crossings.contains (toString mn) then
      crossings := crossings.push (toString mn)
    if let some info := env.find? mn then
      if let some v := info.value? then
        let hits := v.foldConsts ({} : NameSet) fun cn s =>
          if crossingDecls.contains cn then s.insert cn else s
        for cn in hits.toList do
          unless crossings.contains (toString cn) do
            crossings := crossings.push (toString cn)
  let sortedCrossings := crossings.qsort (· < ·)
  let attested := a.graph.intros.filter fun i => i.tier matches .attested _
  lines := lines.push
    s!"review-strength sites — {sortedCrossings.size} crossing(s), {attested.length} \
      attested intro(s), {ctr.exits.length} declared exit(s):"
  for cn in sortedCrossings do
    lines := lines.push s!"  crossing {cn}"
  for i in attested do
    lines := lines.push s!"  {i.tier.label} {i.node.render} : {i.kind.render}"
  for e in ctr.exits do
    lines := lines.push s!"  exit {e.render}"
  -- the verdict: where does this module's guarantee actually come from?
  let components := nontrivial.size + singletons
  let base :=
    if verts.isEmpty then
      "no kinds resolved against this graph — read the footprint over the namespaces \
       that declare the boundary's kinds"
    else if components ≥ 2 then
      s!"type-strength: the kinds span {components} components"
    else if nontrivial.size == 1 then
      s!"compensation required: the working kinds co-inhabit one derivation cluster — \
        the kind algebra cannot refuse a mis-wiring here; discrimination rests on the \
        roles, pins, and goldens"
    else
      "single-kind boundary: the kind algebra has nothing to separate"
  let caveats := String.join <|
    (if sharedGroups.isEmpty then [] else
      [s!"; {sharedGroups.size} same-kind group(s) swap invisibly to any cluster separation"])
      ++ (if sortedCrossings.isEmpty && attested.isEmpty then [] else
          [s!"; review-strength at {sortedCrossings.size + attested.length} site(s)"])
      ++ (if ctr.exits.isEmpty then [] else
          [s!"; erased beyond {ctr.exits.length} exit(s)"])
  lines := lines.push s!"verdict: {base}{caveats}"
  logInfo m!"{String.intercalate "\n" lines.toList}"

/-- The cluster rows of one boundary's **module interface document**
(`ModuleCard.ClusterRow`): for each inter-derivability cluster of two or more kinds,
the boundary's own port kinds that resolve into it (`resolveKind` — an ambiguous or
out-of-scope rendering resolves to nothing, exactly as in the footprint), with the
cluster named by its alphabetical representative, compared case-insensitively — the
same representative that names the cluster's diagram. A boundary touching no cluster
contributes no rows. -/
def clusterRows (kg : KindGraph)
    (c : Provenance.Contract Provenance.NodeId Provenance.KindRef) :
    List ModuleCard.ClusterRow := Id.run do
  let portKinds := (c.ports.map (·.kind)).eraseDups
  let mut rows : List ModuleCard.ClusterRow := []
  for cl in kg.clusters.filter (·.size ≥ 2) do
    let hit := portKinds.filter fun k =>
      match resolveKind kg k with
      | some i => cl.contains i
      | none => false
    if hit.isEmpty then continue
    let rep := ((cl.map fun i => kindShortName kg.kinds[i]!).qsort
      fun a b => a.toLower < b.toLower)[0]!
    rows := rows ++ [{ representative := rep, kinds := hit.map (·.render) }]
  return rows

end PropertyKindCalculus.KindGraph
