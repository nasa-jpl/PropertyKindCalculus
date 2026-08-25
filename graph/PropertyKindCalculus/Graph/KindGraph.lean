import PropertyKindCalculus.KindEdges
import PropertyKindCalculus.Index.Basic
import ForMathlib.Combinatorics.Digraph.Condensation

/-!
# The kind-level derivation graph — inter-derivability as strongly connected components

The authored kind-algebra edges are *rules*, and rules compose: every registered witness
(`ProductKind`, `QuotientKind`, …, the table classes) lets a value of its operand kinds
become a value of its result kind by licensed steps alone, with no attest and no review.
This module assembles those rules into a digraph on the authored kinds — one vertex per
`KindOfProperty` constant in scope, one edge per (operand, result) pair of a scanned
witness — and reads its strongly connected components:

  * **a nontrivial component is an inter-derivability cluster**: each member kind can be
    manufactured from any other by licensed derivations alone. That is the intended shape
    for representation variants of one metrological role — and a *defect* when two kinds
    with distinct roles land in one cluster, because the role distinction is then
    unenforceable: any value walks the cycle and re-enters at the other kind, and the mint
    ratchet never sees it, since every step is licensed;
  * **the condensation is the derivability hierarchy**: which roles are upstream of which,
    with `Digraph.isAcyclic_condensation` guaranteeing the hierarchy is well founded; an
    inter-cluster crossing with no licensed edge is an obligatory attest site, enumerable
    at the vocabulary level;
  * **`#kind_scc`** reports the clusters and the hierarchy summary; **`#kind_scc_clean`**
    is the gate: every cluster of two or more kinds must be declared in its `allowing`
    list, so a future rule addition that merges two roles *fails the build* instead of
    silently widening a cluster nobody re-reads. Like `#kind_boundary_clean`, the gate
    carries no message and pins nothing: it throws, so there is nothing to re-bless.

The graph is data (`KindGraph`), its digraph is `ForMathlib`-decidable, and the component
computation runs through the same `Digraph.Reachable` instances a probe would `decide` —
the report and any kernel statement about the same value cannot disagree.
-/

namespace PropertyKindCalculus

namespace KindGraph

open Lean

/-- One licensed-derivation edge between authored kinds: operand index to result index in
the vertex array, with the authoring declaration and the witness family it came from. -/
structure Edge where
  src : Nat
  dst : Nat
  author : Name
  via : Name
deriving BEq, Repr, Inhabited

end KindGraph

/-- The kind-level derivation graph: the authored kinds in scope, and one edge per
(operand, result) pair of every scanned kind-algebra witness. -/
structure KindGraph where
  kinds : Array Lean.Name
  edges : Array KindGraph.Edge
deriving Repr, Inhabited

namespace KindGraph

/-- The digraph on the kind vertices: adjacency is the existence of a licensed edge. -/
def digraph (kg : KindGraph) : Digraph (Fin kg.kinds.size) where
  Adj i j := (kg.edges.any fun e => e.src == i.1 && e.dst == j.1) = true

instance (kg : KindGraph) : DecidableRel kg.digraph.Adj :=
  fun _ _ => inferInstanceAs (Decidable (_ = true))

/-- The forward-reachable index set from `i`, as a Boolean vector: `kg.kinds.size`
edge sweeps saturate, one productive vertex per sweep at worst — the same saturation
argument as `Provenance.influencedFrom`, on arrays. -/
def reachVec (kg : KindGraph) (i : Nat) : Array Bool := Id.run do
  let n := kg.kinds.size
  let mut vis : Array Bool := Array.replicate n false
  if i < n then vis := vis.set! i true
  for _ in [0:n] do
    for e in kg.edges do
      if vis[e.src]! && !vis[e.dst]! then
        vis := vis.set! e.dst true
  return vis

/-- Mutual derivability of two vertex indices — the strongly connected component
relation of the kind digraph. -/
def interderivable (kg : KindGraph) (i j : Nat) : Bool :=
  (kg.reachVec i)[j]! && (kg.reachVec j)[i]!

/-- The strongly connected components, as index groups in first-mention order.
Singletons included; a cluster of two or more is the inter-derivability finding. Only
vertices touching an edge can share a component, so reach sets are computed for those
alone. -/
def clusters (kg : KindGraph) : Array (Array Nat) := Id.run do
  let n := kg.kinds.size
  let mut active : Array Bool := Array.replicate n false
  for e in kg.edges do
    if e.src < n then active := active.set! e.src true
    if e.dst < n then active := active.set! e.dst true
  let mut reach : Array (Array Bool) := Array.replicate n #[]
  for i in [0:n] do
    if active[i]! then reach := reach.set! i (kg.reachVec i)
  let mut seen : Array Bool := Array.replicate n false
  let mut out : Array (Array Nat) := #[]
  for i in [0:n] do
    if seen[i]! then continue
    if !active[i]! then
      seen := seen.set! i true
      out := out.push #[i]
      continue
    let mut members : Array Nat := #[]
    for j in [0:n] do
      if active[j]! && (reach[i]!)[j]! && (reach[j]!)[i]! then
        members := members.push j
    for j in members do
      seen := seen.set! j true
    out := out.push members
  return out

/-- Acyclicity of the kind digraph: no kind re-derives itself through licensed edges —
no nontrivial cluster and no self-edge. -/
def acyclicB (kg : KindGraph) : Bool :=
  kg.edges.all (fun e => e.src != e.dst) && kg.clusters.all (·.size == 1)

/-- The licensed edges crossing between distinct components — the rendered form of the
condensation's edge set, the derivability hierarchy. -/
def hierarchyEdges (kg : KindGraph) : Array Edge := Id.run do
  let mut memo : Std.HashMap Nat (Array Bool) := {}
  let mut out : Array Edge := #[]
  for e in kg.edges do
    let vec ← match memo.get? e.dst with
      | some v => pure v
      | none =>
        let v := kg.reachVec e.dst
        memo := memo.insert e.dst v
        pure v
    if !vec[e.src]! then
      out := out.push e
  return out

/-! ## The harvest -/

open Lean

/-- The operand and result argument positions of a witness family's application, per the
family's own equation shape (`PowerKind`'s first argument is the exponent, not a kind;
`DifferenceKind` relates a kind to itself and contributes no cross-kind edge). -/
def rolesOf (spec : KindEdges.EdgeSpec) : Option (List Nat × Nat) :=
  if spec.const == ``PropertyKindCalculus.ProductKind then some ([0, 1], 2)
  else if spec.const == ``PropertyKindCalculus.QuotientKind then some ([0, 1], 2)
  else if spec.const == ``PropertyKindCalculus.ReciprocalKind then some ([0], 1)
  else if spec.const == ``PropertyKindCalculus.TranscendentalKind then some ([0], 1)
  else if spec.const == ``PropertyKindCalculus.PowerKind then some ([1], 2)
  else if spec.const == ``PropertyKindCalculus.ReferenceKind then some ([0], 1)
  else if spec.const == ``PropertyKindCalculus.KindMul then some ([0, 1], 2)
  else if spec.const == ``PropertyKindCalculus.KindDiv then some ([0, 1], 2)
  else none

private def constArg? (args : Array Lean.Expr) (i : Nat) : Option Lean.Name :=
  match args[i]? with
  | some (.const c _) => some c
  | _ => none

open Meta in
/-- Assemble the kind graph of a scope: vertices are the authored `KindOfProperty`
constants the scope covers; edges come from both of `#kind_edges`' channels — the type
scan and the inline body scan — dissected into (operand, result) pairs instead of
rendered. Only edges with both endpoints in scope are kept: the graph answers for the
vocabulary it was asked about. -/
def kindGraphOf (scope : Index.Scope) : MetaM KindGraph := do
  let env ← getEnv
  let kinds := Index.constantsOfType env ``PropertyKindCalculus.KindOfProperty scope
  let mut idxOf : Std.HashMap Name Nat := {}
  let mut ctr := 0
  for k in kinds do
    idxOf := idxOf.insert k ctr
    ctr := ctr + 1
  let reachable := KindEdges.producerModules env
  let mut edges : Array Edge := #[]
  for (name, info) in env.constants.toList do
    if let some idx := env.getModuleIdxFor? name then
      unless reachable.contains idx.toNat do continue
    let typeEdges := KindEdges.collectEdges info.type #[]
    let bodyEdges ← do
      if ← KindEdges.bodyScannable reachable env name info then
        lambdaTelescope info.value! fun _ body =>
          pure (KindEdges.collectInlineEdges env body #[])
      else
        pure #[]
    for (spec, args) in typeEdges ++ bodyEdges do
      let some (ops, res) := rolesOf spec | continue
      let some resName := constArg? args res | continue
      let some ri := idxOf.get? resName | continue
      for oi in ops do
        let some opName := constArg? args oi | continue
        let some si := idxOf.get? opName | continue
        edges := edges.push
          { src := si, dst := ri, author := KindEdges.parentOf name, via := spec.const }
  return { kinds, edges := edges.toList.eraseDups.toArray }

/-! ## Rendering -/

private def shortName (n : Name) : String :=
  match n with
  | .str _ s => s
  | _ => toString n

/-- One cluster's members, sorted, with the licensed edges wiring them. -/
def renderCluster (kg : KindGraph) (cl : Array Nat) : String := Id.run do
  let names := (cl.map fun i => shortName kg.kinds[i]!).qsort (· < ·)
  let inside := kg.edges.filter fun e =>
    cl.any (fun i => i == e.src) && cl.any (fun i => i == e.dst)
  let edgeLines := (inside.map fun e =>
    s!"{shortName kg.kinds[e.src]!} → {shortName kg.kinds[e.dst]!} \
      [{shortName e.via}] ({e.author})").qsort (· < ·)
  let mut s := s!"  ⚠ \{{String.intercalate ", " names.toList}}"
  for l in edgeLines.toList.eraseDups do
    s := s ++ s!"\n      {l}"
  return s

/-! ## D2 rendering — diagram sources for the component findings -/

private def d2Header : String :=
  "# generated by #kind_scc_d2 — regenerate with the producing script, do not edit"

/-- The D2 source of one cluster's wiring: every member kind a node, every licensed
edge a labeled connection — the witness family as the label, with distinct authoring
declarations of the same (operand, result, family) triple collapsed into a `×n`
multiplicity. Pure on the graph value: the diagram and the `#kind_scc` pin render the
same edge set. -/
def d2Cluster (kg : KindGraph) (cl : Array Nat) : String := Id.run do
  let mut lines : Array String := #[d2Header, "direction: right"]
  for n in (cl.map fun i => shortName kg.kinds[i]!).qsort (· < ·) do
    lines := lines.push n
  let inside := kg.edges.filter fun e => cl.contains e.src && cl.contains e.dst
  let triples := (inside.map fun e =>
    (shortName kg.kinds[e.src]!, shortName kg.kinds[e.dst]!, shortName e.via)).toList
  let mut edgeLines : Array String := #[]
  for t in triples.eraseDups do
    let count := triples.count t
    let label := if count > 1 then s!"{t.2.2} ×{count}" else t.2.2
    edgeLines := edgeLines.push s!"{t.1} -> {t.2.1}: \"{label}\""
  for l in edgeLines.qsort (· < ·) do
    lines := lines.push l
  return String.intercalate "\n" lines.toList ++ "\n"

/-- The node identifier of a component in the condensation diagram: a singleton is its
kind's own name; a nontrivial cluster is `scc_` plus its alphabetical representative —
the same representative that names the cluster's own diagram file. -/
private def compId (kg : KindGraph) (cl : Array Nat) : String :=
  if cl.size == 1 then shortName kg.kinds[cl[0]!]!
  else s!"scc_{((cl.map fun i => shortName kg.kinds[i]!).qsort (· < ·))[0]!}"

/-- The D2 source of the condensation — the derivability hierarchy: one node per
strongly connected component that touches a licensed edge, nontrivial clusters drawn
as hexagons labeled by their representative and size, and the cross-component edges
collapsed to one arrow carrying the licensed-edge count. Within-component edges are
not drawn — they are the cluster diagrams' content. -/
def d2Condensation (kg : KindGraph) : String := Id.run do
  let cls := kg.clusters
  let n := kg.kinds.size
  let mut comp : Array Nat := Array.replicate n 0
  for ci in [0:cls.size] do
    for v in cls[ci]! do
      comp := comp.set! v ci
  let mut activeComp : Array Bool := Array.replicate cls.size false
  for e in kg.edges do
    activeComp := (activeComp.set! comp[e.src]! true).set! comp[e.dst]! true
  let mut lines : Array String := #[d2Header, "direction: down"]
  let mut nodeLines : Array String := #[]
  for ci in [0:cls.size] do
    if !activeComp[ci]! then continue
    let cl := cls[ci]!
    if cl.size == 1 then
      nodeLines := nodeLines.push (shortName kg.kinds[cl[0]!]!)
    else
      let names := (cl.map fun i => shortName kg.kinds[i]!).qsort (· < ·)
      nodeLines := nodeLines.push
        s!"{compId kg cl}: \{\n  label: \"{names[0]!} ⋯ ({cl.size} kinds)\"\n  shape: hexagon\n}"
  for l in nodeLines.qsort (· < ·) do
    lines := lines.push l
  let pairs := ((kg.edges.filter fun e => comp[e.src]! != comp[e.dst]!).map
    fun e => (comp[e.src]!, comp[e.dst]!)).toList
  let mut edgeLines : Array String := #[]
  for p in pairs.eraseDups do
    let count := pairs.count p
    let arrow := s!"{compId kg cls[p.1]!} -> {compId kg cls[p.2]!}"
    edgeLines := edgeLines.push (if count > 1 then s!"{arrow}: \"×{count}\"" else arrow)
  for l in edgeLines.qsort (· < ·) do
    lines := lines.push l
  return String.intercalate "\n" lines.toList ++ "\n"

end KindGraph

open Lean Elab Command in
/-- `#kind_scc [ns …]` — the kind-level component report: the authored kinds in scope,
their licensed-derivation edge count, every inter-derivability cluster of two or more
kinds with the edges that wire it, and whether the kind digraph is acyclic. The reviewed
enumeration to pin beside `#kind_edges`; `#kind_scc_clean` is its gate. -/
elab "#kind_scc" nss:ident* : command => liftTermElabM do
  let kg ← KindGraph.kindGraphOf (nss.map (·.getId))
  let nontrivial := kg.clusters.filter (·.size ≥ 2)
  let mut lines : Array String := #[]
  for cl in nontrivial do
    lines := lines.push (kg.renderCluster cl)
  let selfEdges := kg.edges.filter fun e => e.src == e.dst
  let summary := s!"kind graph — {kg.kinds.size} kind(s), {kg.edges.size} licensed \
    derivation edge(s), {nontrivial.size} inter-derivable cluster(s) of size ≥ 2, \
    {selfEdges.size} within-kind edge(s)"
  if lines.isEmpty then
    logInfo m!"{summary}"
  else
    logInfo m!"{summary}\n{String.intercalate "\n" lines.toList}"

/-- One sanctioned cluster of the `#kind_scc_clean` gate: the kinds expected to be
mutually derivable, as a parenthesized group. -/
syntax sccAllowGroup := "(" ident+ ")"

open Lean Elab Command in
/-- `#kind_scc_clean [ns …] [(k …) …]` — **inter-derivability, stated as a gate.**
Every cluster of two or more mutually derivable kinds must be declared as a
parenthesized group (matched by name or suffix, at the same size); an undeclared
cluster throws with its wiring printed. What the gate buys: a new witness registration
whose composition with the existing rules merges two kind roles fails the build at the
vocabulary level, before any value walks the new cycle. -/
elab "#kind_scc_clean" nss:ident* grps:sccAllowGroup* : command =>
  liftTermElabM do
    let kg ← KindGraph.kindGraphOf (nss.map (·.getId))
    let allowed : Array (Array Name) :=
      grps.map fun g => g.raw[1].getArgs.map (·.getId)
    let nontrivial := kg.clusters.filter (·.size ≥ 2)
    let sanctioned (cl : Array Nat) : Bool :=
      allowed.any fun grp =>
        grp.size == cl.size && cl.all fun i =>
          grp.any fun a => a == kg.kinds[i]! || a.isSuffixOf kg.kinds[i]!
    let offending := nontrivial.filter (fun cl => !sanctioned cl)
    unless offending.isEmpty do
      let rendered := offending.map kg.renderCluster
      throwError "kind-level SCC: {offending.size} undeclared inter-derivable \
        cluster(s)\n{String.intercalate "\n" rendered.toList}\n\n\
        Each cluster's kinds can be manufactured from one another by licensed \
        derivations alone — no attest, no review. If the cluster is intentional \
        (representation variants of one role), declare it: \
        `#kind_scc_clean … (kindA kindB)`. If it is not, one of the printed \
        witness registrations merges two roles and must be split or retired."

open Lean Elab Command in
/-- `#kind_scc_d2 "dir" [ns …]` — write the D2 diagram sources of the kind-level
component findings into `dir`: `condensation.d2`, the derivability hierarchy, and one
`cluster_<kind>.d2` per inter-derivability cluster of two or more kinds, each named by
its alphabetical representative — the same representative that labels the cluster's
hexagon in the condensation. The script-facing twin of `#kind_scc`: run it from a
`lake env lean` driver, then render the sources with `d2`. -/
elab "#kind_scc_d2" dir:str nss:ident* : command => liftTermElabM do
  let kg ← KindGraph.kindGraphOf (nss.map (·.getId))
  let out := dir.getString
  IO.FS.createDirAll out
  let mut files : Array String := #[]
  for cl in kg.clusters.filter (·.size ≥ 2) do
    let rep := ((cl.map fun i => KindGraph.shortName kg.kinds[i]!).qsort (· < ·))[0]!
    let path := System.FilePath.mk out / s!"cluster_{rep}.d2"
    IO.FS.writeFile path (kg.d2Cluster cl)
    files := files.push path.toString
  let condPath := System.FilePath.mk out / "condensation.d2"
  IO.FS.writeFile condPath kg.d2Condensation
  files := files.push condPath.toString
  logInfo m!"kind SCC D2 — {files.size} file(s) written:\n\
    {String.intercalate "\n" files.toList}"

end PropertyKindCalculus
