/-
# KindQueries — the assembled graph, asked

`#kind_contract` and its verdicts state what a boundary *is*; these commands ask the
assembled object what a boundary *does* — the queries `Provenance.Influence` defines,
surfaced at the same contract names the other commands take, over the same
`assembleContract` value, so a propagation table and a wiring theorem about one contract
are readings of one object.

  * `#kind_contract_propagation c` — the **metrological contract** of `c`: for every
    source port, the produced ports the occurrences carry it to. A signature states the
    ports' kinds; this relation adds how metrological information moves between them —
    and it is the machine-readable seed of an interface's generated documentation, the
    algorithm-flow figure with the wiring checked.
  * `#kind_output_ledger c` — the **per-output review surface** of `c`: for every
    produced port, the assumption ledger (the source ports, gated ingests, and attested
    mints, with reasons, that the value rests on) and the trust decomposition (how much
    of the pedigree is kernel-checked derivation, what the byte gate carries, what stands
    on attestation, and which exits the pedigree crosses).

Both render *from* the executable closures; the `Graph` library proves those closures
compute reachability in the value-flow digraph, so a port pair absent from the
propagation table is a theorem-backed non-influence, not a rendering choice.
-/

import PropertyKindCalculus.KindIncidence
import PropertyKindCalculus.Influence

namespace PropertyKindCalculus.KindQueries

open Lean PropertyKindCalculus.KindIncidence
open PropertyKindCalculus.Provenance (NodeId KindRef)

/-- The propagation table of a contract over its assembled graph, one sorted line per
source port. -/
def propagationLines (c : Provenance.Contract NodeId KindRef)
    (g : Provenance NodeId KindRef) : List String :=
  let pairs := c.propagation g
  let srcs := (c.ports.filter fun p => !p.dir.produced).map (·.node)
  (srcs.map fun s =>
    let outs := (pairs.filter (·.1 == s)).map (renderNode ·.2)
    if outs.isEmpty then
      s!"{renderNode s} → (no produced port)"
    else
      s!"{renderNode s} → {String.intercalate ", " outs}").mergeSort (· ≤ ·)

/-- The ledger lines of one produced port: sources split by what each is, then the
trust decomposition tallies. -/
def ledgerLines (g : Provenance NodeId KindRef) (out : NodeId) : List String := Id.run do
  let ledger := g.assumptionLedger out
  let split := g.trustSplit out
  let mut lines : List String := []
  let ports := (ledger.ports.map renderPort).map ("    " ++ ·) |>.mergeSort (· ≤ ·)
  let gated := (ledger.gated.map fun n => s!"    gated {renderNode n}").mergeSort (· ≤ ·)
  let attested :=
    (ledger.attested.map fun (n, why) => s!"    attested {renderNode n} — {why}")
    |>.mergeSort (· ≤ ·)
  lines := lines ++ [s!"  {renderNode out}:"] ++ ports ++ gated ++ attested
  lines := lines ++ [s!"    pedigree: {split.derived.length} derived, \
    {split.gated.length} gated, {split.attested.length} attested, \
    {split.exited.length} exit(s) crossed"]
  return lines

open Elab Command in
/-- `#kind_contract_propagation c` — the propagation relation of the contract `c` over
the assembly its members compute: which source ports reach which produced ports. -/
elab "#kind_contract_propagation " c:ident : command => liftTermElabM do
  let cname ← realizeGlobalConstNoOverload c
  let ctr ← contractValueOf cname
  let a ← assembleContract ctr
  let lines := propagationLines ctr a.graph
  logInfo m!"propagation — contract '{ctr.name}', {ctr.members.length} member(s):\n\
    {String.intercalate "\n" lines}"

open Elab Command in
/-- `#kind_output_ledger c` — the per-output assumption ledger and trust decomposition
of every produced port of the contract `c`, over the assembly its members compute. -/
elab "#kind_output_ledger " c:ident : command => liftTermElabM do
  let cname ← realizeGlobalConstNoOverload c
  let ctr ← contractValueOf cname
  let a ← assembleContract ctr
  let outs := (ctr.ports.filter (·.dir.produced)).map (·.node)
  if outs.isEmpty then
    logInfo m!"output ledger — contract '{ctr.name}' declares no produced ports"
  else
    let lines := (outs.map (ledgerLines a.graph)).flatten
    logInfo m!"output ledger — contract '{ctr.name}':\n\
      {String.intercalate "\n" lines}"

end PropertyKindCalculus.KindQueries
