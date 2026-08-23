/-
# Provenance — the metrological provenance hypergraph as data

The calculus's audit surfaces each report one relation of a single underlying object.
`#kind_boundary_audit` reports where values acquire kinds, with the evidence tier that
sanctions each site (`BoundaryAudit`); `#kind_edges` enumerates the authored kind-algebra
edges, each occurrence attributed to its use site (`KindEdges`); and a model's coverage
probe pins the closure its pipeline exercises. This module defines the object those
relations constitute — the **metrological provenance hypergraph**, the formal counterpart
of Dybkær's dissection of a complete property statement into system, component,
kind-of-property, procedure, and result. Its nodes are kinded values; its hyperedges are
witness-family occurrences — a `ProductKind k₁ k₂ k` occurrence relates two operands and
a result, hence *hyper*graph, and relates them in *order*: a quotient's numerator and
denominator are different ports of the edge, and the same node may occur twice
(`kx / kx`), so incidence is an ordered list, never a set. Sources carry the boundary
audit's evidence tiers; exits mark the erasure boundary, where kinded provenance hands
off to the bare carrier and the byte gate, not the type system, carries the claim onward.

The structure is *data* — prelude-only, carrier- and application-generic, parametric in
the node-identifier type `ν` and the kind type `κ` — so a graph can be authored by hand
in a probe, constructed by an elaborator harvest, or replayed from a report. Its fields
are lists and its checker is structural recursion over them, so well-formedness is
decided by *evaluation* in a probe (`#guard`) and by *kernel reduction* in a proof
(`decide`) — the kernel checks the wiring — and the applications' theorems get list
induction as their proof skeleton. A harvest that needs per-node attribution puts it
*inside* its choice of `ν` (a node id may be a declaration–binder pair); the occurrence's
use site is a field because use-site attribution is constitutive of the occurrence
relation itself — two uses of one witness are two occurrences, wherever the elaborator
lifted or shared the proof term.

## Well-formedness is structural; edges stay authored claims

`wellFormed` checks the wiring: every node declared exactly once; every occurrence typed
(operands and result carry the kinds their node declarations state, at the family's
operand count); results land only on derivation targets — a `derived` node or an output
port, never on a source, whose whole point is that it is *not* derived; and every derived
node, output port, and exit is reached from the sources (input and configuration ports,
gated ingests, attested mints) through the occurrences — reached through the *closure*,
so a cycle of occurrences feeding each other licenses nothing. That last condition is the
boundary audit's "raw mints = 0" made compositional: a node that is neither a source nor
reachable through authored occurrences is exactly an anonymous mint, and the predicate
refuses the graph that contains one.

What well-formedness deliberately does not check is the *truth* of any edge. Per the
trust model (`QuantityClassification`, "The trust model — witnesses are authored, not
checked"), whether `k` really is the product kind of `k₁` and `k₂` is the author's
metrological claim, judged by enumerating the authored witnesses; the graph records which
claims were used where, and inherits its soundness story from that enumeration rather
than re-adjudicating it.

## The identity wire — `copy`

One edge family is not a witness family: `copy`, the identity wire. It exists because an
interface can restate a node the wiring already has — a pass-through step's output *is*
its input, and a multi-output step's components are the interior nodes its body names —
and the graph still owes an occurrence that reaches the output port, or the port is
indistinguishable from an anonymous mint. A `copy` relates one operand to its result and
claims nothing metrological: the value is the same value under a second name. Because
that claim is structural rather than authored, it is the one family whose semantic
content `wellFormed` itself checks — a copy must preserve the kind — where every witness
family's equation remains the authored claim the trust model reviews by enumeration.
Enumeration surfaces list authored licenses, so they never show a `copy`; it belongs to
the wiring, and to the graph renderings of it.
-/

namespace PropertyKindCalculus

/-- The role a port plays in a step's interface: an input the step consumes, a
configuration value it reads (a declared constant mint — a cited coefficient table, a
bound, a threshold), or an output it produces. Inputs and configuration are sources of
the graph; outputs are derivation targets. -/
inductive Provenance.PortDir where
  | input
  | config
  | output
deriving DecidableEq, Repr, Inhabited

/-- How a port role prints in a rendered report: `input` / `config` / `output`. -/
def Provenance.PortDir.label : Provenance.PortDir → String
  | .input => "input"
  | .config => "config"
  | .output => "output"

/-- The evidence tier of a node-introduction event — the boundary audit's tiers, carried
into the graph. `derived` is the interior case: the kind is reached through an authored
occurrence, and well-formedness demands the occurrence exist. `gated` is a source with
runtime evidence: a checked ingest admitted the value, and the gate declaration is the
evidence. `attested` is a declared source with no machine-checkable evidence: the
harvested reason string is the node's label, carried so every report rendered from the
graph shows the one-line justification at the node that rests on it. -/
inductive Provenance.IntroTier where
  | derived
  | gated
  | attested (reason : String)
deriving DecidableEq, Repr, Inhabited

/-- Is this tier a source of the graph — a node known before any occurrence fires? -/
def Provenance.IntroTier.isSource : Provenance.IntroTier → Bool
  | .derived => false
  | .gated => true
  | .attested _ => true

/-- How an introduction tier prints in a rendered report: `derived` / `gated` /
`attested "reason"` — the attested case shows its one-line justification, per the
header's doctrine that every rendering carries it at the node that rests on it. -/
def Provenance.IntroTier.label : Provenance.IntroTier → String
  | .derived => "derived"
  | .gated => "gated"
  | .attested r => s!"attested \"{r}\""

/-- The hyperedge labels: the witness families of the core calculus — `ProductKind`,
`QuotientKind`, `ReciprocalKind`, `TranscendentalKind`, `PowerKind` (carrying its
rational exponent — an exponent is data of the edge, not an operand node), and the
operator-table registrations `KindMul`/`KindDiv` — plus `copy`, the identity wire
(header, "The identity wire"): harvested wiring, never an authored license. -/
inductive Provenance.EdgeFamily where
  | product
  | quotient
  | reciprocal
  | transcendental
  | power (exp : Rat)
  | tableMul
  | tableDiv
  | copy
deriving DecidableEq, Repr, Inhabited

/-- The number of operand nodes an occurrence of this family relates (its result is not
counted; a `power` edge's exponent is carried by the label, not an operand). -/
def Provenance.EdgeFamily.operandCount : Provenance.EdgeFamily → Nat
  | .product | .quotient | .tableMul | .tableDiv => 2
  | .reciprocal | .transcendental | .power _ | .copy => 1

/-- Render a `power` exponent in the enumeration commands' grammar: the spelling the
pretty printer gives the authored literal — `1 / 2`, `-1`, `3` — so an edge renders one
way whether it was read off a witness type or carried as edge data. -/
def Provenance.EdgeFamily.renderExp (p : Rat) : String :=
  if p.den == 1 then toString p.num else s!"{p.num} / {p.den}"

/-- Render an edge in the kind-equation grammar the enumeration commands print
(`a · b → c`, `a / b → c`, `1 / a → b`, `transcendental : a → b`, `a ^ p → b`,
`[table] …`; a `copy` is `a → b`), from already-rendered operand and result names. -/
def Provenance.EdgeFamily.render (f : Provenance.EdgeFamily)
    (operands : List String) (result : String) : String :=
  let o (i : Nat) : String := operands.getD i "_"
  match f with
  | .product => s!"{o 0} · {o 1} → {result}"
  | .quotient => s!"{o 0} / {o 1} → {result}"
  | .reciprocal => s!"1 / {o 0} → {result}"
  | .transcendental => s!"transcendental : {o 0} → {result}"
  | .power p => s!"{o 0} ^ {Provenance.EdgeFamily.renderExp p} → {result}"
  | .tableMul => s!"[table] {o 0} · {o 1} → {result}"
  | .tableDiv => s!"[table] {o 0} / {o 1} → {result}"
  | .copy => s!"{o 0} → {result}"

/-- A kind-typed port: one node of a step's interface, with the kind its signature
states and the role it plays. Input and configuration ports are sources; an output port
is a derivation target an occurrence must reach. -/
structure Provenance.Port (ν κ : Type) where
  /-- The port's node identifier. -/
  node : ν
  /-- The kind the signature states for this port. -/
  kind : κ
  /-- The port's role: input, configuration, or output. -/
  dir : Provenance.PortDir
deriving Repr, Inhabited

/-- A node-introduction event for an interior or source node that is not a port: the
node, the kind it is introduced at, and the evidence tier that introduces it. -/
structure Provenance.Intro (ν κ : Type) where
  /-- The introduced node's identifier. -/
  node : ν
  /-- The kind the node is introduced at. -/
  kind : κ
  /-- The evidence tier: derived interior node, gated ingest, or attested mint. -/
  tier : Provenance.IntroTier
deriving Repr, Inhabited

/-- One hyperedge occurrence: a use of an edge family at a site — a witness family
discharged, or the identity `copy` wired — relating its ordered operand nodes (each with
the kind the edge names for that position) to its result node. Order matters and
repetition counts — a quotient's numerator and denominator are distinct positions even
when one node fills both — which is why incidence is a list of pairs and not a set. -/
structure Provenance.Occurrence (ν κ : Type) where
  /-- The witness family this occurrence uses. -/
  family : Provenance.EdgeFamily
  /-- The ordered operands: each incident node with the kind the witness names for its
  position. -/
  operands : List (ν × κ)
  /-- The result node the occurrence derives. -/
  result : ν
  /-- The kind the witness names for the result. -/
  resultKind : κ
  /-- The use site the occurrence is attributed to (rendered; a declaration name). Two
  uses of one witness are two occurrences. -/
  site : String
deriving Repr, Inhabited

/-- **The metrological provenance hypergraph**, as data: kind-typed ports, node
introductions carrying the audit's evidence tiers, witness-family occurrences with
ordered incidence, and marked exits at the erasure boundary. Parametric in the node
identifier type `ν` and the kind type `κ`; `wellFormed` below is the structural
well-formedness judgment. -/
structure Provenance (ν κ : Type) where
  /-- The interface: kind-typed ports. -/
  ports : List (Provenance.Port ν κ)
  /-- The node-introduction events for non-port nodes, each with its evidence tier. -/
  intros : List (Provenance.Intro ν κ)
  /-- The hyperedge occurrences. -/
  occurrences : List (Provenance.Occurrence ν κ)
  /-- The marked exits: nodes whose values leave the calculus for the bare carrier. -/
  exits : List ν
deriving Repr, Inhabited

namespace Provenance

variable {ν κ : Type} [BEq ν] [BEq κ]

/-- The kind a node is declared at — by a port, or else by an introduction event.
`none` for an undeclared node. -/
def kindOf? (g : Provenance ν κ) (n : ν) : Option κ :=
  match g.ports.find? (·.node == n) with
  | some p => some p.kind
  | none => (g.intros.find? (·.node == n)).map (·.kind)

/-- The sources: the nodes known before any occurrence fires — input and configuration
ports, gated ingests, and attested mints. -/
def sources (g : Provenance ν κ) : List ν :=
  (g.ports.filter (fun p => !(p.dir == .output))).map (·.node)
    ++ (g.intros.filter (·.tier.isSource)).map (·.node)

/-- One monotone sweep of the closure: each occurrence whose operands are all known
adds its result, in occurrence order. -/
def sweep (occs : List (Occurrence ν κ)) (ks : List ν) : List ν :=
  occs.foldl (init := ks) fun ks o =>
    if o.operands.all (fun oc => ks.contains oc.1) && !ks.contains o.result then
      ks ++ [o.result]
    else ks

/-- `fuel` sweeps of the closure, starting from `ks`. -/
def sweeps (occs : List (Occurrence ν κ)) : Nat → List ν → List ν
  | 0, ks => ks
  | fuel + 1, ks => sweeps occs fuel (sweep occs ks)

/-- The nodes reached from the sources through the occurrences: the least fixpoint of
"an occurrence whose operands are all known makes its result known", in discovery
order. One sweep per occurrence saturates, since each productive sweep adds at least
one result. This is forward reachability on the hypergraph, and the engine of
`wellFormed`'s central condition. -/
def known (g : Provenance ν κ) : List ν :=
  sweeps g.occurrences g.occurrences.length g.sources

/-- Every node is declared exactly once, ports and introductions jointly: a node with
two declarations would have two kinds or two tiers, and every lookup would silently
choose one. -/
def uniquelyDeclared (g : Provenance ν κ) : Bool :=
  let ids := g.ports.map (·.node) ++ g.intros.map (·.node)
  ids.all fun n => (ids.filter (· == n)).length == 1

/-- Every occurrence is typed: its operand count is its family's, and each operand and
the result carry exactly the kind the corresponding node's declaration states — so an
occurrence cannot re-kind a node, and cannot touch an undeclared one. A `copy` must
additionally preserve the kind: the identity wire's claim is structural, so it is the
one family whose equation well-formedness itself checks (header, "The identity
wire"). -/
def occurrencesTyped (g : Provenance ν κ) : Bool :=
  g.occurrences.all fun o =>
    o.operands.length == o.family.operandCount
      && o.operands.all (fun oc => g.kindOf? oc.1 == some oc.2)
      && g.kindOf? o.result == some o.resultKind
      && (!(o.family matches .copy) || o.operands.all (fun oc => oc.2 == o.resultKind))

/-- Every occurrence's result is a derivation target: a `derived` introduction or an
output port. Never a source — a gated or attested node's whole point is that its kind
is *not* derived — and never an input or configuration port. -/
def resultsAreDerivations (g : Provenance ν κ) : Bool :=
  g.occurrences.all fun o =>
    g.intros.any (fun i => i.node == o.result && i.tier == .derived)
      || g.ports.any (fun p => p.node == o.result && p.dir == .output)

/-- The central condition — the boundary audit's "raw mints = 0", compositional: every
`derived` introduction, every output port, and every exit is in `known`, i.e. reached
from the sources through the occurrence closure. A derived node no occurrence chain
produces is an anonymous mint; an occurrence cycle feeding itself licenses nothing,
because the closure starts from the sources. -/
def sourcesReach (g : Provenance ν κ) : Bool :=
  let ks := g.known
  g.intros.all (fun i => !(i.tier == .derived) || ks.contains i.node)
    && g.ports.all (fun p => !(p.dir == .output) || ks.contains p.node)
    && g.exits.all ks.contains

/-- Structural well-formedness of the provenance hypergraph: unique declarations, typed
occurrences, results on derivation targets only, and sources reaching every derived
node, output, and exit. Decided by evaluation in a probe and by kernel reduction in a
proof; the truth of each edge remains the authored claim the trust model reviews by
enumeration. -/
def wellFormed (g : Provenance ν κ) : Bool :=
  g.uniquelyDeclared && g.occurrencesTyped && g.resultsAreDerivations && g.sourcesReach

/-- `Prop`-level well-formedness, for statements and `decide`. -/
def WellFormed (g : Provenance ν κ) : Prop := g.wellFormed = true

instance (g : Provenance ν κ) : Decidable g.WellFormed :=
  inferInstanceAs (Decidable (g.wellFormed = true))

end Provenance

end PropertyKindCalculus
