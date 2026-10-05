import Verso
import VersoManual
import VersoBlueprint
-- Importing the library being documented lets the `(lean := "PropertyKindCalculus.…")`
-- nodes below resolve to real declarations and report their *proved* status. The graph
-- library carries the reachability reading of the pedigree closure the first capstone is
-- argued over and the two seal and bisimulation modules; the dimension library carries the
-- third capstone; the tape library carries the recording carrier, the denotation bridge and
-- the seal of the computation; the three test modules carry the witnesses.
import PropertyKindCalculus
import PropertyKindCalculus.Graph.Flow
import PropertyKindCalculus.Graph.Seal
import PropertyKindCalculus.Graph.Bisimulation
import PropertyKindCalculus.DimensionalHomogeneity
import PropertyKindCalculus.Torch.Paradigm.TapeParity
import PropertyKindCalculus.Torch.Paradigm.TapeSeal
import PropertyKindCalculus.Tests.Graph.Seal
import PropertyKindCalculus.Tests.Graph.Bisimulation
import PropertyKindCalculus.Tests.Dimension.Homogeneity
-- The three layers and their ladders, drawn: the `svg_figure` directive and the figure it
-- inlines.
import PropertyKindCalculusBlueprint.Figures

open Verso.Genre
open Verso.Genre.Manual
open Informal
open PropertyKindCalculusBlueprint

#doc (Manual) "Capstone theorems — what the calculus can do" =>
%%%
tag := "capstones"
%%%

A reader who has followed the chapters so far knows what the calculus _is_: a kind is a
type index, two kinds meet only under a witnessed law, a boundary is declared and then
decided, and a model carries its attestations as hypotheses. The question a reviewer asks
first is a different one: _what can the calculus do?_ What guarantee does a model earn by
being written in it — stated as a theorem whose hypotheses the build discharges and whose
conclusion a reviewer can use without reading the model? Three theorems answer it, one per
layer of the calculus — the provenance layer, the computation layer and the dimension
layer, laid out below — read through {ref "paradigm"}[the taint-tracking paradigm]:

1. *The seal of a module.* Once a module's inputs, constants and attestations are
   declared, no other raw datum reaches its outputs: every leaf of an output's pedigree is
   a declared source. Stated over the {tech}[metrological provenance hypergraph] the
   build harvests from the module's members; its hypotheses are the two kernel-decided
   judgments the build already pins per boundary.
2. *The seal of the computation.* The same guarantee for the computation itself, at every
   carrier the module is instantiated at: an output depends only on the sources the
   hypergraph names for it, every constant it uses is one the audit lists, and every kind
   change in the computation sits at a declared crossing. Stated over the
   {tech}[computational tape graph] of the tape a carrier-generic module records, related to
   the provenance hypergraph by a {tech}[kind-transporting weak bisimulation].
3. *Dimensional homogeneity of the kind algebra.* Every derived kind in a well-formed
   provenance hypergraph carries the dimension the family rules compute from its operands,
   so the dimension functor is a homomorphism along every occurrence — not only along the
   edges an interaction algebra curates.

Four named objects appear in these statements, and this chapter keeps them apart. The
{tech}[metrological provenance hypergraph] is the kinded object the first capstone is
stated over, harvested from the source, and it is where every kind originates; the
{tech}[value-flow digraph] is its binary shadow, the graph reachability is proved on. The
{tech}[tape] is not a graph but a record — the sequence of carrier operations a module
writes when evaluated at the recording carrier — and the {tech}[computational tape graph]
is the directed acyclic graph that record determines, the object the second capstone
relates to the provenance hypergraph; it carries no kinds until the
{tech}[kind-transporting weak bisimulation] transports them. None of the four is the
{tech}[blueprint dependency graph] drawn at the end of this document, which is a picture of
the document itself.

This chapter was written blueprint-first, in the discipline {ref "proved-spine"}[the proved
spine] records after the fact: each theorem was stated informally with its hypotheses and
its proof sketched against the declarations that existed, and the declarations were then
written to the sketches. Every node now links the declaration that discharges it, and the
ledger at the end records what the sketches priced and what remains an instrument rather
than a theorem. Two rules govern every statement below. *Non-vacuity is a deliverable, not a hope*: each capstone owes three
witnesses — an instance whose hypotheses the kernel decides, a mutant that fails the
hypothesis _and_ the conclusion, so that the hypothesis is shown to carry the weight, and a
pinned axiom profile. *The seal is no undeclared entry, not no entry*: raw data enters a
sealed module through its declared gates — a {tech}[checked ingest], a {tech}[constant
mint], an {tech}[attestation] with its reason — and the theorem's content is that the
build's list of gates is complete.

# The layers and their ladders

Each capstone is stated over one object, and those objects are the calculus's three
layers.

- *The provenance layer* — its object the {tech}[metrological provenance hypergraph]: what
  the source declares. Every node has a kind, every source has a tier, every hyperedge is
  a use of a law. Its value is that a module's assumptions become one object, and the seal
  of a module says that object's list of gates is complete for every output.
- *The computation layer* — its object the {tech}[computational tape graph]: what the code
  computes, at every carrier. Its value is that the seal becomes a claim about the
  executable rather than about a reading of the source.
- *The dimension layer* — its object the dimension functor over the kinds the hypergraph
  carries: what the laws in use must satisfy. Its value is that it is the only layer able
  to refute an authored law. Witnesses and attestations are claims; dimension can say no
  wherever the kinds carry one.

There is no single ladder from the first layer through the second to the third. There are
two ladders, and both stand on the provenance layer, because the computation layer checks
that the computation realizes the hypergraph while the dimension layer checks that the
laws inside the hypergraph cohere. A rung below both carries the source up to the
provenance layer. Each rung's status is the status of the nodes it names, which the
dependency graph and the ledger at the end of this chapter carry.

:::table +header
*
  * Rung
  * What carries it
  * Lost without it
*
  * Source to the provenance layer
  * the {tech}[boundary audit]; the {tech}[harvest]; {bpref "cap_def_wellFormed"}[well-formedness] and {bpref "def_contract"}[agreement of the declared boundary], decided per boundary; {bpref "cap_lem_pedigree_reachable"}[the reachability reading]; {bpref "cap_thm_seal"}[the seal of a module]
  * Per-site verdicts never compose to outputs: an anonymous mint two hops upstream of an output is visible only to a reader of the report.
*
  * Provenance layer to computation layer
  * {bpref "cap_lem_tape_cone"}[the cone lemma]; {bpref "cap_def_bisimulation"}[the bisimulation] with {bpref "cap_thm_bisimulation_sound"}[its soundness] and {bpref "cap_thm_strong_bisimulation"}[its strong form after contraction]; {bpref "cap_def_evaluates"}[the denotation bridge] and the closure tactic `tape_hom`; {bpref "cap_thm_semantic_seal"}[the seal of the computation]
  * The seal is about the harvest's transcript. A constant the recorder bakes, a path compaction introduces, an opaque callee the harvest saw as one node: all go unseen, and the harvest's attributions stay trusted instead of cross-checked.
*
  * Provenance layer to dimension layer
  * {bpref "thm_dim_homomorphism"}[the curated homomorphism]; the coverage command's verdict per authored edge; {bpref "cap_thm_dimensional_seal"}[dimensional homogeneity]
  * Outputs rest on declared sources through possibly wrong laws: a wrong edge is a kind-level fact nobody checks.
:::

The {tech}[kind-transporting weak bisimulation] is therefore the relation between the
provenance layer and the computation layer. It never touches the dimension layer directly,
but that layer's verdicts ride along it: every tape sub-graph that realizes an occurrence
realizes a law the dimension layer has judged coherent.

The three layers and the two ladders, drawn on one module — `y = a · b + e`, the module the
bisimulation witnesses below decide — seen at three granularities:

:::svg_figure "three-layers" PropertyKindCalculusBlueprint.Figures.threeLayers
The three layers and their two ladders, drawn on the module `y = a · b + e` at three
granularities.

The middle band is the metrological provenance hypergraph, the kinded one. The top band is
its image under the dimension functor, node by node and occurrence by occurrence, with the
family rule each occurrence must satisfy. The bottom band is the computational tape graph
the same module records at a complex carrier, where the one `product` occurrence expands to
four multiplications, a subtraction and an addition: the four products are the interior
vertices no node of the hypergraph names, the silent steps that make the bisimulation weak,
and the `additive` occurrence expands componentwise, with no interior at all. `R` runs from
each node to each of its observable components; the dotted boxes are the realizations of
the two occurrences.
:::

# The seal of a module — the provenance hypergraph

The first capstone is stated over the
{deftech}[metrological provenance hypergraph]{index}[metrological provenance hypergraph] —
the object every audit report presents one relation of. Its nodes are kinded values; its
hyperedges are occurrences of the witness families, each relating its operands to its
result _in order_, since a quotient's numerator and denominator are different ports of one
edge; its sources carry the {tech}[evidence tier] the boundary audit assigns them; and its
exits mark where a value leaves the calculus for the bare carrier. It is data — prelude-only,
parametric in the node and kind types — so it can be authored by hand in a probe or produced
by the {deftech}[harvest]{index}[harvest]: the elaboration-time walk that reads a declared
boundary's member definitions and builds their hypergraph from them, ports from the
members' signatures, occurrences from the kinded operations in their bodies, sources from
the tiers the {tech}[boundary audit] assigns and from the reason each attestation states at
its call site. The harvest's output for one boundary is its
{deftech}[assembly]{index}[assembly]: the hypergraph together with the signature positions
found to carry no kind and the level each node belongs to. The capstone's hypotheses are
the two judgments already decided per boundary: structural well-formedness of the
hypergraph, and agreement between the {tech}[declared boundary] and the one its members
compute. The order matters for what the seal rests on: the audit's tiers and the
attestations' reasons are inputs to the harvest, the harvest builds the hypergraph, and the
theorem is stated over that hypergraph with the two judgments as its hypotheses — the
audits establish the hypotheses, the harvest builds the object, and the theorem gives the
seal.

:::group "capstones_seal"
The seal of a module and what it rests on: well-formedness of the provenance hypergraph,
agreement of the declared boundary with the computed one
({uses "def_contract"}[the declared boundary]), and the reachability reading of the
pedigree. Everything the statement rests on exists and is proved; the theorem is the one
statement nobody has yet made over it.
:::

:::definition "cap_def_wellFormed" (parent := "capstones_seal") (lean := "PropertyKindCalculus.Provenance.wellFormed")
Structural well-formedness of the provenance hypergraph: every node declared exactly once;
every occurrence typed at its family's operand count, with operands and result carrying
their nodes' declared kinds; every occurrence result a derivation target — a `derived`
introduction or a produced port, never a source; and every derived node, produced port and
exit reached from the sources through the conjunctive closure of the occurrences. The last
clause is the boundary audit's "raw mints = 0" made compositional: a derived node no
occurrence chain produces is an anonymous mint, and an occurrence cycle feeding itself
licenses nothing, because the closure starts from the sources. `#kind_assembly_decide`
reflects the judgment into a kernel theorem per boundary.
:::

:::proof "cap_def_wellFormed"
Four structural recursions over lists, conjoined; decided by evaluation in a probe and by
kernel reduction in a theorem. The sources are the non-produced ports together with the
gated and attested introductions (`sources`), and the closure is a fuel-bounded fixpoint
that saturates in one sweep per occurrence (`reachableFrom`).
:::

:::definition "cap_def_pedigree" (parent := "capstones_seal") (lean := "PropertyKindCalculus.Provenance.ancestorsOf")
The {deftech}[pedigree]{index}[pedigree] of a node set: everything it is derived from, the
set itself included — the backward closure through the occurrences, computed as the forward
influence closure of the reversed incidence, one reversed unit occurrence per operand
position. The sources among an output's pedigree are its
{deftech}[influencers]{index}[influencers]: the term list of an uncertainty budget over the
hypergraph's edges, and the source set whose attached conditions a downstream flag may
claim for that output. Split by what each source _is_, the same set is the output's
{deftech}[assumption ledger]{index}[assumption ledger]: the ports left open at the
boundary, the gated ingests, the attested mints with their harvested reasons.
:::

:::proof "cap_def_pedigree"
One engine for both directions: the disjunctive sweep that adds a result when _some_
operand is known, run over the occurrence list reversed edge by edge. Fuel is one sweep per
reversed occurrence plus one, the sweep that observes saturation.
:::

:::theorem "cap_lem_pedigree_reachable" (parent := "capstones_seal") (lean := "PropertyKindCalculus.Provenance.mem_ancestorsOf_iff") (tags := "proved") (effort := "small")
Membership in the executable pedigree is reachability in the
{deftech}[value-flow digraph]{index}[value-flow digraph] — the binary shadow of the
provenance hypergraph, one vertex per node and one edge per operand-to-result pair of an
occurrence: `a` is among the ancestors of `b` exactly when a path of such edges leads from
`a` to `b`. The same saturation argument yields the pedigree hop by hop — a member is a
root or an operand of some occurrence, and the pedigree is closed under one backward hop —
which is how the capstone below is argued while its hypotheses are decided over lists.
:::

:::proof "cap_lem_pedigree_reachable"
The saturation argument for the forward closure — a sweep only appends, appended nodes are
pairwise-distinct occurrence results, so with one sweep per occurrence plus one the closure
has either observed a fixpoint or would have outgrown its own bound — applied to the
reversed incidence, whose step relation is the converse of the flow digraph's adjacency.
:::

:::theorem "cap_thm_seal" (parent := "capstones_seal") (lean := "PropertyKindCalculus.Provenance.pedigree_seal") (tags := "capstone, proved") (effort := "medium") (priority := "high")
*The {deftech}[seal of a module]{index}[seal of a module].* Let `g` be a provenance
hypergraph and `c` a declared boundary, with `g` {uses "cap_def_wellFormed"}[well-formed]
and `c` agreeing with `g` — the two judgments `#kind_assembly_decide` and
`#kind_contract_decide` pin ({uses "def_contract"}[the declared boundary]). Then for every
produced port or exit `y` of `c`, every node `a` in {uses "cap_def_pedigree"}[the pedigree
of `y`] is either a source of `g` — a non-produced port of `c`, a gated ingest, or an
attested mint carrying its reason — or the result of some occurrence all of whose operands
are themselves in the pedigree of `y`. Equivalently: the pedigree of an output has no leaf
outside the sources, and the assumption ledger the build prints for `y` is the complete
list of what `y` rests on. In the paradigm's words, once the module's gates are declared,
no other raw datum reaches its outputs.
:::

:::proof "cap_thm_seal"
Read hop by hop (the two closure facts beside {uses "cap_lem_pedigree_reachable"}[the
reachability reading]), a node `a` in the pedigree of `y` is `y` itself or an operand of
some occurrence, and `occurrencesTyped` makes it a declared node — a port or an
introduction. If `a` is a non-produced port or a gated or attested introduction, it is a
source. Otherwise `a` is a `derived` introduction or a produced port, and `sourcesReach`
places it in the conjunctive closure `known`, so some occurrence produces `a` with every
operand in `known`; each such operand is in the pedigree of `y`, which is closed under a
backward hop. The hypothesis
on `c` enters only to identify the non-produced ports of `g` with the boundary's declared
inputs, configuration and parameters, so that the conclusion speaks of the declared
interface rather than of whatever the harvest happened to port. The case `a = y` and the
step from a known node to a source or an occurrence result are the induction principle of
the conjunctive closure (`reachableFrom_sound`, in the core), which the dimension capstone
reuses. The executable form — a decidable `undeclaredLeaves g y`, empty exactly under the
conclusion — is `sealed_of_wellFormed`, what an instance pins with `decide`; the boundary
reading, `seal_of_agrees`, adds the hypothesis on `c`. All three stand beside the
reachability reading, in the graph library.
:::

:::theorem "cap_thm_seal_witnesses" (parent := "capstones_seal") (lean := "PropertyKindCalculus.Tests.GraphSeal.seal_witnesses") (tags := "proved") (effort := "small")
*Non-vacuity of the seal.* Three witnesses, each a pinned probe. (i) Two instances: an
authored hypergraph — the influence probe, labelled by numbers so the kernel decides it —
whose well-formedness and seal `decide` closes, with the theorem applied to it; and a
harvested one, the interval composition's declared boundary, whose well-formedness and
agreement the kernel already decides, for which `#kind_seal_decide` adds the seal theorem by
kernel reduction of the executable conclusion at every output. (ii) A mutant: the same
hypergraph with one anonymous mint added — a `derived` introduction no occurrence produces,
wired into an output — fails `wellFormed` _and_ has a non-empty `undeclaredLeaves` at that
output, exactly the mint, so the hypothesis is the discriminating one and the conclusion is
not closed by the shape of the statement. (iii) The axiom profile of
{uses "cap_thm_seal"}[the seal], pinned to the three classical axioms.
:::

:::proof "cap_thm_seal_witnesses"
(i) and (ii) are `decide` theorems over the authored hypergraph and its mutant, conjoined
as the linked declaration, and a kernel-decided seal over the harvested one; (iii) is
`#print axioms` under `#guard_msgs`. The mutant is the check the methodology asks of every
gate — a tactic that closes a goal is not evidence that the hypothesis fired — carried into
the capstone itself.
:::

What the first capstone does not claim: it is a theorem about the provenance hypergraph the
harvest produced. That the hypergraph is the code — that the harvest attributed every mint,
erasure and occurrence to the right node and missed none — is what the boundary audit, the
mint ratchet and the unkinded sweep assert about the source, and each of those is an
instrument, not a hypothesis of the theorem. The seal of the computation is what turns that
residual trust into a cross-check.

# The seal of the computation — the tape

A carrier-generic module has a second record of its computation, one that no harvest
produces. The {deftech}[tape]{index}[tape] is automatic differentiation's word for the
record of the operations a program performs, in the order it performs them. TorchLean's
autograd tape is that record as data: a grow-only array of nodes, each one operation with
the ids of its parents in operand order, its forward value and its local backward rule, and
every operation appends exactly one node. The name comes from reverse-mode differentiation,
which replays the record backward to accumulate gradients; the calculus never runs that
pass. It reads the tape forward — the code generator lowers it, and the evaluator the cone
lemma below is about re-computes every node from an environment of leaf values. A tape is
therefore a straight-line program, not a graph. A module writes one when instantiated at
the {deftech}[recording carrier]{index}[recording carrier] — the carrier whose values are
not numbers but thunks that append their sub-expression to the tape and return the result
node. Because the branchless carrier class carries no ordering to `Bool`, a module written
against it cannot branch on its data, so one recording covers every input.

The {deftech}[computational tape graph]{index}[computational tape graph] is the directed
acyclic graph the record determines: one vertex per tape node, an edge from each parent to
its node, the in-edges of a vertex ordered as its parents are — acyclic because every
parent precedes its node in the array. Its leaves are of exactly two sorts, a named input
and a baked constant; its roots are the recorded outputs; and it carries no kinds, since a
value of any kind records the same node. The name pairs it with the metrological
provenance hypergraph: one is what the source declares about kinds, the other is what the
code computes, and the second capstone is the relation between them. Graph or hypergraph?
A tape node _is_ its operation, so a vertex's ordered in-edges are the one hyperedge into
it, and reading the tape as an ordered hypergraph adds nothing to the graph. The provenance
hypergraph is a hypergraph in a stronger sense: its occurrences are objects apart from its
nodes, and several occurrences may derive one node. The
{deftech}[compacted tape]{index}[compacted tape] — the tape after its identical
sub-expressions are merged, so that its graph is the graph of the _distinct_ sub-expressions
rather than of their unfolding — is the very object the code generator lowers to a kernel.

:::group "capstones_semantic"
The seal of the computation: the second capstone relates the tape graph to the provenance
hypergraph, transports the hypergraph's kinds onto it through a weak bisimulation, and
states the seal for the computation at every carrier through the denotation bridge.
:::

:::definition "cap_def_tape" (parent := "capstones_semantic") (lean := "PropertyKindCalculus.Paradigm.TapeBuilder")
The recording carrier, as a structure: one deferred build action that, run inside the tape
monad, appends this sub-expression's nodes and yields its result node. Every
branchless-carrier operation is realized as one appended node, so instantiating a module at
this carrier _builds_ its tape, with one leaf per named input and one per host constant.
:::

:::proof "cap_def_tape"
Each arithmetic operation runs its operands and emits one node. Sharing is not recorded — a
sub-expression named twice emits twice — and the compaction that merges identical
sub-expressions is a separate pass over the recorded tape.
:::

:::definition "cap_def_evaluates" (parent := "capstones_semantic") (lean := "PropertyKindCalculus.Paradigm.TapeParity.Evaluates")
The {deftech}[denotation bridge]{index}[denotation bridge]: a recording-carrier value
_evaluates_ to a tensor when, on any tape, running it succeeds, its result node carries that
tensor, and the run only extends the tape. Each carrier operation preserves the bridge with
its matching elementwise operation, proved once per operation, so a module's parity with its
own eager value at the same source is the mechanical chaining of those lemmas — and needs
no numerical side condition, both carriers using the same clamped operations.
:::

:::proof "cap_def_evaluates"
A four-conjunct predicate; the per-operation preservation lemmas are proved from the tape's
forward-value faithfulness lemmas through a run bridge, and a composite kernel's parity is a
chain of them.
:::

:::theorem "cap_lem_tape_cone" (parent := "capstones_semantic") (lean := "PropertyKindCalculus.Paradigm.TapeSeal.evalTape_cone") (tags := "proved") (effort := "small")
*Evaluation reads only the cone.* Re-evaluating a tape from an environment of leaf values
gives, at every node, a value that depends only on the leaves in that node's backward cone
in the tape graph: two environments agreeing on the cone's named leaves give the same value
at the node. The
tape-side counterpart of {uses "cap_lem_pedigree_reachable"}[the pedigree reading].
:::

:::proof "cap_lem_tape_cone"
Strong induction over the vertex id, through the node-value characterisation of the
evaluator's fold (`evalTape_node_value`): a leaf reads its own name or constant, and an
operation applies its scalar to values already established for its parents, each earlier
in the tape and each in the cone.
:::

:::definition "cap_def_bisimulation" (parent := "capstones_semantic") (lean := "PropertyKindCalculus.Paradigm.Match.weak")
*The {deftech}[kind-transporting weak bisimulation]{index}[kind-transporting weak bisimulation].*
The relation that ties the two graphs of one module together: the provenance hypergraph
`g`, harvested from the source, where every kind originates, and the computational tape
graph of the tape `T` the same module records, which carries none. `R` relates nodes of `g`
to vertices of the tape graph. It is total on the _observable_ vertices — leaves, roots, and the operands and
results of every matched occurrence — and silent on the interior vertices a single kinded
operation expands to at the carrier: the real projections of a complex product, the
sub-graph of a principal square root, the plumbing an operation registered as carrier
vocabulary performs. That silence is what makes it _weak_: an interior vertex is a step
neither side observes. It simulates in both directions, which is what makes it a
_bisimulation_. Hypergraph to tape: every occurrence of `g` is matched to a tape sub-graph
whose frontier is the images of the occurrence's operands and whose operations realize the
occurrence's family, per a realization table with one entry per family and carrier. Tape to
hypergraph: every path of the tape graph between observable vertices projects along `R` to
a path of `g` — the direction the seal consumes. `R` matches leaves to sources, ports by
name and constants by value. A `step` edge to a member whose audit tier licenses a
re-typing is realized by a wire, and it is the only place the kinds transported along `R`
may change across a tape edge. The coarsest reading `R` preserves is the boundary's
{deftech}[propagation relation]{index}[propagation relation] — which source ports reach
which produced ports through the occurrences — and comparing that relation, rather than
occurrence lists, is what makes the match robust to sharing. `R` is not a bijection, for
four reasons present in the code: compaction merges tape nodes many-to-one; one kinded
operation is several carrier operations; two uses of one witness are two occurrences by
design; and a nominal selection is resolved at recording time into one tape per branch.

The relation is a weak bisimulation in the textbook sense — Sangiorgi's, through cslib's
labelled transition systems — between two systems over one label alphabet: a visible step
is an edge family with the operand position it enters at, and the silent step is the wiring
the harvest records as `copy`, a procedure edge, and every carrier-level interior step. The
provenance layer's transitions are the hops of its occurrences; the tape graph's are its
edges, labelled through the match. As data the relation is a *match*: a component table —
each node of `g` with the tape vertices realizing it, one for a real carrier, two for a
complex one — and one realization per occurrence, the interior vertices of its sub-graph.
The observable relation is node to component; the interior of a realization is related to
the occurrence's result, the result under construction. Acceptance is a decidable judgment
on the match, each clause of which some proof below consumes.
:::

:::proof "cap_def_bisimulation"
Decided, never assumed: acceptance is a Boolean over the match, decided by evaluation in a
probe and by kernel reduction in a theorem. A matcher that _finds_ the match from the
leaves of a recorded tape — ports by name, constants by recording site, each occurrence by
a realization table per family and carrier — is the instrument the ledger prices, and the
refactoring it needs stands: the recorder must name its constant leaves, and either mark
the scope of each member call on the tape or the matcher must widen the member set to the
closure the tape sees through.
:::

:::theorem "cap_thm_bisimulation_sound" (parent := "capstones_semantic") (lean := "PropertyKindCalculus.Paradigm.Match.isWeakBisimulation_weak") (tags := "proved") (effort := "medium")
*The accepted match is a weak bisimulation.* When acceptance holds for `R` between a
well-formed `g` and `T`, {uses "cap_def_bisimulation"}[the bisimulation] is a weak
bisimulation, in both directions: every hop of `g` from a node is matched, from each of the
node's components, by a tape step with the same label up to silent steps, and every tape
step from a vertex is matched from every node the vertex is related to. The direction the
seal consumes follows as a corollary: every path of the tape graph from a component of a
node `s` to a component of a node `b` projects along `R` to a path of the value-flow
digraph from `s` to `b` (`reachable_of_tape_path_comps`); and every tape edge between two
observable vertices realizes one hop of one occurrence of `g`, with the kinds that
occurrence names for its operand and its result (`occurrence_of_edge`) — so the kinds
transported along `R` change across a tape edge only where an occurrence of `g` states the
change. The tape-side analogue of the lemma that makes the influence probe's `false` a
theorem — so an accepted match is evidence rather than a report.
:::

:::proof "cap_thm_bisimulation_sound"
By factoring rather than by induction over an acceptance derivation: the strong
bisimulation with the contracted tape graph composed with the contraction
({uses "cap_thm_strong_bisimulation"}[the contraction lemma]), cslib's composition of weak
bisimulations. The projection is the tape-to-hypergraph half of the saturated bisimulation,
iterated along the path, with the observable vertices at both ends read back to their
nodes through injectivity of the component table; the kind clause is covering and
closedness of the sub-graphs read at one edge, with `occurrencesTyped` for the kinds.
:::

:::definition "cap_def_contraction" (parent := "capstones_semantic") (lean := "PropertyKindCalculus.Paradigm.Match.contracted")
*The {deftech}[contracted tape graph]{index}[contracted tape graph].* Let acceptance hold
for `R` between `g` and `T`, so that each occurrence `o` of `g` has a realizing sub-graph
`S_o` of the tape graph: its interior, its roots — the components of the result — and its
frontier, the components of the operands in operand order. The contraction collapses each
`S_o` to one ordered hyperedge from the frontier to the roots, labelled by the occurrence's
family and the operand position; a wire is a silent step. It is defined — an ordered
hypergraph of the same signature as `g`, with no interior — under the clauses acceptance
decides of the sub-graphs: _closed_, every parent of a sub-graph vertex is an interior or a
frontier vertex, so no value enters except through the operands; _interior-private_, every
edge leaving an interior vertex stays inside `S_o`, so no interior value is read from
outside; _progressing_, every interior vertex feeds the sub-graph, so it lies on a path to
a root; _used_, every frontier vertex feeds the sub-graph; _disjoint_, the interiors of
distinct sub-graphs do not overlap and no interior vertex is a component; and _covering_,
every operation vertex of the tape graph lies in some `S_o`. Leaves are matched by
recording site, not by value, so that two constants of one value stay two leaves.
:::

:::proof "cap_def_contraction"
One hyperedge per accepted occurrence, between components; the clauses are Boolean
conjuncts of acceptance, and a sub-graph violating one is a match acceptance refuses. The
recorder's obligation is the named constant leaf, the same one the bisimulation's
definition already prices.
:::

:::theorem "cap_thm_strong_bisimulation" (parent := "capstones_semantic") (lean := "PropertyKindCalculus.Paradigm.Match.isBisimulation_contracted") (tags := "proved") (effort := "medium")
*Contraction makes the bisimulation strong.* Under acceptance and well-formedness, `R`
restricted to the observable vertices — node to component — is a strong bisimulation
between `g` and {uses "cap_def_contraction"}[the contracted tape graph]: every hop of `g`
is matched by one hyperedge of the contraction and conversely, with no silent step, and
once the two node-identity mismatches are quotiented away it is an isomorphism of ordered
hypergraphs — compaction, by matching against a hypergraph quotiented by derivation
equality; nominal selection, by matching per branch. The contraction itself — a component
to every component of its node, a root to every interior vertex of its realization — is a
weak bisimulation between the contracted and the actual tape graph
(`isSWBisimulation_contraction`), and {uses "cap_def_bisimulation"}[the weak bisimulation]
between `g` and the tape graph is their composite: the weak bisimulation factors as this
strong one composed with the contraction, which is the standard relation between weak and
strong bisimulation up to silent-step abstraction. What the strong form deliberately loses
is the interior, and the interior is where the numerical side conditions live: the license
clause and the adequacy layer keep working on the uncontracted tape graph.
:::

:::proof "cap_thm_strong_bisimulation"
The strong half is a corollary of acceptance alone — totality and injectivity of the
component table, one realization per occurrence, and well-formedness for the result of
every occurrence to be a declared node. The contraction's half is where the sub-graph
clauses work: an interior vertex reaches a root through silent steps (progress, with the
tape's order for termination), a frontier vertex enters the sub-graph (used), and a step
from an interior vertex stays inside it (interior-private), while an interior vertex is
related to nothing observable (disjointness). No new instrument: acceptance already
decides every clause.
:::

:::theorem "cap_thm_semantic_seal" (parent := "capstones_semantic") (lean := "PropertyKindCalculus.Paradigm.TapeSeal.semantic_seal") (tags := "capstone, proved") (effort := "large") (priority := "high")
*The {deftech}[seal of the computation]{index}[seal of the computation].* Let `f` be a
module written once against the branchless carrier class with fixed-extent iteration, `g`
its provenance hypergraph with `c` its declared boundary, and `T` the well-formed tape `f`
records. Suppose (H1) `g` is well-formed, so that {uses "cap_thm_seal"}[the seal of the
module] holds of it and, under agreement, of `c`; (H2) acceptance holds for a match `R`
between `g` and the computational tape graph of `T`; and (H3) at a carrier, the value of
`f` at an output `o` {uses "cap_def_evaluates"}[evaluates] to the re-evaluation of `T` at
the vertex realizing `o`. Then for every node `o` — in particular every produced port —
and every vertex `r` realizing it: two environments that agree on the leaves realizing the
influencers of `o` — the sources `g` names for it — give the same value at `r`, hence the
same value of `f` at that carrier (`semantic_seal_of_denotes`); every leaf in the cone of
`r`, a named input or a baked constant, realizes an influencer of `o` — every constant the
computation uses is one the assumption ledger lists; and every tape edge between observable
vertices realizes one hop of one occurrence of `g`, with the kinds that occurrence names —
every kind change in the computation sits under an occurrence the source states. The
hypergraph's absence claims become semantic: an input the harvest says cannot reach `o`
provably does not, in the computation, at every carrier the bridge reaches.
:::

:::proof "cap_thm_semantic_seal"
By (H3) the value of `o` at the carrier is the tape's value at `r`; by
{uses "cap_lem_tape_cone"}[the cone lemma] that value depends only on the named leaves in
the cone of `r`; by {uses "cap_thm_bisimulation_sound"}[the accepted match] each such leaf
is a component of a source whose tape path to `r` projects to a path of the value-flow
digraph to `o`, so the source is an influencer of `o` — the assumption ledger (H1) prints.
The kind clause is the accepted match's edge reading.
:::

:::theorem "cap_thm_semantic_seal_witnesses" (parent := "capstones_semantic") (lean := "PropertyKindCalculus.Tests.Bisimulation.bisimulation_witnesses") (tags := "proved") (effort := "medium")
*Non-vacuity of the seal of the computation.* (i) An instance in which acceptance is
decided by the kernel and the recorded tape is the accepted graph: the module
`y = a · b + e` at the complex carrier over the recording carrier, whose hypergraph has a
product and a same-kind sum and whose tape expands the product to `(ac − bd) + (ad + bc)j`
— four interior vertices the bisimulation is silent on. Acceptance is closed by `decide`;
the strong bisimulation, the contraction, the weak bisimulation, the cone lemma and the seal
of the computation are instantiated on it; and the tape the recorder writes, compacted,
projects vertex for vertex onto that graph — a runtime check, since the tape's stored
tensors are opaque to the kernel — with the recorded values checked against the seal's
value clause. (ii) A mutant: a tape that bakes one constant the hypergraph does not list —
acceptance refuses it, at the leaf clause the constant clause rests on. (iii) The axiom
profiles of {uses "cap_thm_semantic_seal"}[the seal of the computation], the cone lemma and
the bisimulation theorems, pinned. The worked model's branchless dielectric chain — whose
hypergraph is pinned, whose tape is recorded and whose (H3) is a chain of `Evaluates`
lemmas — is the instrument the ledger still prices: the match between its two objects is
what the recorder decision fixes.
:::

:::proof "cap_thm_semantic_seal_witnesses"
(i) and (ii) are kernel-decided theorems over an authored pair, conjoined as the linked
declaration, and a runtime check over the recorded tape; (iii) is `#print axioms`. Where
(H3) is only a bit-exact runtime gate — the iterated retrieval, the table lookups — an
instance is gated, not proved, and the ledger says so.
:::

What the second capstone changes, and what it leaves. It covers bits and, through `R`,
kinds: the tape graph's kinds are the hypergraph's, transported, and the matcher checks the
hypergraph's occurrence structure — each family against the operation that realizes it —
against an instrument the harvest does not share. Read as a guarantee about the code: every
occurrence maps to a tape sub-graph realizing its family, every tape path between
observable vertices projects to a hypergraph path, and the kinds transported along `R`
change only at the image of a declared crossing — so the computation is kind-preserving in
exactly that sense, on a graph that carries no kinds of its own; and speaking of values at
every carrier needs (H3), the denotation bridge, beside it. What remains trusted is
smaller: that the harvest read each node's kind off the kernel-checked term at the right
node, since `R` transports kinds and does not re-derive them; and the code generator and
toolchain below the tape, which {ref "deployment-template"}[the deployment template] lists
as such.

# Dimensional homogeneity along the hypergraph

Three results grow in scope here, and the third capstone is the jump from the first two to
the third. {bpref "thm_dim_homomorphism"}[The curated homomorphism] is proved: for a
curated interaction algebra, whenever the algebra sanctions a product, the result's
dimension is the product of the operands' dimensions. It holds because the algebra carries
that side condition in its definition, so it is per algebra, and only for the product and
quotient edges an author chose to mirror into one. The coverage command is mechanical: it
walks every authored edge under a namespace across all nine witness families and evaluates
each family's dimensional rule. It is total, but per edge, and its output is a report
rather than a theorem. The capstone below composes both: given a well-formed hypergraph
whose occurrences all carry coherent families, dimension is a homomorphism along every
occurrence and hence along every path, so the dimension of every derived node and every
output is the one computed from the sources' dimensions by composing the rules. A per-edge
verdict says each step balances; the capstone says the whole model balances end to end —
dimensional analysis of the entire algorithm as a theorem — and it covers the families the
model actually uses, transcendental, power, copy and difference among them, which no
interaction algebra curates. In the paradigm's words: the seal of a module says nothing
undeclared enters, and homogeneity says every law traversed coheres, so an output's kind
rests on declared sources through coherent laws.

:::group "capstones_dimension"
The kind algebra's edges are authored claims: a product witness proves only that its three
kinds are ratio-scale, and that _these_ kinds meet is the author's metrological claim. One
layer can refute such a claim — the dimension functor, where a wrong edge over dimensioned
kinds fails to balance — and the coverage command walks every authored edge and reports it
coherent, parametric, or refuted. The third capstone lifts the per-edge verdict to the
hypergraph: dimension is a homomorphism along every occurrence of a well-formed provenance
hypergraph, not only along the edges an interaction algebra curates.
:::

:::theorem "cap_thm_dimensional_seal" (parent := "capstones_dimension") (lean := "PropertyKindCalculus.DimensionalHomogeneity.dimensional_homogeneity") (tags := "capstone, proved") (effort := "medium") (priority := "high")
*{deftech}[Dimensional homogeneity]{index}[dimensional homogeneity] along the hypergraph.*
Let `g` be a {uses "cap_def_wellFormed"}[well-formed] provenance hypergraph and `dimOf` the
declared dimension of each kind, such that the declared assignment of dimensions to nodes
is homomorphic along every occurrence — the family's rule, applied to the operands'
dimensions, gives the result's: a product adds the operand exponents, a quotient subtracts
them, a reciprocal negates them, a power scales them by its exponent, a transcendental
demands dimension one, a copy and a reference preserve, a same-kind sum demands equal
operands — the verdict the coverage command reports as `[coherent]`, stated per occurrence
and decided by the executable `coherent`. Then every assignment that follows the rules along
every occurrence from the same source dimensions agrees with the declared one on every
known node — every derived node, produced port and exit: the dimension of every output is
the one the rules compute from the sources' alone, and the dimension functor is a
homomorphism along every path of `g`. Stated over any rule algebra in the core
(`Provenance.homogeneity`) and instantiated on PhysLib's dimensions with the coverage
command's rules (`dimRule`); the hypergraph-level, total form of
{uses "thm_dim_homomorphism"}[the curated homomorphism], which is per edge and per algebra.
:::

:::proof "cap_thm_dimensional_seal"
Induction over the conjunctive closure from the sources (`reachableFrom_sound`, the same
principle the seal of a module rests on), one case per occurrence, closed by the rule: two
homomorphic assignments agreeing on the operands agree on the result. Well-formedness
supplies that every derived node and every output is in the closure. The coverage rows as
hypergraph data are the declared assignment `declaredDim dimOf g` and the per-occurrence
verdict `coherent`, which `coherent_iff` identifies with the hypothesis. Non-vacuity: the
refuted `L · L → L` edge as a mutant occurrence that fails the verdict and, together with
it, the conclusion — the rule-following assignment gives the output `L²`, not the declared
`L` (`homogeneity_witnesses`). What remains an instrument is reading `dimOf` off the
environment's `DimensionedKind` registry for a harvested hypergraph, which the coverage
command does by elaboration and the theorem takes as a hypothesis.
:::

# Status ledger

*Done — what each capstone rests on, and the capstones themselves.*

- The provenance hypergraph with its well-formedness judgment, the pedigree closure and its
  reachability reading, the boundary judgments `agrees` and `discharges`, and the
  per-boundary kernel theorems the worked model pins for each of its declared boundaries.
- The recording carrier, the compaction pass, the code generator, and the denotation bridge
  with whole-kernel parity theorems for the branchless dielectric chain, its reflectivity,
  and the fit's forward, residual and Jacobian kernels.
- The dimension functor, the curated homomorphism, and the coverage command with its pinned
  refutation of an incoherent edge.
- The three capstones and their supporting lemmas, each linked above: the seal of a module
  in the graph library, with its executable form, its boundary reading and the induction
  principle of the conjunctive closure it and the third capstone share; the
  kind-transporting weak bisimulation in cslib's labelled transition systems, factored as
  the strong bisimulation with the contracted tape graph composed with the contraction; the
  cone lemma and the seal of the computation on the tape evaluator; dimensional homogeneity
  over any rule algebra, instantiated on PhysLib's dimensions. Each with its instance, its
  mutant and its pinned axiom profile.

*Open — each item with whose move it is.*

- Capstone 2, the matcher: acceptance is decided on a match a probe authors. A matcher that
  finds the match from the leaves of a recorded tape — ports by name, constants by recording
  site, each occurrence by a realization table per family and carrier — is the instrument
  to run on the dielectric pair, where the hypergraph, the tape and the parity theorem all
  exist, reading what disagrees before the seal of the computation is claimed of the worked
  model; the expected disagreement classes are the four named in the bisimulation's
  definition (`cap_def_bisimulation`). *Library and worked model.*
- Capstone 2, the recorder decision: scope markers per member call, or membership widened
  to the closure the tape sees through — the choice that fixes the matcher's cost, and
  what makes an assembly's procedure edges matchable beside the occurrences they summarize.
  *Owner.*
- Capstone 2, the iterated retrieval's parity theorem, today a bit-exact runtime gate.
  *Worked model.*
- Capstone 3, the declared dimensions from the environment: the coverage command resolves
  each kind to its `DimensionedKind` by elaboration; the assignment the capstone consumes is
  authored per probe today, and the walk that reads it off the registry for a harvested
  hypergraph is the bridge from the command's report to the theorem's hypothesis.
  *Library.*

# What the capstones do not claim

- The truth of an attestation. It is a hypothesis of the model; the seal says only that the
  build's list of them is complete. Where the attestation defers a requirement, the
  {ref "requirements-as-evidence"}[requirement clause] counts it, with its reason, as one
  the apparatus still owes.
- The harvest's kind readings. The bisimulation transports them and does not re-derive them.
- Anything below the tape — the code generator, the toolchain, the foreign interface — which
  the deployment template lists as what remains trusted.
- Accuracy against nature, which needs a true value the kernel never has; that boundary is
  the uncertainty chapter's, and the {ref "requirements-as-evidence"}[requirement clause]
  is where a demand of that kind is stated as an empirical requirement against a named
  referent, gated or attested, rather than left unsaid.
