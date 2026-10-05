/-
# The terminological dictionary — one name per concept

Each entry records the citable identity of a term the calculus uses: the canonical phrase
(`key`), the short form a document may use once the canonical phrase has appeared
(`short`), a one-sentence gloss, the declarations that carry the concept (`decls`, checked
to exist when the blueprint is built), the blueprint section that defines the term
(`definedIn`, the tag of the section holding the term's one `{deftech}`), the retired
phrasings a document must not use (`avoid`), and the entries a reader should see beside it
(`seeAlso`).

Three rules the data encodes, and the gate enforces:

  * **One defining site.** A term is defined by exactly one `{deftech}` in the blueprint,
    under the section `definedIn` names; every other mention is a `{tech}` link to it, or
    plain prose using the same phrase.
  * **Canonical first, short after.** A chapter, a module docstring, or a plan document
    uses the canonical phrase at the concept's first mention and may use `short` afterward.
  * **Retired means refused.** A phrasing listed under `avoid` fails the gate wherever the
    gate reads — the blueprint and the root plan documents — and is counted in the
    library's docstrings by a ratchet that may only fall.

Prelude-only data, in the idiom of `Requirements.Catalogue` and `Rubrics.Catalogue`: there is
deliberately no prose here beyond the gloss, because a definition transcribed into prose is a
definition that drifts. The chapter that explains a term is the one `definedIn` names.
-/

module

@[expose] public section Blanket

namespace PropertyKindCalculus.Terminology

/-- One entry of the dictionary. -/
structure Term where
  /-- The canonical phrase, as written in prose. -/
  key : String
  /-- The sanctioned short form, usable after the canonical phrase has appeared. -/
  short : Option String := none
  /-- A one-sentence gloss; the explaining prose lives in the section `definedIn` names. -/
  gloss : String
  /-- The declarations that carry the concept; the blueprint build checks each exists. -/
  decls : List Lean.Name := []
  /-- The tag of the blueprint section that holds the term's one `{deftech}`. -/
  definedIn : String
  /-- Retired phrasings the gate refuses. -/
  avoid : List String := []
  /-- Entries to read beside this one; each must be a `key` of the dictionary. -/
  seeAlso : List String := []
  deriving Inhabited

/-- The dictionary. Entries are kept in the order a reader meets the concepts; the rendered
table sorts them. -/
def dictionary : List Term :=
  [ { key := "metrological provenance hypergraph",
      short := some "provenance hypergraph",
      gloss := "The object every audit report presents one relation of, and the one where \
                every kind originates: kinded values as nodes, occurrences of the witness \
                families as ordered hyperedges, sources carrying their evidence tier, and \
                exits where a value leaves the calculus; prelude-only data, authored by hand \
                in a probe or produced by the harvest from the source.",
      decls := [`PropertyKindCalculus.Provenance, `PropertyKindCalculus.Provenance.wellFormed],
      definedIn := "capstones",
      avoid := ["provenance graph", "harvested graph", "assembled graph"],
      seeAlso := ["harvest", "assembly", "value-flow digraph",
                  "kind-transporting weak bisimulation"] }
  , { key := "harvest",
      gloss := "The elaboration-time walk that reads a declared boundary's member \
                definitions and builds their provenance hypergraph: ports from the \
                signatures, occurrences from the kinded operations, sources from the \
                boundary audit's tiers and the attestations' reasons.",
      decls := [`PropertyKindCalculus.KindIncidence.Assembly],
      definedIn := "capstones",
      seeAlso := ["assembly", "metrological provenance hypergraph", "boundary audit"] }
  , { key := "assembly",
      gloss := "The harvest's output for one declared boundary: its provenance hypergraph \
                together with the signature positions found to carry no kind and the \
                level each node belongs to.",
      decls := [`PropertyKindCalculus.KindIncidence.Assembly],
      definedIn := "capstones",
      seeAlso := ["harvest", "declared boundary"] }
  , { key := "value-flow digraph",
      short := some "flow digraph",
      gloss := "The binary shadow of a provenance hypergraph: one vertex per node, one \
                edge per operand-to-result pair of an occurrence; the graph reachability \
                is stated over, so that the executable closures can be proved to compute it.",
      decls := [`PropertyKindCalculus.Provenance.flowDigraph,
                `PropertyKindCalculus.Provenance.mem_ancestorsOf_iff],
      definedIn := "capstones",
      seeAlso := ["metrological provenance hypergraph", "pedigree"] }
  , { key := "pedigree",
      gloss := "Everything a node set is derived from, the set included: the backward \
                closure through the occurrences.",
      decls := [`PropertyKindCalculus.Provenance.ancestorsOf,
                `PropertyKindCalculus.Provenance.eq_or_operand_of_mem_ancestorsOf,
                `PropertyKindCalculus.Provenance.operand_mem_ancestorsOf],
      definedIn := "capstones",
      seeAlso := ["influencers", "assumption ledger", "value-flow digraph"] }
  , { key := "influencers",
      gloss := "The sources among an output's pedigree: the term list of an uncertainty \
                budget over the graph's edges, and the source set whose attached conditions \
                a downstream flag may claim for that output.",
      decls := [`PropertyKindCalculus.Provenance.influencers],
      definedIn := "capstones",
      seeAlso := ["pedigree", "assumption ledger"] }
  , { key := "assumption ledger",
      gloss := "An output's influencers split by what each source is — the ports left open \
                at the boundary, the gated ingests, the attested mints with their reasons.",
      decls := [`PropertyKindCalculus.Provenance.assumptionLedger,
                `PropertyKindCalculus.Provenance.trustSplit],
      definedIn := "capstones",
      seeAlso := ["influencers", "evidence tier"] }
  , { key := "propagation relation",
      gloss := "Which source ports of a declared boundary reach which of its produced ports \
                through the occurrences — the reading of an interface that says how \
                information moves through it, not only what it takes and returns.",
      decls := [`PropertyKindCalculus.Provenance.Contract.propagation],
      definedIn := "capstones",
      seeAlso := ["declared boundary", "kind-transporting weak bisimulation"] }
  , { key := "evidence tier",
      short := some "tier",
      gloss := "How a value came to carry its kind: derived through a law of the algebra, \
                gated by a check at ingest, or attested by its author with a reason.",
      decls := [`PropertyKindCalculus.Provenance.IntroTier],
      definedIn := "paradigm",
      seeAlso := ["attestation", "checked ingest", "constant mint"] }
  , { key := "attestation",
      gloss := "A kind claim with no machine-checkable evidence, stated where used with its \
                reason: a hypothesis of the model, not an axiom of the calculus.",
      decls := [`PropertyKindCalculus.Quantity.attest],
      definedIn := "paradigm",
      seeAlso := ["evidence tier", "boundary audit"] }
  , { key := "checked ingest",
      gloss := "The entry of raw, external data into the calculus through a check — the \
                `@[kindIngest]` tier — whose evidence is the check itself.",
      definedIn := "paradigm",
      seeAlso := ["evidence tier", "constant mint"] }
  , { key := "constant mint",
      gloss := "The entry of an adjudicated constant — a cited coefficient, a threshold, a \
                structural constant of the model — through the `@[kindConst]` tier, its \
                provenance the declaration's docstring.",
      definedIn := "paradigm",
      seeAlso := ["checked ingest", "evidence tier"] }
  , { key := "crossing",
      gloss := "A re-typing of a value that already carries one kind as another, with no \
                law of the algebra to derive it: trust granted by hand, tagged \
                `@[kindCrossing]` and enumerated by the boundary audit.",
      definedIn := "paradigm",
      seeAlso := ["boundary audit", "emission"] }
  , { key := "emission",
      gloss := "Where a kinded value leaves the calculus as a bare number for a consumer \
                outside it — a deploy driver, a serializer, the parity apparatus — tagged \
                `@[kindEmission]`.",
      definedIn := "paradigm",
      seeAlso := ["crossing", "boundary audit"] }
  , { key := "boundary audit",
      gloss := "The environment walk `#kind_boundary_audit` that lists every site where a \
                value acquires or sheds a kind, each with the tier that sanctions it, and \
                fails the build on a site no tier sanctions.",
      definedIn := "paradigm",
      seeAlso := ["evidence tier", "harvest"] }
  , { key := "declared boundary",
      short := some "contract",
      gloss := "The interface a metrology module declares: its members, its kind-typed \
                ports with the role each plays, its exits, and its deciders; decided \
                against what the members compute, in both directions.",
      decls := [`PropertyKindCalculus.Provenance.Contract,
                `PropertyKindCalculus.Provenance.Contract.agrees],
      definedIn := "metrological-modularity",
      seeAlso := ["metrology module", "assembly", "propagation relation"] }
  , { key := "metrology module",
      gloss := "A software component — the declarations one boundary names as its members, \
                which need not be a file or a namespace — whose interface is a declared \
                boundary, whose behavior is a measurement model attached as a theorem edge, \
                whose implementation is a carrier-parametric measurement function, and \
                whose licenses and mereology are declared.",
      definedIn := "metrological-modularity",
      avoid := ["unit of software", "software unit"],
      seeAlso := ["declared boundary", "measurement model", "license clause"] }
  , { key := "measurement model",
      gloss := "The VIM relation among the quantities involved in a measurement, attached \
                to a declared boundary as a checked theorem edge rather than as prose.",
      decls := [`PropertyKindCalculus.Provenance.Relation],
      definedIn := "metrological-modularity",
      seeAlso := ["metrology module", "license clause"] }
  , { key := "carrier ladder",
      gloss := "The number types one carrier-parametric definition is instantiated at, \
                ordered from proof to execution — the reals for proof, binary32 as the \
                rounding specification, `Float` for execution, the tape for the kernel — \
                each a rung, reached from the abstract carrier by one map. Laws survive \
                the climb up to one rounding per operation; side conditions phrased in a \
                carrier's own arithmetic do not survive it at all.",
      decls := [`PropertyKindCalculus.Carrier, `PropertyKindCalculus.CarrierRefinement],
      definedIn := "representation-parametricity",
      seeAlso := ["license clause", "recording carrier", "denotation bridge"] }
  , { key := "license clause",
      gloss := "The part of a measurement-model relation that extends its witness beyond \
                the carrier rung it is proved at: one entry per further rung, each a named \
                repair theorem — exact, where rounding is the identity on the values in \
                play, or nonneg, where nonnegative on-grid weights rule cancellation out — \
                or an independent witness restated at that rung; a rung with neither is \
                refused.",
      decls := [`PropertyKindCalculus.Provenance.RelationLicense,
                `PropertyKindCalculus.Provenance.TransferStatus],
      definedIn := "metrological-modularity",
      seeAlso := ["carrier ladder", "measurement model", "metrology module"] }
  , { key := "requirement",
      gloss := "What a metrology module's quantities must satisfy, stated as data beside the \
                declared boundary it governs: the statement in the author's words, the \
                governed boundary and port, the objects it quantifies over, and the evidence \
                by which it is met — provable or empirical, or attested with a reason.",
      decls := [`PropertyKindCalculus.Provenance.Requirement],
      definedIn := "metrological-modularity",
      seeAlso := ["provable requirement", "empirical requirement", "requirement scope",
                  "declared boundary"] }
  , { key := "provable requirement",
      gloss := "A requirement whose statement closes over the model's own declarations and \
                kinded quantities, so a theorem about the model discharges it: a theorem edge \
                from the governed boundary to a specification boundary, or a theorem, with \
                spot checks where the model runs; a negative one, by the absence of a \
                license.",
      decls := [`PropertyKindCalculus.Provenance.RequirementKind],
      definedIn := "metrological-modularity",
      seeAlso := ["empirical requirement", "specification boundary", "spot check",
                  "measurement model"] }
  , { key := "empirical requirement",
      gloss := "A requirement whose statement names a referent the model does not define, so \
                no theorem about the model alone can discharge it — the falsifiable kind, \
                discharged by a gate against the referent or deferred by an attestation.",
      decls := [`PropertyKindCalculus.Provenance.RequirementKind],
      definedIn := "metrological-modularity",
      avoid := ["falsifiable requirement", "validation requirement",
                "observational requirement", "testable requirement"],
      seeAlso := ["referent", "provable requirement", "attestation"] }
  , { key := "referent",
      gloss := "A kinded quantity the model does not define — a datasheet value, a prior, a \
                reference measurement — marked `@[kindReferent]` with where it comes from: \
                what an empirical requirement is decided against, and what a provable \
                requirement's statement may not name.",
      decls := [`PropertyKindCalculus.Provenance.Requirement.referents],
      definedIn := "metrological-modularity",
      seeAlso := ["empirical requirement", "attestation"] }
  , { key := "requirement scope",
      gloss := "The objects a requirement quantifies over: every object the boundary is \
                evaluated for, every object of a named sort (reached through `Sorted`), \
                named objects, or the objects a named decider selects.",
      decls := [`PropertyKindCalculus.Provenance.RequirementScope],
      definedIn := "metrological-modularity",
      seeAlso := ["requirement"] }
  , { key := "spot check",
      gloss := "A named `Bool` declaration a provable requirement cites and the requirement \
                command evaluates, requiring `true`: the runtime evidence that the proof \
                reaches the carrier the model runs on and the operational inputs — a check \
                of the proof's reach, not a discharge.",
      decls := [`PropertyKindCalculus.Provenance.Requirement.spotChecks],
      definedIn := "metrological-modularity",
      seeAlso := ["provable requirement", "carrier ladder"] }
  , { key := "specification boundary",
      gloss := "A declared boundary whose one member computes the bound a requirement is \
                checked against, told from a model boundary by its role: the right side of a \
                provable requirement's theorem edge, and itself the subject of no \
                requirement.",
      decls := [`PropertyKindCalculus.Provenance.BoundaryRole,
                `PropertyKindCalculus.Provenance.Contract.role],
      definedIn := "metrological-modularity",
      seeAlso := ["declared boundary", "provable requirement"] }
  , { key := "kind-of-property",
      short := some "kind",
      gloss := "The common defining aspect of mutually comparable properties, carried as a \
                type index of every quantity; a kind-of-quantity when its scale has \
                magnitude.",
      decls := [`PropertyKindCalculus.KindOfProperty],
      definedIn := "proved-spine",
      seeAlso := ["metrological provenance hypergraph"] }
  , { key := "tape",
      gloss := "Automatic differentiation's word for the record of the operations a program \
                performs, in the order it performs them: a grow-only array of nodes, each \
                one operation with its parent ids in operand order and its forward value, \
                every operation appending one node. A carrier-generic module writes one when \
                instantiated at the recording carrier; the calculus reads it forward and \
                never runs the backward pass the name comes from. A straight-line program, \
                not a graph, with kinds erased.",
      decls := [`Runtime.Autograd.Tape, `PropertyKindCalculus.Paradigm.TapeBuilder],
      definedIn := "capstones",
      seeAlso := ["computational tape graph", "recording carrier", "compacted tape",
                  "denotation bridge"] }
  , { key := "computational tape graph",
      short := some "tape graph",
      gloss := "The unkinded, computational counterpart of the metrological provenance \
                hypergraph: the directed acyclic graph a tape determines, one vertex per \
                tape node, an edge from each parent to its node, in-edges ordered as the \
                parents are; leaves are the named inputs and the baked constants, roots the \
                recorded outputs. A tape node is its own operation, so a vertex's ordered \
                in-edges are the one hyperedge into it and the hypergraph reading adds \
                nothing — unlike the provenance hypergraph, whose occurrences are objects \
                apart from its nodes. The object the second capstone relates to the \
                provenance hypergraph.",
      decls := [`PropertyKindCalculus.Paradigm.TapeGraph,
                `PropertyKindCalculus.Paradigm.TapeCodegen.ofTape, `Runtime.Autograd.Node],
      definedIn := "capstones",
      avoid := ["computational graph", "elementwise DAG", "megakernel DAG"],
      seeAlso := ["tape", "metrological provenance hypergraph",
                  "kind-transporting weak bisimulation", "compacted tape"] }
  , { key := "recording carrier",
      gloss := "The carrier whose values are thunks appending their sub-expression to a \
                tape; instantiating a module at it builds the module's tape.",
      decls := [`PropertyKindCalculus.Paradigm.TapeBuilder],
      definedIn := "capstones",
      seeAlso := ["tape"] }
  , { key := "compacted tape",
      gloss := "A tape after its identical sub-expressions are merged: the object the code \
                generator lowers to one kernel.",
      decls := [`PropertyKindCalculus.Paradigm.TapeCSE.cseCompact],
      definedIn := "capstones",
      seeAlso := ["tape"] }
  , { key := "denotation bridge",
      gloss := "The predicate relating a recording-carrier value to the tensor it computes, \
                preserved by every carrier operation, so that a module's parity with its own \
                eager value is a chain of per-operation lemmas.",
      decls := [`PropertyKindCalculus.Paradigm.TapeParity.Evaluates],
      definedIn := "capstones",
      seeAlso := ["tape", "seal of the computation"] }
  , { key := "kind-transporting weak bisimulation",
      short := some "bisimulation",
      gloss := "The relation tying the two graphs of one module together: the metrological \
                provenance hypergraph, harvested from the source, where every kind \
                originates, and the computational tape graph, recorded by evaluation, which \
                carries none. It matches sources to leaves and each occurrence to the tape \
                sub-graph realizing its family; weak because it is silent on the interior \
                of a carrier-level expansion, a bisimulation because it simulates in both \
                directions — every occurrence realized on the tape, every tape path \
                projected to a hypergraph path — and along it the hypergraph's kinds are \
                transported onto the tape graph. A weak bisimulation in the textbook sense, \
                over labelled transition systems: the provenance layer's hops labelled by \
                family and operand position, the tape's edges labelled through the match, \
                wires and interior steps silent. As data it is a match — each node with the \
                tape vertices realizing it, each occurrence with the interior of its \
                sub-graph — whose acceptance is decidable.",
      decls := [`PropertyKindCalculus.Paradigm.Match, `PropertyKindCalculus.Paradigm.Match.accepts,
                `PropertyKindCalculus.Paradigm.Match.weak,
                `PropertyKindCalculus.Paradigm.Match.isWeakBisimulation_weak],
      definedIn := "capstones",
      avoid := ["kind-transporting simulation"],
      seeAlso := ["metrological provenance hypergraph", "computational tape graph",
                  "contracted tape graph", "propagation relation", "seal of the computation"] }
  , { key := "contracted tape graph",
      gloss := "The computational tape graph with each realized occurrence's sub-graph \
                collapsed to one ordered hyperedge — its operands the sub-graph's frontier \
                in operand order, its results the sub-graph's roots, its label the family; \
                defined under the clauses acceptance decides of the sub-graphs — closed, \
                interior-private, progressing, used, pairwise disjoint, covering every \
                operation. On it the kind-transporting weak bisimulation becomes strong, \
                the silent steps gone.",
      decls := [`PropertyKindCalculus.Paradigm.Match.contracted,
                `PropertyKindCalculus.Paradigm.Match.isBisimulation_contracted],
      definedIn := "capstones",
      seeAlso := ["computational tape graph", "kind-transporting weak bisimulation"] }
  , { key := "seal of a module",
      gloss := "The first capstone: once a module's gates are declared, every leaf of an \
                output's pedigree is a declared source — no undeclared raw datum reaches \
                the outputs.",
      decls := [`PropertyKindCalculus.Provenance.pedigree_seal,
                `PropertyKindCalculus.Provenance.sealed],
      definedIn := "capstones",
      seeAlso := ["seal of the computation", "pedigree"] }
  , { key := "seal of the computation",
      gloss := "The second capstone: the seal of a module carried onto the computational \
                tape graph at every carrier — an output depends only on its influencers and \
                the listed constants, and every kind change in the computation is one an \
                occurrence of the hypergraph states.",
      decls := [`PropertyKindCalculus.Paradigm.TapeSeal.semantic_seal],
      definedIn := "capstones",
      seeAlso := ["seal of a module", "kind-transporting weak bisimulation",
                  "denotation bridge"] }
  , { key := "dimensional homogeneity",
      gloss := "The third capstone: along every occurrence of a well-formed provenance \
                hypergraph the dimension of the result is the one the family's rule \
                computes from the operands — dimension is a homomorphism along every path.",
      decls := [`PropertyKindCalculus.DimensionalHomogeneity.dimensional_homogeneity,
                `PropertyKindCalculus.Provenance.homogeneity,
                `PropertyKindCalculus.InteractionAlgebra.dim_homomorphism],
      definedIn := "capstones",
      seeAlso := ["seal of a module"] }
  , { key := "blueprint dependency graph",
      short := some "dependency graph",
      gloss := "The graph of this blueprint's own nodes and their `uses` edges — a \
                rendering of the document, and not one of the graphs the calculus defines.",
      definedIn := "how-to-read-the-status",
      seeAlso := ["metrological provenance hypergraph", "value-flow digraph", "tape",
                  "computational tape graph"] }
  ]

/-- The canonical phrases. -/
def keys : List String := dictionary.map (·.key)

/-- Every canonical phrase occurs once. -/
def uniqueKeys : Bool := keys.all fun k => (keys.filter (· == k)).length == 1

/-- Every `seeAlso` names an entry. -/
def seeAlsoResolve : Bool := dictionary.all fun t => t.seeAlso.all keys.contains

/-- No retired phrasing is a canonical phrase or a sanctioned short form of any entry. -/
def avoidDisjoint : Bool :=
  dictionary.all fun t => t.avoid.all fun a =>
    !(keys.contains a) && !(dictionary.any fun u => u.short == some a)

#guard uniqueKeys
#guard seeAlsoResolve
#guard avoidDisjoint

/-- Look up an entry by its canonical phrase. -/
def termByKey? (k : String) : Option Term := dictionary.find? (·.key == k)

/-- The retired-phrasing sites that remain in the library's own docstrings and comments, as
`scripts/check-doc-pins.py` counts them. A ratchet, in the sense of the mint ratchet: the
gate fails when the count differs from this pin in either direction — a rise is a
regression, a fall asks for the pin to be lowered in the same change — so the number can
only move by a conscious edit. -/
def libraryRetiredSites : Nat := 22

end PropertyKindCalculus.Terminology

end Blanket
