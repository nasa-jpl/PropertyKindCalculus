/-
Copyright (c) 2026 California Institute of Technology. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nicolas Rouquette
-/
import PropertyKindCalculus.Index.Basic
import PropertyKindCalculus.DocGenMath.Attr

/-!
# The annotation catalogue and where each annotation is used

PropertyKindCalculus asks an author to state three kinds of thing that cannot be inferred:

* **where the calculus is left** — a kind crossing, a carrier-vocabulary exception, an emission.
  These are *checked*: `#kind_boundary_audit` fails on a boundary site that carries no tier, so the
  annotation is not documentation, it is the discharge of a proof obligation about the code.
* **how a definition should read** — the rendering family, which turns a `Quantity` definition into
  typeset mathematics in its own docstring.
* **what an external document says** — the requirement and cross-reference families, which are
  indexed by machinery that already exists (`{traceability}`, `{crossrefs}`).

The catalogue below is the first of those three lists made explicit, and it is curated *text*: what
an annotation means is not derivable from its registration. What is derivable — and therefore
harvested rather than listed — is **where each one is used**, which is what `annotationUses` returns.

The catalogue is the single place a new annotation must be added for the "Using the library" chapter
to describe it. That is a deliberate cost: one edit, in one file, next to the others, rather than a
chapter that silently omits an annotation nobody remembered to document.
-/

namespace PropertyKindCalculus.Index

open Lean Meta

/-! ## The catalogue -/

/-- Is an annotation enforced by a build-time check, or is it advisory metadata? The distinction the
chapter has to make first: `@[kindCrossing]` discharges an obligation the audit would otherwise fail
on, whereas `@[pkc_math_symbol]` changes only how something reads. -/
inductive Enforcement where
  /-- A build-time check fails without it, or rejects a misuse of it. -/
  | checked (by_ : String)
  /-- It changes rendering or records metadata; nothing fails if it is absent. -/
  | advisory
deriving Repr, Inhabited, BEq

/-- How an annotation's enforcement reads in the table. -/
def Enforcement.description : Enforcement → String
  | .checked by_ => s!"checked — {by_}"
  | .advisory    => "advisory"

/-- One annotation of the library's surface. -/
structure Annotation where
  /-- How it is written, as an author writes it. -/
  syntax_ : String
  /-- What it may be attached to. -/
  attachesTo : String
  /-- What it does, in one sentence. -/
  effect : String
  /-- Whether a build-time check depends on it. -/
  enforcement : Enforcement
  /-- The index table listing its occurrences, or `""` when another index already covers it. -/
  table : String
  /-- The tag of the document section that documents it, or `""` when none does. A reference table
  whose rows do not reach the prose that explains them is a table a reader has to search *around*,
  so the catalogue carries the link target rather than leaving each document to re-derive it.
  Documents that define no section by this tag fall back to rendering the syntax as inline code. -/
  section_ : String := ""
deriving Repr, Inhabited

/-- Every annotation PropertyKindCalculus defines.

Grouped as the chapter presents them: the boundary family (checked), the rendering family
(advisory), and the metadata family (advisory, and indexed by the pre-existing `{traceability}` and
`{crossrefs}` directives rather than duplicated here). -/
def catalogue : Array Annotation := #[
  -- The boundary family — invariants 4, 6 and 7.
  { syntax_ := "@[kindCrossing]", attachesTo := "a definition"
    effect := "Two kinds can meet in two ways. Under a *law* — an authored edge such as \
      `ProductKind k₁ k₂ k` or a `KindMul` entry — the calculus derives a third kind from two, and \
      the use site needs no annotation, because the edge already licenses it. A *crossing* is the \
      case no law covers: a value already carrying one kind is re-typed as another on the author's \
      signature rather than on a derivation. An edge is a rule the calculus applies; a crossing is \
      a place the calculus is left, which is why it must be declared and why the audit counts it. \
      Both kinds are stated in the signature, on the argument side as much as the result; the mint \
      or erasure inside is the crossing's mechanism, reviewed once."
    enforcement := .checked "rejected at elaboration if no argument carries a registered carrier; \
      #kind_boundary_audit also reports an untagged boundary site as a violation"
    table := "crossings"
    section_ := "annotation-kindCrossing" },
  { syntax_ := "@[kindIngest]", attachesTo := "a definition"
    effect := "Declares a checked ingest mint: raw external/host data enters the calculus for the \
      first time, admitted through some check. The dual of @[kindCrossing] — no argument need \
      carry a kind, because none has been established yet."
    enforcement := .checked "#kind_boundary_audit reports an untagged boundary site as a violation"
    table := "crossings"
    section_ := "annotation-kindIngest" },
  { syntax_ := "@[kindConst]", attachesTo := "a definition"
    effect := "Declares a constant mint: an adjudicated value enters the calculus as data — a \
      cited table, a configuration bound, a seed, a threshold, or a structural constant."
    enforcement := .checked "#kind_boundary_audit reports an untagged boundary site as a violation"
    table := "crossings"
    section_ := "annotation-kindConst" },
  { syntax_ := "@[carrierVocab]", attachesTo := "a definition"
    effect := "Registers kind-preserving representation plumbing — an operation the kind algebra \
      does not name (a branchless min, a map over a coefficient table) that must drop to the carrier."
    enforcement := .checked "#kind_boundary_audit reports an untagged boundary site as a violation"
    table := "crossings"
    section_ := "annotation-carrierVocab" },
  { syntax_ := "@[kindEmission]", attachesTo := "a definition"
    effect := "Marks a genuine emission boundary: a kinded value becomes a naked one for a consumer \
      outside the calculus (a deploy driver, a tape recorder)."
    enforcement := .checked "#kind_boundary_audit reports an untagged boundary site as a violation"
    table := "crossings"
    section_ := "annotation-kindEmission" },
  { syntax_ := "@[kindCarrier]", attachesTo := "a structure"
    effect := "Registers a downstream single-field quantity-like carrier, so the boundary audit \
      recognizes its mints and erasures — and so its records and operations are indexed."
    enforcement := .checked "rejected at elaboration if the declaration is not a structure"
    table := "carriers"
    section_ := "annotation-kindCarrier" },
  { syntax_ := "@[kindCounterexample]", attachesTo := "a Provenance.Contract or \
      Provenance.Relation definition"
    effect := "Marks a deliberate provenance counterexample — a falsification probe kept because \
      its checker refuses it. The by-type sweeps (#kind_contracts, #kind_contracts_decide, \
      #kind_relations) list it as exempted instead of gating on it, and the contracts and \
      provenance-coverage tables neither count it as a witness nor as a coverage subject."
    enforcement := .checked "rejected at elaboration if the declaration is not a \
      Provenance.Contract or Provenance.Relation"
    table := ""
    section_ := "annotation-kindCounterexample" },
  -- The rendering family — RENDERING.md.
  { syntax_ := "@[pkc_math]", attachesTo := "a Quantity-valued definition"
    effect := "Renders the definition as typeset LaTeX into its own docstring, so doc-gen4 and the \
      InfoView display the equation. Clauses `keeping` and `substituting` control let-bindings and \
      derivations; a literal string argument overrides the rendering entirely."
    enforcement := .checked "rejected if `keeping` names an unbound let, if `substituting` names a \
      recursive definition, or if a literal override is combined with either clause"
    table := "pkc-math"
    section_ := "annotation-pkc-math" },
  { syntax_ := "@[pkc_math_symbol \"…\"]", attachesTo := "any declaration"
    effect := "Fixes the LaTeX a token renders as, overriding every naming heuristic. The optional \
      `operator` modifier prints a one-argument application as juxtaposition rather than a call."
    enforcement := .advisory
    table := "pkc-math-symbol"
    section_ := "annotation-pkc-math-symbol" },
  { syntax_ := "@[pkc_math_config]", attachesTo := "a structure"
    effect := "Declares a configuration type: its field projections render as the qualified constant \
      `Struct.field` rather than as a function applied to the configuration value."
    enforcement := .checked "rejected at elaboration if the declaration is not a structure"
    table := "pkc-math-config"
    section_ := "annotation-pkc-math-config" },
  { syntax_ := "@[pkc_math_transparent]", attachesTo := "a definition"
    effect := "Marks a notational wrapper the renderer should see through, so the wrapped term is \
      rendered in place of a call to the wrapper."
    enforcement := .advisory
    table := "pkc-math-transparent"
    section_ := "annotation-pkc-math-transparent" },
  -- The metadata family — already indexed by their own directives.
  { syntax_ := "@[requirement \"…\" role]", attachesTo := "any declaration"
    effect := "Records that the declaration specifies, proves, implements or exemplifies a numbered \
      requirement."
    enforcement := .advisory
    table := ""
    section_ := "annotations-metadata-family" },
  { syntax_ := "@[dybkaer \"…\" \"…\"]", attachesTo := "any declaration"
    effect := "Records the Dybkær *Ontology on Property* section and term this declaration formalizes."
    enforcement := .advisory
    table := ""
    section_ := "annotations-metadata-family" },
  { syntax_ := "@[vim4 \"…\" \"…\"]", attachesTo := "any declaration"
    effect := "Records the VIM 4 2CD entry and term this declaration corresponds to."
    enforcement := .advisory
    table := ""
    section_ := "annotations-metadata-family" },
  -- The examination-coverage exception (Dimension library) — the declared negative of M6.
  { syntax_ := "@[kindPrincipleFree \"…\"]", attachesTo := "a `DimensionedKind` definition"
    effect := "Declares that a dimension-one kind is legitimately without an examination \
      principle, with the reason: `#kind_examination_coverage` lists it as exempted and \
      `#kind_examination_clean` does not fire on it. Inert on a kind that carries a principle."
    enforcement := .checked "rejected at elaboration unless the declaration is a \
      `DimensionedKind` and the reason is non-empty"
    table := ""
    section_ := "" },
  -- The declared exceptions of the boundary censuses — M12's and M21's honest negatives.
  { syntax_ := "@[kindRelationFree \"…\"]", attachesTo := "a `Provenance.Contract` definition"
    effect := "Declares that a boundary legitimately has no theorem edge — its behavior is not \
      a measurement model — with the reason: `#kind_relation_coverage` lists it as exempted \
      and `#kind_relation_clean` does not fire on it. Inert on a boundary an edge names."
    enforcement := .checked "rejected at elaboration unless the declaration is a \
      `Provenance.Contract` and the reason is non-empty"
    table := ""
    section_ := "" },
  { syntax_ := "@[kindInversionTotal \"…\"]", attachesTo := "a `Provenance.Contract` definition"
    effect := "Declares that an inverted boundary legitimately has no conditional port — the \
      inversion is total on its input type — with the reason: `#kind_inversion_coverage` \
      lists it as exempted and `#kind_inversion_clean` does not fire on it. Inert on a \
      boundary that declares a conditional port."
    enforcement := .checked "rejected at elaboration unless the declaration is a \
      `Provenance.Contract` and the reason is non-empty"
    table := ""
    section_ := "" },
  { syntax_ := "@[kindDiagnostic \"…\"]", attachesTo := "a `KindOfProperty` definition"
    effect := "Declares a kind to be a quality or conditioning output a consumer must read, \
      with what it diagnoses: `#kind_diagnostic_coverage` then asks the declared boundaries \
      in scope for a produced port carrying it. The mark is the census's enrollment — an \
      unmarked kind is not walked, and removing a mark is the exemption."
    enforcement := .checked "rejected at elaboration unless the declaration is a \
      `KindOfProperty` and the description is non-empty"
    table := ""
    section_ := "" }]

/-- The annotation reference table. Pure data — it describes the surface, and so needs no
environment.

The first column links into the prose that explains each annotation, so the table is an entry point
rather than a summary a reader has to leave in order to use. A document that defines no section by
the recorded tag renders the syntax as inline code, exactly as before. -/
def annotationsTable : IndexTable :=
  { id := "annotations"
    title := "The annotations PropertyKindCalculus defines"
    headers := #["Annotation", "Attaches to", "Effect", "Enforcement"]
    rows := catalogue.map fun a => #[
      if a.section_.isEmpty then .code a.syntax_ else .tag a.section_ a.syntax_,
      .text a.attachesTo, .prose a.effect,
      .prose a.enforcement.description] }

/-! ## The commands

The annotations state what an author *declares*; the commands are what an author *asks*. Both are
curated text for the same reason — what a command is for is not derivable from its `elab` — and both
are listed here so that neither can be added to the library and silently missed by the chapter that
documents the surface.

The distinction the table draws is between a command that is merely *read* and one that is
**pinned**. `#kind_edges` answers a question; `#kind_boundary_audit` answers a question that a probe
file freezes with `#guard_msgs`, at which point the answer changing is a build failure. That is what
makes the audits part of the type discipline rather than reports about it. -/

/-- One command of the library's surface. -/
structure Command where
  /-- How it is written, as an author writes it. -/
  syntax_ : String
  /-- The library that defines it — which decides what a document must import to run it. -/
  library : String
  /-- What it answers, in one sentence. -/
  effect : String
  /-- What pinning it with `#guard_msgs` buys, or `""` if it is a reading aid rather than a gate. -/
  gate : String
  /-- The tag of the document section that documents it, or `""` when none does. -/
  section_ : String := ""
deriving Repr, Inhabited

/-- Every command PropertyKindCalculus defines, ordered so that each base command is followed by
its suffixed forms, and grouped as the chapter presents them: the boundary audit, the edge audits,
the kind graph, the per-declaration incidence queries, the provenance layer, and the index readers.

Three forms recur, and the suffix names which one a command is. A bare command *reads* — the answer
goes to the InfoView. A `#guard_msgs`-pinned reading becomes a *record*: the whole answer is
reviewable in the diff, and a changed answer fails the build. A `_clean` command is the *gate* that
a record cannot be: it carries no message and pins nothing, it throws, so there is nothing to
re-bless. `_decide` is the third form — the same check run in the kernel, leaving a theorem behind
rather than a message. -/
def commands : Array Command := #[
  -- The boundary audit — the record, then the two gates a record cannot be.
  { syntax_ := "#kind_boundary_audit ns …", library := "PropertyKindCalculus"
    effect := "Walks every compute definition in the namespaces and reports each that mints or \
      erases a registered carrier, with the kinds it mints and the tier that sanctions it; an \
      untagged boundary site is reported as a violation."
    gate := "a new anonymous interior mint fails the build, the way a new axiom fails a pinned \
      axiom profile"
    section_ := "boundary-family" },
  { syntax_ := "#kind_boundary_clean ns …", library := "PropertyKindCalculus"
    effect := "The invariant rather than the inventory: throws when any boundary-active \
      declaration in scope carries no tier attribute. It carries no message and pins nothing, so \
      re-blessing the audit's pin cannot silence it."
    gate := "the command is the gate; there is no message to re-bless"
    section_ := "boundary-family" },
  { syntax_ := "#kind_mint_ratchet ns …", library := "PropertyKindCalculus"
    effect := "Throws on a raw carrier mint inside a @[kindCrossing] or @[carrierVocab] body, \
      where every mint must instead be a licensed derivation or a Quantity.attest whose reason is \
      harvested. @[kindConst], @[kindIngest] and @[kindEmission] keep raw mints legal at the \
      declaration granularity."
    gate := "the command is the gate; at the ratcheted tiers a new anonymous mint fails the build \
      instead of joining a list nobody re-reads"
    section_ := "boundary-family" },
  { syntax_ := "#kind_crossings [ns …]", library := "PropertyKindCalculus"
    effect := "Enumerates the tagged boundary registry — every sanctioned site with the first line \
      of its docstring, grouped by tier."
    gate := ""
    section_ := "boundary-family" },
  -- The edge audits — the coverage record, then its gate.
  { syntax_ := "#kind_edges k", library := "PropertyKindCalculus"
    effect := "Prints every authored kind-algebra edge mentioning the kind `k` — named witness \
      theorems, call-site witnesses lifted out of definitions, and operator-table registrations."
    gate := "the complete set of edges a kind supports is fixed, so a new one is a visible change"
    section_ := "edge-audits" },
  { syntax_ := "#kind_dimensional_coverage ns …", library := "Dimension"
    effect := "Resolves every authored edge's kinds to their declared DimensionedKind and evaluates \
      the family's dimensional rule, reporting each edge as coherent, parametric, undimensioned, \
      conflicting, or incoherent."
    gate := "an edge over a kind carrying no dimension, or one whose dimensions do not balance, \
      fails the build"
    section_ := "edge-audits" },
  { syntax_ := "#kind_dimensional_clean ns …", library := "Dimension"
    effect := "The coverage invariant rather than its record: throws while any edge in scope is \
      undimensioned, conflicting or incoherent. Parametric generic vocabulary is not a violation. \
      Its one false alarm is an under-imported closure, which the error says."
    gate := "the command is the gate; there is no message to re-bless"
    section_ := "edge-audits" },
  -- The examination census — the model template's M6 as a walk, then its gate.
  { syntax_ := "#kind_examination_coverage ns …", library := "Dimension"
    effect := "Walks every dimension-one `DimensionedKind` in the namespaces and reports each as \
      individuated by its examination principle, exempted by an `@[kindPrincipleFree]` mark, or \
      UNINDIVIDUATED — the census behind the model template's M6, which the dimension functor \
      cannot supply because it sends every such kind to `1`."
    gate := "a dimension-one kind declared without a principle or a mark fails the pin"
    section_ := "" },
  { syntax_ := "#kind_examination_clean ns …", library := "Dimension"
    effect := "The census as a gate: throws while any dimension-one kind in scope carries neither \
      an examination principle nor a declared exemption. Records an audit receipt exactly when \
      it does not fire, which is what lets a document's M6 read green only in a build where the \
      census ran."
    gate := "the command is the gate; there is no message to re-bless"
    section_ := "" },
  -- The boundary censuses (core) — M12, M15, and M21's domain half, each a record and a gate.
  { syntax_ := "#kind_relation_coverage ns …", library := "PropertyKindCalculus"
    effect := "Walks every `Provenance.Contract` in the namespaces and reports each as witnessed \
      by the theorem edges naming it (relations walked unscoped, counterexamples excluded), \
      exempted by a `@[kindRelationFree]` mark, or UNWITNESSED — the census behind M12."
    gate := "a boundary declared anywhere in scope that no edge names fails the pin"
    section_ := "" },
  { syntax_ := "#kind_relation_clean ns …", library := "PropertyKindCalculus"
    effect := "The census as a gate: throws while any declared boundary in scope is unwitnessed \
      and unexempted. Records an audit receipt exactly when it does not fire."
    gate := "the command is the gate; there is no message to re-bless"
    section_ := "" },
  { syntax_ := "#kind_mereology_coverage ns …", library := "PropertyKindCalculus"
    effect := "Walks every produced port (`output` or `conditional`) of every `Provenance.Contract` \
      in the namespaces and reports each as classed by its declared aggregation class or \
      UNDECLARED — the census behind M15. No exception mark: the class vocabulary names \
      every honest negative."
    gate := "a produced port with no `aggregations` entry fails the pin"
    section_ := "" },
  { syntax_ := "#kind_mereology_clean ns …", library := "PropertyKindCalculus"
    effect := "The census as a gate: throws while any produced port in scope carries no \
      aggregation class. Records an audit receipt exactly when it does not fire."
    gate := "the command is the gate; there is no message to re-bless"
    section_ := "" },
  { syntax_ := "#kind_inversion_coverage ns …", library := "PropertyKindCalculus"
    effect := "Walks every `Provenance.Contract` in the namespaces that an `inverts` edge names as \
      its left side and reports each as guarded by a `conditional` port (with its decider \
      where named), exempted by a `@[kindInversionTotal]` mark, or UNGUARDED — the census \
      behind M21's domain half."
    gate := "an inverted boundary with no conditional port and no exemption fails the pin"
    section_ := "" },
  { syntax_ := "#kind_inversion_clean ns …", library := "PropertyKindCalculus"
    effect := "The census as a gate: throws while any inverted boundary in scope is unguarded \
      and unexempted. Records an audit receipt exactly when it does not fire."
    gate := "the command is the gate; there is no message to re-bless"
    section_ := "" },
  { syntax_ := "#kind_wellposedness_coverage ns …", library := "PropertyKindCalculus"
    effect := "Walks every `inverts` edge (`Provenance.Relation`) in the namespaces and reports \
      each as well-posed by its `wellPosed` witness on its declared `domain`, surfaced by its \
      `ambiguity` witness, or UNDECIDED — the census behind M20 and M21's ambiguity half. No \
      exception mark: the two fields are total over the honest negatives."
    gate := "an inverts edge declaring neither a well-posedness nor an ambiguity fails the pin"
    section_ := "" },
  { syntax_ := "#kind_wellposedness_clean ns …", library := "PropertyKindCalculus"
    effect := "The census as a gate: throws while any `inverts` edge in scope answers for its \
      inversion with neither a well-posedness witness nor a surfaced ambiguity. Records an \
      audit receipt exactly when it does not fire."
    gate := "the command is the gate; there is no message to re-bless"
    section_ := "" },
  { syntax_ := "#kind_diagnostic_coverage ns …", library := "PropertyKindCalculus"
    effect := "Walks every `@[kindDiagnostic]`-marked kind in the namespaces and reports each \
      as exported by the produced ports carrying it or SIDECHANNELED — the census behind \
      M22. Enrollment is the mark, so a scope with no marks records that visibly."
    gate := "a marked kind no declared boundary exports fails the pin"
    section_ := "" },
  { syntax_ := "#kind_diagnostic_clean ns …", library := "PropertyKindCalculus"
    effect := "The census as a gate: throws while any diagnostic kind in scope is carried by \
      no produced port. Records an audit receipt exactly when it does not fire."
    gate := "the command is the gate; there is no message to re-bless"
    section_ := "" },
  -- The kind graph — the component report, its gate, and its diagram twin.
  { syntax_ := "#kind_scc [ns …]", library := "Graph"
    effect := "The kind-level component report: the authored kinds in scope, their \
      licensed-derivation edge count, every inter-derivability cluster of two or more kinds with \
      the edges that wire it, and whether the kind digraph is acyclic."
    gate := "the reviewed enumeration to pin beside #kind_edges — a new cluster is a visible change"
    section_ := "graph-incidence" },
  { syntax_ := "#kind_scc_clean [ns …] [(k …) …]", library := "Graph"
    effect := "Inter-derivability as a gate: every cluster of two or more mutually derivable kinds \
      must be declared as a parenthesized group at the same size; an undeclared cluster throws \
      with its wiring printed."
    gate := "a new witness registration that merges two kind roles fails the build at the \
      vocabulary level, before any value walks the new cycle"
    section_ := "graph-incidence" },
  { syntax_ := "#kind_scc_d2 \"dir\" [ns …]", library := "Graph"
    effect := "Writes the D2 diagram sources of the component findings into a directory — the \
      condensation and one file per inter-derivability cluster. The script-facing twin of \
      #kind_scc, run from a `lake env lean` driver."
    gate := ""
    section_ := "graph-incidence" },
  { syntax_ := "#kind_footprint c ns…", library := "Graph"
    effect := "The SCC footprint of a declared boundary against the kind graph: the component \
      partition of its port and interior kinds, the same-kind port groups, the review-strength \
      sites, and the verdict naming where the module's guarantee comes from."
    gate := "the boundary's exposure to inter-derivability is fixed, so a widened footprint is a \
      visible change"
    section_ := "graph-incidence" },
  -- Per-declaration incidence — what one definition's signature and body state.
  { syntax_ := "#kind_ports d", library := "PropertyKindCalculus"
    effect := "Prints every port a declaration's kind-typed signature states — inputs, \
      configuration reads, outputs, each with its stated kind — followed by the signature's \
      unkinded positions."
    gate := "a port that changes kind, or an unkinded position that appears, fails the pin"
    section_ := "graph-incidence" },
  { syntax_ := "#kind_occurrences d", library := "PropertyKindCalculus"
    effect := "Prints every authored license discharged inline in a declaration's value — each \
      consuming application's edge with the operand quantities that met there, in body order, \
      with multiplicity."
    gate := "the licenses a body actually discharges are fixed, so a new one is a visible change"
    section_ := "graph-incidence" },
  { syntax_ := "#kind_graph d", library := "PropertyKindCalculus"
    effect := "Prints the constructed step graph — ports, introduction events, wired occurrences \
      with their assumed/partial markers, exits — and the evaluated well-formedness verdict."
    gate := "the wiring is fixed, so a rewired body is a visible change"
    section_ := "graph-incidence" },
  { syntax_ := "#kind_graph_decide d", library := "PropertyKindCalculus"
    effect := "Reflects the constructed graph into a term and adds the theorem `d.kindGraphWf`, \
      proved by `decide` — kernel reduction of the structural checker on the harvested object. \
      Errors out before troubling the kernel when the graph is not well-formed."
    gate := "the command is the gate; the pin freezes the kernel receipt"
    section_ := "graph-incidence" },
  { syntax_ := "#kind_assembly [d₁, d₂, …]", library := "PropertyKindCalculus"
    effect := "Assembles the listed declarations into one multi-step graph and prints it — each \
      level with its inclusion mode, the union graph, the citation relation, and the evaluated \
      verdict."
    gate := "the assembled wiring is fixed across the whole set, not one declaration at a time"
    section_ := "graph-incidence" },
  { syntax_ := "#kind_assembly_decide [d₁, d₂, …]", library := "PropertyKindCalculus"
    effect := "Reflects the assembled union graph into a term and adds the theorem \
      `d₁.kindAssemblyWf`, proved by `decide`. Errors out before troubling the kernel when the \
      assembly is not well-formed."
    gate := "the command is the gate; the pin freezes the kernel receipt"
    section_ := "graph-incidence" },
  -- The provenance layer — one contract, then the by-type sweep; the same for edges.
  { syntax_ := "#kind_contract c", library := "PropertyKindCalculus"
    effect := "Assembles the members a contract declares and compares that assembly's boundary \
      with the boundary the contract declares — parameters and decided conditional ports, then \
      what each side has and the other does not, then the verdict. Where #kind_assembly says the \
      wiring holds together, this says the members are the ones the declared interface belongs to."
    gate := "a boundary that stops being the one its members compute fails the pin"
    section_ := "provenance-sweeps" },
  { syntax_ := "#kind_contract_decide c", library := "PropertyKindCalculus"
    effect := "Adds the theorem `c.kindContractOk : c.Agrees (graph)`, proved by `decide` — kernel \
      reduction of the boundary comparison against the author's own contract definition, which the \
      proposition names rather than copies. Errors out when the boundaries disagree."
    gate := "the command is the gate; the pin freezes the kernel receipt"
    section_ := "provenance-sweeps" },
  { syntax_ := "#kind_contracts ns …", library := "PropertyKindCalculus"
    effect := "Surveys every `Provenance.Contract` declared under the namespaces — membership is \
      by type, so declaring a boundary enrolls it — re-checking each as `#kind_contract` does, \
      with violations as ✗ rows and `@[kindCounterexample]` declarations as exempted ⊘ rows."
    gate := "a boundary declared anywhere in scope and inconsistent with what its members \
      compute fails the pin, including one nobody remembered to check by name"
    section_ := "provenance-sweeps" },
  { syntax_ := "#kind_contracts_decide ns …", library := "PropertyKindCalculus"
    effect := "The same sweep as a hard gate with kernel receipts: any violation is an error, \
      and each passing contract gains the kernel theorem `c.kindContractOk` unless it already \
      stands."
    gate := "the command is the gate; the pin freezes the kernel receipts"
    section_ := "provenance-sweeps" },
  { syntax_ := "#kind_relation r", library := "PropertyKindCalculus"
    effect := "Checks the theorem edge a `Provenance.Relation` declares between two contracts — a \
      sorry-free witness, the conclusion in the claimed shape, the tolerance, hypothesis and \
      license clauses each answered for by name — and prints it."
    gate := "every failure throws, so the command is the report and the gate at once — there is no \
      reading of it that states a violation"
    section_ := "provenance-sweeps" },
  { syntax_ := "#kind_relations ns …", library := "PropertyKindCalculus"
    effect := "The by-type edge survey: every `Provenance.Relation` under the namespaces \
      re-checked as `#kind_relation` checks one, failures as ✗ rows and counterexamples as ⊘ rows, \
      the header counting edges, violations and exemptions."
    gate := "a newly violated edge fails the pin, and so does a vanished one or an exemption \
      nobody declared"
    section_ := "provenance-sweeps" },
  { syntax_ := "#kind_discharges c d", library := "PropertyKindCalculus"
    effect := "Compares two contracts with no graph and no harvest: what the deploying contract \
      did with each parameter the deployed contract handed it, and whether anything was left \
      unanswered."
    gate := "a parameter that stops being answered is a visible change"
    section_ := "provenance-sweeps" },
  { syntax_ := "#kind_discharges_decide c d", library := "PropertyKindCalculus"
    effect := "Adds the theorem `c.kindDischarges.d : c.Discharges d`, proved by `decide` — kernel \
      reduction of the tier relation on the two authors' own contract definitions. Errors out when \
      the tiers do not stack, printing what is unanswered."
    gate := "the command is the gate; the pin freezes the kernel receipt"
    section_ := "provenance-sweeps" },
  { syntax_ := "#kind_unkinded c", library := "PropertyKindCalculus"
    effect := "Prints the unkinded ledger of the scope a contract declares: the count, then one \
      line per naked position and per unkinded flow, deduplicated by member."
    gate := "the pin fails when a silence appears AND when one is fixed, which is what keeps the \
      ledger honest about which direction it moved"
    section_ := "provenance-sweeps" },
  { syntax_ := "#kind_unkinded_clean c", library := "PropertyKindCalculus"
    effect := "The ledger as a gate: errors unless the scope's ledger is empty. Separate from the \
      pin above for the reason every violation-capable pin needs a separate gate — pinning a \
      violation is how it stops being noticed."
    gate := "the command is the gate; there is no message to re-bless"
    section_ := "provenance-sweeps" },
  { syntax_ := "#kind_contract_propagation c", library := "PropertyKindCalculus"
    effect := "The propagation relation of a contract over the assembly its members compute: which \
      source ports reach which produced ports."
    gate := ""
    section_ := "provenance-sweeps" },
  { syntax_ := "#kind_output_ledger c", library := "PropertyKindCalculus"
    effect := "The per-output assumption ledger and trust decomposition of every produced port of \
      a contract, over the assembly its members compute."
    gate := ""
    section_ := "provenance-sweeps" },
  { syntax_ := "#kind_budget b c", library := "Uncertainty"
    effect := "Checks an uncertainty budget's attachment to a boundary and renders it: the port \
      must be a produced port at the budget's kind, the assembly acyclic, every term naming a \
      source that influences the port — and the influencing sources the budget omits render as \
      `unbudgeted source(s)`, so what is not propagated is in the report rather than absent."
    gate := "every violation throws, so the command is the report and the gate at once"
    section_ := "provenance-sweeps" },
  -- The index readers — no gate but the first, whose job is a derived table that stops matching.
  { syntax_ := "#pkc_index \"…\" [ns …]", library := "Index"
    effect := "Prints one generated index as plain text — the same table a document renders, \
      available without building a document."
    gate := "a derived table that stops matching is a build failure rather than an absence nobody \
      notices"
    section_ := "reading-an-index" },
  { syntax_ := "#pkc_summary_overflow [ns …]", library := "Index"
    effect := "Reports the docstrings an index table quotes whose first paragraph is too long for \
      the column that quotes it, widest first."
    gate := ""
    section_ := "reading-an-index" },
  { syntax_ := "#pkc_index_page \"…\" [\"…\", …] [ns …]", library := "Index"
    effect := "Writes the named indexes into the elaborating module's own module docstring, so \
      doc-gen4 renders them as that module's page."
    gate := ""
    section_ := "reading-an-index" }]

/-- The command reference table. Pure data, like `annotationsTable`. -/
def commandsTable : IndexTable :=
  { id := "commands"
    title := "The commands PropertyKindCalculus defines"
    headers := #["Command", "Library", "What it answers", "Pinned"]
    rows := commands.map fun c => #[
      if c.section_.isEmpty then .code c.syntax_ else .tag c.section_ c.syntax_,
      .code c.library, .prose c.effect,
      if c.gate.isEmpty then .text "—" else .prose c.gate] }

/-! ## Occurrences

Each harvest below is a one-line read of a registry, except the three that go through
`tagAttrDecls` / `paramAttrEntries` — see the note in `Index.Basic` on why enumerating a
`TagAttribute` needs a module walk while enumerating a `SimplePersistentEnvExtension` does not. -/

/-- Boundary sites in scope, with the tier that sanctions each and the kinds it mints.

This is the table the whole exercise is for. A kind crossing must be *authored*, so this list is the
complete, checkable statement of where the calculus is left and what is re-typed when it is. -/
def crossingsTable (scope : Scope) : MetaM IndexTable := do
  let env ← getEnv
  let headers := #["Site", "Tier", "Kinds minted", "What it does"]
  let tags := (BoundaryAudit.boundaryTags env).filter (fun t => scope.covers t.decl)
  if tags.isEmpty then
    return IndexTable.empty "crossings" "Authored kind crossings" headers
  -- The mint kinds come from the audit's own walk, so the table cannot disagree with the audit.
  let sites ← BoundaryAudit.boundarySites scope
  let mintsOf : Name → Array String := fun d =>
    match sites.find? (·.decl == d) with
    | some s => s.mints
    | none   => #[]
  let mut rows : Array (Array IndexCell) := #[]
  for t in tags.qsort (fun a b => nameLt a.decl b.decl) do
    rows := rows.push #[
      .decl t.decl (lastComponent t.decl),
      .code t.tier.label,
      .code (String.intercalate ", " ((mintsOf t.decl).toList.map shortenNames)),
      .prose (← summaryLine env t.decl)]
  return { id := "crossings", title := "Authored kind crossings", headers, rows }

/-- The registered kind carriers: the two built into the calculus plus every structure a downstream
layer registered with `@[kindCarrier]`. Never scoped — the point of the table is that the registry is
open, so a reader wants to see what downstream layers added. -/
def carriersTable : MetaM IndexTable := do
  let env ← getEnv
  let carriers := BoundaryAudit.kindCarrierNames env
  let builtin : Array Name :=
    #[``PropertyKindCalculus.Quantity, ``PropertyKindCalculus.CertifiedQuantity,
      ``PropertyKindCalculus.NominalValue]
  let mut rows : Array (Array IndexCell) := #[]
  for c in carriers do
    rows := rows.push #[
      .decl c (lastComponent c),
      .text (if builtin.contains c then "built in" else "registered with @[kindCarrier]"),
      .prose (← summaryLine env c)]
  return { id := "carriers", title := "Registered kind carriers"
           headers := #["Carrier", "Origin", "What it is"], rows }

/-- `@[pkc_math]`-rendered definitions in scope, with the clauses each one requested. -/
def pkcMathTable (scope : Scope) : MetaM IndexTable := do
  let env ← getEnv
  let headers := #["Definition", "Rendering mode", "What it is"]
  let uses := (DocGenMath.pkcMathUses env).filter (fun u => scope.covers u.decl)
  if uses.isEmpty then
    return IndexTable.empty "pkc-math" "Rendered definitions" headers
  let mut rows : Array (Array IndexCell) := #[]
  for u in uses.qsort (fun a b => nameLt a.decl b.decl) do
    rows := rows.push #[
      .decl u.decl (lastComponent u.decl),
      .text u.modeDescription,
      .prose (← summaryLine env u.decl)]
  return { id := "pkc-math", title := "Rendered definitions", headers, rows }

/-- `@[pkc_math_symbol]` declarations in scope, with the LaTeX each fixes.

The seven `MironovNK` fields are the motivating case: two of them (`nu`, `mvt`) are *load-bearing*
rather than cosmetic, because the rendering heuristic maps a Greek-letter spelling to its letter and
would otherwise print a refractive index as an angular frequency. A table of these is therefore a
table of the places where a heuristic was deliberately overruled. -/
def pkcMathSymbolTable (scope : Scope) : MetaM IndexTable := do
  let env ← getEnv
  let headers := #["Declaration", "Renders as", "Layout"]
  let entries := (paramAttrEntries DocGenMath.pkcMathSymbolAttr env).filter
    (fun e => scope.covers e.1)
  if entries.isEmpty then
    return IndexTable.empty "pkc-math-symbol" "Fixed notation" headers
  let rows := entries.map fun (n, notation_) => #[
    IndexCell.decl n (lastComponent n),
    .code notation_.latex,
    .text (if notation_.operator then "prefix operator" else "function head")]
  return { id := "pkc-math-symbol", title := "Fixed notation", headers, rows }

/-- The declarations carrying a bare tag attribute (`@[pkc_math_config]`,
`@[pkc_math_transparent]`), with their docstring gloss. -/
def tagTable (id title heading : String) (attr : TagAttribute) (scope : Scope) :
    MetaM IndexTable := do
  let env ← getEnv
  let headers := #[heading, "What it is"]
  let decls := (tagAttrDecls attr env).filter scope.covers
  if decls.isEmpty then return IndexTable.empty id title headers
  let mut rows : Array (Array IndexCell) := #[]
  for d in decls do
    rows := rows.push #[.decl d (lastComponent d), .prose (← summaryLine env d)]
  return { id, title, headers, rows }

/-- Configuration types (`@[pkc_math_config]`) in scope. -/
def configTable (scope : Scope) : MetaM IndexTable :=
  tagTable "pkc-math-config" "Configuration types" "Type" DocGenMath.pkcMathConfigAttr scope

/-- Notational wrappers (`@[pkc_math_transparent]`) in scope. -/
def transparentTable (scope : Scope) : MetaM IndexTable :=
  tagTable "pkc-math-transparent" "Notational wrappers" "Wrapper"
    DocGenMath.pkcMathTransparentAttr scope

/-! ## Which docstrings an index quotes

`summaryLine` reads a *first paragraph* precisely so that nobody has to write a docstring to a
character budget. But the four tables above open a column with one, and a paragraph much longer than
the column is an ellipsis where a summary should be — a cell that stops before it has said what the
declaration is.

The declarations that can happen to are exactly the ones those tables quote, which is the union
below and not "every documented declaration in scope": a docstring no index reads cannot ellipsize
anywhere, and reporting it would bury the ones that can. Carriers are unscoped for the same reason
`carriersTable` is — a downstream chapter renders the built-in carriers alongside its own, so the
carrier overflowing *its* column may well be one of PropertyKindCalculus's. -/

/-- Every declaration whose docstring an index table quotes. -/
def quotedDecls (env : Environment) (scope : Scope) : Array Name :=
  let inScope (ns : Array Name) : Array Name := ns.filter scope.covers
  let all :=
    inScope ((BoundaryAudit.boundaryTags env).map (·.decl))
      ++ BoundaryAudit.kindCarrierNames env
      ++ inScope ((DocGenMath.pkcMathUses env).map (·.decl))
      ++ inScope (tagAttrDecls DocGenMath.pkcMathConfigAttr env)
      ++ inScope (tagAttrDecls DocGenMath.pkcMathTransparentAttr env)
  all.toList.eraseDups.toArray.qsort nameLt

/-- A quoted docstring whose first paragraph does not fit the column that quotes it. -/
structure SummaryOverflow where
  /-- The declaration whose docstring overflows. -/
  decl : Name
  /-- The visible width of its first paragraph. -/
  width : Nat
deriving Repr, Inhabited

/-- The quoted docstrings whose first paragraph exceeds `maxLen` visible characters, widest first —
what `#pkc_summary_overflow` reports. -/
def summaryOverflows (env : Environment) (scope : Scope) (maxLen : Nat := 160) :
    IO (Array SummaryOverflow) := do
  let mut out : Array SummaryOverflow := #[]
  for d in quotedDecls env scope do
    let doc := (← findDocString? env d).getD ""
    if doc.isEmpty then continue
    let w := summaryWidth doc
    if w > maxLen then out := out.push { decl := d, width := w }
  return out.qsort fun a b =>
    if a.width == b.width then nameLt a.decl b.decl else a.width > b.width

end PropertyKindCalculus.Index
