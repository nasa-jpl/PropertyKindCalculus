/-
# The application templates — what a document built on this calculus must address

The calculus is specified against twenty-seven requirements
(`PropertyKindCalculus.Requirements`). Those say what *the calculus* must do. This
module says what a *document that applies it* must do: one template for a domain
model, one for the deployment of such a model.

The two are separate templates because they answer to different readers and
discharge different obligations. A model document states what a boundary **is** —
its kind-typed ports, its measurement model, the theorem edges relating it to its
neighbors. A deployment document states what deploying one **adds** — the platform
and data contracts, the sizing the run was measured at, the image it ships in, the
gate that accepts it. Neither restates the other, and neither restates the calculus:
a domain document *cites* the blueprint for the discipline and gets on with its
subject.

Like `Requirements.Catalogue`, this records the citable identity of each rubric — its
identifier, group, one-line title, the kind of evidence that would discharge it, what
the document's author must *do* about it, and whether anything can check that the
author did it everywhere. There is deliberately **no status field**: whether a document
addresses a rubric is derived from the conformance sites it declares
(`PropertyKindCalculus.Rubrics.Attributes`), never asserted here. The prose that
*argues* each rubric lives in the blueprint chapters, as the design text for the
requirements does; what lives here is the part a chapter must not restate, because a
sentence transcribed into prose is a sentence that drifts.
-/

namespace PropertyKindCalculus.Rubrics

/-- Which template a rubric belongs to. -/
inductive Template where
  /-- Applying the calculus to a domain: the model document. -/
  | model
  /-- Deploying a domain model: the deployment document. -/
  | deployment
  deriving Repr, Inhabited, DecidableEq, BEq

/-- The template as printed. -/
def Template.label : Template → String
  | .model      => "Model template"
  | .deployment => "Deployment template"

/-- The identifier prefix each template's rubrics carry — `M…` for the model
template, `D…` for the deployment template. -/
def Template.prefix : Template → String
  | .model      => "M"
  | .deployment => "D"

/-- The sections a template falls into, in presentation order. Model groups and
deployment groups are separate constructors rather than a shared spine: the two
templates address different obligations, and a group that meant one thing in a model
document and another in a deployment document would be the conflation the calculus
exists to refuse. -/
inductive RubricGroup where
  /-- M1–M4: what the model is a model *of*, and what it assumes. -/
  | premise
  /-- M5–M10: the declared kind vocabulary, and the audits that close it. -/
  | kindVocabulary
  /-- M11–M16: the model as metrological modules. -/
  | modules
  /-- M17–M19: carriers, numerical adequacy, and uncertainty. -/
  | adequacy
  /-- M20–M22: inversion, its domain, and honest failure. -/
  | wellPosedness
  /-- M23–M26: how the document is checked, and what a green status does not mean. -/
  | assurance
  /-- D1–D2: what is deployed, and what the deployment document is *for*. -/
  | deployedUnits
  /-- D3–D5: the contracts a deployed unit is held to. -/
  | contracts
  /-- D6–D8: what the run was sized at, and what a job may change. -/
  | sizing
  /-- D9–D11: the image, its toolchain, and how it becomes a registered algorithm. -/
  | platform
  /-- D12–D14: what accepts a deployment, and what the green signals actually covered. -/
  | acceptance
  /-- D15–D17: re-running it, and the limits. -/
  | reproducibility
  deriving Repr, Inhabited, DecidableEq, BEq

/-- The group as printed. -/
def RubricGroup.label : RubricGroup → String
  | .premise         => "The premise"
  | .kindVocabulary  => "The kind vocabulary"
  | .modules         => "The model as modules"
  | .adequacy        => "Carriers, adequacy and uncertainty"
  | .wellPosedness   => "Well-posedness and honest failure"
  | .assurance       => "Assurance"
  | .deployedUnits   => "What is deployed"
  | .contracts       => "The contracts"
  | .sizing          => "Sizing and knobs"
  | .platform        => "The platform"
  | .acceptance      => "Acceptance"
  | .reproducibility => "Reproducibility and limits"

/-- The template a group belongs to. -/
def RubricGroup.template : RubricGroup → Template
  | .premise | .kindVocabulary | .modules
  | .adequacy | .wellPosedness | .assurance => .model
  | .deployedUnits | .contracts | .sizing
  | .platform | .acceptance | .reproducibility => .deployment

/-- The model template's groups, in presentation order. -/
def modelGroups : List RubricGroup :=
  [ .premise, .kindVocabulary, .modules, .adequacy, .wellPosedness, .assurance ]

/-- The deployment template's groups, in presentation order. -/
def deploymentGroups : List RubricGroup :=
  [ .deployedUnits, .contracts, .sizing, .platform, .acceptance, .reproducibility ]

/-- The groups of a template, in presentation order. -/
def Template.groups : Template → List RubricGroup
  | .model      => modelGroups
  | .deployment => deploymentGroups

/-- What would *count* as addressing a rubric — an intrinsic property of the rubric,
not of the document. Four obligations of different character live in these
templates, and reporting them in one vocabulary would let the weakest kind of
evidence stand in for the strongest:

  * `exposition` is discharged by **a section of the document that states it**. There
    is nothing to prove: the obligation is that a reader can find the answer, so the
    evidence is a cross-reference to a tagged section, and a dangling tag is a render
    error.
  * `generated` is discharged by **a view read off the compiled environment** — an
    index, a card, a graph. The obligation is specifically that it is *generated*: a
    table transcribed by hand satisfies the letter and not the rubric, because it can
    drift from what it describes and a generated one cannot.
  * `checked` is discharged by **a kernel-checked declaration** — a theorem edge, a
    proof, an audit that gates the build.
  * `measured` is discharged by **a reported measurement**, which is weaker evidence
    than a proof and must be labeled as one: a measured result names the parameter it
    was swept over, the denominator it is relative to, and the statistic it reports.

Recording the kind lets each rubric be reported in its own honest vocabulary
(*stated* / *generated* / *proved* / *measured*) instead of a single "done". -/
inductive Evidence where
  /-- A section of the document states it. -/
  | exposition
  /-- A view generated from the compiled environment. -/
  | generated
  /-- A kernel-checked declaration. -/
  | checked
  /-- A reported measurement, labeled as one. -/
  | measured
  deriving Repr, Inhabited, DecidableEq, BEq

/-- The evidence kind as printed. -/
def Evidence.label : Evidence → String
  | .exposition => "exposition"
  | .generated  => "generated"
  | .checked    => "checked"
  | .measured   => "measured"

/-- The word a *discharged* rubric of this evidence kind is reported with. -/
def Evidence.dischargedWord : Evidence → String
  | .exposition => "stated"
  | .generated  => "generated"
  | .checked    => "proved"
  | .measured   => "measured"

/-- Whether anything can check that a document did what a rubric asks *everywhere* — and
if so, how strongly the check is held.

`Evidence` says what kind of thing discharges a rubric; `Closure` says whether the
document's answer can be enumerated. The two axes are independent, and conflating them is
how a template assembled out of exemplars comes to read as an inventory: two annotated
theorems and two hundred discharge a `checked` rubric identically, because
`Conformance.status` can ask only whether a site exists, never whether the sites are all
of them.

A census needs three things, and each of them either exists or does not:

  * **a population that is a type.** `#kind_contracts` sweeps every `Provenance.Contract`
    under a namespace — membership is by type, so *declaring* a boundary enrolls it. That
    is the whole difference between a census and a list: enrolment has to be a side effect
    of doing the work, never a second act of remembering. Where the population is what the
    document *says*, no such type exists and no census can.
  * **a decidable per-member predicate.** `examPrinciple ≠ none` is one. "Each separation
    the model *relies on*" is not — the nearest mechanical proxy is a different claim, and
    choosing it is a design decision rather than a formality.
  * **declarable exceptions.** A census with honest negatives and no way to record them is
    a census someone will switch off. `@[kindCounterexample]` and `#kind_scc_clean`'s
    declared clusters are the library's two idioms for it: a legitimate gap becomes data
    rather than a sentence in a docstring no audit can read.

The strength of a held population is the library's own ladder: a reading, a reading pinned
with `#guard_msgs` so that a changed answer fails the build, or a `_clean` audit that
throws and leaves nothing to re-bless. -/
inductive Closure where
  /-- No census, and none possible: the population is the document's own prose. This is
  not a weakness to be repaired — an argument addressed to a reader is what the `premise`
  group *is* — but it is the reason such a rubric can never report more than that the
  section exists. -/
  | prose
  /-- The population can be enumerated from the environment, but nothing walks it yet, so
  the rubric is discharged by exemplars and is only as complete as the author's memory.
  The string names the population a sweep would have to cover. -/
  | pending (population : String)
  /-- A generated view or a pinned reading: the population is walked and cannot omit a
  member, and a changed answer is visible in the diff. The string names the mechanism as
  an author writes it; `audits` names the receipts (`PropertyKindCalculus.AuditReceipt`)
  a document must hold for the rubric to read green — the command names without their
  `#` — and is empty for a mechanism that is a generator rather than a command. -/
  | record (mechanism : String) (audits : List String := [])
  /-- An audit that fails the build on a member that does not satisfy the rubric, so an
  omission is not merely visible but fatal. The string names the mechanism; `audits`, as
  for `record`, the receipts a document must hold. -/
  | gate (mechanism : String) (audits : List String := [])
  deriving Repr, Inhabited, DecidableEq, BEq

/-- The closure as printed in the template table's `Requires` column. -/
def Closure.tag : Closure → String
  | .prose      => "no census"
  | .pending _  => "census possible"
  | .record .. => "pinned"
  | .gate ..   => "gated"

/-- The mechanism that holds the population, or the population a sweep would have to
cover; empty for `prose`, which has neither. -/
def Closure.detail : Closure → String
  | .prose       => ""
  | .pending p   => p
  | .record m _  => m
  | .gate m _    => m

/-- Whether the rubric's population is enumerable at all — false only for `prose`. -/
def Closure.censusable : Closure → Bool
  | .prose => false
  | _      => true

/-- Whether the population is walked today, rather than merely walkable. -/
def Closure.held : Closure → Bool
  | .record .. | .gate .. => true
  | _                     => false

/-- The audit receipts a document must hold for this closure to count as run: empty for
`prose`, for `pending`, and for a `record` that is a generator rather than a command. -/
def Closure.audits : Closure → List String
  | .record _ as | .gate _ as => as
  | _                         => []

/-- The identity of one rubric: its identifier, one-line title, group, and the kind
of evidence that discharges it.

There is deliberately **no status field**, for the reason `Requirements.Requirement`
has none: a rubric's status is a fact *derived* from the conformance sites a document
declares, and recording it twice would reintroduce exactly the drift this layer
exists to eliminate. -/
structure Rubric where
  /-- The identifier, as printed — `"M1"` … `"M26"`, `"D1"` … `"D17"`. -/
  id : String
  /-- A one-line title: the obligation as a *property of the document*. -/
  title : String
  /-- The group, which also fixes the template. -/
  group : RubricGroup
  /-- What would count as addressing it. -/
  evidence : Evidence
  /-- What the *author* does about it, in the imperative: the artifact to produce, not
  the property it establishes. The title says what a conforming document has; this says
  what its author writes. Separate fields because the two are read at different moments —
  the title when deciding whether a document conforms, this when building one — and
  because a reader who has only the title routinely cannot derive it. -/
  obligation : String
  /-- Whether anything can check the author did it everywhere. -/
  closure : Closure
  deriving Repr, Inhabited

/-- The template a rubric belongs to. -/
def Rubric.template (r : Rubric) : Template := r.group.template

/-- The numeric part of a rubric id (`"M12"` ↦ `12`), for natural sorting. -/
def Rubric.number (r : Rubric) : Nat :=
  (r.id.dropWhile (!·.isDigit)).toNat!

/-- **The model template.** What a document applying the calculus to a domain must
address. The single source of truth for the model conformance matrix's rows. -/
def modelTemplate : List Rubric :=
  [ { id := "M1", group := .premise, evidence := .exposition,
      closure := .prose,
      title := "The measurand and the deliverable are named and kept apart from what a \
                reference measurement reports",
      obligation := "Name the measurand and the deliverable in the model's own quantities, \
                     and say what a reference measurement reports instead — with the \
                     conversion that relates them where they differ, which is the step a \
                     validation comparing the two must perform" }
  , { id := "M2", group := .premise, evidence := .exposition,
      closure := .prose,
      title := "Why the kind layer is load-bearing in this domain: which quantities are of \
                dimension one, and which confusions survive a unit check",
      obligation := "State which of this model's quantities land on dimension one and which \
                     of its confusions survive a unit check, and cite the model's own \
                     dimensional-coverage table for the census the paragraph summarizes" }
  , { id := "M3", group := .premise, evidence := .exposition,
      closure := .prose,
      title := "The typing discipline is cited, not re-argued",
      obligation := "Name what the document assumes of the calculus and point at where it \
                     is established; do not restate the case for kinds" }
  , { id := "M4", group := .premise, evidence := .exposition,
      closure := .prose,
      title := "The measurement chain in the order the physics runs it, and the layer map \
                saying where each claim lives",
      obligation := "Give the measurement chain in the order the physics runs it, and a map \
                     from each claim the document makes to the library layer that holds it" }
  , { id := "M5", group := .kindVocabulary, evidence := .generated,
      closure := .record "the generated kind, record and operation index, walked from the \
                          compiled environment",
      title := "Every quantity the document names is a declared kind-typed quantity, \
                inventoried rather than surveyed",
      obligation := "Declare every quantity the document names as a kind-typed declaration, \
                     and render the inventory with the generated index rather than a table \
                     written beside it" }
  , { id := "M6", group := .kindVocabulary, evidence := .generated,
      closure := .gate "`#kind_examination_clean ns …`, with `#kind_examination_coverage` \
                        as the record and `@[kindPrincipleFree]` the declared exception; a \
                        bare `KindOfProperty` no `DimensionedKind` wraps is reported, not \
                        skipped" ["kind_examination_clean"],
      title := "Kinds of dimension one are individuated by their examination principle, \
                with the procedure ⊑ method ⊑ principle refinement recorded",
      obligation := "Give every kind of dimension one an examination principle and record \
                     the procedure ⊑ method ⊑ principle chain; where such a kind is \
                     deliberately principle-free, declare the exception so an audit can \
                     read it" }
  , { id := "M7", group := .kindVocabulary, evidence := .checked,
      closure := .pending "the pairs of dedicated kinds a signature makes meet — the \
                           mechanical proxy for `relied on`, which has to be chosen before \
                           it can be swept",
      title := "Dedications to systems and components are declared, and each separation the \
                model relies on is proved rather than assumed",
      obligation := "Declare the dedications to systems and components, and prove each \
                     separation an argument in the document rests on rather than asserting \
                     it" }
  , { id := "M8", group := .kindVocabulary, evidence := .generated,
      closure := .record "`#kind_edges k`, and the Algebra column of the generated kinds \
                          table",
      title := "The arithmetic surface is closed: the complete list of products, quotients \
                and powers the model is permitted to form",
      obligation := "Author every product, quotient and power the model may form, and \
                     publish the closed surface as a generated table — the empty cells \
                     included, since those are the combinations the model has decided are \
                     meaningless" }
  , { id := "M9", group := .kindVocabulary, evidence := .checked,
      closure := .gate "`#kind_boundary_clean ns …` and `#kind_mint_ratchet ns …`"
                        ["kind_boundary_clean", "kind_mint_ratchet"],
      title := "Every departure from the algebra is authored, and an audit that gates the \
                build makes the inventory complete rather than a survey",
      obligation := "Author every departure from the algebra — a genuine meeting of two \
                     kinds, kind-preserving plumbing, a point where a kinded value leaves \
                     the calculus — and run the audit that fails the build on an unauthored \
                     one" }
  , { id := "M10", group := .kindVocabulary, evidence := .generated,
      closure := .record "`#kind_dimensional_coverage ns …` and `#kind_scc ns …`, pinned \
                          with `#guard_msgs`; the `_clean` forms gate where a model can \
                          afford it" ["kind_dimensional_coverage", "kind_scc"],
      title := "Dimensional coverage is audited edge by edge, and inter-derivability the \
                algebra cannot refuse is reported rather than hidden",
      obligation := "Pin the dimensional-coverage reading and the inter-derivability \
                     report, so a newly undimensioned edge or a newly merged cluster is a \
                     change a reader sees in the diff" }
  , { id := "M11", group := .modules, evidence := .checked,
      closure := .gate "`#kind_contracts ns …`, or `#kind_contracts_decide ns …` for kernel \
                        receipts" ["kind_contracts"],
      title := "Each boundary is a declared metrological module of kind-typed ports",
      obligation := "Declare each boundary as a contract of kind-typed ports, and sweep the \
                     namespace so that a boundary declared anywhere is enrolled without \
                     being listed by name" }
  , { id := "M12", group := .modules, evidence := .checked,
      closure := .gate "`#kind_relation_clean ns …`, with `#kind_relation_coverage` as \
                        the record and `@[kindRelationFree]` the declared \
                        exception" ["kind_relation_clean"],
      title := "A module's behavior is a measurement model carried as a theorem edge, not \
                as prose beside it",
      obligation := "Carry each module's behavior as a relation naming a theorem, not as \
                     prose beside the module" }
  , { id := "M13", group := .modules, evidence := .checked,
      closure := .gate "`#kind_relations ns …`" ["kind_relations"],
      title := "The implementation's relation to the measurement model is named — equals, \
                inverts, refines, or bounded by a kinded tolerance",
      obligation := "Name the relation the implementation bears to the measurement model — \
                     equals, inverts, refines, or bounded by a kinded tolerance — and let \
                     the sweep check that the witness is sorry-free and about those two \
                     boundaries" }
  , { id := "M14", group := .modules, evidence := .checked,
      closure := .gate "`#kind_relations ns …`, which fails on a license clause not \
                        answered for by name" ["kind_relations"],
      title := "Licenses are stated per carrier rung, because laws transfer across the \
                carrier ladder and side conditions do not",
      obligation := "List on the edge itself one license per carrier rung the claim is \
                     extended to beyond the rung its witness is stated at, each answered \
                     for by a named repair or a named per-rung restatement" }
  , { id := "M15", group := .modules, evidence := .checked,
      closure := .gate "`#kind_mereology_clean ns …`, with `#kind_mereology_coverage` as \
                        the record; no exception mark, since the aggregation vocabulary \
                        names every honest negative" ["kind_mereology_clean"],
      title := "Mereology is declared per output port, and any recarving or sharding is \
                licensed by that declaration",
      obligation := "Declare per output port whether it aggregates over parts, and license \
                     any recarving or sharding of a batch by that declaration rather than \
                     by the fact that it worked" }
  , { id := "M16", group := .modules, evidence := .generated,
      closure := .record "the module card, generated from the declared contract",
      title := "One specification sheet per boundary, generated from the checked \
                declaration rather than written beside it",
      obligation := "Generate one specification sheet per boundary from the declared \
                     contract, so the commit that changes a contract either regenerates the \
                     sheet or fails" }
  , { id := "M17", group := .adequacy, evidence := .checked,
      closure := .pending "registered carriers with no declared bridge — the carriers are \
                           enumerable (the `Carrier`/`NumCarrier` instance vocabulary, \
                           specification from executable by `LawfulCarrier`), but a bridge \
                           that is a theorem rather than a `CarrierRefinement` instance has \
                           no declaration form, so a sweep today would report every real \
                           bridge as missing; the form comes first",
      title := "The specification carrier and the executable carrier are distinguished, and \
                the refinement bridge between them is named",
      obligation := "Register the specification carrier and the executable carrier as \
                     distinct, and name the bridge that carries a claim from one to the \
                     other" }
  , { id := "M18", group := .adequacy, evidence := .checked,
      closure := .pending "deployed output ports carrying no adequacy claim",
      title := "The deployed representation is shown numerically adequate at the scale of \
                the input uncertainties",
      obligation := "Show that the deployed representation loses no information at the \
                     scale of the input uncertainties — a claim about this model's numbers, \
                     not a preference for wider floats" }
  , { id := "M19", group := .adequacy, evidence := .checked,
      closure := .pending "reported uncertainties that name neither a rung nor a coverage",
      title := "Uncertainty names the rung of the method ladder it was computed at, and the \
                coverage its recorded variance certifies",
      obligation := "Name, for each reported uncertainty, the rung of the method ladder it \
                     was computed at and the coverage its recorded variance certifies" }
  , { id := "M20", group := .wellPosedness, evidence := .checked,
      closure := .gate "`#kind_wellposedness_clean ns …` — every `inverts` edge declares \
                        its well-posedness (`wellPosed`, an `∃!`-concluding sorry-free \
                        theorem, with the `domain` its statement mentions) or surfaces its \
                        ambiguity — with `#kind_wellposedness_coverage` as the record; no \
                        exception mark, the two fields are total over the honest negatives; \
                        the fields themselves are validated by `#kind_relation`"
                       ["kind_wellposedness_clean"],
      title := "Where the model is inverted, existence and uniqueness are proved on a \
                declared domain",
      obligation := "Where the model is inverted, prove existence and uniqueness on a \
                     domain the document declares — both the proof and the domain it is \
                     about" }
  , { id := "M21", group := .wellPosedness, evidence := .checked,
      closure := .gate "`#kind_inversion_clean ns …` for the domain half — every inverted \
                        boundary declares a `conditional` port — with \
                        `#kind_inversion_coverage` as the record and `@[kindInversionTotal]` \
                        the declared exception; `#kind_wellposedness_clean ns …` for the \
                        ambiguity half — an inverts edge that does not prove well-posedness \
                        surfaces its `ambiguity` as a declaration"
                       ["kind_inversion_clean", "kind_wellposedness_clean"],
      title := "Failure outside that domain is detected and reported, and ambiguity is \
                surfaced rather than silently resolved",
      obligation := "Detect and report failure outside that domain, and surface ambiguity \
                     rather than resolving it silently to whichever root the algorithm \
                     reached first" }
  , { id := "M22", group := .wellPosedness, evidence := .checked,
      closure := .pending "quality and conditioning outputs a consumer needs that no \
                           contract declares as ports — produced ports are enumerable, but \
                           nothing marks a port or a kind as diagnostic, so the population \
                           is not yet a type; the form comes first",
      title := "The conditioning and quality outputs a consumer must read are part of the \
                declared contract, not a side channel",
      obligation := "Put the conditioning and quality outputs a consumer must read into the \
                     declared contract as ports, not into a side channel a downstream stage \
                     may or may not read" }
  , { id := "M23", group := .assurance, evidence := .generated,
      closure := .record "the document's own harvest of cited declarations, which cannot \
                          omit a node it renders",
      title := "Every load-bearing definition and theorem links to the declaration that \
                realizes it and carries that declaration's machine-checked status",
      obligation := "Cite each load-bearing definition and theorem by the declaration that \
                     realizes it, so the rendered claim carries that declaration's \
                     machine-checked status" }
  , { id := "M24", group := .assurance, evidence := .generated,
      closure := .record "the graph and ledger directives, generated from the cited nodes",
      title := "A dependency graph and an assurance ledger are generated from those same \
                nodes, so neither can omit a cited claim",
      obligation := "Generate the dependency graph and the assurance ledger from the same \
                     nodes the chapters cite, so neither view can omit a claim the other \
                     carries" }
  , { id := "M25", group := .assurance, evidence := .exposition,
      closure := .prose,
      title := "The limits of a green status are stated plainly: which rung each theorem \
                holds at, and which results are measured rather than proved",
      obligation := "State plainly what this document's green status does not mean: which \
                     rung each theorem holds at, and which of its numbers are measured \
                     rather than proved" }
  , { id := "M26", group := .assurance, evidence := .measured,
      closure := .pending "reported measurements, once each is declared as data rather than \
                           written as a number in a sentence",
      title := "Each reported measurement names the parameter it was swept over, the \
                denominator it is relative to, and the statistic it reports",
      obligation := "For each reported measurement, name the parameter it was swept over, \
                     the denominator it is relative to, and the statistic it reports" } ]

/-- **The deployment template.** What a document deploying a domain model must
address. The single source of truth for the deployment conformance matrix's rows. -/
def deploymentTemplate : List Rubric :=
  [ { id := "D1", group := .deployedUnits, evidence := .exposition,
      closure := .prose,
      title := "What is deployed, and which model boundary each deployed unit realizes",
      obligation := "List the deployed units, and name for each the model boundary it \
                     realizes" }
  , { id := "D2", group := .deployedUnits, evidence := .exposition,
      closure := .prose,
      title := "The document states what deploying the model adds, and cites the model \
                document for what the module is",
      obligation := "State what deploying the model adds, and cite the model document for \
                     what the module is" }
  , { id := "D3", group := .contracts, evidence := .checked,
      closure := .pending "declared payload faces with no validation ahead of the first \
                           decode",
      title := "The data contract is declared, compiled in, and validated against a \
                producer's own claims before any payload is decoded",
      obligation := "Declare the payload interface, compile it into the executable, and \
                     validate it against the producer's own claims before any payload is \
                     decoded" }
  , { id := "D4", group := .contracts, evidence := .checked,
      closure := .gate "`#kind_discharges_decide c d`" ["kind_discharges_decide"],
      title := "The platform contract is kind-typed and held to the registration payload, \
                with the discharge relation decided by the kernel",
      obligation := "Kind-type the argument plane the scheduler passes, hold it to the \
                     registration payload, and let the kernel decide the discharge relation \
                     between the two" }
  , { id := "D5", group := .contracts, evidence := .generated,
      closure := .record "the deployment card, generated per declared unit",
      title := "One deployment card per deployed unit, each panel read off a declared \
                object rather than written beside it",
      obligation := "Generate one deployment card per deployed unit, each panel read off a \
                     declared object rather than written beside it" }
  , { id := "D6", group := .sizing, evidence := .measured,
      closure := .pending "sizing constants, once the measured records behind each are \
                           declared",
      title := "The run is sized from measured records, not from constants typed by hand",
      obligation := "Size the run from measured records, and name the records each size \
                     came from" }
  , { id := "D7", group := .sizing, evidence := .measured,
      closure := .pending "reported operating points, once the sweep behind each is \
                           declared",
      title := "Operating points come from a sweep whose own turnover or plateau names \
                them, reported with the dispersion any threshold has to beat",
      obligation := "Sweep the parameter, let the machine's own turnover or plateau name \
                     the operating point, and report the dispersion any threshold has to \
                     beat" }
  , { id := "D8", group := .sizing, evidence := .exposition,
      closure := .pending "settable environment knobs, once declared as data rather than \
                           listed in prose",
      title := "Every environment knob a job may set is enumerated with what it decides",
      obligation := "Enumerate every environment knob a job may set, with what each one \
                     decides" }
  , { id := "D9", group := .platform, evidence := .exposition,
      closure := .prose,
      title := "The image facts are stated: what ships per unit, the toolchain and \
                architecture spectrum it was built for, and the ABI floor it runs against",
      obligation := "State what ships per unit, the toolchain and architecture spectrum it \
                     was built for, and the ABI floor it runs against" }
  , { id := "D10", group := .platform, evidence := .exposition,
      closure := .record "the deployed version and registration payload, derived from the \
                          artifact",
      title := "Registration and version derivation are mechanized, so a deployed version \
                is derived from the artifact rather than asserted beside it",
      obligation := "Derive the deployed version from the artifact and mechanize \
                     registration, so neither is asserted beside what actually shipped" }
  , { id := "D11", group := .platform, evidence := .exposition,
      closure := .prose,
      title := "Backend interchange is stated: what the same source does on each target, \
                and what changes when the target changes",
      obligation := "State what the same source does on each target, and what changes when \
                     the target does" }
  , { id := "D12", group := .acceptance, evidence := .checked,
      closure := .gate "the acceptance run itself, executed against the model document's \
                        specification",
      title := "Acceptance is a gate against the specification the model document proves — \
                run as proof-by-execution, not asserted",
      obligation := "Run acceptance as a gate against the specification the model document \
                     proves — proof by execution, not an assertion that the two agree" }
  , { id := "D13", group := .acceptance, evidence := .measured,
      closure := .pending "performance claims, once each names the paired run in the \
                           deployed executable behind it",
      title := "Performance claims are a paired A/B in the deployed executable, never a \
                microbenchmark quoted as a prediction",
      obligation := "Make every performance claim a paired A/B in the deployed executable, \
                     never a microbenchmark quoted as a prediction" }
  , { id := "D14", group := .acceptance, evidence := .exposition,
      closure := .prose,
      title := "Each green signal names which of the changed lines it actually compiled or \
                ran, so a passing pipeline is not quoted as evidence for a path it never \
                touched",
      obligation := "Say, for each green signal quoted as evidence, which of the changed \
                     lines it actually compiled or ran" }
  , { id := "D15", group := .reproducibility, evidence := .exposition,
      closure := .prose,
      title := "Failure, checkpoint and resume semantics are stated: what a partially \
                completed job leaves behind, and what resuming it does",
      obligation := "State what a partially completed job leaves behind, and what resuming \
                     it does with that" }
  , { id := "D16", group := .reproducibility, evidence := .generated,
      closure := .record "the manifest, generated from the artifacts that ran",
      title := "A reproducibility manifest carries the pins and digests of what actually \
                ran, generated from the artifacts rather than transcribed",
      obligation := "Generate the reproducibility manifest from the artifacts — the pins \
                     and digests of what actually ran, not of what was intended" }
  , { id := "D17", group := .reproducibility, evidence := .exposition,
      closure := .prose,
      title := "What is trusted is stated plainly: the boundaries the verification does not \
                cross, and what a consumer is therefore taking on faith",
      obligation := "Name the boundaries this deployment's verification does not cross, and \
                     what a consumer is therefore taking on faith" } ]

/-- Every rubric of both templates, model first. -/
def catalogue : List Rubric := modelTemplate ++ deploymentTemplate

/-- The rubrics of one template. -/
def Template.rubrics : Template → List Rubric
  | .model      => modelTemplate
  | .deployment => deploymentTemplate

/-- Look up a rubric by id. -/
def rubricById? (id : String) : Option Rubric :=
  catalogue.find? (·.id == id)

end PropertyKindCalculus.Rubrics
