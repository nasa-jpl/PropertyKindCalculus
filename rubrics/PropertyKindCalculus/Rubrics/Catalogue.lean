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

Like `Requirements.Catalogue`, this records only the citable identity of each
rubric — its identifier, one-line title, group, and the kind of evidence that would
discharge it. There is deliberately **no status field**: whether a document addresses
a rubric is derived from the conformance sites it declares
(`PropertyKindCalculus.Rubrics.Attributes`), never asserted here. The prose that
*argues* each rubric lives in the blueprint chapters, as the design text for the
requirements does.
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

/-- The identity of one rubric: its identifier, one-line title, group, and the kind
of evidence that discharges it.

There is deliberately **no status field**, for the reason `Requirements.Requirement`
has none: a rubric's status is a fact *derived* from the conformance sites a document
declares, and recording it twice would reintroduce exactly the drift this layer
exists to eliminate. -/
structure Rubric where
  /-- The identifier, as printed — `"M1"` … `"M26"`, `"D1"` … `"D17"`. -/
  id : String
  /-- A one-line title. -/
  title : String
  /-- The group, which also fixes the template. -/
  group : RubricGroup
  /-- What would count as addressing it. -/
  evidence : Evidence
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
      title := "The measurand and the deliverable are named and kept apart from what a \
                reference measurement reports" }
  , { id := "M2", group := .premise, evidence := .exposition,
      title := "Why the kind layer is load-bearing in this domain: which quantities are of \
                dimension one, and which confusions survive a unit check" }
  , { id := "M3", group := .premise, evidence := .exposition,
      title := "The typing discipline is cited, not re-argued" }
  , { id := "M4", group := .premise, evidence := .exposition,
      title := "The measurement chain in the order the physics runs it, and the layer map \
                saying where each claim lives" }
  , { id := "M5", group := .kindVocabulary, evidence := .generated,
      title := "Every quantity the document names is a declared kind-typed quantity, \
                inventoried rather than surveyed" }
  , { id := "M6", group := .kindVocabulary, evidence := .generated,
      title := "Kinds of dimension one are individuated by their examination principle, with \
                the procedure ⊑ method ⊑ principle refinement recorded" }
  , { id := "M7", group := .kindVocabulary, evidence := .checked,
      title := "Dedications to systems and components are declared, and each separation the \
                model relies on is proved rather than assumed" }
  , { id := "M8", group := .kindVocabulary, evidence := .generated,
      title := "The arithmetic surface is closed: the complete list of products, quotients \
                and powers the model is permitted to form" }
  , { id := "M9", group := .kindVocabulary, evidence := .checked,
      title := "Every departure from the algebra is authored, and an audit that gates the \
                build makes the inventory complete rather than a survey" }
  , { id := "M10", group := .kindVocabulary, evidence := .generated,
      title := "Dimensional coverage is audited edge by edge, and inter-derivability the \
                algebra cannot refuse is reported rather than hidden" }
  , { id := "M11", group := .modules, evidence := .checked,
      title := "Each boundary is a declared metrological module of kind-typed ports" }
  , { id := "M12", group := .modules, evidence := .checked,
      title := "A module's behavior is a measurement model carried as a theorem edge, not as \
                prose beside it" }
  , { id := "M13", group := .modules, evidence := .checked,
      title := "The implementation's relation to the measurement model is named — equals, \
                inverts, refines, or bounded by a kinded tolerance" }
  , { id := "M14", group := .modules, evidence := .checked,
      title := "Licenses are stated per carrier rung, because laws transfer across the \
                carrier ladder and side conditions do not" }
  , { id := "M15", group := .modules, evidence := .checked,
      title := "Mereology is declared per output port, and any recarving or sharding is \
                licensed by that declaration" }
  , { id := "M16", group := .modules, evidence := .generated,
      title := "One specification sheet per boundary, generated from the checked declaration \
                rather than written beside it" }
  , { id := "M17", group := .adequacy, evidence := .checked,
      title := "The specification carrier and the executable carrier are distinguished, and \
                the refinement bridge between them is named" }
  , { id := "M18", group := .adequacy, evidence := .checked,
      title := "The deployed representation is shown numerically adequate at the scale of \
                the input uncertainties" }
  , { id := "M19", group := .adequacy, evidence := .checked,
      title := "Uncertainty names the rung of the method ladder it was computed at, and the \
                coverage its recorded variance certifies" }
  , { id := "M20", group := .wellPosedness, evidence := .checked,
      title := "Where the model is inverted, existence and uniqueness are proved on a \
                declared domain" }
  , { id := "M21", group := .wellPosedness, evidence := .checked,
      title := "Failure outside that domain is detected and reported, and ambiguity is \
                surfaced rather than silently resolved" }
  , { id := "M22", group := .wellPosedness, evidence := .checked,
      title := "The conditioning and quality outputs a consumer must read are part of the \
                declared contract, not a side channel" }
  , { id := "M23", group := .assurance, evidence := .generated,
      title := "Every load-bearing definition and theorem links to the declaration that \
                realizes it and carries that declaration's machine-checked status" }
  , { id := "M24", group := .assurance, evidence := .generated,
      title := "A dependency graph and an assurance ledger are generated from those same \
                nodes, so neither can omit a cited claim" }
  , { id := "M25", group := .assurance, evidence := .exposition,
      title := "The limits of a green status are stated plainly: which rung each theorem \
                holds at, and which results are measured rather than proved" }
  , { id := "M26", group := .assurance, evidence := .measured,
      title := "Each reported measurement names the parameter it was swept over, the \
                denominator it is relative to, and the statistic it reports" } ]

/-- **The deployment template.** What a document deploying a domain model must
address. The single source of truth for the deployment conformance matrix's rows. -/
def deploymentTemplate : List Rubric :=
  [ { id := "D1", group := .deployedUnits, evidence := .exposition,
      title := "What is deployed, and which model boundary each deployed unit realizes" }
  , { id := "D2", group := .deployedUnits, evidence := .exposition,
      title := "The document states what deploying the model adds, and cites the model \
                document for what the module is" }
  , { id := "D3", group := .contracts, evidence := .checked,
      title := "The data contract is declared, compiled in, and validated against a \
                producer's own claims before any payload is decoded" }
  , { id := "D4", group := .contracts, evidence := .checked,
      title := "The platform contract is kind-typed and held to the registration payload, \
                with the discharge relation decided by the kernel" }
  , { id := "D5", group := .contracts, evidence := .generated,
      title := "One deployment card per deployed unit, each panel read off a declared object \
                rather than written beside it" }
  , { id := "D6", group := .sizing, evidence := .measured,
      title := "The run is sized from measured records, not from constants typed by hand" }
  , { id := "D7", group := .sizing, evidence := .measured,
      title := "Operating points come from a sweep whose own turnover or plateau names them, \
                reported with the dispersion any threshold has to beat" }
  , { id := "D8", group := .sizing, evidence := .exposition,
      title := "Every environment knob a job may set is enumerated with what it decides" }
  , { id := "D9", group := .platform, evidence := .exposition,
      title := "The image facts are stated: what ships per unit, the toolchain and \
                architecture spectrum it was built for, and the ABI floor it runs against" }
  , { id := "D10", group := .platform, evidence := .exposition,
      title := "Registration and version derivation are mechanized, so a deployed version is \
                derived from the artifact rather than asserted beside it" }
  , { id := "D11", group := .platform, evidence := .exposition,
      title := "Backend interchange is stated: what the same source does on each target, and \
                what changes when the target changes" }
  , { id := "D12", group := .acceptance, evidence := .checked,
      title := "Acceptance is a gate against the specification the model document proves — \
                run as proof-by-execution, not asserted" }
  , { id := "D13", group := .acceptance, evidence := .measured,
      title := "Performance claims are a paired A/B in the deployed executable, never a \
                microbenchmark quoted as a prediction" }
  , { id := "D14", group := .acceptance, evidence := .exposition,
      title := "Each green signal names which of the changed lines it actually compiled or \
                ran, so a passing pipeline is not quoted as evidence for a path it never \
                touched" }
  , { id := "D15", group := .reproducibility, evidence := .exposition,
      title := "Failure, checkpoint and resume semantics are stated: what a partially \
                completed job leaves behind, and what resuming it does" }
  , { id := "D16", group := .reproducibility, evidence := .generated,
      title := "A reproducibility manifest carries the pins and digests of what actually ran, \
                generated from the artifacts rather than transcribed" }
  , { id := "D17", group := .reproducibility, evidence := .exposition,
      title := "What is trusted is stated plainly: the boundaries the verification does not \
                cross, and what a consumer is therefore taking on faith" } ]

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
