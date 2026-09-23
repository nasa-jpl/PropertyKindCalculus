import Verso
import VersoManual
import VersoBlueprint
import PropertyKindCalculusBlueprint.RubricTable

open Verso.Genre
open Verso.Genre.Manual
open Informal
open PropertyKindCalculusBlueprint.RubricTemplate

#doc (Manual) "Applying the calculus to a domain: the model template" =>
%%%
tag := "model-template"
%%%

The preceding chapters say what the calculus is and what it proves. This one is guidance
for the domain expert who builds on them: what a *domain model* owes to its reader, and
how a document can report, on every build, which of those obligations it has discharged.

The obligation is not obvious, and getting it wrong is cheap. A model that declares its
kinds, proves its algebra and ships green nodes can still leave a reader unable to answer
the questions that decide whether the model may be used — what it is a model *of*, which
of its quantities the dimension layer cannot separate, at which carrier each theorem
holds, and which of its numbers were proved rather than measured. None of those is a
matter of taste: each has an answer, and a document either contains it or it does not.
The template below is that list of questions.

# What a template is, and what it is not

A rubric is an obligation to *answer*, not a section to write. Two documents that
discharge the same rubric may look nothing alike: one may answer M2 in a paragraph of its
introduction and another in the closing page of a chapter, and both conform. What the
template fixes is the question and the *kind of evidence* that settles it.

Of those two, it is the evidence that is worth stating carefully: a checklist that names
its questions but not what settles them can be checked off by asserting the answers. Four
kinds of evidence appear, and they are not interchangeable:

- *Exposition.* A tagged section of the document states the answer. There is nothing to
  prove — the obligation is that a reader can find it — so the evidence is a
  cross-reference, and a cross-reference to a section that does not exist is a render
  error.
- *Generated.* A view read off the compiled environment: an index, a specification sheet,
  a graph. The obligation is specifically that it is *generated*. A table transcribed by
  hand sits on the page looking identical and satisfies the letter of the rubric, so the
  evidence required is not the table but the declaration that produces or gates it —
  which only the generated one has.
- *Checked.* A kernel-checked declaration: a theorem edge, a proof, an audit that fails
  the build when the property it checks does not hold.
- *Measured.* A reported measurement. This is weaker evidence than a proof and the
  template keeps it weaker on purpose: a measured result is discharged by naming the
  parameter it was swept over, the denominator it is relative to, and the statistic it
  reports.

Reporting all four as a single "done" would let a cross-reference pass for a proof.
Reported separately, a document's own matrix says which of its answers are proved and
which are merely written down.

Each rubric therefore carries two texts, written for different moments. The *rubric* is a
property of a finished document — what a reader can check by reading it. The *author's
part* is an instruction: the artifact to produce, in the imperative. Neither is derivable
from the other by someone who has not built such a document before, which is why the
template carries both rather than leaving the second to be inferred from the first.

:::rubric_count model
:::

# The template

The rows below are generated from `PropertyKindCalculus.Rubrics.modelTemplate`, so a
rubric added to the catalogue appears here without this chapter being edited, and one
removed cannot linger in it. The *author's part* column is the one to read while building
a document; the sections that follow argue why each group asks for what it asks. The
argument is not repeated in the table and the instruction is not repeated in the prose, so
neither can drift from the other.

:::rubric_template model
:::

# The premise — what the model is a model of

The first four rubrics are the ones most often assumed rather than stated, because to the
model's authors they are obvious.

- *M1 — Measurand and deliverable.* The measurand and what the model delivers, kept apart
  from what a reference measurement reports. These are routinely different quantities that
  share a name, and the gap between them is where validation quietly goes wrong: comparing
  a retrieved value against a field measurement of a different kind is an error no amount
  of downstream rigor recovers from, because the two are related only through a conversion
  the comparison never performed.
- *M2 — Why kinds are load-bearing here.* Why the kind layer is load-bearing
  *in this domain* rather than in general. This blueprint argues the general case; a model
  document's job is the specific one — which of its own quantities land on dimension one,
  and which of its own confusions survive a unit check. A model whose quantities are
  mostly dimensioned has a weaker claim on the machinery than one where the dimension
  layer discriminates almost nothing, and saying which it is tells a reader how much of
  the model's safety is coming from where.
- *M3 — Cite the discipline, do not re-argue it.* The converse obligation, and a
  prohibition as much as a requirement. A domain document that restates the case for kinds
  ages against this blueprint, contradicts it in the details, and buries its own subject.
  The right form is a section that names what is assumed and points at where it is
  established.
- *M4 — The spine: measurement chain and layer map.* The measurement chain in the order
  the physics runs it, and the map from the document's claims to the layers of the library
  that hold them. This is what lets a reader who cares about one step find the one chapter
  and the one layer that answer for it.

# The kind vocabulary — and the audits that close it

A model's kind vocabulary is only as good as its *closure*. Two things can escape it: a
quantity the document names but the code carries as a bare number, and an operation on
kinded values the declared algebra never licensed — a product formed outside the
arithmetic surface, or a crossing between two kinds performed without being authored. The
difference between a model that has declared some kinds and a model whose kind discipline
is load-bearing is whether anything checks for either, and rubrics M5 through M10 are all
variations on that question. The closure asked for is over the document's own vocabulary
and not over its domain: it makes no claim that the model covers the physics, only that
every quantity the model *does* name is inside the discipline, and every step out of the
discipline is authored.

- *M5 — The kind inventory.* Every quantity the document names is a declared kind-typed
  quantity, reported as an *inventory* rather than a survey — a table generated by walking
  the compiled environment, which cannot omit a declaration the way a grep can.
- *M6 — Individuating dimension one.* Kinds of dimension one are individuated by their
  examination principle, with the procedure ⊑ method ⊑ principle refinement recorded:
  inside the dimension-one fiber the principle is the *only* thing that separates two
  kinds, so a model that declares such kinds without recording what examines them has
  named them, not individuated them.
- *M7 — Dedications, and the separations proved.* Dedications to systems and components
  are declared, and — the part that makes it a `checked` rubric rather than a `generated`
  one — each separation the model *relies on* is proved. A dedication nothing depends on
  separating is inventory; a dedication a chapter's argument rests on is a theorem.
- *M8 — The arithmetic surface.* The complete list of products, quotients and powers the
  model is permitted to form. Read the other way, it is the list of combinations the model
  has decided are meaningless, which is the more useful reading and the one a generated
  table gives for free.
- *M9 — Authored departures, gated by an audit.* The rubric the group exists for. Every
  departure from the algebra — a genuine meeting of two kinds, kind-preserving plumbing
  the algebra does not name, a point where a kinded value leaves the calculus — must be
  *authored*, and an audit that fails the build on an unauthored one is what turns the
  resulting list from a survey into an inventory. Without that audit the list means "the
  crossings someone thought to write down"; with it, the list is closed.
- *M10 — Dimensional coverage and inter-derivability.* Two audits that report rather than
  gate. Dimensional coverage checks each authored edge against the dimension functor — the
  one layer that can mechanically refute an authored axiom, since an edge over genuinely
  dimensioned kinds whose exponents fail to balance is *wrong*, not merely undeclared —
  and its value is the inventory it produces: where the dimensioned content actually
  lives, and how much of the model is dimension one and therefore the kind layer's problem
  alone. And where kinds are inter-derivable — where each can be manufactured from the
  others by licensed steps, so the algebra cannot refuse a substitution between them — the
  template asks that this be drawn and pinned rather than left implicit. A model with such
  clusters is not defective; a model that has them and does not say so is.

# The model as modules

Rubrics M11 through M16 are the *Metrological modularity* chapter's paradigm read as an
obligation on a document.

- *M11 — Boundaries as declared modules.* Each boundary is a declared metrological module
  of kind-typed ports.
- *M12 — Behavior as a theorem edge.* A module's behavior is a measurement model carried
  as a theorem edge rather than as prose beside it.
- *M13 — The implementation relation, named.* The implementation's relation to that model
  is *named*: equals, inverts, refines, or bounded by a kinded tolerance.
- *M14 — Licenses per carrier rung.* The rubric this project has been bitten by, and it
  generalizes past metrology: laws transfer across the carrier ladder and side conditions
  do not. A theorem proved over the reals is a statement about the reals; the licenses
  under which it survives to the executable carrier are separate, per rung, and must be
  stated there. A document that proves at one rung and deploys at another without saying
  so has published a claim about something other than the thing it ships.
- *M15 — Mereology per output port.* Mereology is declared per output port — which outputs
  aggregate over parts and which do not — and any recarving or sharding of a batch is
  licensed by that declaration rather than by the fact that it happened to work.
- *M16 — A specification sheet per boundary.* One specification sheet per boundary,
  generated from the checked declaration: the page one hands a prospective consumer, which
  the same commit that changes a contract either regenerates or fails on.

# Carriers, adequacy and uncertainty

Three rubrics separate the specification from the thing that runs.

- *M17 — Two carriers, and the bridge.* The specification carrier and the executable
  carrier are distinguished, and the bridge between them is named.
- *M18 — Numerical adequacy.* The deployed representation is shown *numerically adequate*:
  it loses no information at the scale of the input uncertainties. That is a claim about
  the model's own numbers rather than a general preference for wider floats.
- *M19 — The uncertainty rung and its coverage.* Uncertainty names the rung of the method
  ladder it was computed at and the coverage its recorded variance certifies; an
  uncertainty reported without either is a number without an interpretation.

# Well-posedness and honest failure

- *M20 — Existence and uniqueness on a declared domain.* Where a model is inverted,
  existence and uniqueness are proved *on a declared domain* — a proof, and a domain the
  proof is about.
- *M21 — Failure outside the domain.* What happens outside it. This is the rubric that
  separates a retrieval that is right where it applies from one that is dangerous where it
  does not: failure outside the domain must be detected and reported, and ambiguity must
  be surfaced rather than silently resolved to whichever root the algorithm happened to
  reach.
- *M22 — Conditioning in the contract.* The conditioning and quality outputs a consumer
  needs in order to act on either are part of the declared contract, not a side channel a
  downstream stage may or may not read.

# Assurance — and what a green status does not mean

The last group is about the document's own evidence.

- *M23 — Claims linked to declarations.* Every load-bearing definition and theorem links
  to the declaration realizing it and carries that declaration's machine-checked status,
  so a reader can follow any equation to the source the deployed code is built from.
- *M24 — Graph and ledger from the same nodes.* A dependency graph and an assurance ledger
  generated from those same nodes — generated from the same nodes specifically, so that
  neither view can omit a claim the chapters cite.
- *M25 — The limits of a green status.* The rubric that keeps the other twenty-five
  honest. A green status means a particular thing, and the two ways it is over-read are
  both worth stating in the document rather than leaving to the reader: a theorem proved
  at the real-number carrier is not a statement about the floating-point kernel that runs,
  and a measured quantity is not a proved one. A document that states both limits plainly
  is stronger than one that does not, not weaker.
- *M26 — What a measurement must name.* The measurement half of that, made concrete. A
  speedup is a curve and not a number; a best-of-`n` is biased by `n`; a threshold below
  the dispersion of the measurement it is compared against decides nothing. The rubric is
  discharged by naming, for each reported measurement, the parameter it was swept over,
  the denominator it is relative to, and the statistic it reports.

# What the machine can hold, and what it cannot

Everything above is about what a document must contain. This section is about something
else: whether anything can check that it contains *all* of it.

:::rubric_closure_count model
:::

The two are easy to confuse, because a conformance matrix reports them in one word. A
status is computed from whether the document offers a *site* — one declaration, one
section — in each channel the rubric's evidence kind requires. A site is never a claim
about the rest, so two annotated theorems and two hundred read identically. Where a
rubric's population can be walked by the machine, that gap can be closed; where it cannot,
the rubric is reporting an exemplar and has to be read as one.

A census needs three things, and each of them either exists or does not.

- *A population that is a type.* `#kind_contracts` sweeps every declared contract under a
  namespace — membership is by type, so declaring a boundary enrolls it. That is the whole
  difference between a census and a list: enrolment has to be a side effect of doing the
  work, never a second act of remembering. Where the population is what the document
  *says* — the measurand, the case for kinds in this domain, the limits of a green status
  — no such type exists, and no census can.
- *A decidable per-member predicate.* M6 has one: a kind of dimension one either carries
  an examination principle or it does not. M7 does not — "each separation the model
  *relies on*" is not a machine notion, and the nearest mechanical proxy, every pair of
  dedicated kinds that meet in one signature, is a different claim. Choosing that proxy is
  a design decision to be made and written down, not a formality to be skipped on the way
  to an audit.
- *Declarable exceptions.* A census with honest negatives and no way to record them is a
  census someone will switch off. Kinds of dimension one that are principle-free on
  purpose — a geometry vocabulary, a nominal designation — are the ordinary case, and an
  audit that cannot be told so is an audit that gets deleted. `@[kindCounterexample]` and
  the declared clusters `#kind_scc_clean` takes are the library's two idioms for it: the
  legitimate gap becomes data rather than a sentence in a docstring no audit can read.

Where all three hold, the population can be held at one of three strengths, and the
library names them. A *reading* answers a question. A *record* is a reading pinned with
`#guard_msgs`: the whole answer is reviewable in the diff and a changed answer fails the
build. A *gate* is the `_clean` form, which throws and carries no message to re-bless —
kept separate from the record for the reason every violation-capable pin needs a gate
beside it, that pinning a violation is how it stops being noticed.

The table below says where each rubric of this template stands. The rows to watch are the
ones reading *census possible*: their population could be enumerated and nothing
enumerates it, so the rubric is discharged by whichever instances the author remembered,
and a green cell on such a row is a statement about those instances and not about the
model.

:::rubric_closure model
:::

# How a document declares conformance

A document answers to the template by declaring *where* it addresses each rubric, through
two channels with different guarantees. A *declaration site* is the `@[rubric "M12"]`
attribute on a real declaration, applied from a separate module the way the requirement
annotations are; because it attaches to a declaration, a site cannot name one that does
not exist, and a rename is a compile error. A *section site* names the tag of the
section that states the rubric; the conformance matrix renders it as a cross-reference, so
a dangling tag is a render error.

*Every* rubric requires a section site, whatever its evidence kind. The template is a
claim about a document, so a rubric discharged only by a declaration is one the document
never mentions, and reporting that as addressed would be the false green the whole
arrangement exists to prevent. What the evidence kind adds is whether a declaration is
required *as well*: for everything but exposition, it is.

A rubric with sites in some but not every required channel therefore reads `partial`
rather than passing, and it does so in both directions. A generated view cited by section
with no generator named is a hand-maintained table claiming to be a live one; a theorem
annotated with no section citing it is a green declaration the document is silent about.
Both are the case a single "done" would hide.

The status of each rubric is therefore computed from the sites and the rubric's own
evidence kind. There is no switch to forget to flip, and the worked instance of the whole
arrangement is soil-moisture-model's technical reference, whose conformance matrix is
generated this way against this template.

One limit of that computation is worth stating where an author will meet it. The status
asks whether a site *exists*, never what the site covers. A rubric whose closure is a
census can therefore be discharged by a declaration that is not that census — two theorems
standing in for a sweep — and no cell of the matrix distinguishes the two. Until a rubric
names the audit that closes it and the status requires that audit among its sites, a green
cell on a *census possible* row means the author remembered; the closure table above is
where a reader finds out which cells those are.
