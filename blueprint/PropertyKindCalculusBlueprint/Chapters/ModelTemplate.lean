import Verso
import VersoManual
import VersoBlueprint
import PropertyKindCalculusBlueprint.RubricTable

open Verso.Genre
open Verso.Genre.Manual
open Informal
open PropertyKindCalculusBlueprint.RubricTemplate

#doc (Manual) "Applying the calculus to a domain: the model template" =>

The preceding chapters say what the calculus is and what it proves. This one is about the
document on the other side of it: what a *domain model* built on the calculus owes its
reader.

The obligation is not obvious, and getting it wrong is cheap. A model that declares its
kinds, proves its algebra and ships green nodes can still leave a reader unable to answer
the questions that decide whether the model may be used — what it is a model *of*, which
of its quantities the dimension layer cannot separate, at which carrier each theorem
holds, and which of its numbers were proved rather than measured. Those questions do not
have a house style; they have answers, and a document either contains them or it does not.
The template below is that list of questions.

# What a template is, and what it is not

A rubric is an obligation to *answer*, not a section to write. Two documents that
discharge the same rubric may look nothing alike: one may answer M2 in a paragraph of its
introduction and another in the closing page of a chapter, and both conform. What the
template fixes is the question and the *kind of evidence* that settles it.

That second half is the part worth stating carefully, because it is where a checklist
usually goes soft. Four kinds of evidence appear, and they are not interchangeable:

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
  the build.
- *Measured.* A reported measurement. This is a weaker thing than a proof and the
  template keeps it weaker on purpose: a measured result is discharged by naming the knob
  it was swept over, the denominator it is relative to, and the statistic it reports.

Reporting all four as a single "done" would let the cheapest evidence stand for the
dearest. Reported separately, a document's own matrix says which of its answers are
proved and which are merely written down.

:::rubric_count model
:::

# The premise — what the model is a model of

The first four rubrics are the ones most often assumed rather than stated, because to the
model's authors they are obvious.

M1 asks for the measurand and what the model delivers, *kept apart from what a reference
measurement reports*. These are routinely different quantities that share a name, and the
gap between them is where validation quietly goes wrong: comparing a retrieved value
against a field measurement of a different kind is an error no amount of downstream rigor
recovers from, because the two are related only through a conversion the comparison never
performed.

M2 asks why the kind layer is load-bearing *in this domain* rather than in general. The
blueprint argues the general case; a model document's job is the specific one — which of
its own quantities land on dimension one, and which of its own confusions survive a unit
check. A model whose quantities are mostly dimensioned has a weaker claim on the
machinery than one where the dimension layer discriminates almost nothing, and saying
which it is tells a reader how much of the model's safety is coming from where.

M3 is the converse obligation, and it is a prohibition as much as a requirement: cite the
discipline, do not re-argue it. A domain document that restates the case for kinds ages
against the blueprint, contradicts it in the details, and buries its own subject. The
right form is a section that names what is assumed and points at where it is established.

M4 asks for the spine — the measurement chain in the order the physics runs it, and the
map from the document's claims to the layers of the library that hold them. This is what
lets a reader who cares about one step find the one chapter and the one layer that answer
for it.

# The kind vocabulary — and the audits that close it

A model's kind vocabulary is only as good as its *closure*. The difference between a
model that has declared some kinds and a model whose kind discipline is load-bearing is
whether anything checks that nothing escaped, and rubrics M5 through M10 are all
variations on that question.

M5 asks that every quantity the document names be a declared kind-typed quantity, and
asks for it as an *inventory* rather than a survey — a table generated by walking the
compiled environment, which cannot omit a declaration the way a grep can. M6 asks that
kinds of dimension one be individuated by their examination principle, with the
procedure ⊑ method ⊑ principle refinement recorded: inside the dimension-one fiber the
principle is the *only* thing that separates two kinds, so a model that declares such
kinds without recording what examines them has named them, not individuated them. M7
asks that dedications to systems and components be declared, and — the part that makes it
a `checked` rubric rather than a `generated` one — that each separation the model *relies
on* be proved. A dedication nothing depends on separating is inventory; a dedication a
chapter's argument rests on is a theorem.

M8 asks for the arithmetic surface: the complete list of products, quotients and powers
the model is permitted to form. Read the other way, it is the list of combinations the
model has decided are meaningless, which is the more useful reading and the one a
generated table gives for free.

M9 is the rubric the group exists for. Every departure from the algebra — a genuine
meeting of two kinds, kind-preserving plumbing the algebra does not name, a point where a
kinded value leaves the calculus — must be *authored*, and an audit that fails the build
on an unauthored one is what turns the resulting list from a survey into an inventory.
Without that audit the list means "the crossings someone thought to write down"; with it,
the list is closed.

M10 asks for two audits that report rather than gate. Dimensional coverage checks each
authored edge against the dimension functor — the one layer that can mechanically refute
an authored axiom, since an edge over genuinely dimensioned kinds whose exponents fail to
balance is *wrong*, not merely undeclared — and its value is the inventory it produces:
where the dimensioned content actually lives, and how much of the model is dimension one
and therefore the kind layer's problem alone. And where kinds are inter-derivable — where
each can be manufactured from the others by licensed steps, so the algebra cannot refuse a
substitution between them — the template asks that this be drawn and pinned rather than
left implicit. A model with such clusters is not defective; a model that has them and does
not say so is.

# The model as modules

Rubrics M11 through M16 are the *Metrological modularity* chapter's paradigm read as an
obligation on a document. Each boundary is a declared module of kind-typed ports (M11);
its behavior is a measurement model carried as a theorem edge rather than prose beside it
(M12); the implementation's relation to that model is *named* — equals, inverts, refines,
or bounded by a kinded tolerance (M13).

M14 is the rubric this project has been bitten by, and it generalizes past metrology:
laws transfer across the carrier ladder and side conditions do not. A theorem proved over
the reals is a statement about the reals; the licenses under which it survives to the
executable carrier are separate, per rung, and must be stated there. A document that
proves at one rung and deploys at another without saying so has published a claim about
something other than the thing it ships.

M15 asks that mereology be declared per output port — which outputs aggregate over parts
and which do not — and that any recarving or sharding of a batch be licensed by that
declaration rather than by the fact that it happened to work. M16 asks for one
specification sheet per boundary, generated from the checked declaration: the page one
hands a prospective consumer, which the same commit that changes a contract either
regenerates or fails on.

# Carriers, adequacy and uncertainty

Three rubrics separate the specification from the thing that runs. M17 asks that the
specification carrier and the executable carrier be distinguished and the bridge between
them named. M18 asks that the deployed representation be shown *numerically adequate* —
that it loses no information at the scale of the input uncertainties — which is a claim
about the model's own numbers rather than a general preference for wider floats. M19 asks
that uncertainty name the rung of the method ladder it was computed at and the coverage
its recorded variance certifies; an uncertainty reported without either is a number
without an interpretation.

# Well-posedness and honest failure

Where a model is inverted, M20 asks for existence and uniqueness *on a declared domain* —
a proof, and a domain the proof is about. M21 asks what happens outside it. This is the
rubric that separates a retrieval that is right where it applies from one that is
dangerous where it does not: failure outside the domain must be detected and reported,
and ambiguity must be surfaced rather than silently resolved to whichever root the
algorithm happened to reach. M22 asks that the conditioning and quality outputs a consumer
needs in order to act on either be part of the declared contract, not a side channel a
downstream stage may or may not read.

# Assurance — and what a green status does not mean

The last group is about the document's own evidence. M23 asks that every load-bearing
definition and theorem link to the declaration realizing it and carry that declaration's
machine-checked status, so a reader can follow any equation to the source the deployed
code is built from. M24 asks for a dependency graph and an assurance ledger generated from
those same nodes — generated from the same nodes specifically, so that neither view can
omit a claim the chapters cite.

M25 is the rubric that keeps the other twenty-five honest. A green status means a
particular thing, and the two ways it is over-read are both worth stating in the document
rather than leaving to the reader: a theorem proved at the real-number carrier is not a
statement about the floating-point kernel that runs, and a measured quantity is not a
proved one. A document that states both limits plainly is stronger than one that does not,
not weaker.

M26 makes the measurement half of that concrete. A speedup is a curve and not a number; a
best-of-`n` is biased by `n`; a threshold below the dispersion of the measurement it is
compared against decides nothing. The rubric is discharged by naming, for each reported
measurement, the knob it was swept over, the denominator it is relative to, and the
statistic it reports.

# The template

The rows below are generated from `PropertyKindCalculus.Rubrics.modelTemplate`, so a
rubric added to the catalogue appears here without this chapter being edited, and one
removed cannot linger in it.

:::rubric_template model
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
