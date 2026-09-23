import Verso
import VersoManual
import VersoBlueprint
import PropertyKindCalculusBlueprint.RubricTable

open Verso.Genre
open Verso.Genre.Manual
open Informal
open PropertyKindCalculusBlueprint.RubricTemplate

#doc (Manual) "Deploying a domain model: the deployment template" =>
%%%
tag := "deployment-template"
%%%

A model document says what a boundary *is*. A deployment document says what deploying one
*adds*, and the two are different enough that a single document doing both does neither
well. The model's reader wants to know what is proved and at which carrier; the
deployment's reader wants to know what will run, on what, against which contract, and what
would have to fail for the result to be rejected.

The separation is not editorial tidiness. Almost everything the deployment adds is
*unproved by construction*: an image is built, not derived; a shard size is measured, not
theorem-backed; a queue is chosen. Mixing that material into the model document lets the
model's green nodes lend it an assurance it does not have. Keeping it separate forces the
deployment to carry its own evidence, which is what this template enumerates.

:::rubric_count deployment
:::

# The template

The rows below are generated from `PropertyKindCalculus.Rubrics.deploymentTemplate`. The
*author's part* column is the one to read while building a document; the sections that
follow argue why each group asks for what it asks. Conformance is declared exactly as for
the model template: declaration sites through the `@[rubric …]` attribute, section sites
through the document's own tags, and a status computed from the two against each rubric's
evidence kind.

:::rubric_template deployment
:::

# What is deployed

- *D1 — The deployed units.* The list — which units are deployed, and which model boundary
  each one realizes. A deployment that cannot name the boundary it implements has no
  specification to be judged against, and its acceptance gate is therefore a comparison
  against itself.
- *D2 — What deploying adds.* The counterpart of the model template's M3, pointed the
  other way: state what deploying adds, and cite the model document for what the module
  is. A deployment document that re-explains the physics duplicates a text that will move
  without it.

# The contracts

Three rubrics fix what a deployed unit is held to, and all three ask for the contract to
be *decidable* rather than documented.

- *D3 — The data contract.* The payload interface a unit reads and writes, declared,
  compiled into the executable, and validated against a producer's own claims
  *before any payload is decoded*. Checking after decoding is checking too late — by then
  a mis-channeled array has already been read as something it is not, and the failure
  surfaces as a wrong number rather than a rejection.
- *D4 — The platform contract.* The argument plane the job scheduler passes, kind-typed
  and held to the registration payload, with the discharge relation between the two
  decided by the kernel rather than kept in step by hand. This is the seam where a
  deployment most often rots — the registration record and the executable's expectations
  drift apart across a rename — and it is the one seam where a machine-checked relation
  costs almost nothing.
- *D5 — A deployment card per unit.* One deployment card per deployed unit, each panel
  read off a declared object. The card is the specification sheet of the *deployment*
  rather than of the model: the argument plane, the payload contract faces, the sizing,
  the knobs, the container facts. Its value comes entirely from being read off
  declarations, so that changing a contract either regenerates the card or fails.

# Sizing and knobs

D6 and D7 are the rubrics that a deployment document is most tempted to skip, because the
numbers involved are easy to type and hard to justify.

- *D6 — Sizing from measured records.* A run is sized from measured records rather than
  from constants typed by hand. A hand-typed size does not report the machine; it reports
  how far from saturation the author's memory happened to be.
- *D7 — Operating points from a sweep.* Operating points come from a sweep whose own
  turnover or plateau names them, reported with the dispersion any threshold has to beat.
  A threshold below the resolution of the measurement that produced it decides nothing,
  and — the part worth watching for — it fails *silently*, printing an optimum chosen by
  scatter. Reporting the dispersion beside the decision is what makes the failure visible,
  and refusing a comparison the data cannot support is a better answer than making one.
- *D8 — The environment knobs.* Every environment knob a job may set is enumerated with
  what it decides. A knob that is settable and undocumented is a way for a run to differ
  from the run that was accepted.

# The platform

- *D9 — The image facts.* What ships per unit, the toolchain and architecture spectrum it
  was built for, and the ABI floor it runs against. The reason to state the spectrum
  rather than "it builds" is that the development box and the deployment image routinely
  differ in both compiler version and target set, and either difference can hide a failure
  that cannot appear locally.
- *D10 — Mechanized registration and version derivation.* Registration and version
  derivation are mechanized, so a deployed version is *derived from the artifact* rather
  than asserted beside it.
- *D11 — Backend interchange.* What backend interchange means for this deployment: what
  the same source does on each target, and what changes when the target does.

# Acceptance

- *D12 — Acceptance as a gate.* Acceptance is a gate against the specification the model
  document proves — run, as proof-by-execution, rather than asserted. This is the
  load-bearing link between the two documents: without it, everything the model proved
  stops at the model's own boundary.
- *D13 — A paired A/B in the executable.* Performance claims are a paired A/B in the
  deployed executable. A microbenchmark ranks; it does not predict. An isolated win of a
  factor of two and a half can be zero in the binary that ships, and the only measurement
  that settles the question is the one taken in the executable whose behavior is being
  claimed.
- *D14 — What each green signal covered.* The rubric that costs the least and is skipped
  the most: each green signal must name which of the changed lines it actually compiled or
  ran. A pipeline that passes without compiling the changed path is evidence about the
  paths it did compile and about nothing else, and quoting it as though it covered the
  change is how two defects survive three green signals.

# Reproducibility and limits

- *D15 — Failure, checkpoint and resume semantics.* What a partially completed job leaves
  behind, and what resuming it does with that.
- *D16 — The reproducibility manifest.* A manifest carrying the pins and digests of what
  actually ran, generated from the artifacts rather than transcribed from intent.
- *D17 — What is trusted.* The rubric that closes the template the way M25 closes the
  model's. Every deployment has boundaries its verification does not cross — a foreign
  function interface, a vendor runtime, a scheduler — and naming them is what lets a
  consumer distinguish what was checked from what was assumed. A deployment document that
  claims no limits is claiming the strongest thing in it, which is never true.

# What the machine can hold here

:::rubric_closure_count deployment
:::

The framing is the model template's — a census needs a population that is a type, a
decidable predicate on its members, and a way to declare the honest exceptions — but this
template's profile differs in kind, for the reason the chapter opened with. Almost
everything a deployment adds is unproved by construction: an image is built, a queue is
chosen, an ABI floor is what it is. More of this template is therefore prose, and a
document that states those facts plainly has done what can be done about them.

What is worth seeing in the table below is that the rows reading *census possible* are
nearly all one move from being held, and it is the same move each time. The sizing
records, the sweep behind each operating point, the settable knobs, the paired run behind
a performance claim — every one of them is data the deployment already has and currently
writes into a sentence. Declared instead of narrated, each becomes a population something
can walk, which is the step M9 took for crossings in the model template and the reason
that rubric gates where its neighbours only report.

:::rubric_closure deployment
:::
