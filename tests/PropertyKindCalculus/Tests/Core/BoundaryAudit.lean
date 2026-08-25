/-
# Validation probes — the boundary audit (invariants 6 & 7)

`#kind_boundary_audit` is to the calculus's *boundaries* what `#kind_edges` is to its *edges*
and `#print axioms` is to its proofs: the machine enumeration that a probe pins, so a new
untagged interior mint fails the build. This probe authors one site of each sanctioned tier
(`@[kindCrossing]`, `@[kindIngest]`, `@[carrierVocab]`, `@[kindConst]`, `@[kindEmission]`), a
kind-parametric site (whose mint must render `(kind-parametric)`, not a loose de Bruijn index),
an *applied* kind-parametric site (a named kind family applied to the site's variable — the
family keeps its name and the argument renders `(parametric)`, a token deliberately NOT
containing the bare case's, so the two cases are grep-distinct), one **untagged**
mint (the violation the audit must catch), a clean pass-through and a Prop-former (which must
*not* register — a specification is legitimately about `.magnitude`, exactly as a theorem is),
and a downstream carrier registered through `@[kindCarrier]`, then pins the sorted report and
the crossings enumeration.

`crossingSite` and `taggedSite` take a KINDED argument (`probeKind2`), not a raw `Float` —
`@[kindCrossing]`'s own `add` now rejects a naked-argument declaration (a crossing must have
something already kinded to cross FROM); `ingestSite` is the naked-argument shape's correct
home instead, one site of the new `@[kindIngest]` tier.

The attest probes pin the *attested-mint* column: a literal-reason site whose duplicate
renders with an explicit `(×2)` count, a parametric-kind site (the stable token, with the
reason alongside), and a DOWNSTREAM attestor registered through `@[kindAttest]` — whose own
body holds the sanctioned raw mint the walk must *skip*, exactly as it skips a carrier's own
`.mk`: were the skip wrong, `taggedAttest` would appear `⚠ UNTAGGED` and break the pin. -/
import PropertyKindCalculus.BoundaryAudit

namespace PropertyKindCalculus.Tests.BoundaryAudit

open PropertyKindCalculus

/-- The probe kind whose boundary sites the audit reports. -/
def probeKind : KindOfProperty := { id := "boundary-audit probe kind", scale := .ratio }

/-- A second probe kind, distinct from `probeKind` — `crossingSite`'s SOURCE, so the crossing is
genuinely kind-to-kind rather than raw-to-kind. -/
def probeKind2 : KindOfProperty := { id := "boundary-audit probe kind 2", scale := .ratio }

/-- A tagged crossing that mints probeKind from an already-kinded probeKind2 value. -/
@[kindCrossing]
def crossingSite (x : Quantity probeKind2 Float) : Quantity probeKind Float := ⟨x.magnitude⟩

/-- A checked ingest mint: a raw carrier value enters the calculus as probeKind, admitted by an
inline (trivial, here) check — the naked-argument shape `crossingSite` above is no longer
allowed to have. -/
@[kindIngest]
def ingestSite (x : Float) : Quantity probeKind Float := ⟨x⟩

/-- A carrier-vocabulary exception: a branchless min dropping to the carrier. -/
@[carrierVocab]
def vocabSite (a b : Quantity probeKind Float) : Quantity probeKind Float :=
  ⟨min a.magnitude b.magnitude⟩

/-- A kind-parametric vocabulary site: the minted kind is a *variable* of the site, so the
report renders `(kind-parametric)` — never a bare de Bruijn index or a pretty-printer
failure, both of which would poison a pinned block. -/
@[carrierVocab]
def parametricSite (k : KindOfProperty) (x : Float) : Quantity k Float := ⟨x⟩

/-- A probe kind *family*: one kind per label — the applied-parametric case's target. -/
def probeFamily (label : String) : KindOfProperty :=
  { id := s!"boundary-audit probe family {label}", scale := .ratio }

/-- An applied kind-parametric site: the minted kind is a named family at a variable argument.
The family's head is real information and keeps its name in the report; only the argument is
unnameable, so its own stable word marks the application — `probeFamily (parametric)`, a
token that does not contain the bare case's `(kind-parametric)`, so neither case can be
mistaken for (or found by a search for) the other. -/
@[carrierVocab]
def parametricFamilySite (label : String) (x : Float) : Quantity (probeFamily label) Float := ⟨x⟩

/-- A declared constant mint: an adjudicated value enters the calculus as data. -/
@[kindConst]
def constSite : Quantity probeKind Float := ⟨0.5⟩

/-- An emission boundary: a kinded value becomes naked for a consumer. -/
@[kindEmission]
def emissionSite (x : Quantity probeKind Float) : Float := x.magnitude

/-- The violation: an untagged mint, with no tier sanctioning it. -/
def violationSite (x : Float) : Quantity probeKind Float := ⟨x⟩

/-- A clean pass-through: no literal mint or erasure, so it is *not* boundary-active and must not
appear in the report (the audit does not false-positive on kinds flowing through). -/
def cleanSite (x : Quantity probeKind Float) : Quantity probeKind Float := x

/-- A Prop-former: a specification stated over `.magnitude`. Like a theorem, it is *about* the
boundary, not a boundary — it must not appear in the report. -/
def specSite (x : Quantity probeKind Float) : Prop := x.magnitude = 0.5

/-! ## A downstream carrier registered through `@[kindCarrier]` -/

/-- A toy single-field carrier, standing in for the model's `DedicatedQuantity`. -/
@[kindCarrier]
structure Tagged (k : KindOfProperty) (R : Type) where
  /-- The carried magnitude. -/
  magnitude : R

/-- A tagged crossing minting the registered downstream carrier from an already-kinded value. -/
@[kindCrossing]
def taggedSite (x : Quantity probeKind2 Float) : Tagged probeKind Float := ⟨x.magnitude⟩

/-! ## The attest probes — the attested-mint column -/

/-- An attested interior mint, twice with one reason: the report carries the harvested reason
and groups the two identical sites with an explicit count — multiplicity is the point of the
attested column, never deduplicated away. -/
@[carrierVocab]
def attestSite (x : Quantity probeKind Float) : Quantity probeKind Float :=
  let seed : Quantity probeKind Float := .attest "an authored accumulator seed" 0.0
  let bias : Quantity probeKind Float := .attest "an authored accumulator seed" 0.0
  x + seed + bias

/-- An attested parametric mint: the attested kind is a *variable* of the site, rendering the
same stable token a raw parametric mint does — with the reason alongside. -/
@[carrierVocab]
def attestParametricSite (k : KindOfProperty) (x : Float) : Quantity k Float :=
  .attest "an authored parametric wrap" x

/-- A downstream attestor registered through `@[kindAttest]`, standing in for a model layer's
wrapper over its own carrier: its body holds the one sanctioned raw mint — the mechanism,
reviewed at registration — so the walk must skip it rather than flag it UNTAGGED. -/
@[kindAttest]
def taggedAttest (k : KindOfProperty) (_why : String) (m : Float) : Tagged k Float := ⟨m⟩

/-- A site minting the downstream carrier through the downstream attestor: the report shows the
attested site here, and `taggedAttest` itself never appears. -/
@[carrierVocab]
def taggedAttestSite (x : Quantity probeKind Float) : Tagged probeKind Float :=
  taggedAttest probeKind "a downstream carrier's authored wrap" x.magnitude

/-! ## The pinned audit report and crossings enumeration -/

/--
info: boundary audit:
[carrierVocab] PropertyKindCalculus.Tests.BoundaryAudit.attestParametricSite — attests: (kind-parametric) ‹an authored parametric wrap›
[carrierVocab] PropertyKindCalculus.Tests.BoundaryAudit.attestSite — attests: probeKind ‹an authored accumulator seed› (×2)
[carrierVocab] PropertyKindCalculus.Tests.BoundaryAudit.parametricFamilySite — mints: PropertyKindCalculus.Tests.BoundaryAudit.probeFamily (parametric)
[carrierVocab] PropertyKindCalculus.Tests.BoundaryAudit.parametricSite — mints: (kind-parametric)
[carrierVocab] PropertyKindCalculus.Tests.BoundaryAudit.taggedAttestSite — attests: probeKind ‹a downstream carrier's authored wrap›
[carrierVocab] PropertyKindCalculus.Tests.BoundaryAudit.vocabSite — mints: probeKind
[kindConst] PropertyKindCalculus.Tests.BoundaryAudit.constSite — mints: probeKind
[kindCrossing] PropertyKindCalculus.Tests.BoundaryAudit.crossingSite — mints: probeKind
[kindCrossing] PropertyKindCalculus.Tests.BoundaryAudit.taggedSite — mints: probeKind
[kindEmission] PropertyKindCalculus.Tests.BoundaryAudit.emissionSite — erases (emission-only)
[kindIngest] PropertyKindCalculus.Tests.BoundaryAudit.ingestSite — mints: probeKind
⚠ UNTAGGED PropertyKindCalculus.Tests.BoundaryAudit.violationSite — mints: probeKind
12 boundary site(s): 11 tagged, 1 UNTAGGED — invariant 6/7 violation
-/
#guard_msgs in
#kind_boundary_audit PropertyKindCalculus.Tests.BoundaryAudit

/--
info: tagged boundary crossings:
[carrierVocab] PropertyKindCalculus.Tests.BoundaryAudit.attestParametricSite — An attested parametric mint: the attested kind is a *variable* of the site, rendering the
[carrierVocab] PropertyKindCalculus.Tests.BoundaryAudit.attestSite — An attested interior mint, twice with one reason: the report carries the harvested reason
[carrierVocab] PropertyKindCalculus.Tests.BoundaryAudit.parametricFamilySite — An applied kind-parametric site: the minted kind is a named family at a variable argument.
[carrierVocab] PropertyKindCalculus.Tests.BoundaryAudit.parametricSite — A kind-parametric vocabulary site: the minted kind is a *variable* of the site, so the
[carrierVocab] PropertyKindCalculus.Tests.BoundaryAudit.taggedAttestSite — A site minting the downstream carrier through the downstream attestor: the report shows the
[carrierVocab] PropertyKindCalculus.Tests.BoundaryAudit.vocabSite — A carrier-vocabulary exception: a branchless min dropping to the carrier.
[kindConst] PropertyKindCalculus.Tests.BoundaryAudit.constSite — A declared constant mint: an adjudicated value enters the calculus as data.
[kindCrossing] PropertyKindCalculus.Tests.BoundaryAudit.crossingSite — A tagged crossing that mints probeKind from an already-kinded probeKind2 value.
[kindCrossing] PropertyKindCalculus.Tests.BoundaryAudit.taggedSite — A tagged crossing minting the registered downstream carrier from an already-kinded value.
[kindEmission] PropertyKindCalculus.Tests.BoundaryAudit.emissionSite — An emission boundary: a kinded value becomes naked for a consumer.
[kindIngest] PropertyKindCalculus.Tests.BoundaryAudit.ingestSite — A checked ingest mint: a raw carrier value enters the calculus as probeKind, admitted by an
-/
#guard_msgs in
#kind_crossings PropertyKindCalculus.Tests.BoundaryAudit


/-! ## `#kind_boundary_clean` — the invariant, which cannot be re-blessed

The audit pinned above is a `#guard_msgs` record of a namespace that deliberately contains one
untagged site, and re-pinning such a record is exactly how the invariant would be signed away
by accident. `#kind_boundary_clean` carries no message to re-pin: it throws while any site is
untagged, so the two commands fail for independent reasons. -/

/-- error: boundary audit: 1 UNTAGGED boundary site(s) — invariant 6/7 violation
  ⚠ PropertyKindCalculus.Tests.BoundaryAudit.violationSite — mints: probeKind

Every declaration that mints or erases a registered carrier must carry the tier that sanctions it (`@[kindCrossing]`/`@[kindIngest]`/`@[carrierVocab]`/`@[kindConst]`/`@[kindEmission]`), with the reason in its docstring. Tag each site at the tier it actually is — do NOT re-pin a `#kind_boundary_audit` message whose summary says `violation`, which turns the build green and the invariant off.
-/
#guard_msgs (whitespace := lax) in
#kind_boundary_clean PropertyKindCalculus.Tests.BoundaryAudit

/-! A namespace whose every boundary site is adjudicated: the command passes silently, so a
clean scope adds nothing to the build output and only a violation is ever heard from. -/
namespace Clean

/-- A tagged constant mint — the whole boundary of this namespace, and it is sanctioned. -/
@[kindConst]
def onlySite : Quantity probeKind Float := ⟨1.0⟩

end Clean

-- no message: every site under `Clean` carries its tier
#guard_msgs in
#kind_boundary_clean PropertyKindCalculus.Tests.BoundaryAudit.Clean

/-! ## `#kind_mint_ratchet` — the phase-2 discipline: the raw column emptied where authored

The audit's two-column split makes raw mints *visible*; the ratchet makes the raw column
*empty* at the authored tiers (`[kindCrossing]`/`[carrierVocab]`): every mint there must be a
licensed derivation (which never reaches the raw column) or an attested one (which lands in
the reviewed column with its reason). `[kindConst]`/`[kindIngest]`/`[kindEmission]` keep raw
mints legal at the def granularity. Like `#kind_boundary_clean` it throws and pins nothing, so
it cannot be re-blessed. The parent namespace deliberately holds raw crossing/vocab mints, so
the gate fails on it — the error pinned here — and the `Ratcheted` namespace below is the
passing shape. -/

/-- error: mint ratchet: 5 `[kindCrossing]`/`[carrierVocab]` site(s) with raw mints
  ⚠ [carrierVocab] PropertyKindCalculus.Tests.BoundaryAudit.parametricFamilySite — mints: PropertyKindCalculus.Tests.BoundaryAudit.probeFamily (parametric)
  ⚠ [carrierVocab] PropertyKindCalculus.Tests.BoundaryAudit.parametricSite — mints: (kind-parametric)
  ⚠ [carrierVocab] PropertyKindCalculus.Tests.BoundaryAudit.vocabSite — mints: probeKind
  ⚠ [kindCrossing] PropertyKindCalculus.Tests.BoundaryAudit.crossingSite — mints: probeKind
  ⚠ [kindCrossing] PropertyKindCalculus.Tests.BoundaryAudit.taggedSite — mints: probeKind

At these tiers every mint must be a licensed derivation (`castCarrier`, `Quantity.get!`, a witness edge) or a `Quantity.attest why m` whose reason is harvested — a raw `⟨…⟩` is an anonymous claim the reviewed column never sees.
-/
#guard_msgs (whitespace := lax) in
#kind_mint_ratchet PropertyKindCalculus.Tests.BoundaryAudit

namespace Ratcheted

/-- A ratcheted crossing: the authored edge's mint carries its adjudication as an attest
reason — reviewed column, not raw. -/
@[kindCrossing]
def adjudicatedCrossing (x : Quantity probeKind2 Float) : Quantity probeKind Float :=
  .attest "the authored probe edge — kind 2's magnitude read at the probe kind" x.magnitude

/-- A ratcheted vocabulary site: a representation move through `castCarrier`, which keeps the
kind by parametricity — no mint anywhere, raw or reviewed. -/
@[carrierVocab]
def liftedVocab (x : Quantity probeKind Float) : Quantity probeKind (Array Float) :=
  x.castCarrier (fun m => #[m])

/-- A declared constant: raw `⟨…⟩` stays legal here — the value IS the data, and the def-level
tag with this docstring is the adjudication. -/
@[kindConst]
def ratchetConst : Quantity probeKind Float := ⟨2.5⟩

/-- A checked ingest: raw `⟨…⟩` stays legal here — the (trivial, here) check is the license. -/
@[kindIngest]
def ratchetIngest (x : Float) : Quantity probeKind Float := ⟨x⟩

/-- An emission body with a residual re-entry mint: legal at the def granularity — the
emission tier's own adjudication — so the ratchet does not fire on it. -/
@[kindEmission]
def ratchetEmission (x : Quantity probeKind Float) : Float × Quantity probeKind Float :=
  (x.magnitude, ⟨x.magnitude⟩)

end Ratcheted

-- no message: every crossing/vocab mint under `Ratcheted` is licensed or attested, and the
-- const/ingest/emission raw mints are at tiers the ratchet leaves at def granularity
#guard_msgs in
#kind_mint_ratchet PropertyKindCalculus.Tests.BoundaryAudit.Ratcheted

end PropertyKindCalculus.Tests.BoundaryAudit
