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
home instead, one site of the new `@[kindIngest]` tier. -/
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

/-! ## The pinned audit report and crossings enumeration -/

/--
info: boundary audit:
[carrierVocab] PropertyKindCalculus.Tests.BoundaryAudit.parametricFamilySite — mints: PropertyKindCalculus.Tests.BoundaryAudit.probeFamily (parametric)
[carrierVocab] PropertyKindCalculus.Tests.BoundaryAudit.parametricSite — mints: (kind-parametric)
[carrierVocab] PropertyKindCalculus.Tests.BoundaryAudit.vocabSite — mints: probeKind
[kindConst] PropertyKindCalculus.Tests.BoundaryAudit.constSite — mints: probeKind
[kindCrossing] PropertyKindCalculus.Tests.BoundaryAudit.crossingSite — mints: probeKind
[kindCrossing] PropertyKindCalculus.Tests.BoundaryAudit.taggedSite — mints: probeKind
[kindEmission] PropertyKindCalculus.Tests.BoundaryAudit.emissionSite — erases (emission-only)
[kindIngest] PropertyKindCalculus.Tests.BoundaryAudit.ingestSite — mints: probeKind
⚠ UNTAGGED PropertyKindCalculus.Tests.BoundaryAudit.violationSite — mints: probeKind
9 boundary site(s): 8 tagged, 1 UNTAGGED — invariant 6/7 violation
-/
#guard_msgs in
#kind_boundary_audit PropertyKindCalculus.Tests.BoundaryAudit

/--
info: tagged boundary crossings:
[carrierVocab] PropertyKindCalculus.Tests.BoundaryAudit.parametricFamilySite — An applied kind-parametric site: the minted kind is a named family at a variable argument.
[carrierVocab] PropertyKindCalculus.Tests.BoundaryAudit.parametricSite — A kind-parametric vocabulary site: the minted kind is a *variable* of the site, so the
[carrierVocab] PropertyKindCalculus.Tests.BoundaryAudit.vocabSite — A carrier-vocabulary exception: a branchless min dropping to the carrier.
[kindConst] PropertyKindCalculus.Tests.BoundaryAudit.constSite — A declared constant mint: an adjudicated value enters the calculus as data.
[kindCrossing] PropertyKindCalculus.Tests.BoundaryAudit.crossingSite — A tagged crossing that mints probeKind from an already-kinded probeKind2 value.
[kindCrossing] PropertyKindCalculus.Tests.BoundaryAudit.taggedSite — A tagged crossing minting the registered downstream carrier from an already-kinded value.
[kindEmission] PropertyKindCalculus.Tests.BoundaryAudit.emissionSite — An emission boundary: a kinded value becomes naked for a consumer.
[kindIngest] PropertyKindCalculus.Tests.BoundaryAudit.ingestSite — A checked ingest mint: a raw carrier value enters the calculus as probeKind, admitted by an
-/
#guard_msgs in
#kind_crossings PropertyKindCalculus.Tests.BoundaryAudit

end PropertyKindCalculus.Tests.BoundaryAudit
