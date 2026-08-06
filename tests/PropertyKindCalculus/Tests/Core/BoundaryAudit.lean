/-
# Validation probes — the boundary audit (invariants 6 & 7)

`#kind_boundary_audit` is to the calculus's *boundaries* what `#kind_edges` is to its *edges*
and `#print axioms` is to its proofs: the machine enumeration that a probe pins, so a new
untagged interior mint fails the build. This probe authors one site of each sanctioned tier
(`@[kindCrossing]`, `@[carrierVocab]`, `@[kindConst]`, `@[kindEmission]`), one **untagged**
mint (the violation the audit must catch), a clean pass-through and a Prop-former (which must
*not* register — a specification is legitimately about `.magnitude`, exactly as a theorem is),
and a downstream carrier registered through `@[kindCarrier]`, then pins the sorted report and
the crossings enumeration.
-/
import PropertyKindCalculus.BoundaryAudit

namespace PropertyKindCalculus.Tests.BoundaryAudit

open PropertyKindCalculus

/-- The probe kind whose boundary sites the audit reports. -/
def probeKind : KindOfProperty := { id := "boundary-audit probe kind", scale := .ratio }

/-- A tagged crossing that mints probeKind from a raw carrier value. -/
@[kindCrossing]
def crossingSite (x : Float) : Quantity probeKind Float := ⟨x⟩

/-- A carrier-vocabulary exception: a branchless min dropping to the carrier. -/
@[carrierVocab]
def vocabSite (a b : Quantity probeKind Float) : Quantity probeKind Float :=
  ⟨min a.magnitude b.magnitude⟩

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

/-- A tagged crossing minting the registered downstream carrier. -/
@[kindCrossing]
def taggedSite (x : Float) : Tagged probeKind Float := ⟨x⟩

/-! ## The pinned audit report and crossings enumeration -/

/--
info: boundary audit:
[carrierVocab] PropertyKindCalculus.Tests.BoundaryAudit.vocabSite — mints: probeKind
[kindConst] PropertyKindCalculus.Tests.BoundaryAudit.constSite — mints: probeKind
[kindCrossing] PropertyKindCalculus.Tests.BoundaryAudit.crossingSite — mints: probeKind
[kindCrossing] PropertyKindCalculus.Tests.BoundaryAudit.taggedSite — mints: probeKind
[kindEmission] PropertyKindCalculus.Tests.BoundaryAudit.emissionSite — erases (emission-only)
⚠ UNTAGGED PropertyKindCalculus.Tests.BoundaryAudit.violationSite — mints: probeKind
6 boundary site(s): 5 tagged, 1 UNTAGGED — invariant 6/7 violation
-/
#guard_msgs in
#kind_boundary_audit PropertyKindCalculus.Tests.BoundaryAudit

/--
info: tagged boundary crossings:
[carrierVocab] PropertyKindCalculus.Tests.BoundaryAudit.vocabSite — A carrier-vocabulary exception: a branchless min dropping to the carrier.
[kindConst] PropertyKindCalculus.Tests.BoundaryAudit.constSite — A declared constant mint: an adjudicated value enters the calculus as data.
[kindCrossing] PropertyKindCalculus.Tests.BoundaryAudit.crossingSite — A tagged crossing that mints probeKind from a raw carrier value.
[kindCrossing] PropertyKindCalculus.Tests.BoundaryAudit.taggedSite — A tagged crossing minting the registered downstream carrier.
[kindEmission] PropertyKindCalculus.Tests.BoundaryAudit.emissionSite — An emission boundary: a kinded value becomes naked for a consumer.
-/
#guard_msgs in
#kind_crossings PropertyKindCalculus.Tests.BoundaryAudit

end PropertyKindCalculus.Tests.BoundaryAudit
