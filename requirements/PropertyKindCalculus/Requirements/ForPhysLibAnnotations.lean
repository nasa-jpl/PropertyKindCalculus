/-
# Requirement annotations on the ForPhysLib benchmark — applied from afar

Attaches the `@[requirement …]` traceability attribute to the ForPhysLib case-study
declarations that *exemplify* requirements minted from that benchmark — chiefly R21
(ergonomics and erasure), whose evidence was proved in the benchmark's scorecard
before the requirement existed in the catalogue — and to the ClassicalMechanics
audit contracts, the worked exemplars of R24's scoped-audit discipline.

The one place the Requirements library reaches into the `ForPhysLib` library, the
same isolation discipline `DimensionAnnotations` follows for the Dimension layer.
Pulls in PhysLib + Mathlib transitively — as `DimensionAnnotations` already does, so
this adds no dependency the library did not have.
-/

module

public import ForPhysLib.CaseStudies.HarmonicOscillator.Scorecard
meta import ForPhysLib.CaseStudies.HarmonicOscillator.Scorecard
public import ForPhysLib.ClassicalMechanics.Audits
meta import ForPhysLib.ClassicalMechanics.Audits
public import PropertyKindCalculus.Requirements.Attributes
meta import PropertyKindCalculus.Requirements.Attributes

/-! ## Ergonomics and erasure (R21) -/

@[expose] public section Blanket

attribute [requirement "R21" exemplifies "the most verbose authoring (PKC longhand) computes exactly the least verbose one (bare reals), at the potential-energy model"]
  PropertyKindCalculus.Examples.HarmonicOscillator.Scorecard.mr11_pkc_same_value
attribute [requirement "R21" exemplifies "the OperatorTable form `m * (ω * ω) * (x * x)` elaborates to the same term as the longhand form — character-identical to bare reals"]
  PropertyKindCalculus.Examples.HarmonicOscillator.Scorecard.mr11_operators_same_term

/-! ## Object identity at system scale (R19, R22) -/

attribute [requirement "R22" exemplifies "same kind, different object: the tagging dilemma resolved by two independent axes rather than a dimension tag"]
  PropertyKindCalculus.Examples.HarmonicOscillator.Attempt4.no_dilemma

/-! ## Specialization at the quantity level (R2) -/

attribute [requirement "R2" exemplifies "kinetic and potential energy: distinct kinds, mutually comparable, and the Hamiltonian lands at the join — the benchmark probe that minted the specialization lift"]
  PropertyKindCalculus.Examples.HarmonicOscillator.Scorecard.mr32_attempt4_swept

/-! ## The audit as a claim about its scope, never about the library (R24) -/

attribute [requirement "R24" exemplifies "the kinded interior of a whole PhysLib directory, gated unkinded-empty: a naked binder added to the scope is a build failure"]
  ForPhysLib.ClassicalMechanics.Audits.interiorScope
attribute [requirement "R24" exemplifies "the same directory's ingest boundary, measured rather than gated — 72 unkinded positions enumerated so growth is visible — while the silent mint ratchet lets the blessed scope grow only by attestation"]
  ForPhysLib.ClassicalMechanics.Audits.ingestBoundary

end Blanket
