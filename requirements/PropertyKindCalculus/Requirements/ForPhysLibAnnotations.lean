/-
# Requirement annotations on the ForPhysLib benchmark — applied from afar

Attaches the `@[requirement …]` traceability attribute to the ForPhysLib case-study
declarations that *exemplify* requirements minted from that benchmark — chiefly R21
(ergonomics and erasure), whose evidence was proved in the benchmark's scorecard
before the requirement existed in the catalogue.

The one place the Requirements library reaches into the `ForPhysLib` library, the
same isolation discipline `DimensionAnnotations` follows for the Dimension layer.
Pulls in PhysLib + Mathlib transitively — as `DimensionAnnotations` already does, so
this adds no dependency the library did not have.
-/

import ForPhysLib.CaseStudies.HarmonicOscillator.Scorecard
import PropertyKindCalculus.Requirements.Attributes

/-! ## Ergonomics and erasure (R21) -/

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
