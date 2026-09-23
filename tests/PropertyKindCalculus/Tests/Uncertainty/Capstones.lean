/-
# Validation probes — the axiom profile behind every `proved` capstone of the uncertainty chapter

The blueprint marks a node `proved` to mean *sorry-free as certified by the axiom set*, not
merely that no `sorry` keyword appears. That is a claim about a Lean declaration, and this file
is where the uncertainty chapter's capstones discharge it: one `#print axioms` gate per node, so
a proof silently relocated behind a `sorry` — which emits no warning at its callers — fails the
build here rather than going on being advertised as proved.

Three of the chapter's capstones are gated in `UncertaintyLadder` alongside their worked
inhabitation witnesses (`gum_eq_willink_of_normal`, `Adequacy.verdict_sound`,
`Coverage.coverageBound_stdUnc`); the remaining five are gated here. `[propext,
Classical.choice, Quot.sound]` is the expected profile — Mathlib measure theory and real
analysis are classical — and what the gate rules out is `sorryAx`.
-/

module

public import PropertyKindCalculus.Uncertainty.Convolution
public import PropertyKindCalculus.Uncertainty.BudgetDagLaws
public import PropertyKindCalculus.Uncertainty.Adequacy.Fp32Grounding
public import PropertyKindCalculus.Uncertainty.Adequacy.DagBound
public import PropertyKindCalculus.Uncertainty.Adequacy.ExecBridge
public import PropertyKindCalculus.Uncertainty.Adequacy.RefinementBridge

@[expose] public section Blanket

namespace PropertyKindCalculus.Tests.UncertaintyCapstones

open PropertyKindCalculus

/-- info: 'PropertyKindCalculus.Uncertainty.cumulantsOf_combinedDeviation' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Uncertainty.cumulantsOf_combinedDeviation

/-- info: 'PropertyKindCalculus.Uncertainty.BudgetExpr.propagateQ_unc_eq_combinedQ' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Uncertainty.BudgetExpr.propagateQ_unc_eq_combinedQ

/-- info: 'PropertyKindCalculus.Uncertainty.Adequacy.round32_sterbenz_exact' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Uncertainty.Adequacy.round32_sterbenz_exact

/-- info: 'PropertyKindCalculus.Uncertainty.Adequacy.dag_fp32_box_faithful' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Uncertainty.Adequacy.dag_fp32_box_faithful

/-- info: 'PropertyKindCalculus.Uncertainty.Adequacy.exec_verdict_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Uncertainty.Adequacy.exec_verdict_sound

/-- info: 'PropertyKindCalculus.Uncertainty.Adequacy.flagFree_iff_exactRepresentable' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Uncertainty.Adequacy.flagFree_iff_exactRepresentable

/-- info: 'PropertyKindCalculus.Uncertainty.Adequacy.dag_fp32_box_exact_of_exactRepresentable' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Uncertainty.Adequacy.dag_fp32_box_exact_of_exactRepresentable

/-! ## The minimality lever, and that the relocated condition is not vacuous

`round32_eq_self_iff` is what makes `ExactRepresentable` *minimal* rather than merely sufficient: it
says the representable reals are exactly the fixed points of rounding, so no weaker condition on a
node's exact value stops that node from rounding. The two probes below check the characterization
fires in each direction on a value it can decide, so the pin above is a pin on something that
discriminates. -/

open TorchLean.Floats Uncertainty.Adequacy in
example : round32 (1:ℝ) = 1 := (round32_eq_self_iff 1).mpr one_representable

open TorchLean.Floats Uncertainty.Adequacy FloatLib.Floats.Formats.Flocq FloatLib.Numerics in
example : genericFormat binaryRadix fexp32 (round32 (0.1 : ℝ)) :=
  (round32_eq_self_iff _).mp (round32_fix (round32_representable 0.1))

/-! ## Which bridge carries which half of A3′ (`UNCERTAINTY.md` §7)

The consolidation question was whether the adequacy layer should route through `CarrierRefinement`
or through TorchLean's per-operation error bounds. The answer is both, with a division of labour,
and `Adequacy.RefinementBridge` is where that is checked rather than asserted: the refinement's
rounding *is* the format's, so the exactness half of A3′ is a `CarrierRefinement` statement, while
the forward-error accumulation stays metric. The pins below are on the identification itself. -/

/-- info: 'PropertyKindCalculus.Uncertainty.Adequacy.refinementFixes_iff_exactRepresentable' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
  #print axioms Uncertainty.Adequacy.refinementFixes_iff_exactRepresentable

/-- info: 'PropertyKindCalculus.Uncertainty.Adequacy.toSpec_box_exact' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Uncertainty.Adequacy.toSpec_box_exact

-- The identification the whole argument rests on: the R10 bridge's rounding is `round32`, by
-- definition and not by transport.
open TorchLean.Floats Uncertainty.Adequacy in
example (x : ℝ) : CarrierRefinement.round (E := FP32) x = round32 x := rfl

end PropertyKindCalculus.Tests.UncertaintyCapstones

end Blanket
