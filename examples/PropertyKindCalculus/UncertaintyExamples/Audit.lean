/-
# The provenance audit — the by-type gate over every boundary and edge in scope

The sweeps below enroll by **type**: every `Provenance.Contract` and every
`Provenance.Relation` declared anywhere under `PropertyKindCalculus.UncertaintyExamples`
is a subject, so an author who declares a boundary or an edge has enrolled it — there is
no per-declaration command to remember, and a new module's declarations are swept the
moment this module imports it. That is also why this module imports every sibling: a
sweep sees only its import closure, and an audit that under-imports under-reports
silently. The umbrella imports this module last, so the audit builds whenever the
library does.

Four tiers, each pinned:

  * `#kind_contracts` / `#kind_relations` — the reports: every subject re-checked as the
    per-name commands check one, violations as `✗` rows, and the `WaterCloudModel`
    falsification probes as `@[kindCounterexample]`-exempted `⊘` rows. The headers count
    subjects, violations, and exemptions, so the pins fail on a new violation, a
    vanished subject, or an exemption creep — not only on the rows they show.
  * `#kind_wellposedness_coverage` / `_clean` — the census over the `inverts` edges:
    the one live edge answers for its inversion with its `∃!` on the declared domain
    *and* the surfaced collapse outside it, so the gate passes and leaves its receipt.
  * `#kind_contracts_decide` — the kernel receipts: each passing boundary gains the
    theorem `c.kindContractOk : c.Agrees (graph)`, here rather than per name.
  * the `contracts` and `provenance-coverage` tables — the join and its complement:
    which theorem edges land on each boundary (counterexamples are not witnesses), and
    the declared absences. The one absence pinned below is real and stands recorded:
    the retrieval's soil-moisture output carries no declared uncertainty budget, while
    the forward's σ⁰ output does (rung 6 of the capstone).
-/

module

public import PropertyKindCalculus.UncertaintyExamples.DegenhardtFictive
public import PropertyKindCalculus.UncertaintyExamples.WillinkGaugeBlock
public import PropertyKindCalculus.UncertaintyExamples.DegenhardtSensitivity
public import PropertyKindCalculus.UncertaintyExamples.LadderNesting
public import PropertyKindCalculus.UncertaintyExamples.DegenhardtSsprc
public import PropertyKindCalculus.UncertaintyExamples.SsprcNesting
public import PropertyKindCalculus.UncertaintyExamples.DegenhardtAllocation
public import PropertyKindCalculus.UncertaintyExamples.WaterCloudModel
public meta import PropertyKindCalculus.UncertaintyExamples.WaterCloudModel
public import PropertyKindCalculus.UncertaintyExamples.AdequacySwamping
public import PropertyKindCalculus.UncertaintyExamples.AdequacyLadder
public import PropertyKindCalculus.UncertaintyExamples.AdequacyDag
public import PropertyKindCalculus.UncertaintyExamples.AdequacySterbenz32
public import PropertyKindCalculus.UncertaintyExamples.AdequacyExecBridge
public import PropertyKindCalculus.UncertaintyExamples.AdequacyCoupling
public import PropertyKindCalculus.UncertaintyExamples.AutogradDirectSim
public import PropertyKindCalculus.UncertaintyExamples.BudgetDagDensity
public import PropertyKindCalculus.UncertaintyExamples.Coverage
public import PropertyKindCalculus.Index
-- Private scope only, and no paired `public import`: core seals `Lean.Name.beq`, so a kernel
-- `decide` over a provenance graph whose kinds are `Name`s gets stuck without this.
import all Init.Prelude
-- Private scope only: an imported `theorem` reads back from `Environment.find?` as `.axiomInfo`,
-- and `#kind_relations` classifies its witnesses by that constructor. `import all` restores
-- `.thmInfo` for this module.
import all PropertyKindCalculus.UncertaintyExamples.WaterCloudModel

public section -- pkc-blanket
@[expose] section -- pkc-blanket-expose

/--
info: kind contracts — 4 contract(s), 2 exempted
  PropertyKindCalculus.UncertaintyExamples.WaterCloudModel.wcmBoundary: 'WCM forward (σ⁰)' — 8 ports, 0 exits, 1 member step(s)
  PropertyKindCalculus.UncertaintyExamples.WaterCloudModel.wcmRetrievalBoundary: 'WCM retrieval (mv)' — 8 ports, 0 exits, 1 member step(s)
  ⊘ PropertyKindCalculus.UncertaintyExamples.WaterCloudModel.Falsification.forgottenParameter: counterexample, exempted
  ⊘ PropertyKindCalculus.UncertaintyExamples.WaterCloudModel.Falsification.misdeclaredKind: counterexample, exempted
-/

#guard_msgs in #kind_contracts PropertyKindCalculus.UncertaintyExamples

/--
info: kind relations — 9 theorem edge(s), 8 exempted
  PropertyKindCalculus.UncertaintyExamples.WaterCloudModel.retrievalInvertsForward: 'WCM retrieval (mv)' inverts 'WCM forward (σ⁰)' — PropertyKindCalculus.UncertaintyExamples.WaterCloudModel.wcmRetrieveQ_wcmForwardQ [well-posed: PropertyKindCalculus.UncertaintyExamples.WaterCloudModel.wcmForwardQ_well_posed on PropertyKindCalculus.UncertaintyExamples.WaterCloudModel.soilGainNonzero] [ambiguity: PropertyKindCalculus.UncertaintyExamples.WaterCloudModel.wcmForwardQ_ambiguous_of_degenerate]
  ⊘ PropertyKindCalculus.UncertaintyExamples.WaterCloudModel.Falsification.misclaimedShape: counterexample, exempted
  ⊘ PropertyKindCalculus.UncertaintyExamples.WaterCloudModel.Falsification.misplacedWellPosed: counterexample, exempted
  ⊘ PropertyKindCalculus.UncertaintyExamples.WaterCloudModel.Falsification.strandedWitness: counterexample, exempted
  ⊘ PropertyKindCalculus.UncertaintyExamples.WaterCloudModel.Falsification.undomainedWellPosed: counterexample, exempted
  ⊘ PropertyKindCalculus.UncertaintyExamples.WaterCloudModel.Falsification.unmentionedDomain: counterexample, exempted
  ⊘ PropertyKindCalculus.UncertaintyExamples.WaterCloudModel.Falsification.unstatedHypothesis: counterexample, exempted
  ⊘ PropertyKindCalculus.UncertaintyExamples.WaterCloudModel.Falsification.wrongShapeAmbiguity: counterexample, exempted
  ⊘ PropertyKindCalculus.UncertaintyExamples.WaterCloudModel.Falsification.wrongShapeWellPosed: counterexample, exempted
-/
#guard_msgs in #kind_relations PropertyKindCalculus.UncertaintyExamples

/--
info: well-posedness coverage:
[well-posed] PropertyKindCalculus.UncertaintyExamples.WaterCloudModel.retrievalInvertsForward — PropertyKindCalculus.UncertaintyExamples.WaterCloudModel.wcmForwardQ_well_posed on PropertyKindCalculus.UncertaintyExamples.WaterCloudModel.soilGainNonzero; ambiguity: PropertyKindCalculus.UncertaintyExamples.WaterCloudModel.wcmForwardQ_ambiguous_of_degenerate
⊘ exempted PropertyKindCalculus.UncertaintyExamples.WaterCloudModel.Falsification.strandedWitness — counterexample
⊘ exempted PropertyKindCalculus.UncertaintyExamples.WaterCloudModel.Falsification.undomainedWellPosed — counterexample
⊘ exempted PropertyKindCalculus.UncertaintyExamples.WaterCloudModel.Falsification.unmentionedDomain — counterexample
⊘ exempted PropertyKindCalculus.UncertaintyExamples.WaterCloudModel.Falsification.unstatedHypothesis — counterexample
⊘ exempted PropertyKindCalculus.UncertaintyExamples.WaterCloudModel.Falsification.wrongShapeAmbiguity — counterexample
⊘ exempted PropertyKindCalculus.UncertaintyExamples.WaterCloudModel.Falsification.wrongShapeWellPosed — counterexample
7 inverts edge(s): 1 well-posed, 0 ambiguity surfaced, 6 exempted — clean
-/
#guard_msgs in #kind_wellposedness_coverage PropertyKindCalculus.UncertaintyExamples

-- no message: the one live inverts edge answers for its inversion both ways
#guard_msgs in #kind_wellposedness_clean PropertyKindCalculus.UncertaintyExamples

/--
info: kind contracts — 2 contract(s) kernel-accepted, 2 exempted
  PropertyKindCalculus.UncertaintyExamples.WaterCloudModel.wcmBoundary: kernel-accepted (theorem 'PropertyKindCalculus.UncertaintyExamples.WaterCloudModel.wcmBoundary.kindContractOk')
  PropertyKindCalculus.UncertaintyExamples.WaterCloudModel.wcmRetrievalBoundary: kernel-accepted (theorem 'PropertyKindCalculus.UncertaintyExamples.WaterCloudModel.wcmRetrievalBoundary.kindContractOk')
  ⊘ PropertyKindCalculus.UncertaintyExamples.WaterCloudModel.Falsification.forgottenParameter: counterexample, exempted
  ⊘ PropertyKindCalculus.UncertaintyExamples.WaterCloudModel.Falsification.misdeclaredKind: counterexample, exempted
-/
#guard_msgs in #kind_contracts_decide PropertyKindCalculus.UncertaintyExamples

/--
info: Declared boundaries (4 row(s))
Contract | Boundary | Interface | Members | Clauses | Theorem edges
forgottenParameter | 'WCM retrieval (mv), cfg.d forgotten' | 7 ports (3 params), 0 exits | 1 | counterexample |
misdeclaredKind | 'WCM retrieval (mv), σ0 misdeclared' | 8 ports (4 params), 0 exits | 1 | counterexample |
wcmBoundary | 'WCM forward (σ⁰)' | 8 ports (4 params), 0 exits | 1 |  | retrievalInvertsForward
wcmRetrievalBoundary | 'WCM retrieval (mv)' | 8 ports (4 params), 0 exits | 1 |  | retrievalInvertsForward
-/
#guard_msgs (whitespace := lax) in
#pkc_index "contracts" PropertyKindCalculus.UncertaintyExamples

/--
info: Provenance coverage absences (1 row(s))
Absence | Contract | At
no uncertainty budget | wcmRetrievalBoundary | wcmRetrieveQ/result : soilMoisture
-/
#guard_msgs (whitespace := lax) in
#pkc_index "provenance-coverage" PropertyKindCalculus.UncertaintyExamples

end -- pkc-blanket-expose
end -- pkc-blanket
