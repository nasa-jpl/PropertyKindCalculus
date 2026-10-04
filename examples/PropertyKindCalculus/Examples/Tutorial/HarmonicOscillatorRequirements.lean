/-
# Tutorial — the harmonic oscillator's requirements, both categories

`HarmonicOscillatorSquare` walks the four-category square for two bodies and three
springs; the ForPhysLib case study (`Attempt4Pkc`) types the same oscillator against the
MR list. Neither says what the oscillator's quantities *must* satisfy. This module states
that, as `Provenance.Requirement` data the sweeps read, in both categories the construct
carries:

  * **Provable** — the statement closes over the model. HP1 bounds the static compliance
    of body A by its wall spring's (`c_A ≤ 1/k_A`): a model boundary, a *specification
    boundary* whose one member computes the bound, a `boundedBy` edge proved at `ℝ`, and a
    spot check at `Float` on the operational numbers. HP2 bounds the driven oscillator's
    admittance by its resistance (`|Z|² ≥ c²`) the same way, spot-checked at the complex
    carrier. HP5 states that the pair's mass is the licensed sum of its bodies', over the
    pair's sort; HP6 is the *negative* half of the same fact — angular frequency is never
    summed over the pair — discharged by the absence of the license.
  * **Empirical** — the statement names a referent the model does not define: the
    springs' datasheet (HE1's linear range, HE5's stiffness band) and the weighed springs
    (HE2). Each is **attested** here, with the reason in the author's words, because the
    numbers are the apparatus's to supply and not the tutorial's to invent; the census
    counts them, and the count is meant to fall.

Every boundary below is kernel-accepted (`#kind_contract_decide`); every requirement is
checked by `#kind_requirement`, surveyed, censused, and gated. Imports the case study, and
so PhysLib and Mathlib; outside the `Examples` root for that reason.
-/

module

public import PropertyKindCalculus.Examples.Tutorial.HarmonicOscillatorSquare
meta import PropertyKindCalculus.Examples.Tutorial.HarmonicOscillatorSquare
public import ForPhysLib.CaseStudies.HarmonicOscillator.Attempt4Pkc
meta import ForPhysLib.CaseStudies.HarmonicOscillator.Attempt4Pkc
public import PropertyKindCalculus.KindRequirement
meta import PropertyKindCalculus.KindRequirement
-- Private scope only: core seals `Lean.Name.beq`, so a kernel `decide` over a provenance
-- graph whose kinds are `Name`s gets stuck without this (as `Tests/Core/KindContracts.lean`).
import all Init.Prelude
import all PropertyKindCalculus.Provenance

@[expose] public section Blanket

namespace PropertyKindCalculus.Examples.Tutorial.HarmonicOscillator

open PropertyKindCalculus
open PropertyKindCalculus.Provenance (NodeId KindRef)
open PropertyKindCalculus.Examples.HarmonicOscillator.Attempt4

/-! ## HP1 — static compliance of body A, bounded by its wall spring's compliance

A port's kind is a named constant (`KindRef.decl`), so the case study's dimensioned kinds
get one name each here; the suffix tells them from the square's bare kinds. -/

/-- The case study's spring constant, by name. -/
def stiffnessDK : KindOfProperty := springConstant.kind
/-- Compliance: displacement per force. -/
def complianceK : KindOfProperty := { id := "compliance", scale := .ratio }

/-- **The model member.** Static equilibrium of the three-spring chain with a force on A
and B free: `x_A = c_A · F`, `c_A = (k_B + k_C) / (k_A k_B + k_A k_C + k_B k_C)`. -/
noncomputable def complianceA (kA kC kB : Quantity stiffnessDK ℝ) : Quantity complianceK ℝ :=
  ⟨(kB.magnitude + kC.magnitude)
    / (kA.magnitude * kB.magnitude + kA.magnitude * kC.magnitude
        + kB.magnitude * kC.magnitude)⟩

/-- **The specification member.** The wall spring's own compliance, `1 / k_A`. -/
noncomputable def complianceBound (kA : Quantity stiffnessDK ℝ) : Quantity complianceK ℝ :=
  ⟨1 / kA.magnitude⟩

/-- The domain the requirement holds on, named so the edge can list it. -/
def complianceDomain (kA kC kB : Quantity stiffnessDK ℝ) : Prop :=
  0 < kA.magnitude ∧ 0 ≤ kC.magnitude ∧ 0 ≤ kB.magnitude
    ∧ 0 < kA.magnitude * kB.magnitude + kA.magnitude * kC.magnitude
        + kB.magnitude * kC.magnitude

/-- **The witness.** Names a member of each boundary, concludes with an order relation,
binds the named domain. -/
theorem compliance_bounded (kA kC kB : Quantity stiffnessDK ℝ) (h : complianceDomain kA kC kB) :
    (complianceA kA kC kB).magnitude ≤ (complianceBound kA).magnitude := by
  obtain ⟨hA, hC, hB, hpos⟩ := h
  show (kB.magnitude + kC.magnitude)
      / (kA.magnitude * kB.magnitude + kA.magnitude * kC.magnitude
          + kB.magnitude * kC.magnitude) ≤ 1 / kA.magnitude
  rw [div_le_div_iff₀ hpos hA]
  nlinarith [mul_nonneg hB hC]

/-- The model's boundary: three stiffnesses in, one compliance out. -/
def complianceBoundary : Provenance.Contract NodeId KindRef where
  name := "static compliance of body A"
  members := [``complianceA]
  ports := [⟨(NodeId.binder "kA").within ``complianceA, .decl ``stiffnessDK, .input⟩,
            ⟨(NodeId.binder "kC").within ``complianceA, .decl ``stiffnessDK, .input⟩,
            ⟨(NodeId.binder "kB").within ``complianceA, .decl ``stiffnessDK, .input⟩,
            ⟨NodeId.result.within ``complianceA, .decl ``complianceK, .output⟩]
  exits := []

/-- The specification's boundary: one stiffness in, the bound out — the other role. -/
def complianceSpec : Provenance.Contract NodeId KindRef where
  name := "specification — compliance of the wall spring"
  members := [``complianceBound]
  ports := [⟨(NodeId.binder "kA").within ``complianceBound, .decl ``stiffnessDK, .input⟩,
            ⟨NodeId.result.within ``complianceBound, .decl ``complianceK, .output⟩]
  exits := []
  role := .specification

#kind_contract_decide complianceBoundary
#kind_contract_decide complianceSpec

/-- The theorem edge HP1 is discharged by. -/
def complianceBoundedByWallSpring : Provenance.Relation where
  left := ``complianceBoundary
  right := ``complianceSpec
  kind := .boundedBy
  witness := ``compliance_bounded
  claim := "the displacement of A per unit force never exceeds the compliance of its wall spring"
  hypotheses := [``complianceDomain]

/-- The same model at the executable carrier, for the spot check. -/
def complianceAFloat (kA kC kB : Float) : Quantity complianceK Float :=
  ⟨(kB + kC) / (kA * kB + kA * kC + kB * kC)⟩

/-- The same bound at the executable carrier. -/
def complianceBoundFloat (kA : Float) : Quantity complianceK Float := ⟨1 / kA⟩

/-- **The spot check.** The bound holds at `Float` on the tutorial's stiffnesses:
`5/36 ≤ 1/6`. -/
def hp1_spot : Bool :=
  decide ((complianceAFloat 6 2 3).magnitude ≤ (complianceBoundFloat 6).magnitude)

/-- HP1, as the sweeps read it: provable, through the edge, spot-checked, about body A. -/
def hp1 : Provenance.Requirement where
  name := "HP1"
  statement := "the static displacement of A per unit force never exceeds the compliance \
    of its wall spring: c_A ≤ 1/k_A"
  kind := .provable
  governs := ``complianceBoundary
  port := some (NodeId.result.within ``complianceA)
  scope := .objects [``Body.A]
  witness := ``complianceBoundedByWallSpring
  spotChecks := [``hp1_spot]

/--
info: kind requirement 'HP1' (provable) on 'static compliance of body A'
statement: the static displacement of A per unit force never exceeds the compliance of its wall spring: c_A ≤ 1/k_A
governs: 'static compliance of body A' at complianceA/result
scope: objects PropertyKindCalculus.Examples.Tutorial.HarmonicOscillator.Body.A
edge: PropertyKindCalculus.Examples.Tutorial.HarmonicOscillator.complianceBoundedByWallSpring — 'static compliance of body A' bounded by 'specification — compliance of the wall spring'
witness: PropertyKindCalculus.Examples.Tutorial.HarmonicOscillator.compliance_bounded
spot check: PropertyKindCalculus.Examples.Tutorial.HarmonicOscillator.hp1_spot = true
-/
#guard_msgs in #kind_requirement hp1

/-! ## HP2 — the driven oscillator's admittance, bounded by its resistance

`|Z|² = c² + (mω − k/ω)² ≥ c²`, in the squared real form the carrier computes (`abs2`). -/

/-- The squared impedance, as a kind. -/
def impedanceSqK : KindOfProperty := { id := "mechanical impedance squared", scale := .ratio }
/-- The case study's impedance, by name. -/
def impedanceDK : KindOfProperty := Tier5.impedance.kind
/-- The case study's mass, by name. -/
def massDK : KindOfProperty := mass.kind
/-- The case study's angular frequency, by name. -/
def angFreqDK : KindOfProperty := angularFrequency.kind

/-- **The model member.** `|Z|²` from the four parameters. -/
noncomputable def impedanceAbs2 (c : Quantity impedanceDK ℝ) (m : Quantity massDK ℝ)
    (ω : Quantity angFreqDK ℝ) (k : Quantity stiffnessDK ℝ) :
    Quantity impedanceSqK ℝ :=
  ⟨c.magnitude ^ 2 + (m.magnitude * ω.magnitude - k.magnitude / ω.magnitude) ^ 2⟩

/-- **The specification member.** The resistance squared. -/
noncomputable def resistanceSq (c : Quantity impedanceDK ℝ) : Quantity impedanceSqK ℝ :=
  ⟨c.magnitude ^ 2⟩

/-- **The witness.** Unconditional: no domain. -/
theorem admittance_bounded (c : Quantity impedanceDK ℝ) (m : Quantity massDK ℝ)
    (ω : Quantity angFreqDK ℝ) (k : Quantity stiffnessDK ℝ) :
    (resistanceSq c).magnitude ≤ (impedanceAbs2 c m ω k).magnitude := by
  show c.magnitude ^ 2
    ≤ c.magnitude ^ 2 + (m.magnitude * ω.magnitude - k.magnitude / ω.magnitude) ^ 2
  nlinarith [sq_nonneg (m.magnitude * ω.magnitude - k.magnitude / ω.magnitude)]

/-- The model's boundary. -/
def impedanceBoundary : Provenance.Contract NodeId KindRef where
  name := "driven oscillator — squared impedance"
  members := [``impedanceAbs2]
  ports := [⟨(NodeId.binder "c").within ``impedanceAbs2, .decl ``impedanceDK, .input⟩,
            ⟨(NodeId.binder "m").within ``impedanceAbs2, .decl ``massDK, .input⟩,
            ⟨(NodeId.binder "ω").within ``impedanceAbs2, .decl ``angFreqDK, .input⟩,
            ⟨(NodeId.binder "k").within ``impedanceAbs2, .decl ``stiffnessDK, .input⟩,
            ⟨NodeId.result.within ``impedanceAbs2, .decl ``impedanceSqK, .output⟩]
  exits := []

/-- The specification's boundary. -/
def admittanceSpec : Provenance.Contract NodeId KindRef where
  name := "specification — resistance squared"
  members := [``resistanceSq]
  ports := [⟨(NodeId.binder "c").within ``resistanceSq, .decl ``impedanceDK, .input⟩,
            ⟨NodeId.result.within ``resistanceSq, .decl ``impedanceSqK, .output⟩]
  exits := []
  role := .specification

#kind_contract_decide impedanceBoundary
#kind_contract_decide admittanceSpec

/-- The theorem edge HP2 is discharged by. The model is on the left; the witness reads
`spec ≤ model`, which is the direction the requirement states. -/
def impedanceBoundedByResistance : Provenance.Relation where
  left := ``impedanceBoundary
  right := ``admittanceSpec
  kind := .boundedBy
  witness := ``admittance_bounded
  claim := "the velocity response per unit driving force never exceeds 1/c: |Z|² ≥ c²"

/-- **The spot check**, at the complex executable carrier the case study runs on:
`|Z|² = 25 ≥ 9 = c²` for its `Z = 3 + 4i`. -/
def hp2_spot : Bool := decide (Tier5.Z.magnitude.abs2 ≥ 9.0)

/-- HP2: provable, through the edge, spot-checked, over every driven oscillator. -/
def hp2 : Provenance.Requirement where
  name := "HP2"
  statement := "the velocity response per unit driving force never exceeds 1/c: |Z|² ≥ c²"
  kind := .provable
  governs := ``impedanceBoundary
  port := some (NodeId.result.within ``impedanceAbs2)
  scope := .sort ``Tier5.drivenS
  witness := ``impedanceBoundedByResistance
  spotChecks := [``hp2_spot]

/--
info: kind requirement 'HP2' (provable) on 'driven oscillator — squared impedance'
statement: the velocity response per unit driving force never exceeds 1/c: |Z|² ≥ c²
governs: 'driven oscillator — squared impedance' at impedanceAbs2/result
scope: sort PropertyKindCalculus.Examples.HarmonicOscillator.Attempt4.Tier5.drivenS
edge: PropertyKindCalculus.Examples.Tutorial.HarmonicOscillator.impedanceBoundedByResistance — 'driven oscillator — squared impedance' bounded by 'specification — resistance squared'
witness: PropertyKindCalculus.Examples.Tutorial.HarmonicOscillator.admittance_bounded
spot check: PropertyKindCalculus.Examples.Tutorial.HarmonicOscillator.hp2_spot = true
-/
#guard_msgs in #kind_requirement hp2

/-! ## HP5 and HP6 — the pair's mass is a sum, its angular frequency never is

MR8's two halves, at the quantity level: the square's `pairMass` is the licensed assembly
(`Assembles pairS massK`), and there is no `Assembles pairS angFreqK`. -/

/-- The arithmetic the license for `pairS` and `massK` licenses: the pair's mass from
its bodies'. -/
def pairMassOf (mA mB : Quantity massK Int) : Quantity massK Int :=
  ⟨mA.magnitude + mB.magnitude⟩

/-- The pair's boundary. -/
def pairBoundary : Provenance.Contract NodeId KindRef where
  name := "coupled pair — mass"
  members := [``pairMassOf]
  ports := [⟨(NodeId.binder "mA").within ``pairMassOf, .decl ``massK, .input⟩,
            ⟨(NodeId.binder "mB").within ``pairMassOf, .decl ``massK, .input⟩,
            ⟨NodeId.result.within ``pairMassOf, .decl ``massK, .output⟩]
  exits := []

#kind_contract_decide pairBoundary

/-- **HP5's witness.** The boundary's sum is the licensed assembly over the square's
carving of the pair into its bodies. -/
theorem pairMassOf_is_assembled :
    (pairMassOf ⟨3⟩ ⟨5⟩).magnitude = pairMass.magnitude := rfl

/-- **HP5's spot check.** -/
def hp5_spot : Bool := (pairMassOf ⟨3⟩ ⟨5⟩).magnitude == 8

/-- HP5: provable by a bare theorem, over every coupled pair. -/
def hp5 : Provenance.Requirement where
  name := "HP5"
  statement := "the mass of the pair is the sum of its bodies' masses, as the license for \
    the pair's sort states"
  kind := .provable
  governs := ``pairBoundary
  port := some (NodeId.result.within ``pairMassOf)
  scope := .sort ``pairS
  witness := ``pairMassOf_is_assembled
  spotChecks := [``hp5_spot]

/--
info: kind requirement 'HP5' (provable) on 'coupled pair — mass'
statement: the mass of the pair is the sum of its bodies' masses, as the license for the pair's sort states
governs: 'coupled pair — mass' at pairMassOf/result
scope: sort PropertyKindCalculus.Examples.Tutorial.HarmonicOscillator.pairS
witness: PropertyKindCalculus.Examples.Tutorial.HarmonicOscillator.pairMassOf_is_assembled
axioms: propext
spot check: PropertyKindCalculus.Examples.Tutorial.HarmonicOscillator.hp5_spot = true
-/
#guard_msgs in #kind_requirement hp5

/-- The license HP6 requires absent: angular frequency assembling into the pair. -/
def pairAngFreqLicense : Prop := Assembles pairS angFreqK

/-- HP6: the negative requirement, discharged by the registry's silence. -/
def hp6 : Provenance.Requirement where
  name := "HP6"
  statement := "angular frequency is never summed over the pair: the normal mode is a \
    property of the pair's sort, and no license assembles it from the bodies'"
  kind := .provable
  governs := ``pairBoundary
  scope := .sort ``pairS
  absent := ``pairAngFreqLicense

/--
info: kind requirement 'HP6' (provable) on 'coupled pair — mass'
statement: angular frequency is never summed over the pair: the normal mode is a property of the pair's sort, and no license assembles it from the bodies'
governs: every produced port of 'coupled pair — mass'
scope: sort PropertyKindCalculus.Examples.Tutorial.HarmonicOscillator.pairS
absent: no instance of PropertyKindCalculus.Examples.Tutorial.HarmonicOscillator.pairAngFreqLicense
-/
#guard_msgs in #kind_requirement hp6

/-! ## HE1, HE2, HE5 — the empirical rows, attested

Each names a referent the model does not define, and each is deferred with its reason:
the numbers are the apparatus's to supply. When they arrive, the referent is declared as a
kinded quantity under `@[kindReferent "…"]`, the gate is written against it, and the
attestation is dropped — one edit per row, and the census's attested count falls. -/

/-- HE1: the linear model is used only within the physical spring's linear range. -/
def he1 : Provenance.Requirement where
  name := "HE1"
  statement := "the linear model is used only where the physical spring obeys Hooke's law: \
    |x| ≤ x_max from the spring's datasheet"
  kind := .empirical
  governs := ``complianceBoundary
  scope := .sort ``springS
  attested := "x_max is the spring datasheet's to supply; gated at ingest once declared as \
    a referent"

/-- HE2: the springs are massless, to within a stated fraction of the lighter body. -/
def he2 : Provenance.Requirement where
  name := "HE2"
  statement := "each spring's mass is at most 1 % of the lighter body's"
  kind := .empirical
  governs := ``pairBoundary
  scope := .sort ``springS
  attested := "massless-spring idealization; discharged when the springs are weighed"

/-- HE5: every spring's stiffness lies within its datasheet band. -/
def he5 : Provenance.Requirement where
  name := "HE5"
  statement := "every linear spring's stiffness lies within [k_min, k_max] from its \
    datasheet batch"
  kind := .empirical
  governs := ``complianceBoundary
  scope := .sort ``springS
  attested := "the band is the datasheet's to supply; gated at ingest per spring once \
    declared as referents"

/--
info: kind requirement 'HE5' (empirical) on 'static compliance of body A'
statement: every linear spring's stiffness lies within [k_min, k_max] from its datasheet batch
governs: every produced port of 'static compliance of body A'
scope: sort PropertyKindCalculus.Examples.Tutorial.HarmonicOscillator.springS
attested: the band is the datasheet's to supply; gated at ingest per spring once declared as referents
-/
#guard_msgs in #kind_requirement he5

/-! ## The survey, the census and the gate -/

/--
info: kind requirements — 7 requirement(s): 4 provable, 3 empirical, 3 attested
  PropertyKindCalculus.Examples.Tutorial.HarmonicOscillator.he1: 'HE1' (empirical) on 'static compliance of body A' — attested: x_max is the spring datasheet's to supply; gated at ingest once declared as a referent
  PropertyKindCalculus.Examples.Tutorial.HarmonicOscillator.he2: 'HE2' (empirical) on 'coupled pair — mass' — attested: massless-spring idealization; discharged when the springs are weighed
  PropertyKindCalculus.Examples.Tutorial.HarmonicOscillator.he5: 'HE5' (empirical) on 'static compliance of body A' — attested: the band is the datasheet's to supply; gated at ingest per spring once declared as referents
  PropertyKindCalculus.Examples.Tutorial.HarmonicOscillator.hp1: 'HP1' (provable) on 'static compliance of body A' — by PropertyKindCalculus.Examples.Tutorial.HarmonicOscillator.complianceBoundedByWallSpring
  PropertyKindCalculus.Examples.Tutorial.HarmonicOscillator.hp2: 'HP2' (provable) on 'driven oscillator — squared impedance' — by PropertyKindCalculus.Examples.Tutorial.HarmonicOscillator.impedanceBoundedByResistance
  PropertyKindCalculus.Examples.Tutorial.HarmonicOscillator.hp5: 'HP5' (provable) on 'coupled pair — mass' — by PropertyKindCalculus.Examples.Tutorial.HarmonicOscillator.pairMassOf_is_assembled
  PropertyKindCalculus.Examples.Tutorial.HarmonicOscillator.hp6: 'HP6' (provable) on 'coupled pair — mass' — absent PropertyKindCalculus.Examples.Tutorial.HarmonicOscillator.pairAngFreqLicense
-/
#guard_msgs in #kind_requirements PropertyKindCalculus.Examples.Tutorial.HarmonicOscillator

/--
info: requirement coverage:
[governed] PropertyKindCalculus.Examples.Tutorial.HarmonicOscillator.complianceBoundary ('static compliance of body A') complianceA/result — by 'HE1', 'HE5', 'HP1'
[governed] PropertyKindCalculus.Examples.Tutorial.HarmonicOscillator.impedanceBoundary ('driven oscillator — squared impedance') impedanceAbs2/result — by 'HP2'
[governed] PropertyKindCalculus.Examples.Tutorial.HarmonicOscillator.pairBoundary ('coupled pair — mass') pairMassOf/result — by 'HE2', 'HP5', 'HP6'
⊘ specification PropertyKindCalculus.Examples.Tutorial.HarmonicOscillator.admittanceSpec ('specification — resistance squared') — the subject of no requirement
⊘ specification PropertyKindCalculus.Examples.Tutorial.HarmonicOscillator.complianceSpec ('specification — compliance of the wall spring') — the subject of no requirement
5 row(s) over 3 model boundary(ies): 3 governed, 2 exempted — clean
requirements: 4 provable, 3 empirical, 3 attested
-/
#guard_msgs in #kind_requirement_coverage PropertyKindCalculus.Examples.Tutorial.HarmonicOscillator

#kind_requirement_clean PropertyKindCalculus.Examples.Tutorial.HarmonicOscillator

end PropertyKindCalculus.Examples.Tutorial.HarmonicOscillator

end Blanket
