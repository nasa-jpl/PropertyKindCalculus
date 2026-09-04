/-
# Validation probes — aggregation (R9)

Inhabitation and axiom-profile probes for extensivity. The extensive-aggregation capstone is a
`∀`-quantified law over the mereology of systems; the danger it must avoid is being proved for an
`Extensive` predicate that nothing satisfies. So the probe *builds* a genuine extensive
measurement (leaf-counting mass) and drives the law through a **depth-2** decomposition — the
Rule-2 boundary that exercises the inductive step, not just a single atom — then re-exhibits the
source's non-extensive counterexample so the predicate is shown to be discriminating. The
same two questions are then put to the other two aggregation modes: the §13.5.4 intensive
capstone is driven through a depth-2 uniform carving, and the whole-proper case — the one
Bunge's four types do not name — is shown to be occupied, by a witness that refutes *both*
of the other laws.
-/

import PropertyKindCalculus

namespace PropertyKindCalculus.Tests.Aggregation

open PropertyKindCalculus

/-- Mass, a ratio kind — the archetypal extensive quantity. -/
def massKind : KindOfProperty := { id := "mass", scale := .ratio }

/-- The number of atomic parts under a decomposition. -/
def countLeaves : Decomposition System → Int
  | .atom _      => 1
  | .union a b   => countLeaves a + countLeaves b

/-- A genuinely additive mass measurement: each part reads its own leaf count, so a union reads
the sum of its parts' readings — the defining shape of an extensive quantity. -/
def massOf : Measurement System := fun d => { kind := massKind, numeral := countLeaves d, reference := "kg" }

/-- `massOf` is extensive for `massKind`: every part is of kind `massKind` (`ofKind`), and a union
reads as the sum of its parts (`additive`) — both by `rfl`, so the witness is real, not assumed. -/
theorem massOf_extensive : Extensive massKind massOf := ⟨fun _ => rfl, fun _ _ => rfl⟩

/-- Three atomic sub-systems. -/
def s₁ : System := { id := "s1" }
def s₂ : System := { id := "s2" }
def s₃ : System := { id := "s3" }

/-- A depth-2 decomposition `(s₁ ⊔ s₂) ⊔ s₃` — nested, so the aggregation recursion is exercised. -/
def whole : Decomposition System := .union (.union (.atom s₁) (.atom s₂)) (.atom s₃)

-- Inhabitation (Rule 2 — the non-degenerate, nested case): the value on the *whole* equals the
-- sum over *all three* atomic parts, obtained by applying the capstone to a real decomposition.
theorem r9_whole_eq_leafSum : (massOf whole).numeral = leafSum massOf whole :=
  extensive_additive massOf_extensive whole

-- and it computes to the leaf count, 3.
#guard (massOf whole).numeral == 3
#guard leafSum massOf whole == 3

-- Boundary — the predicate is discriminating: volume on mixing is *not* extensive (96 < 50 + 50),
-- so `Extensive` genuinely rules something out. (Re-exhibits the source counterexample.)
theorem r9_mixing_not_extensive : ¬ Extensive volume volMix := mixing_subadditive.2

/-- info: 'PropertyKindCalculus.extensive_additive' does not depend on any axioms -/
#guard_msgs in #print axioms extensive_additive

/-- info: 'PropertyKindCalculus.mixing_subadditive' does not depend on any axioms -/
#guard_msgs in #print axioms mixing_subadditive

/-! ## Intensity and whole-properness (R9)

The same two dangers, for the two laws stated beside extensivity: a capstone proved for a
predicate nothing satisfies, and a "neither" case that is empty because nothing can inhabit
it. Both are answered by driving the law through a concrete, nested witness. -/

/-- A depth-2 carving of one homogeneous fluid: `(A ⊔ B) ⊔ C`, three parcels of the same
water — nested, so the intensive recursion is exercised past its base case. -/
def parcels : Decomposition System :=
  .union (.union (.atom ⟨"A"⟩) (.atom ⟨"B"⟩)) (.atom ⟨"C"⟩)

/-- Every leaf of that carving reads 1000 kg/m³ — the hypothesis the intensive capstone
consumes, discharged by `rfl` at each of the three leaves. -/
theorem parcels_uniform :
    Decomposition.Forall (fun s => (densityHomogeneous (.atom s)).numeral = 1000) parcels :=
  ⟨⟨rfl, rfl⟩, rfl⟩

-- Inhabitation (Rule 2 — the nested case): the whole of a uniform carving reads the parts'
-- common value, obtained by applying the capstone to a real depth-2 decomposition.
theorem r9_intensive_whole_eq : (densityHomogeneous parcels).numeral = 1000 :=
  intensive_uniform densityHomogeneous_intensive parcels parcels_uniform

-- Boundary — the two branches are exclusive, so `Intensive` is not a weakening of
-- `Extensive`: the same measurement that satisfies one refutes the other.
theorem r9_density_not_extensive : ¬ Extensive fluidDensity densityHomogeneous :=
  density_not_extensive

-- Inhabitation — the whole-proper case is occupied: the coupled pair's normal-mode frequency is
-- neither summed from its parts nor shared with them, and both refutations are checked.
theorem r9_normalMode_not_extensive : ¬ Extensive oscillatorFrequency normalModeFreq :=
  normalMode_wholeProper.not_extensive

theorem r9_normalMode_not_intensive : ¬ Intensive oscillatorFrequency normalModeFreq :=
  normalMode_wholeProper.not_intensive

-- … and the number an aggregating library would report is wrong on an exhibited carving.
theorem r9_normalMode_leafSum_ne :
    ∃ d : Decomposition System, (normalModeFreq d).numeral ≠ leafSum normalModeFreq d :=
  normalMode_wholeProper.exists_leafSum_ne

/-- info: 'PropertyKindCalculus.intensive_uniform' does not depend on any axioms -/
#guard_msgs in #print axioms intensive_uniform

/-- info: 'PropertyKindCalculus.not_extensive_of_intensive' depends on axioms: [propext] -/
#guard_msgs in #print axioms not_extensive_of_intensive

/-- info: 'PropertyKindCalculus.WholeProper.not_extensive' does not depend on any axioms -/
#guard_msgs in #print axioms WholeProper.not_extensive

/-- info: 'PropertyKindCalculus.WholeProper.not_intensive' does not depend on any axioms -/
#guard_msgs in #print axioms WholeProper.not_intensive


/-! ## Extensivity about a shared parameter (R9)

The parametrized predicate carries the same two dangers, and one more of its own: a law about a
parameter is worthless if the parameter never matters. So the probe drives the whole-tree law at
a *chosen* axis, and then exhibits the case the parameter rules out — two parts read about their
own axes, summing to a number that is not the whole's.
-/

-- Inhabitation: the rod's inertia is extensive about *every* axis, so the capstone applies at
-- each — `ExtensiveAbout` is not a weaker predicate that only holds somewhere.
theorem r9_rod_extensive_about (a : Int) : Extensive pointMassInertia (rodInertia a) :=
  (inertiaMeasurement_extensiveAbout PointMass.mass PointMass.position).at a

theorem r9_rod_leafSum (a : Int) :
    (rodInertia a rod).numeral = leafSum (rodInertia a) rod :=
  extensive_additive (r9_rod_extensive_about a) rod

-- and it computes: 2 about the centre, 4 about the left mass — the same rod, two numbers.
#guard (rodInertia 0 rod).numeral == 2
#guard (rodInertia (-1) rod).numeral == 4

-- Boundary — the parameter is load-bearing: parts read about axes through themselves sum to 0
-- where the rod about its centre reads 2, so `ExtensiveAbout` genuinely rules something out.
theorem r9_rod_mixed_axes_wrong :
    (rodInertia 0 rod).numeral
      ≠ (rodInertia (-1) rodLeft).numeral + (rodInertia 1 rodRight).numeral :=
  rod_mixed_axes_wrong

/-- info: 'PropertyKindCalculus.ExtensiveAbout.at' does not depend on any axioms -/
#guard_msgs in #print axioms ExtensiveAbout.at

/-- info: 'PropertyKindCalculus.extensiveAbout_mixed' does not depend on any axioms -/
#guard_msgs in #print axioms extensiveAbout_mixed

/-- info: 'PropertyKindCalculus.extensiveAbout_mixed_ne' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms extensiveAbout_mixed_ne

/-- info: 'PropertyKindCalculus.inertiaMeasurement_extensiveAbout' does not depend on any axioms -/
#guard_msgs in #print axioms inertiaMeasurement_extensiveAbout

/-- info: 'PropertyKindCalculus.rod_mixed_axes_wrong' does not depend on any axioms -/
#guard_msgs in #print axioms rod_mixed_axes_wrong

/-! ## The weighted-mean mode, and what its license is worth per carrier (R9)

The centre-of-mass mode is carrier-parametric, so the probe asks the same two questions of it at
the *executable* carrier — where the law it is meant to support does not hold — rather than only
at `ℝ`, where `Tests.AggregationLaws` drives `mean_const`.

The danger a smart constructor carries is that it refuses nothing. So `mk?` is driven at a
carving it must accept and at one it must refuse, and the refusal is checked to be the *only*
one: the weights that sum to zero, not merely some weights.

The danger the *license* carries is subtler and is the reason this section exists. `Float`'s
`≠ 0` is a decidable test that `NaN` passes, so an all-`NaN` carving is licensed and its mean of
a constant is `NaN` — the law `mean_const` states over `ℝ` is false here, and nothing in the
structure could have caught it. That is not a defect to be repaired by strengthening the field;
it is the reason the mode is carried across an explicit ladder of carriers and the law stops at
the lawful ones. -/

/-- Two parts, weighted 1 and 3 — a carving whose total is 4 at any carrier. -/
def pairParts : Decomposition Bool := .union (.atom true) (.atom false)

/-- The `Float` weights of that carving. -/
def floatWeight : Bool → Float := fun b => if b then 1.0 else 3.0

-- The total is what the fold says it is, and the licensed constructor accepts it.
#guard totalWeight floatWeight pairParts == 4.0
#guard (WeightedCarving.mk? pairParts floatWeight).isSome

-- Boundary — `mk?` refuses, and refuses only, a carving with no weight. Weights that cancel
-- are the interesting refusal: each part is weighted, the whole is not.
#guard (WeightedCarving.mk? (R := Float) pairParts (fun _ => 0.0)).isNone
#guard (WeightedCarving.mk? (R := Float) pairParts (fun b => if b then 2.0 else -2.0)).isNone

/-- The mean at `Float`, computed through the licensed carving — `some` because the license
holds, so this is the mean of the data and not a fallback. -/
def floatMean (w : Bool → Float) (v : Bool → Float) : Option Float :=
  (WeightedCarving.mk? pairParts w).map (fun c => c.mean v)

-- Inhabitation: the weights are load-bearing at `Float` too — 1·3 + 3·1 over 4 is 3/2, where
-- the unweighted average of the same two values is 2.
#guard floatMean floatWeight (fun b => if b then 3.0 else 1.0) == some 1.5

-- Boundary — **the license is worth nothing at `Float`.** Every weight is `NaN`; the total is
-- `NaN`, which is not `0.0`, so the carving is licensed and `mk?` accepts it. The mean of the
-- constant `1.0` is then `NaN`, not `1.0`: the law `mean_const` proves over `ℝ` is refuted at
-- this carrier by a carving the type system admitted.
#guard (WeightedCarving.mk? (R := Float) pairParts (fun _ => 0.0 / 0.0)).isSome
#guard (floatMean (fun _ => 0.0 / 0.0) (fun _ => 1.0)).map (· == 1.0) == some false

-- and the same `NaN` total is what passed the license: `≠ 0` is true of it.
#guard !((0.0 / 0.0 : Float) == 0.0)

/-- info: 'PropertyKindCalculus.WeightedCarving.mk?_eq_none_iff' depends on axioms: [propext] -/
#guard_msgs in #print axioms WeightedCarving.mk?_eq_none_iff

/-- info: 'PropertyKindCalculus.WeightedCarving.mk?_isSome_iff' depends on axioms: [propext] -/
#guard_msgs in #print axioms WeightedCarving.mk?_isSome_iff

/-- info: 'PropertyKindCalculus.WeightedCarving.mk?_eq_some' does not depend on any axioms -/
#guard_msgs in #print axioms WeightedCarving.mk?_eq_some

/-- info: 'PropertyKindCalculus.WeightedCarving.total_ne_zero'' does not depend on any axioms -/
#guard_msgs in #print axioms WeightedCarving.total_ne_zero'

end PropertyKindCalculus.Tests.Aggregation
