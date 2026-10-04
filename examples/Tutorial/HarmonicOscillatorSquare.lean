/-
# Tutorial — the ontological square, walked for two bodies and three springs

The harmonic oscillator of `ForPhysLib.CaseStudies.HarmonicOscillator`, typed four ways
and scored there against MR1–MR19, never *walks* Lowe's four-category square: its objects
are nominal `System`s that know no sort, its springs are not objects at all, and its
aggregation facts are stated at the measurement level by hand. This module is the walk
the case study lacks, on the same system, every claim compiled — refusals pinned by
`#guard_msgs` with the error the elaborator prints, agreements as `example` and `theorem`.

The system: bodies A, B (sort *point mass*); springs kA, kC, kB (sort *linear spring*);
the pair (sort *coupled oscillator pair*). The numbers are the case study's (mA=3, mB=5),
plus kA=6, kC=2, kB=3 so every series/parallel fact is an integer.

```
    ▓╱╲╱╲╱╲[ A : 3 ]╱╲╱╲╱╲[ B : 5 ]╱╲╱╲╱╲▓
       kA = 6         kC = 2         kB = 3
```

What each corner buys is a refusal or a theorem unavailable without it:

  * **Attributes** (kinds-of-property with a scale) buy the right edge: one body, two
    kinds, refused.
  * **Substances** (object types, `Designated`) buy the bottom edge: two bodies' masses do
    not add, and B's mass cannot stand in for A's.
  * **Modes** (`IndividualQuantity`) make both edges type indices, so the refusals are the
    compiler's.
  * **Kinds** (sorts, with the left edge `Sorted`) buy the top edge *through the object*
    (`dedicatedFor`), the normal mode as a property of the pair's sort and of nothing
    below it, and — the exhibit the case study does not have — the aggregation license
    keyed by the sort: the same two springs add in parallel and are whole-proper in
    series.

Part of the `Tutorial` library (the tutorial's starter files); imports only the Mathlib-free
core. The requirements stated on this system are in `HarmonicOscillatorRequirements`, which
imports the case study and so Mathlib.
-/

module

public import PropertyKindCalculus
-- Private scope only: core seals `Nat.repr` and `String.toByteArray`, so a kernel `decide`
-- over a `String` built by `toString` gets stuck without these (as `MiniObjectTypes.lean`).
import all Init.Prelude
import all Init.Data.Repr
import all Init.Data.ToString.Basic
import all Init.Data.String.Basic
import all PropertyKindCalculus.Bounds
import all PropertyKindCalculus.Unit
import all PropertyKindCalculus.IndividualQuantity
import all PropertyKindCalculus.Extensivity
import all PropertyKindCalculus.Composite
import all PropertyKindCalculus.DedicatedKind
import all PropertyKindCalculus.Foundations
import all PropertyKindCalculus.Mereology

@[expose] public section Blanket

namespace Tutorial.HarmonicOscillator

open PropertyKindCalculus

/-! ## Attributes corner — kinds-of-property (non-substantial universals) -/

-- ANCHOR: attributes
def massK : KindOfProperty := { id := "mass", scale := .ratio }
def stiffnessK : KindOfProperty := { id := "spring constant", scale := .ratio }
def angFreqK : KindOfProperty := { id := "angular frequency", scale := .ratio }
def frequencyK : KindOfProperty := { id := "frequency", scale := .ratio }
def displacementK : KindOfProperty := { id := "displacement", scale := .ratio }
def forceK : KindOfProperty := { id := "force", scale := .ratio }
-- ANCHOR_END: attributes

/-! ## Kinds corner — sorts of system (substantial universals) -/

-- ANCHOR: sorts
def bodyS : SortOfSystem := ⟨"point mass"⟩
def springS : SortOfSystem := ⟨"linear spring"⟩
def pairS : SortOfSystem := ⟨"coupled oscillator pair"⟩
def parallelS : SortOfSystem := ⟨"springs in parallel"⟩
def seriesS : SortOfSystem := ⟨"springs in series"⟩
-- ANCHOR_END: sorts

/-! ## Substances corner — object types (substantial particulars) -/

-- ANCHOR: objects
inductive Body | A | B
deriving DecidableEq, Repr

inductive Spring | kA | kC | kB
deriving DecidableEq, Repr
-- ANCHOR_END: objects

-- ANCHOR: sorted
/-- Left edge, *instantiated by*: every body is a point mass. Declared once, never derived. -/
instance : Sorted Body := ⟨fun _ => bodyS⟩
/-- Every spring is a linear spring. -/
instance : Sorted Spring := ⟨fun _ => springS⟩
-- ANCHOR_END: sorted

-- ANCHOR: designated
/-- Designation (so `toIndividualProperty` can name a body); injectivity by `decide`. -/
instance : Designated Body where
  designation
    | .A => ⟨"body A"⟩
    | .B => ⟨"body B"⟩
  designation_inj {x y} h := by
    cases x <;> cases y <;> first | rfl | exact absurd (System.mk.inj h) (by decide)

instance : Designated Spring where
  designation
    | .kA => ⟨"spring A"⟩
    | .kC => ⟨"spring C"⟩
    | .kB => ⟨"spring B"⟩
  designation_inj {x y} h := by
    cases x <;> cases y <;> first | rfl | exact absurd (System.mk.inj h) (by decide)
-- ANCHOR_END: designated

/-! ## Modes corner — individual quantities (non-substantial particulars) -/

-- ANCHOR: modes
def mA : IndividualQuantity Body.A massK Int := ⟨3⟩
def mB : IndividualQuantity Body.B massK Int := ⟨5⟩
def kA : IndividualQuantity Spring.kA stiffnessK Int := ⟨6⟩
def kC : IndividualQuantity Spring.kC stiffnessK Int := ⟨2⟩
def kB : IndividualQuantity Spring.kB stiffnessK Int := ⟨3⟩
-- ANCHOR_END: modes

/-! ## The four edges, each one line -/

-- ANCHOR: edges
/-- Left edge: a substance instantiates its kind (sort). -/
example : Sorted.sortOf Body.A = bodyS := rfl
example : Sorted.sortOf Spring.kC = springS := rfl
theorem bodies_one_sort : Sorted.sortOf Body.A = Sorted.sortOf Body.B := rfl

/-- Bottom + right edges: the two type indices of a mode, read back as an individual
property — the mode characterizes body A and instantiates mass. -/
example : mA.toIndividualProperty = ⟨massK, ⟨"body A"⟩⟩ := rfl
-- ANCHOR_END: edges

-- ANCHOR: topEdge
/-- Top edge, *characterized by*: the dedicated kind, reached *through the object* by
`dedicatedFor` (up the left edge, across the top). Two bodies of one sort share one
catalogue entry; the object index, not the entry, keeps their masses apart. -/
def whole : Component := ⟨"whole"⟩

theorem a_and_b_share_entry :
    massK.dedicatedFor Body.A whole = massK.dedicatedFor Body.B whole :=
  KindOfProperty.dedicatedFor_congr rfl whole
-- ANCHOR_END: topEdge

-- ANCHOR: normalMode
/-- The normal mode is a property of the *pair's sort* and of nothing below it. -/
def dkOmegaPlus : DedicatedKind := angFreqK.dedicatedTo pairS ⟨"normal mode +"⟩

theorem normal_mode_not_of_a_body : dkOmegaPlus ≠ angFreqK.dedicatedFor Body.A whole :=
  DedicatedKind.distinct_of_sort (by decide)

theorem normal_mode_not_of_a_spring : dkOmegaPlus ≠ angFreqK.dedicatedFor Spring.kC whole :=
  DedicatedKind.distinct_of_sort (by decide)
-- ANCHOR_END: normalMode

-- ANCHOR: noSort
/-! The case study's objects are nominal `System`s and know no sort, so they cannot reach
the top edge through `dedicatedFor` at all — the refusal that says why the tutorial needs
an object type with a `Sorted` instance. -/
/--
error: failed to synthesize instance of type class
  Sorted System

Hint: Type class instance resolution failures can be inspected with the `set_option trace.Meta.synthInstance true` command.
-/
#guard_msgs in
example := massK.dedicatedFor (⟨"oscillator A"⟩ : Object) whole
-- ANCHOR_END: noSort

/-! ## The refusals the two heavy edges buy -/

-- ANCHOR: bottomEdge
/- Bottom edge: masses of two bodies do not add. -/
/--
error: Application type mismatch: The argument
  mB
has type
  IndividualQuantity Body.B massK Int
but is expected to have type
  IndividualQuantity Body.A massK Int
in the application
  IndividualQuantity.add ⋯ mA mB
-/
#guard_msgs in
example := IndividualQuantity.add DifferenceKind.ofScale mA mB
/- Nor stiffnesses of two springs. -/
/--
error: Application type mismatch: The argument
  kC
has type
  IndividualQuantity Spring.kC stiffnessK Int
but is expected to have type
  IndividualQuantity Spring.kA stiffnessK Int
in the application
  IndividualQuantity.add ⋯ kA kC
-/
#guard_msgs in
example := IndividualQuantity.add DifferenceKind.ofScale kA kC
/- B's mass cannot stand in for A's. -/
/--
error: Type mismatch
  mB
has type
  IndividualQuantity Body.B massK Int
but is expected to have type
  IndividualQuantity Body.A massK Int
-/
#guard_msgs in
example : IndividualQuantity Body.A massK Int := mB
-- ANCHOR_END: bottomEdge
-- ANCHOR: rightEdge
/- Right edge: one body, two kinds, refused. -/
/--
error: Application type mismatch: The argument
  x
has type
  IndividualQuantity Body.A displacementK Int
but is expected to have type
  IndividualQuantity Body.A massK Int
in the application
  IndividualQuantity.add ⋯ mA x
-/
#guard_msgs in
example := fun (x : IndividualQuantity Body.A displacementK Int) =>
  IndividualQuantity.add DifferenceKind.ofScale mA x
-- ANCHOR_END: rightEdge

-- ANCHOR: sameDimension
/- One dimension, two kinds (MR4): angular frequency and frequency share 1/time, so a
dimension layer identifies them; the kind keeps them apart with no dimension in sight. -/
/--
error: Application type mismatch: The argument
  f
has type
  IndividualQuantity Body.A frequencyK Int
but is expected to have type
  IndividualQuantity Body.A angFreqK Int
in the application
  IndividualQuantity.add ⋯ ω f
-/
#guard_msgs in
example := fun (ω : IndividualQuantity Body.A angFreqK Int)
    (f : IndividualQuantity Body.A frequencyK Int) =>
  IndividualQuantity.add DifferenceKind.ofScale ω f
-- ANCHOR_END: sameDimension

/-! ## Joint objects — the coupling force, and Newton's third law as a type -/

-- ANCHOR: joint
/-- The force the coupling spring exerts on A, read from A's end: a quantity of the ordered
pair `(A, B)`. -/
def fAB : IndividualQuantity ((Body.A, Body.B) : Body × Body) forceK Int := ⟨-4⟩

/-- The same coupling read from B's end. -/
example : IndividualQuantity ((Body.B, Body.A) : Body × Body) forceK Int := fAB.transpose

/- The two readings are of different objects and do not add. -/
/--
error: Application type mismatch: The argument
  fAB.transpose
has type
  IndividualQuantity (Body.B, Body.A) forceK Int
but is expected to have type
  IndividualQuantity (Body.A, Body.B) forceK Int
in the application
  IndividualQuantity.add ⋯ fAB fAB.transpose
-/
#guard_msgs in
example := IndividualQuantity.add DifferenceKind.ofScale fAB fAB.transpose
-- ANCHOR_END: joint

/-! ## Assembly over the pair: mass is licensed, angular frequency is not -/

-- ANCHOR: pairMass
abbrev Part := Body ⊕ Spring

/-- Mass assembles into a coupled pair. -/
instance : Assembles pairS massK := ⟨DifferenceKind.ofScale⟩

/-- The pair carved into its two bodies (the massive parts). -/
def bodies : Decomposition Body := .union (.atom .A) (.atom .B)

/-- Each body's mass, characterizing *that body as a part of the pair*. -/
def massOf : (b : Body) →
    IndividualQuantity (Composite.part (σ := pairS) (Sum.inl b : Part)) massK Int
  | .A => ⟨3⟩
  | .B => ⟨5⟩

/-- The pair's mass, characterizing the whole. -/
def pairMass : IndividualQuantity (Composite.whole : Composite pairS Part) massK Int :=
  assemble pairS Composite.whole (fun b : Body => Composite.part (Sum.inl b)) bodies massOf

example : pairMass.magnitude = 8 := rfl
-- ANCHOR_END: pairMass

-- ANCHOR: wholePart
/- Whole and part do not add (MR22). -/
/--
error: Application type mismatch: The argument
  massOf Body.A
has type
  IndividualQuantity (Composite.part (Sum.inl Body.A)) massK Int
but is expected to have type
  IndividualQuantity Composite.whole massK Int
in the application
  IndividualQuantity.add ⋯ pairMass (massOf Body.A)
-/
#guard_msgs in
example := IndividualQuantity.add (k := massK) DifferenceKind.ofScale pairMass (massOf .A)
-- ANCHOR_END: wholePart

-- ANCHOR: angFreq
/- Angular frequency carries no license for the pair, so `2 + 4` is not a term. -/
/--
error: failed to synthesize instance of type class
  Assembles pairS angFreqK

Hint: Type class instance resolution failures can be inspected with the `set_option trace.Meta.synthInstance true` command.
-/
#guard_msgs in
example := fun (f : (b : Body) →
      IndividualQuantity (Composite.part (σ := pairS) (Sum.inl b : Part)) angFreqK Int) =>
  assemble (k := angFreqK) pairS Composite.whole
    (fun b : Body => Composite.part (Sum.inl b)) bodies f
-- ANCHOR_END: angFreq

/-! ## Stiffness: the same parts, two sorts of whole — what the Kinds corner buys

Two springs in parallel: `k = kA + kB`. The same two springs in series:
`1/k = 1/kA + 1/kB`. One attribute, two sorts of whole, two different aggregation facts —
the oscillator's own instance of *volume aggregates over a rigid assembly and contracts
over a mixture*. A registry keyed by the kind alone must license both or neither. -/

-- ANCHOR: stiffnessParallel
/-- Stiffness assembles into a parallel pair. -/
instance : Assembles parallelS stiffnessK := ⟨DifferenceKind.ofScale⟩
-- deliberately no `Assembles seriesS stiffnessK`

/-- The two wall springs, as parts. -/
def wallSprings : Decomposition Spring := .union (.atom .kA) (.atom .kB)

def stiffOfPar : (s : Spring) →
    IndividualQuantity (Composite.part (σ := parallelS) s) stiffnessK Int
  | .kA => ⟨6⟩
  | .kC => ⟨2⟩
  | .kB => ⟨3⟩

/-- The parallel whole's stiffness: `6 + 3 = 9`. -/
def parallelStiffness :
    IndividualQuantity (Composite.whole : Composite parallelS Spring) stiffnessK Int :=
  assemble parallelS Composite.whole Composite.part wallSprings stiffOfPar

example : parallelStiffness.magnitude = 9 := rfl
-- ANCHOR_END: stiffnessParallel

-- ANCHOR: stiffnessSeries
/- Series: unlicensed, so the sum is not a term anyone can write. -/
/--
error: failed to synthesize instance of type class
  Assembles seriesS stiffnessK

Hint: Type class instance resolution failures can be inspected with the `set_option trace.Meta.synthInstance true` command.
-/
#guard_msgs in
example := fun (f : (s : Spring) →
      IndividualQuantity (Composite.part (σ := seriesS) s) stiffnessK Int) =>
  assemble (k := stiffnessK) seriesS Composite.whole Composite.part wallSprings f
-- ANCHOR_END: stiffnessSeries

/-! The measurement-level facts behind the two licenses. -/

-- ANCHOR: parallelLaw
def stiffNumeral : Spring → Int
  | .kA => 6
  | .kC => 2
  | .kB => 3

def parallelNumeral : Decomposition Spring → Int
  | .atom s => stiffNumeral s
  | .union a b => parallelNumeral a + parallelNumeral b

def parallelMeasurement : Measurement Spring := fun d =>
  { kind := stiffnessK, numeral := parallelNumeral d, reference := "N/m" }

/-- Parallel stiffness is extensive. -/
theorem parallel_extensive : Extensive stiffnessK parallelMeasurement :=
  ⟨fun _ => rfl, fun _ _ => rfl⟩
-- ANCHOR_END: parallelLaw

-- ANCHOR: seriesLaw
/-- Series stiffness: the harmonic combination, exact on the pairs exhibited
(`6 ∥ 3 = 2`, `6 ∥ 6 = 3`). -/
def seriesNumeral : Decomposition Spring → Int
  | .atom s => stiffNumeral s
  | .union a b => (seriesNumeral a * seriesNumeral b) / (seriesNumeral a + seriesNumeral b)

def seriesMeasurement : Measurement Spring := fun d =>
  { kind := stiffnessK, numeral := seriesNumeral d, reference := "N/m" }

/-- Series stiffness is *whole-proper*: `6 ∥ 3 = 2 ≠ 9`, and `6 ∥ 6 = 3 ≠ 6`. -/
theorem series_whole_proper : WholeProper stiffnessK seriesMeasurement where
  ofKind := fun _ => rfl
  notAdditive := ⟨.kA, .kB, by decide⟩
  notUniform := ⟨.kA, .kA, ⟨rfl, by decide⟩⟩

theorem series_not_extensive : ¬ Extensive stiffnessK seriesMeasurement :=
  series_whole_proper.not_extensive
-- ANCHOR_END: seriesLaw

-- ANCHOR: licenseCashed
/-- The parallel license, cashed: the assembled magnitude is the measured whole. -/
theorem parallel_assembled_is_measured :
    (assemble (k := stiffnessK) parallelS (Composite.whole : Composite parallelS Spring)
        Composite.part wallSprings
        (fun s => ⟨(parallelMeasurement (.atom s)).numeral⟩)).magnitude
      = (parallelMeasurement wallSprings).numeral :=
  assemble_eq_measured parallelS Composite.whole Composite.part parallel_extensive wallSprings

/-- Had someone registered the series sort anyway, the term would elaborate and report a
number the whole does not have. -/
theorem series_registered_would_lie [Assembles seriesS stiffnessK] :
    ∃ d : Decomposition Spring,
      (assemble (k := stiffnessK) (R := Int) seriesS
          (Composite.whole : Composite seriesS Spring) Composite.part d
          (fun s => ⟨(seriesMeasurement (.atom s)).numeral⟩)).magnitude
        ≠ (seriesMeasurement d).numeral :=
  assemble_ne_measured seriesS Composite.whole Composite.part series_whole_proper
-- ANCHOR_END: licenseCashed

end Tutorial.HarmonicOscillator

end Blanket
