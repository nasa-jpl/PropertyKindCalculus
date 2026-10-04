/-
# Tutorial — the ontological square, walked for two bodies and three springs

The harmonic oscillator of `ForPhysLib.CaseStudies.HarmonicOscillator`, typed four ways
and scored there against MR1–MR19, never *walks* Lowe's four-category square: its objects
are nominal `System`s that know no sort, its springs are not objects at all, and its
aggregation facts are stated at the measurement level by hand. This module is the walk
the case study lacks, on the same system, every claim compiled — refusals as
`#check_failure`, agreements as `example` and `theorem`.

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

Part of the separate `Examples` library; imports only the Mathlib-free core. The
requirements stated on this system are in `HarmonicOscillatorRequirements`, which imports
the case study and so Mathlib.
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

namespace PropertyKindCalculus.Examples.Tutorial.HarmonicOscillator

open PropertyKindCalculus

/-! ## Attributes corner — kinds-of-property (non-substantial universals) -/

def massK : KindOfProperty := { id := "mass", scale := .ratio }
def stiffnessK : KindOfProperty := { id := "spring constant", scale := .ratio }
def angFreqK : KindOfProperty := { id := "angular frequency", scale := .ratio }
def displacementK : KindOfProperty := { id := "displacement", scale := .ratio }
def forceK : KindOfProperty := { id := "force", scale := .ratio }

/-! ## Kinds corner — sorts of system (substantial universals) -/

def bodyS : SortOfSystem := ⟨"point mass"⟩
def springS : SortOfSystem := ⟨"linear spring"⟩
def pairS : SortOfSystem := ⟨"coupled oscillator pair"⟩
def parallelS : SortOfSystem := ⟨"springs in parallel"⟩
def seriesS : SortOfSystem := ⟨"springs in series"⟩

/-! ## Substances corner — object types (substantial particulars) -/

inductive Body | A | B
deriving DecidableEq, Repr

inductive Spring | kA | kC | kB
deriving DecidableEq, Repr

/-- Left edge, *instantiated by*: every body is a point mass. Declared once, never derived. -/
instance : Sorted Body := ⟨fun _ => bodyS⟩
/-- Every spring is a linear spring. -/
instance : Sorted Spring := ⟨fun _ => springS⟩

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

/-! ## Modes corner — individual quantities (non-substantial particulars) -/

def mA : IndividualQuantity Body.A massK Int := ⟨3⟩
def mB : IndividualQuantity Body.B massK Int := ⟨5⟩
def kA : IndividualQuantity Spring.kA stiffnessK Int := ⟨6⟩
def kC : IndividualQuantity Spring.kC stiffnessK Int := ⟨2⟩
def kB : IndividualQuantity Spring.kB stiffnessK Int := ⟨3⟩

/-! ## The four edges, each one line -/

/-- Left edge: a substance instantiates its kind (sort). -/
example : Sorted.sortOf Body.A = bodyS := rfl
example : Sorted.sortOf Spring.kC = springS := rfl
theorem bodies_one_sort : Sorted.sortOf Body.A = Sorted.sortOf Body.B := rfl

/-- Bottom + right edges: the two type indices of a mode, read back as an individual
property — the mode characterizes body A and instantiates mass. -/
example : mA.toIndividualProperty = ⟨massK, ⟨"body A"⟩⟩ := rfl

/-- Top edge, *characterized by*: the dedicated kind, reached *through the object* by
`dedicatedFor` (up the left edge, across the top). Two bodies of one sort share one
catalogue entry; the object index, not the entry, keeps their masses apart. -/
def whole : Component := ⟨"whole"⟩

theorem a_and_b_share_entry :
    massK.dedicatedFor Body.A whole = massK.dedicatedFor Body.B whole :=
  KindOfProperty.dedicatedFor_congr rfl whole

/-- The normal mode is a property of the *pair's sort* and of nothing below it. -/
def dkOmegaPlus : DedicatedKind := angFreqK.dedicatedTo pairS ⟨"normal mode +"⟩

theorem normal_mode_not_of_a_body : dkOmegaPlus ≠ angFreqK.dedicatedFor Body.A whole :=
  DedicatedKind.distinct_of_sort (by decide)

theorem normal_mode_not_of_a_spring : dkOmegaPlus ≠ angFreqK.dedicatedFor Spring.kC whole :=
  DedicatedKind.distinct_of_sort (by decide)

/-! The case study's objects are nominal `System`s and know no sort, so they cannot reach
the top edge through `dedicatedFor` at all — the refusal that says why the tutorial needs
an object type with a `Sorted` instance. -/
#check_failure (massK.dedicatedFor (⟨"oscillator A"⟩ : Object) whole)

/-! ## The refusals the two heavy edges buy -/

/- Bottom edge: masses of two bodies do not add. -/
#check_failure (IndividualQuantity.add DifferenceKind.ofScale mA mB)
/- Nor stiffnesses of two springs. -/
#check_failure (IndividualQuantity.add DifferenceKind.ofScale kA kC)
/- B's mass cannot stand in for A's. -/
#check_failure (mB : IndividualQuantity Body.A massK Int)
/- Right edge: one body, two kinds, refused. -/
#check_failure (fun (x : IndividualQuantity Body.A displacementK Int) =>
  IndividualQuantity.add DifferenceKind.ofScale mA x)

/-! ## Joint objects — the coupling force, and Newton's third law as a type -/

/-- The force the coupling spring exerts on A, read from A's end: a quantity of the ordered
pair `(A, B)`. -/
def fAB : IndividualQuantity ((Body.A, Body.B) : Body × Body) forceK Int := ⟨-4⟩

/-- The same coupling read from B's end. -/
example : IndividualQuantity ((Body.B, Body.A) : Body × Body) forceK Int := fAB.transpose

/- The two readings are of different objects and do not add. -/
#check_failure (IndividualQuantity.add DifferenceKind.ofScale fAB fAB.transpose)

/-! ## Assembly over the pair: mass is licensed, angular frequency is not -/

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

/- Whole and part do not add (MR22). -/
#check_failure (IndividualQuantity.add (k := massK) DifferenceKind.ofScale pairMass (massOf .A))

/- Angular frequency carries no license for the pair, so `2 + 4` is not a term. -/
#check_failure (fun (f : (b : Body) →
      IndividualQuantity (Composite.part (σ := pairS) (Sum.inl b : Part)) angFreqK Int) =>
  assemble (k := angFreqK) pairS Composite.whole
    (fun b : Body => Composite.part (Sum.inl b)) bodies f)

/-! ## Stiffness: the same parts, two sorts of whole — what the Kinds corner buys

Two springs in parallel: `k = kA + kB`. The same two springs in series:
`1/k = 1/kA + 1/kB`. One attribute, two sorts of whole, two different aggregation facts —
the oscillator's own instance of *volume aggregates over a rigid assembly and contracts
over a mixture*. A registry keyed by the kind alone must license both or neither. -/

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

/- Series: unlicensed, so the sum is not a term anyone can write. -/
#check_failure (fun (f : (s : Spring) →
      IndividualQuantity (Composite.part (σ := seriesS) s) stiffnessK Int) =>
  assemble (k := stiffnessK) seriesS Composite.whole Composite.part wallSprings f)

/-! The measurement-level facts behind the two licenses. -/

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

end PropertyKindCalculus.Examples.Tutorial.HarmonicOscillator

end Blanket
