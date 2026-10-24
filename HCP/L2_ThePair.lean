/-
# L2 — The pair is a system too

Eight build-checked probes of parts, wholes, and aggregation licenses.
-/

module

public import Physlib.ClassicalMechanics.HarmonicOscillator.Basic
public import ForPhysLib.ClassicalMechanics.Feasibility
public import ForPhysLib.ClassicalMechanics.Kinds
public import PropertyKindCalculus

@[expose] public section

open PropertyKindCalculus

noncomputable section

namespace HCP.L2_ThePair

-- ANCHOR: opened_pair
inductive Body | A | B
deriving DecidableEq, Repr

inductive Spring | kA | kC | kB
deriving DecidableEq, Repr

/--
One pair name is one system; its records are states, configurations, or rival estimates to
compare. Different names denote distinct systems.
-/
inductive PairId | P | Q
deriving DecidableEq, Repr

def bodyS : SortOfSystem := ⟨"point mass"⟩
def springS : SortOfSystem := ⟨"linear spring"⟩
def pairS : SortOfSystem := ⟨"coupled oscillator pair"⟩
def parallelS : SortOfSystem := ⟨"springs in parallel"⟩
def seriesS : SortOfSystem := ⟨"springs in series"⟩

instance : Sorted Body := ⟨fun _ => bodyS⟩
instance : Sorted Spring := ⟨fun _ => springS⟩

instance : Designated Body where
  designation
    | .A => ⟨"body A"⟩
    | .B => ⟨"body B"⟩
  designation_inj {x y} h := by
    cases x <;> cases y <;> first | rfl | exact absurd (System.mk.inj h) (by decide)

instance : Designated Spring where
  designation
    | .kA => ⟨"spring A"⟩
    | .kC => ⟨"coupling spring"⟩
    | .kB => ⟨"spring B"⟩
  designation_inj {x y} h := by
    cases x <;> cases y <;> first | rfl | exact absurd (System.mk.inj h) (by decide)

structure CoupledPair (π : PairId) where
  osc : Body → ClassicalMechanics.HarmonicOscillator
  kC : ℝ
  extension : Spring → ℝ

structure PartOf (π : PairId) where
  part : Body ⊕ Spring
deriving DecidableEq, Repr

def bodyPart (π : PairId) (b : Body) : PartOf π := ⟨Sum.inl b⟩

def springPart (π : PairId) (s : Spring) : PartOf π := ⟨Sum.inr s⟩

def springMagnitude {π : PairId} (p : CoupledPair π) : Spring → ℝ
  | .kA => (p.osc .A).k
  | .kC => p.kC
  | .kB => (p.osc .B).k

def massOf {π : PairId} (p : CoupledPair π) (b : Body) :
    IndividualQuantity
      (Composite.part (σ := pairS) (bodyPart π b))
      ForPhysLib.ClassicalMechanics.massK ℝ :=
  ⟨(p.osc b).m⟩

def stiffnessOf {π : PairId} (p : CoupledPair π) (s : Spring) :
    IndividualQuantity
      (Composite.part (σ := pairS) (springPart π s))
      ForPhysLib.ClassicalMechanics.springConstantK ℝ :=
  ⟨springMagnitude p s⟩

def extensionOf {π : PairId} (p : CoupledPair π) (s : Spring) :
    IndividualQuantity
      (Composite.part (σ := pairS) (springPart π s))
      ForPhysLib.ClassicalMechanics.displacementK ℝ :=
  ⟨p.extension s⟩

def couplingSpringExtensionDifference
    (compressed stretched : CoupledPair .P) :
    IndividualQuantity
      (Composite.part (σ := pairS) (springPart .P .kC))
      ForPhysLib.ClassicalMechanics.displacementK ℝ :=
  IndividualQuantity.add DifferenceKind.ofScale
    (extensionOf stretched .kC)
    (-(extensionOf compressed .kC))

#guard_msgs in
example (compressed stretched : CoupledPair .P) :
    IndividualQuantity
      (Composite.part (σ := pairS) (springPart .P .kC))
      ForPhysLib.ClassicalMechanics.displacementK ℝ :=
  couplingSpringExtensionDifference compressed stretched

theorem couplingSpringExtensionDifference_magnitude
    (compressed stretched : CoupledPair .P) :
    (couplingSpringExtensionDifference compressed stretched).magnitude =
      stretched.extension .kC - compressed.extension .kC := by
  simp [couplingSpringExtensionDifference, IndividualQuantity.add_magnitude,
    IndividualQuantity.neg_magnitude, extensionOf]
  change stretched.extension .kC + (-(compressed.extension .kC)) =
    stretched.extension .kC - compressed.extension .kC
  ring
-- ANCHOR_END: opened_pair

-- ANCHOR: pair_mass
instance : Assembles pairS ForPhysLib.ClassicalMechanics.massK :=
  ⟨DifferenceKind.ofScale⟩

def bodies : Decomposition Body := .union (.atom .A) (.atom .B)

def pairMass {π : PairId} (p : CoupledPair π) :
    IndividualQuantity
      (Composite.whole : Composite pairS (PartOf π))
      ForPhysLib.ClassicalMechanics.massK ℝ :=
  assemble (k := ForPhysLib.ClassicalMechanics.massK) pairS
    (Composite.whole : Composite pairS (PartOf π))
    (fun b : Body => Composite.part (σ := pairS) (bodyPart π b))
    bodies
    (fun b => massOf p b)

theorem pairMass_magnitude {π : PairId} (p : CoupledPair π) :
    (pairMass p).magnitude = (p.osc .A).m + (p.osc .B).m := by
  rfl
-- ANCHOR_END: pair_mass

-- ANCHOR: refused_whole_part
/--
error: Application type mismatch: The argument
  massOf p Body.A
has type
  IndividualQuantity (Composite.part (bodyPart π Body.A)) ForPhysLib.ClassicalMechanics.massK ℝ
but is expected to have type
  IndividualQuantity Composite.whole ForPhysLib.ClassicalMechanics.massK ℝ
in the application
  IndividualQuantity.add ⋯ (pairMass p) (massOf p Body.A)
-/
#guard_msgs in
example {π : PairId} (p : CoupledPair π) :=
  IndividualQuantity.add (k := ForPhysLib.ClassicalMechanics.massK)
    DifferenceKind.ofScale (pairMass p) (massOf p .A)

/--
error: Application type mismatch: The argument
  pairMass q
has type
  IndividualQuantity (@Composite.whole pairS (PartOf PairId.Q)) ForPhysLib.ClassicalMechanics.massK ℝ
but is expected to have type
  IndividualQuantity (@Composite.whole pairS (PartOf PairId.P)) ForPhysLib.ClassicalMechanics.massK ℝ
in the application
  IndividualQuantity.add ⋯ (pairMass p) (pairMass q)
-/
#guard_msgs in
example (o : Body → ClassicalMechanics.HarmonicOscillator) :=
  let p : CoupledPair .P := ⟨o, 2, fun _ => 0⟩
  let q : CoupledPair .Q := ⟨o, 2, fun _ => 0⟩
  IndividualQuantity.add (k := ForPhysLib.ClassicalMechanics.massK)
    DifferenceKind.ofScale (pairMass p) (pairMass (π := .Q) q)
-- ANCHOR_END: refused_whole_part

-- ANCHOR: refused_frequency_assembly
/--
error: failed to synthesize instance of type class
  Assembles pairS ForPhysLib.ClassicalMechanics.Kinds.angularFrequency

Hint: Type class instance resolution failures can be inspected with the `set_option trace.Meta.synthInstance true` command.
-/
#guard_msgs in
example :=
  fun {π : PairId} (p : CoupledPair π) =>
    fun (f : (b : Body) →
      IndividualQuantity
        (Composite.part (σ := pairS) (bodyPart π b))
        ForPhysLib.ClassicalMechanics.Kinds.angularFrequency ℝ) =>
      assemble (k := ForPhysLib.ClassicalMechanics.Kinds.angularFrequency) pairS
        (Composite.whole : Composite pairS (PartOf π))
        (fun b : Body => Composite.part (σ := pairS) (bodyPart π b))
        bodies f
-- ANCHOR_END: refused_frequency_assembly

-- ANCHOR: normal_mode
def whole : Component := ⟨"whole"⟩

def dkOmegaPlus : DedicatedKind :=
  ForPhysLib.ClassicalMechanics.Kinds.angularFrequency.dedicatedTo
    pairS ⟨"normal mode +"⟩

theorem normal_mode_not_of_a_body :
    dkOmegaPlus ≠
      ForPhysLib.ClassicalMechanics.Kinds.angularFrequency.dedicatedFor Body.A whole :=
  DedicatedKind.distinct_of_sort (by decide)

theorem normal_mode_not_of_a_spring :
    dkOmegaPlus ≠
      ForPhysLib.ClassicalMechanics.Kinds.angularFrequency.dedicatedFor Spring.kC whole :=
  DedicatedKind.distinct_of_sort (by decide)
-- ANCHOR_END: normal_mode

-- ANCHOR: parallel_stiffness
instance : Assembles parallelS ForPhysLib.ClassicalMechanics.springConstantK :=
  ⟨DifferenceKind.ofScale⟩

def parallelSprings : Decomposition Spring := .union (.atom .kA) (.atom .kC)

def stiffnessInSort {π : PairId} (p : CoupledPair π) (σ : SortOfSystem) (s : Spring) :
    IndividualQuantity (Composite.part (σ := σ) (springPart π s))
      ForPhysLib.ClassicalMechanics.springConstantK ℝ :=
  ⟨springMagnitude p s⟩

def parallelStiffness {π : PairId} (p : CoupledPair π) :
    IndividualQuantity
      (Composite.whole : Composite parallelS (PartOf π))
      ForPhysLib.ClassicalMechanics.springConstantK ℝ :=
  assemble (k := ForPhysLib.ClassicalMechanics.springConstantK) parallelS
    (Composite.whole : Composite parallelS (PartOf π))
    (fun s : Spring => Composite.part (σ := parallelS) (springPart π s))
    parallelSprings
    (fun s => stiffnessInSort p parallelS s)

theorem parallelStiffness_magnitude {π : PairId} (p : CoupledPair π) :
    (parallelStiffness p).magnitude = (p.osc .A).k + p.kC := by
  rfl
-- ANCHOR_END: parallel_stiffness

-- ANCHOR: refused_series_stiffness
def seriesSprings : Decomposition Spring := .union (.atom .kA) (.atom .kB)

/--
error: failed to synthesize instance of type class
  Assembles seriesS ForPhysLib.ClassicalMechanics.springConstantK

Hint: Type class instance resolution failures can be inspected with the `set_option trace.Meta.synthInstance true` command.
-/
#guard_msgs in
example {π : PairId} (p : CoupledPair π) :=
  assemble (k := ForPhysLib.ClassicalMechanics.springConstantK) seriesS
    (Composite.whole : Composite seriesS (PartOf π))
    (fun s : Spring => Composite.part (σ := seriesS) (springPart π s))
    seriesSprings
    (fun s => stiffnessInSort p seriesS s)
-- ANCHOR_END: refused_series_stiffness

-- ANCHOR: parallelLaw
def stiffnessNumeral : Spring → Int
  | .kA => 6
  | .kC => 2
  | .kB => 3

def parallelNumeral : Decomposition Spring → Int
  | .atom s => stiffnessNumeral s
  | .union a b => parallelNumeral a + parallelNumeral b

def parallelMeasurement : Measurement Spring := fun d =>
  { kind := ForPhysLib.ClassicalMechanics.springConstantK
    numeral := parallelNumeral d
    reference := "N/m" }

theorem parallel_extensive :
    Extensive ForPhysLib.ClassicalMechanics.springConstantK parallelMeasurement :=
  ⟨fun _ => rfl, fun _ _ => rfl⟩
-- ANCHOR_END: parallelLaw

-- ANCHOR: seriesLaw
def seriesNumeral : Decomposition Spring → Int
  | .atom s => stiffnessNumeral s
  | .union a b =>
      (seriesNumeral a * seriesNumeral b) / (seriesNumeral a + seriesNumeral b)

def seriesMeasurement : Measurement Spring := fun d =>
  { kind := ForPhysLib.ClassicalMechanics.springConstantK
    numeral := seriesNumeral d
    reference := "N/m" }

theorem series_kA_kB_exact : (seriesMeasurement seriesSprings).numeral = 2 := by decide

theorem series_whole_proper :
    WholeProper ForPhysLib.ClassicalMechanics.springConstantK seriesMeasurement where
  ofKind := fun _ => rfl
  notAdditive := ⟨.kA, .kB, by decide⟩
  notUniform := ⟨.kA, .kA, ⟨rfl, by decide⟩⟩

theorem series_not_extensive :
    ¬ Extensive ForPhysLib.ClassicalMechanics.springConstantK seriesMeasurement :=
  series_whole_proper.not_extensive
-- ANCHOR_END: seriesLaw

-- ANCHOR: licenseCashed
theorem parallel_assembled_is_measured {π : PairId} (_p : CoupledPair π) :
    (assemble (k := ForPhysLib.ClassicalMechanics.springConstantK) parallelS
        (Composite.whole : Composite parallelS (PartOf π))
        (fun s => Composite.part (σ := parallelS) (springPart π s)) parallelSprings
        (fun s => ⟨(parallelMeasurement (.atom s)).numeral⟩)).magnitude
      = (parallelMeasurement parallelSprings).numeral :=
  assemble_eq_measured parallelS Composite.whole
    (fun s => Composite.part (σ := parallelS) (springPart π s))
    parallel_extensive parallelSprings

theorem series_registered_would_lie
    {π : PairId} (_p : CoupledPair π)
    [Assembles seriesS ForPhysLib.ClassicalMechanics.springConstantK] :
    ∃ d : Decomposition Spring,
      (assemble (k := ForPhysLib.ClassicalMechanics.springConstantK) (R := Int) seriesS
          (Composite.whole : Composite seriesS (PartOf π))
          (fun s => Composite.part (σ := seriesS) (springPart π s)) d
          (fun s => ⟨(seriesMeasurement (.atom s)).numeral⟩)).magnitude
        ≠ (seriesMeasurement d).numeral :=
  assemble_ne_measured seriesS Composite.whole
    (fun s => Composite.part (σ := seriesS) (springPart π s)) series_whole_proper
-- ANCHOR_END: licenseCashed

end HCP.L2_ThePair

end
