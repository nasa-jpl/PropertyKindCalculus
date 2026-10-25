/-
# L2 — The pair is a system too

Eight build-checked probes of parts, wholes, and aggregation licenses.

Edit this worksheet in place, build with `lake build HCP.Worksheets.L2_ThePair`,
and compare with the solution at `HCP/L2_ThePair.lean`.
-/

module

public import Physlib.ClassicalMechanics.HarmonicOscillator.Basic
public import ForPhysLib.ClassicalMechanics.Feasibility
public import ForPhysLib.ClassicalMechanics.Kinds
public import PropertyKindCalculus

@[expose] public section

open PropertyKindCalculus

noncomputable section

namespace HCP.Worksheets.L2_ThePair

-- EXERCISE: opened_pair
-- GIVEN:
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

-- TODO: construct the quantities on their part bearers and compare two records.
def massOf {π : PairId} (p : CoupledPair π) (b : Body) :
    IndividualQuantity
      (Composite.part (σ := pairS) (bodyPart π b))
      ForPhysLib.ClassicalMechanics.massK ℝ := by
  sorry

def stiffnessOf {π : PairId} (p : CoupledPair π) (s : Spring) :
    IndividualQuantity
      (Composite.part (σ := pairS) (springPart π s))
      ForPhysLib.ClassicalMechanics.springConstantK ℝ := by
  sorry

def extensionOf {π : PairId} (p : CoupledPair π) (s : Spring) :
    IndividualQuantity
      (Composite.part (σ := pairS) (springPart π s))
      ForPhysLib.ClassicalMechanics.displacementK ℝ := by
  sorry

def couplingSpringExtensionDifference
    (compressed stretched : CoupledPair .P) :
    IndividualQuantity
      (Composite.part (σ := pairS) (springPart .P .kC))
      ForPhysLib.ClassicalMechanics.displacementK ℝ := by
  sorry

theorem couplingSpringExtensionDifference_magnitude
    (compressed stretched : CoupledPair .P) :
    (couplingSpringExtensionDifference compressed stretched).magnitude =
      stretched.extension .kC - compressed.extension .kC := by
  sorry
-- EXERCISE_END: opened_pair

-- EXERCISE: pair_mass
-- TODO: license mass assembly for pairS, then build the whole-pair mass.
instance : Assembles pairS ForPhysLib.ClassicalMechanics.massK :=
  ⟨by sorry⟩

def bodies : Decomposition Body := .union (.atom .A) (.atom .B)

def pairMass {π : PairId} (p : CoupledPair π) :
    IndividualQuantity
      (Composite.whole : Composite pairS (PartOf π))
      ForPhysLib.ClassicalMechanics.massK ℝ := by
  sorry

theorem pairMass_magnitude {π : PairId} (p : CoupledPair π) :
    (pairMass p).magnitude = (p.osc .A).m + (p.osc .B).m := by
  sorry
-- EXERCISE_END: pair_mass

-- EXERCISE: refused_whole_part
-- TODO: uncomment each expression, read the errors, and say why the bearers do not match.
-- Bearer safety: Refused: type mismatch between pair P's whole-mass bearer and body A's part-mass bearer; this prevents treating a part mass as the pair's whole mass.
-- example {π : PairId} (p : CoupledPair π) :=
--   IndividualQuantity.add (k := ForPhysLib.ClassicalMechanics.massK)
--     DifferenceKind.ofScale (pairMass p) (massOf p .A)
-- Bearer safety: Refused: type mismatch between pair P's and pair Q's whole-mass bearers; this prevents combining masses from distinct pairs as one system.
-- example (o : Body → ClassicalMechanics.HarmonicOscillator) :=
--   let p : CoupledPair .P := ⟨o, 2, fun _ => 0⟩
--   let q : CoupledPair .Q := ⟨o, 2, fun _ => 0⟩
--   IndividualQuantity.add (k := ForPhysLib.ClassicalMechanics.massK)
--     DifferenceKind.ofScale (pairMass p) (pairMass (π := .Q) q)
-- EXERCISE_END: refused_whole_part

-- EXERCISE: refused_frequency_assembly
-- TODO: uncomment the assembly attempt and explain why the pair sort has no such license.
-- Licensed composition: Refused: no Assembles pairS angularFrequency instance licenses deriving the pair's normal-mode frequency from the bodies' frequencies.
-- example :=
--   fun {π : PairId} (p : CoupledPair π) =>
--     fun (f : (b : Body) →
--       IndividualQuantity
--         (Composite.part (σ := pairS) (bodyPart π b))
--         ForPhysLib.ClassicalMechanics.Kinds.angularFrequency ℝ) =>
--       assemble (k := ForPhysLib.ClassicalMechanics.Kinds.angularFrequency) pairS
--         (Composite.whole : Composite pairS (PartOf π))
--         (fun b : Body => Composite.part (σ := pairS) (bodyPart π b))
--         bodies f
-- EXERCISE_END: refused_frequency_assembly

-- EXERCISE: normal_mode
-- GIVEN:
def whole : Component := ⟨"whole"⟩

-- TODO: dedicate angular frequency to the pair sort and prove it is not body- or spring-specific.
def dkOmegaPlus : DedicatedKind := by
  sorry

theorem normal_mode_not_of_a_body :
    dkOmegaPlus ≠
      ForPhysLib.ClassicalMechanics.Kinds.angularFrequency.dedicatedFor Body.A whole := by
  sorry

theorem normal_mode_not_of_a_spring :
    dkOmegaPlus ≠
      ForPhysLib.ClassicalMechanics.Kinds.angularFrequency.dedicatedFor Spring.kC whole := by
  sorry
-- EXERCISE_END: normal_mode

-- EXERCISE: parallel_stiffness
-- TODO: give parallel springs an assembly license and construct their effective stiffness.
instance : Assembles parallelS ForPhysLib.ClassicalMechanics.springConstantK :=
  ⟨by sorry⟩

def parallelSprings : Decomposition Spring := .union (.atom .kA) (.atom .kC)

def stiffnessInSort {π : PairId} (p : CoupledPair π) (σ : SortOfSystem) (s : Spring) :
    IndividualQuantity (Composite.part (σ := σ) (springPart π s))
      ForPhysLib.ClassicalMechanics.springConstantK ℝ := by
  sorry

def parallelStiffness {π : PairId} (p : CoupledPair π) :
    IndividualQuantity
      (Composite.whole : Composite parallelS (PartOf π))
      ForPhysLib.ClassicalMechanics.springConstantK ℝ := by
  sorry

theorem parallelStiffness_magnitude {π : PairId} (p : CoupledPair π) :
    (parallelStiffness p).magnitude = (p.osc .A).k + p.kC := by
  sorry
-- EXERCISE_END: parallel_stiffness

-- EXERCISE: refused_series_stiffness
-- GIVEN:
def seriesSprings : Decomposition Spring := .union (.atom .kA) (.atom .kB)

-- TODO: uncomment the assembly attempt and explain why the series license is absent.
-- Licensed composition: Refused: no Assembles seriesS springConstantK instance; an additive rule would give kA + kB = 9, but the series measurement is 2.
-- example {π : PairId} (p : CoupledPair π) :=
--   assemble (k := ForPhysLib.ClassicalMechanics.springConstantK) seriesS
--     (Composite.whole : Composite seriesS (PartOf π))
--     (fun s : Spring => Composite.part (σ := seriesS) (springPart π s))
--     seriesSprings
--     (fun s => stiffnessInSort p seriesS s)
-- EXERCISE_END: refused_series_stiffness

-- EXERCISE: parallelLaw
-- TODO: define additive parallel measurement and prove its extensive property.
def stiffnessNumeral : Spring → Int
  | .kA => 6
  | .kC => 2
  | .kB => 3

def parallelNumeral : Decomposition Spring → Int := by
  sorry

def parallelMeasurement : Measurement Spring := by
  sorry

theorem parallel_extensive :
    Extensive ForPhysLib.ClassicalMechanics.springConstantK parallelMeasurement := by
  sorry
-- EXERCISE_END: parallelLaw

-- EXERCISE: seriesLaw
-- TODO: define the series measurement, show its exact value, and prove it is not extensive.
def seriesNumeral : Decomposition Spring → Int := by
  sorry

def seriesMeasurement : Measurement Spring := by
  sorry

theorem series_kA_kB_exact : (seriesMeasurement seriesSprings).numeral = 2 := by
  sorry

theorem series_whole_proper :
    WholeProper ForPhysLib.ClassicalMechanics.springConstantK seriesMeasurement := by
  sorry

theorem series_not_extensive :
    ¬ Extensive ForPhysLib.ClassicalMechanics.springConstantK seriesMeasurement := by
  sorry
-- EXERCISE_END: seriesLaw

-- EXERCISE: licenseCashed
-- TODO: connect the assembly theorem to parallel measurement and show a false series license conflicts.
theorem parallel_assembled_is_measured {π : PairId} (_p : CoupledPair π) :
    (assemble (k := ForPhysLib.ClassicalMechanics.springConstantK) parallelS
        (Composite.whole : Composite parallelS (PartOf π))
        (fun s => Composite.part (σ := parallelS) (springPart π s)) parallelSprings
        (fun s => ⟨(parallelMeasurement (.atom s)).numeral⟩)).magnitude
      = (parallelMeasurement parallelSprings).numeral := by
  sorry

theorem series_registered_would_lie
    {π : PairId} (_p : CoupledPair π)
    [Assembles seriesS ForPhysLib.ClassicalMechanics.springConstantK] :
    ∃ d : Decomposition Spring,
      (assemble (k := ForPhysLib.ClassicalMechanics.springConstantK) (R := Int) seriesS
          (Composite.whole : Composite seriesS (PartOf π))
          (fun s => Composite.part (σ := seriesS) (springPart π s)) d
          (fun s => ⟨(seriesMeasurement (.atom s)).numeral⟩)).magnitude
        ≠ (seriesMeasurement d).numeral := by
  sorry
-- EXERCISE_END: licenseCashed

end HCP.Worksheets.L2_ThePair

end
