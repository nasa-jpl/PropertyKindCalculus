import Verso
import VersoManual
import VersoBlueprint
import PropertyKindCalculusBlueprint.References
import HCP.L2_ThePair
import PropertyKindCalculus

open Verso.Genre
open Verso.Genre.Manual
open Informal
open Verso.Code.External
open HCP.L2_ThePair
open PropertyKindCalculus

set_option verso.exampleProject ".."
set_option verso.exampleModule "HCP.L2_ThePair"

#doc (Manual) "L2 — The pair is a system too" =>
%%%
tag := "hcp-l2"
%%%

Once A and B are coupled, what bears the total mass and the oscillation frequency? Open
the L1 black boxes into bodies A and B and springs kA, kC, and kB. The coupling spring
makes the oscillators interact, so L1's no-interaction assumption falls. Mass is borne by
the bodies and stiffness by the springs; the L1 oscillator-indexed `ω² = k/m` does not
survive coupling. The normal-mode angular frequency belongs to the pair whole.

_1. Open the box._ Each body's upstream harmonic oscillator still supplies its wall-spring
parameters; the coupling spring is the new field:

```anchor opened_pair
inductive Body | A | B
deriving DecidableEq, Repr

inductive Spring | kA | kC | kB
deriving DecidableEq, Repr

abbrev Part := Body ⊕ Spring

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

structure CoupledPair where
  osc : Body → ClassicalMechanics.HarmonicOscillator
  kC : ℝ

def springMagnitude (p : CoupledPair) : Spring → ℝ
  | .kA => (p.osc .A).k
  | .kC => p.kC
  | .kB => (p.osc .B).k

def massOf (p : CoupledPair) (b : Body) :
    IndividualQuantity
      (Composite.part (σ := pairS) (Sum.inl b : Part))
      ForPhysLib.ClassicalMechanics.massK ℝ :=
  ⟨(p.osc b).m⟩

def stiffnessOf (p : CoupledPair) (s : Spring) :
    IndividualQuantity
      (Composite.part (σ := pairS) (Sum.inr s : Part))
      ForPhysLib.ClassicalMechanics.springConstantK ℝ :=
  ⟨springMagnitude p s⟩
```

Mass is now indexed by a body part and stiffness by a spring part. The oscillator-indexed
L1 `ω²` was the frequency of an isolated oscillator; it is not the normal-mode frequency
of this coupled pair.

_2. Assemble the pair's mass._ The two body masses are parts of `Composite.whole`; `rfl`
checks that the total reads the upstream oscillator fields:

```anchor pair_mass
instance : Assembles pairS ForPhysLib.ClassicalMechanics.massK :=
  ⟨DifferenceKind.ofScale⟩

def bodies : Decomposition Body := .union (.atom .A) (.atom .B)

def pairMass (p : CoupledPair) :
    IndividualQuantity
      (Composite.whole : Composite pairS Part)
      ForPhysLib.ClassicalMechanics.massK ℝ :=
  assemble (k := ForPhysLib.ClassicalMechanics.massK) pairS
    (Composite.whole : Composite pairS Part)
    (fun b : Body => Composite.part (σ := pairS) (Sum.inl b : Part))
    bodies
    (fun b => massOf p b)

theorem pairMass_magnitude (p : CoupledPair) :
    (pairMass p).magnitude = (p.osc .A).m + (p.osc .B).m := by
  rfl
```

_3. Refuse whole plus part._ Total mass is meaningful, but its whole is not body A:

```anchor refused_whole_part
/--
error: Application type mismatch: The argument
  massOf p Body.A
has type
  IndividualQuantity (Composite.part (Sum.inl Body.A)) ForPhysLib.ClassicalMechanics.massK ℝ
but is expected to have type
  IndividualQuantity Composite.whole ForPhysLib.ClassicalMechanics.massK ℝ
in the application
  IndividualQuantity.add ⋯ (pairMass p) (massOf p Body.A)
-/
#guard_msgs in
example (p : CoupledPair) :=
  IndividualQuantity.add (k := ForPhysLib.ClassicalMechanics.massK)
    DifferenceKind.ofScale (pairMass p) (massOf p .A)
```

_4. Refuse to assemble angular frequency._ The pair's license table has no entry for it:

```anchor refused_frequency_assembly
/--
error: failed to synthesize instance of type class
  Assembles pairS ForPhysLib.ClassicalMechanics.Kinds.angularFrequency

Hint: Type class instance resolution failures can be inspected with the `set_option trace.Meta.synthInstance true` command.
-/
#guard_msgs in
example :=
  fun (f : (b : Body) →
      IndividualQuantity
        (Composite.part (σ := pairS) (Sum.inl b : Part))
        ForPhysLib.ClassicalMechanics.Kinds.angularFrequency ℝ) =>
    assemble (k := ForPhysLib.ClassicalMechanics.Kinds.angularFrequency) pairS
      (Composite.whole : Composite pairS Part)
      (fun b : Body => Composite.part (σ := pairS) (Sum.inl b : Part))
      bodies f
```

_5. Give the normal mode its whole._ A dedicated angular-frequency kind at `pairS` is
distinct from one dedicated to a body or a spring:

```anchor normal_mode
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
```

_6. Assemble parallel stiffness._ With B clamped, A is held by kA and kC in parallel:

```anchor parallel_stiffness
instance : Assembles parallelS ForPhysLib.ClassicalMechanics.springConstantK :=
  ⟨DifferenceKind.ofScale⟩

def parallelSprings : Decomposition Spring := .union (.atom .kA) (.atom .kC)

def stiffnessInSort (p : CoupledPair) (σ : SortOfSystem) (s : Spring) :
    IndividualQuantity (Composite.part (σ := σ) s)
      ForPhysLib.ClassicalMechanics.springConstantK ℝ :=
  ⟨springMagnitude p s⟩

def parallelStiffness (p : CoupledPair) :
    IndividualQuantity
      (Composite.whole : Composite parallelS Spring)
      ForPhysLib.ClassicalMechanics.springConstantK ℝ :=
  assemble (k := ForPhysLib.ClassicalMechanics.springConstantK) parallelS
    (Composite.whole : Composite parallelS Spring)
    (fun s : Spring => Composite.part (σ := parallelS) s)
    parallelSprings
    (fun s => stiffnessInSort p parallelS s)

theorem parallelStiffness_magnitude (p : CoupledPair) :
    (parallelStiffness p).magnitude = (p.osc .A).k + p.kC := by
  rfl
```

_7. Refuse series stiffness._ For two springs chained end to end, no additive series
license is registered:

```anchor refused_series_stiffness
/--
error: failed to synthesize instance of type class
  Assembles seriesS ForPhysLib.ClassicalMechanics.springConstantK

Hint: Type class instance resolution failures can be inspected with the `set_option trace.Meta.synthInstance true` command.
-/
#guard_msgs in
example (p : CoupledPair) :=
  assemble (k := ForPhysLib.ClassicalMechanics.springConstantK) seriesS
    (Composite.whole : Composite seriesS Spring)
    (fun s : Spring => Composite.part (σ := seriesS) s)
    parallelSprings
    (fun s => stiffnessInSort p seriesS s)
```

_8. Check the licenses against measurements._ The numerical measurements use HCP's own
`Spring` and the tutorial's integer examples:

```anchor parallelLaw
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
```

```anchor seriesLaw
def seriesNumeral : Decomposition Spring → Int
  | .atom s => stiffnessNumeral s
  | .union a b =>
      (seriesNumeral a * seriesNumeral b) / (seriesNumeral a + seriesNumeral b)

def seriesMeasurement : Measurement Spring := fun d =>
  { kind := ForPhysLib.ClassicalMechanics.springConstantK
    numeral := seriesNumeral d
    reference := "N/m" }

theorem series_whole_proper :
    WholeProper ForPhysLib.ClassicalMechanics.springConstantK seriesMeasurement where
  ofKind := fun _ => rfl
  notAdditive := ⟨.kA, .kB, by decide⟩
  notUniform := ⟨.kA, .kA, ⟨rfl, by decide⟩⟩

theorem series_not_extensive :
    ¬ Extensive ForPhysLib.ClassicalMechanics.springConstantK seriesMeasurement :=
  series_whole_proper.not_extensive
```

```anchor licenseCashed
theorem parallel_assembled_is_measured :
    (assemble (k := ForPhysLib.ClassicalMechanics.springConstantK) parallelS
        (Composite.whole : Composite parallelS Spring) Composite.part parallelSprings
        (fun s => ⟨(parallelMeasurement (.atom s)).numeral⟩)).magnitude
      = (parallelMeasurement parallelSprings).numeral :=
  assemble_eq_measured parallelS Composite.whole Composite.part
    parallel_extensive parallelSprings

theorem series_registered_would_lie
    [Assembles seriesS ForPhysLib.ClassicalMechanics.springConstantK] :
    ∃ d : Decomposition Spring,
      (assemble (k := ForPhysLib.ClassicalMechanics.springConstantK) (R := Int) seriesS
          (Composite.whole : Composite seriesS Spring) Composite.part d
          (fun s => ⟨(seriesMeasurement (.atom s)).numeral⟩)).magnitude
        ≠ (seriesMeasurement d).numeral :=
  assemble_ne_measured seriesS Composite.whole Composite.part series_whole_proper
```

The measurements verify the curation: parallel stiffness is extensive, while series
stiffness is whole-proper. Registering the series sum would produce a magnitude that
disagrees with its measurement.

The system-context card in `HCP/L2-the-pair.md` lists the bodies, all three springs,
the fixed walls, and the line of motion. The Lean model keeps body mass, spring stiffness,
and the pair's normal-mode frequency on their respective bearers. The on-axis, rigid,
homogeneous, point-like body assumption returns at L3.
