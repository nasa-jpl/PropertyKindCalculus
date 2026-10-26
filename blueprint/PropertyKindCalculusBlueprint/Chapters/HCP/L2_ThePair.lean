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

/-
---
hcp: 3
id: hcp-l2
persona: "PhysLib contributor"
layer: PKC
pull: "Once A and B are coupled, what bears the total mass and the oscillation frequency?"
improvement: "Open the oscillator boxes into parts and model the pair as a whole with sort-specific aggregation licenses."
concepts:
  - informal: "two bodies and three springs form a coupled pair"
    formal: "Body, Spring, PairId, CoupledPair π with signed extensions, and PartOf π with pairS"
    where: "System-context card; HCP.L2_ThePair#opened_pair"
  - informal: "the pair bears the total mass"
    formal: "pairMass has the pair-indexed Composite.whole and assembles body masses"
    where: "HCP.L2_ThePair#pair_mass"
  - informal: "normal-mode frequency belongs to the coupled pair"
    formal: "angularFrequency dedicated to pairS, not bodyS or springS"
    where: "HCP.L2_ThePair#normal_mode"
  - informal: "parallel stiffness adds, but series stiffness does not"
    formal: "Assembles parallelS springConstantK, with no series license"
    where: "HCP.L2_ThePair#parallel_stiffness; HCP.L2_ThePair#refused_series_stiffness"
artifacts: ['Lean lesson HCP.L2_ThePair', 'Blueprint chapter L2 — The pair is a system too']
tools: ['lake build HCP', 'python3 HCP/check-hcp.py']
exercises: 8
disclosure: ['open the oscillator boxes and compare configurations', 'assemble the pair mass', 'refuse whole plus part', 'refuse angular-frequency assembly', 'dedicate the normal mode to the pair', 'assemble parallel stiffness', 'refuse series stiffness', 'check the aggregation licenses against measurements']
owner: 'PKC methodology lead'
state:
  completed: []
---
-/

#doc (Manual) "L2 — The pair is a system too" =>
%%%
tag := "hcp-l2"
%%%

# Synopsis

## Purpose

Open each oscillator into its body and wall spring, add a coupling spring between bodies A and B, and treat the coupled pair as a system of its own sort, `pairS`. `assemble` sums a quantity of kind k over the parts of a whole of sort σ only if an `Assembles σ k` instance exists; the kind alone does not license the sum. The lesson provides `Assembles` instances for mass over a pair's bodies and for stiffness over springs in parallel. It provides none for angular frequency over a pair or for stiffness over springs in series, so those sums fail to type-check.

## PKC vocabulary in scope

New at this step:
- `Composite` (`whole`, `part`) — the object type of a whole and its parts.
- `Decomposition` (`atom`, `union`) — how a whole is carved into parts.
- `Assembles` — the aggregation licence, keyed by the sort of the whole and the kind.
- `assemble` — fold a licensed quantity over a decomposition.
- `Extensive` — a kind whose value over a union is the sum over its parts.
- `DedicatedKind`, `KindOfProperty.dedicatedTo` — a kind dedicated to one sort, such as the pair's normal-mode frequency.
- `Component` — a named component of a system's characterization.
- `displacementK` — spring extension; negative compressed, positive stretched.

Carried from earlier steps: `IndividualQuantity`, `IndividualQuantity.add`, `DifferenceKind.ofScale`, `SortOfSystem`, `Sorted`, `Designated`, `massK`, `springConstantK`.

## Verifiable properties

- `assemble` of the two bodies' masses gives the pair's mass as an `IndividualQuantity` about the pair as a whole (type-checked) `HCP.L2_ThePair#pair_mass`.
- Adding the pair's mass to body A's mass fails with a type mismatch, because one is about the whole and the other about a part; adding pair P's mass to pair Q's mass fails the same way (refused) `HCP.L2_ThePair#refused_whole_part`.
- `assemble` of angular frequency over the pair's bodies fails to type-check: there is no `Assembles pairS` instance for angular frequency (refused) `HCP.L2_ThePair#refused_frequency_assembly`.
- The normal-mode frequency ω₊ is an angular-frequency kind dedicated to the sort `pairS`, and it is provably different from any angular-frequency kind dedicated to a body or a spring (type-checked) `HCP.L2_ThePair#normal_mode`.
- `assemble` of stiffness over springs in parallel type-checks; over springs in series it fails: there is no `Assembles seriesS springConstantK` instance (refused) `HCP.L2_ThePair#parallel_stiffness`, `HCP.L2_ThePair#refused_series_stiffness`.
- The parallel assembly equals the measured stiffness of the parallel combination, and the series law 1/k = 1/k₁ + 1/k₂ gives k = 2 for springs of stiffness 6 and 3 (theorem) `HCP.L2_ThePair#parallelLaw`, `HCP.L2_ThePair#licenseCashed`, `HCP.L2_ThePair#seriesLaw`.

## Errors prevented

- Summing what does not sum: the normal-mode frequency taken as the sum of the bodies' angular frequencies. `assemble` fails because no `Assembles` instance exists (`HCP.L2_ThePair#refused_frequency_assembly`).
- Wrong composition law: the stiffnesses of springs in series added as if the springs were in parallel (`HCP.L2_ThePair#refused_series_stiffness`).
- Whole/part confusion: pair P's mass added to body A's mass, a quantity about the whole combined with a quantity about one of its parts (`HCP.L2_ThePair#refused_whole_part`).

# Persona

You are a PhysLib contributor: a physicist who writes Lean in PhysLib. You know Lean and
PhysLib and trust `Dimension` and `WithDim`; L0 and L1 have established the oscillator
context and the bearer-indexed quantities.

# Pull

Once A and B are coupled, what bears the total mass and the oscillation frequency? Open the L1 black boxes into bodies A and B and springs kA, kC, and kB; kC is the new coupling spring. Each wall-spring oscillator supplies its body's mass and wall-spring stiffness, and the coupling spring makes the oscillators interact, so L1's no-interaction assumption falls. Mass is borne by the bodies and stiffness by the springs; the L1 oscillator-indexed `ω² = k/m` does not survive coupling. The normal-mode angular frequency belongs to the pair whole, which has its own sort. Following L1, one `PairId` name is one system: records under it are its states at different times, configurations, or rival estimates; comparing their shared-bearer quantities is the point. Different names denote distinct systems, so P and Q remain distinct even when their parameters match. Each spring has a signed extension, negative when compressed and positive when stretched; two configurations of pair P can compare their coupling-spring extensions with a typed displacement difference.

# Risks at this step

- *Aggregation.* In coupled pair P, the pair mass assembles from bodies A and B, but their normal-mode frequencies do not add; the mass assembly and frequency refusal are pinned at `HCP.L2_ThePair#pair_mass` and `HCP.L2_ThePair#refused_frequency_assembly`.
- *Sort versus particular.* The license to add body masses belongs to the coupled-pair sort, and parallel stiffness adds where series stiffness does not; the accepted parallel case and refused series case are pinned at `HCP.L2_ThePair#parallel_stiffness` and `HCP.L2_ThePair#refused_series_stiffness`.

*Further reading*
- `Exhibits/PointParticle`.
- `CaseStudies/PointParticle`.
- `Composite.Assembles` with `Exhibits/TwoRovers`.

# Small rigorous improvement

:::table +header
*
  * Question
  * Context change
  * Attribute change
  * Risk shown
  * PhysLib stage
*
  * Once A and B are coupled, what bears the total mass and the oscillation frequency?
  * Open the L1 black boxes into bodies A and B and springs kA, kC, kB; kC joins A and B, so they interact. The coupled pair has its own sort and a nominal PairId independent of its parameters; spring configurations also carry signed extensions.
  * Per-part mass, stiffness, and displacement; total mass of the pair; normal-mode angular frequency of the pair; effective stiffness.
  * The pair's mass adds from its bodies, but normal-mode frequency and series stiffness do not; parallel stiffness adds under its own sort-specific license.
  * Stage 3: sort-specific assembly licenses.
:::

With B clamped, A is held by its wall spring kA and the coupling spring kC in parallel.
The total mass belongs to the pair whole; angular frequency does not add across the bodies,
and a normal mode is a property of the coupled whole. The parallel stiffness is extensive
for the parallel sort, while series stiffness is whole-proper rather than additive. At L3,
each body is still assumed rigid, homogeneous, and point-like, with its mass on the spring
axis; an imbalance would make it wobble.

# Learning path

:::table +header
*
  * #
  * Do
  * Checked by `HCP.L2_ThePair` anchor
  * Concept disclosed
*
  * 1
  * Open the boxes into bodies A/B and springs kA/kC/kB, give each part a nominal pair-indexed bearer, and compare compressed/stretched kC configurations of pair P.
  * `HCP.L2_ThePair#opened_pair`
  * Mass belongs to a body, stiffness and signed extension belong to a spring; `extensionOf` has a typed same-pair difference.
*
  * 2
  * Assemble both body masses into the pair whole.
  * `HCP.L2_ThePair#pair_mass`
  * The pair-specific whole mass is the sum of its parts' masses, read from the real fields.
*
  * 3
  * Try to add the pair mass to body A's mass and to a pair with identical parameters but a different PairId.
  * `HCP.L2_ThePair#refused_whole_part`
  * Whole and part are distinct bearers; P and Q are different systems even when all parameter values and part names match.
*
  * 4
  * Try to assemble the bodies' angular frequencies into the pair.
  * `HCP.L2_ThePair#refused_frequency_assembly`
  * Angular frequency has no `Assembles` license for the pair sort.
*
  * 5
  * Give the normal mode its dedicated kind at the pair sort.
  * `HCP.L2_ThePair#normal_mode`
  * The normal mode is neither a body nor a spring property.
*
  * 6
  * With B clamped, assemble kA and kC as springs in parallel.
  * `HCP.L2_ThePair#parallel_stiffness`
  * The parallel whole has the sum of the two stiffness magnitudes.
*
  * 7
  * Try to assemble kA and kB as two springs chained end to end.
  * `HCP.L2_ThePair#refused_series_stiffness`
  * No series-sort assembly license is registered.
*
  * 8
  * Check the aggregation licenses on the exhibited pairs: parallel kA–kC and series kA–kB.
  * `HCP.L2_ThePair#parallelLaw`; `HCP.L2_ThePair#seriesLaw`; `HCP.L2_ThePair#licenseCashed`
  * Parallel stiffness adds; series kA–kB gives 6 ∥ 3 = 2. Integer measurements are exact only for the exhibited pairs and do not model longer chains.
:::

Worksheet: `HCP/Worksheets/L2_ThePair.lean` · Solution: `HCP/L2_ThePair.lean`

# Lesson

_1. Open the box and represent configurations._ Each body's upstream harmonic oscillator
supplies its wall-spring parameters; the coupling spring supplies stiffness, and each spring
has a signed extension. Two `CoupledPair .P` configurations admit a typed difference of
their kC extensions:

```anchor opened_pair
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

-- Same-name records: Constructs a displacementK IndividualQuantity about pair P's coupling spring as stretched minus compressed extension, comparing two states of one spring.
#guard_msgs in
example (compressed stretched : CoupledPair .P) :
    IndividualQuantity
      (Composite.part (σ := pairS) (springPart .P .kC))
      ForPhysLib.ClassicalMechanics.displacementK ℝ :=
  couplingSpringExtensionDifference compressed stretched

/-- Same-name records: Proves that pair P's coupling-spring displacement difference has magnitude stretched extension minus compressed extension. -/
theorem couplingSpringExtensionDifference_magnitude
    (compressed stretched : CoupledPair .P) :
    (couplingSpringExtensionDifference compressed stretched).magnitude =
      stretched.extension .kC - compressed.extension .kC := by
  simp [couplingSpringExtensionDifference, IndividualQuantity.add_magnitude,
    IndividualQuantity.neg_magnitude, extensionOf]
  change stretched.extension .kC + (-(compressed.extension .kC)) =
    stretched.extension .kC - compressed.extension .kC
  ring
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

def pairMass {π : PairId} (p : CoupledPair π) :
    IndividualQuantity
      (Composite.whole : Composite pairS (PartOf π))
      ForPhysLib.ClassicalMechanics.massK ℝ :=
  assemble (k := ForPhysLib.ClassicalMechanics.massK) pairS
    (Composite.whole : Composite pairS (PartOf π))
    (fun b : Body => Composite.part (σ := pairS) (bodyPart π b))
    bodies
    (fun b => massOf p b)

/-- Licensed composition: Proves that for pair π, the assembled whole-mass magnitude is body A's mass plus body B's mass. -/
theorem pairMass_magnitude {π : PairId} (p : CoupledPair π) :
    (pairMass p).magnitude = (p.osc .A).m + (p.osc .B).m := by
  rfl
```

_3. Refuse whole plus part, and one pair plus another._ Total mass is meaningful, but its
whole is not body A. A second pair is another system even when all parameters and part
names match, because PairId is nominal:

```anchor refused_whole_part
-- Bearer safety: Refused: type mismatch between pair P's whole-mass bearer and body A's part-mass bearer; this prevents treating a part mass as the pair's whole mass.
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

-- Bearer safety: Refused: type mismatch between pair P's and pair Q's whole-mass bearers; this prevents combining masses from distinct pairs as one system.
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
```

_4. Refuse to assemble angular frequency._ The pair's license table has no entry for it:

```anchor refused_frequency_assembly
-- Licensed composition: Refused: no Assembles pairS angularFrequency instance licenses deriving the pair's normal-mode frequency from the bodies' frequencies.
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
```

_5. Give the normal mode its whole._ A dedicated angular-frequency kind at `pairS` is
distinct from one dedicated to a body or a spring:

```anchor normal_mode
def whole : Component := ⟨"whole"⟩

def dkOmegaPlus : DedicatedKind :=
  ForPhysLib.ClassicalMechanics.Kinds.angularFrequency.dedicatedTo
    pairS ⟨"normal mode +"⟩

/-- Kind vs dimension: Proves that pair P's normal-mode kind differs from angular frequency dedicated to body A's whole; the mode belongs to the pair, not A alone. -/
theorem normal_mode_not_of_a_body :
    dkOmegaPlus ≠
      ForPhysLib.ClassicalMechanics.Kinds.angularFrequency.dedicatedFor Body.A whole :=
  DedicatedKind.distinct_of_sort (by decide)

/-- Kind vs dimension: Proves that pair P's normal-mode kind differs from angular frequency dedicated to coupling spring kC's whole. -/
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

/-- Licensed composition: Proves that pair π's parallelS whole has magnitude A.k + kC, the sum licensed for the parallel springs. -/
theorem parallelStiffness_magnitude {π : PairId} (p : CoupledPair π) :
    (parallelStiffness p).magnitude = (p.osc .A).k + p.kC := by
  rfl
```

_7. Refuse series stiffness._ For kA and kB chained end to end, no additive series license
is registered:

```anchor refused_series_stiffness
def seriesSprings : Decomposition Spring := .union (.atom .kA) (.atom .kB)

-- Licensed composition: Refused: no Assembles seriesS springConstantK instance; an additive rule would give kA + kB = 9, but the series measurement is 2.
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
```

_8. Check the licenses against measurements._ The measurements use HCP's own `Spring`.
`PropertyValue.numeral` is fixed at `Int`, so the exhibited kA–kB series chain is exact
(6 ∥ 3 = 2); these integer numerals do not model longer chains:

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

/-- Licensed composition: Proves that parallel springConstantK measurements add over parts, which is the law that licenses parallel stiffness assembly. -/
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

/-- Composition law: Proves that series springs kA = 6 and kB = 3 measure 2, not their additive sum 9; series stiffness is not parallel addition. -/
theorem series_kA_kB_exact : (seriesMeasurement seriesSprings).numeral = 2 := by decide

/-- Composition law: Proves that series measurement is WholeProper—neither additive nor uniform; kA = 6 and kB = 3 measure 2, not their sum 9. -/
theorem series_whole_proper :
    WholeProper ForPhysLib.ClassicalMechanics.springConstantK seriesMeasurement where
  ofKind := fun _ => rfl
  notAdditive := ⟨.kA, .kB, by decide⟩
  notUniform := ⟨.kA, .kA, ⟨rfl, by decide⟩⟩

/-- Composition law: Proves that series springConstantK measurement is not extensive: kA = 6 and kB = 3 measure 2 rather than the additive 9, so no sum license applies. -/
theorem series_not_extensive :
    ¬ Extensive ForPhysLib.ClassicalMechanics.springConstantK seriesMeasurement :=
  series_whole_proper.not_extensive
```

```anchor licenseCashed
/-- Licensed composition: Proves that parallel assembly of kA = 6 and kC = 2 for pair π has measured magnitude 8, as the extensive measurement requires. -/
theorem parallel_assembled_is_measured {π : PairId} (_p : CoupledPair π) :
    (assemble (k := ForPhysLib.ClassicalMechanics.springConstantK) parallelS
        (Composite.whole : Composite parallelS (PartOf π))
        (fun s => Composite.part (σ := parallelS) (springPart π s)) parallelSprings
        (fun s => ⟨(parallelMeasurement (.atom s)).numeral⟩)).magnitude
      = (parallelMeasurement parallelSprings).numeral :=
  assemble_eq_measured parallelS Composite.whole
    (fun s => Composite.part (σ := parallelS) (springPart π s))
    parallel_extensive parallelSprings

/-- Licensed composition: Proves that if seriesS springConstantK assembly is licensed, some decomposition's assembled reading differs from measurement; kA = 6 and kB = 3 give 9 versus 2. -/
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
```

The measurements verify the curation: parallel stiffness is extensive, while series
stiffness is whole-proper. `Measurement` carries an `Int` numeral, so the exhibited
kA–kB series value is exact (6 ∥ 3 = 2); these integer numerals do not model longer chains.
Registering the series sum would produce a magnitude that disagrees with its measurement.

The System-context card section of this chapter lists the bodies, all three springs,
the fixed walls, and the line of motion. The Lean model's nominal `PartOf π` index keeps
parts of differently identified pairs distinct even when their parameters match, while
body mass, spring stiffness, and the pair's normal-mode frequency stay on their respective
bearers. The on-axis, rigid, homogeneous, point-like body assumption returns at L3.

# AI assistance contract

- Use the HCP-owned `Body`, `Spring`, `PartOf`, and `CoupledPair` types; do not import or reuse the Tutorial model.
- Keep body mass, spring stiffness, and pair normal-mode frequency on their respective bearers.
- Give each spring a signed displacement-kind extension (negative when compressed, positive when stretched), and compare configurations under the same `PairId`.
- Treat the pair as a whole distinct from every body and spring part.
- State that the L1 no-interaction assumption falls here and that L3 revisits the on-axis, rigid-body assumption.
- Use sort-specific `Assembles` licenses: mass for the pair and stiffness for parallel springs, but neither angular frequency for the pair nor stiffness for springs in series.
- Treat guarded elaboration errors as evidence only for the refusals they show.

# Questions to ask the model so far

:::table +header
*
  * Question
  * Check
  * What the verdict means
*
  * Where does total mass live?
  * `pair_mass`
  * On `Composite.whole`; the two body masses assemble there.
*
  * Can compressed and stretched configurations of pair P be compared by kC extension?
  * `opened_pair`
  * Yes; the typed displacement difference has magnitude `stretched.extension .kC - compressed.extension .kC`.
*
  * Can a whole mass be added to one of its parts?
  * `refused_whole_part`
  * No; their composite object indices differ.
*
  * Can two pairs' whole masses be added when their parameters are identical?
  * `refused_whole_part`
  * No; nominal `PartOf .P` and `PartOf .Q` have distinct bearer types independent of parameter values.
*
  * Does angular frequency assemble across the pair's bodies?
  * `refused_frequency_assembly`
  * No; the pair sort has no angular-frequency license.
*
  * What sort bears the normal mode?
  * `normal_mode`
  * The dedicated kind is attached to `pairS`, not `bodyS` or `springS`.
*
  * What happens to stiffness when kA and kC act in parallel?
  * `parallel_stiffness`, `parallelLaw`
  * The effective magnitude is their sum, and the measurement is extensive.
*
  * May the same summation rule be used for springs in series?
  * `refused_series_stiffness`, `seriesLaw`, `licenseCashed`
  * No; kA–kB reads 6 ∥ 3 = 2, and a hypothetical sum license reports 9. The `Int` examples are exact only for the exhibited pairs, not longer chains.
:::

# System-context card

:::table +header
*
  * Scope
  * System or component
  * Sort / status
  * L2 assumptions and attributes
*
  * System
  * Coupled pair
  * `pairS`; composite whole
  * Bodies A and B interact through kC. The normal-mode angular frequency belongs to the pair.
*
  * Part
  * Body A
  * `Body.A`, sort `bodyS`
  * Homogeneous, rigid, point-like; mass mA lies on the spring axis.
*
  * Part
  * Body B
  * `Body.B`, sort `bodyS`
  * Homogeneous, rigid, point-like; mass mB lies on the spring axis.
*
  * Part
  * Wall spring kA
  * `Spring.kA`, sort `springS`
  * Linear spring from body A to the fixed wall; stiffness kA and signed extension (negative compressed, positive stretched).
*
  * Part
  * Coupling spring kC
  * `Spring.kC`, sort `springS`
  * Linear spring joining bodies A and B; stiffness kC and signed extension (negative compressed, positive stretched).
*
  * Part
  * Wall spring kB
  * `Spring.kB`, sort `springS`
  * Linear spring from body B to the fixed wall; stiffness kB and signed extension (negative compressed, positive stretched).
*
  * Outside
  * Walls and line
  * Fixed, infinitely massive walls; one-dimensional motion
  * The wall springs remain attached to fixed boundaries and both bodies move along the line.
:::

The Lean model keeps each body's oscillator as the source of its mass and wall-spring
stiffness; `kC` is the pair's new coupling field, and `extensionOf` indexes each signed
displacement by its spring part. One `PairId` name is one system: records under it are states
at different times, configurations, or rival estimates to compare; distinct names are
distinct systems.
`PartOf π` uses nominal identity, so identical parameter records under P and Q still yield
different pair part types. The `Measurement`
numeral is an `Int`: the series example is exact for kA–kB (6 ∥ 3 = 2), but these integer
numerals do not model longer chains. L3 revisits the assumption that each body is rigid,
homogeneous, and point-like with its mass on the spring axis: if the mass is off-axis, the
body wobbles.
