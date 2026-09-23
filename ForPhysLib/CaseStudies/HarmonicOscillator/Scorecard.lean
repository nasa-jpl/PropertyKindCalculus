/-
# The scorecard — the four attempts, head to head

Each attempt lives in **one file** and is scored there against **every** requirement, so that
it can be read end to end as one account of one idea. This module is the only place the
attempts meet: it carries the part of the comparison a build can check, so the table in
`README.md` cannot quietly drift from the files.

Verdicts that are `#check_failure`-shaped (a term that should elaborate and does not, or one
that should be rejected and is not) stay in the attempts themselves, since a rejection is
witnessed by the build succeeding with the probe in place, not by a term this module could
import. What is collected here is the propositions — plus, in Tier 4, the four authorings of
one formula, which is the one comparison that is *inherently* cross-attempt.

## What the checked facts below establish

1. **MR8 is the discriminating requirement.** All four attempts are confronted with the same
   two additions — `m_A + m_B` (meaningful) and `ω_A + ω_B` (not) — and only attempt 4
   distinguishes them. Attempts 1 and 2 accept both; attempt 3 rejects both.
2. **Attempts 2 and 3 fail for one reason, stated twice.**
   `Attempt2.withDim_discriminates_only_dimension` and `Attempt3.tagging_dilemma` are the same
   fact about free commutative groups, met from opposite directions: attempt 2 has too few
   distinctions, attempt 3 has the wrong kind.
3. **Attempt 3's tag is not a dimension.** `Attempt3.forget_collapses_the_tag` shows the
   projection that restores unit semantics is exactly the one that erases the tag.
4. **The resolution is two axes, not a better one.** `Attempt4.no_dilemma` writes down the
   conjunction — same kind, different object — that attempt 3 proved contradictory.
5. **The ergonomic cost is pure ceremony.** All four authorings of `V = m·ω²·x²` compute the
   same number, so the witnesses, casts and object parameters buy nothing at the value level
   and everything at the type level.
6. **Tier 6 needs a third axis, and it is not a finer basis.** Variance is independent of
   dimension in both directions, so no refinement of the dimension group reaches it.
-/

module

public import ForPhysLib.CaseStudies.HarmonicOscillator.Attempt1Reals
meta import ForPhysLib.CaseStudies.HarmonicOscillator.Attempt1Reals
public import ForPhysLib.CaseStudies.HarmonicOscillator.Attempt2Dimension
meta import ForPhysLib.CaseStudies.HarmonicOscillator.Attempt2Dimension
public import ForPhysLib.CaseStudies.HarmonicOscillator.Attempt3Tagged
meta import ForPhysLib.CaseStudies.HarmonicOscillator.Attempt3Tagged
public import ForPhysLib.CaseStudies.HarmonicOscillator.Attempt4Pkc
meta import ForPhysLib.CaseStudies.HarmonicOscillator.Attempt4Pkc

@[expose] public section

namespace PropertyKindCalculus.Examples.HarmonicOscillator.Scorecard

open PropertyKindCalculus

/-! ## MR8 — the discriminating requirement

The same two sums, put to all four attempts. -/

/-- **Attempt 1 · plain reals — ❌.** Both sums elaborate. The mass total is right by luck;
the frequency total is noise, and nothing tells them apart. -/
theorem attempt1_ho8 :
    Attempt1.oscA.m + Attempt1.oscB.m = 8
      ∧ Attempt1.oscA.ω 0 + Attempt1.oscB.ω 0 ≠ Attempt1.ωPlus :=
  Attempt1.mr8_the_point

/-- **Attempt 2 · `WithDim` — ❌.** Identical verdict, one layer up: `Add (WithDim d M)`
accepts both, because extensivity is not a property of a dimension. Adopting dimensions
fixes MR1–MR3 and MR10 and leaves MR8 exactly where it was. -/
theorem attempt2_ho8 :
    Attempt2.totalMass.val = 8 ∧ Attempt2.frequencySum.val ≠ 5 :=
  Attempt2.mr8_the_point

/-- **Attempt 3 · object tagging — ❌, by over-rejection.** The two masses carry different
dimensions, so `m_A + m_B` does not elaborate at all. The meaningful sum is lost along with
the meaningless one, which is what MR8's two-sidedness is for. -/
theorem attempt3_ho8 : ¬ Attempt3.Addable (Attempt3.massOf .A) (Attempt3.massOf .B) :=
  Attempt3.attempt3_chose_distinguishable

/-- **Attempt 4 · PKC — ✅.** Mass is extensive over the pair's decomposition and angular
frequency is not, so the licence exists for one sum and not the other. This is the only cell
in the MR8 row that *distinguishes* rather than uniformly accepting or uniformly rejecting. -/
theorem attempt4_ho8 :
    Extensive Attempt4.mass.kind Attempt4.massMeasurement
      ∧ ¬ Extensive Attempt4.angularFrequency.kind Attempt4.angFreqMeasurement
      ∧ (Attempt4.massMeasurement Attempt4.pairDecomposition).numeral = 8 :=
  Attempt4.mr8_capstone

/-! ## The common diagnosis for attempts 2 and 3

Two theorems, one fact: `Dimension B` is a free commutative group, so the only discrimination
`WithDim` offers is equality of dimensions. Attempt 2 lives on the "equal" side and cannot
separate anything that shares a dimension; attempt 3 moves to the "unequal" side and loses
everything that depends on sharing one. -/

/-- **Attempt 2's diagnosis.** Equal dimensions give equal quantity *types*, hence total
mutual substitutability — MR4, MR7 and MR9 are three instances of this one lemma. -/
theorem attempt2_diagnosis (M : Type) :
    WithDim Attempt2.frequency M = WithDim Attempt2.angularFrequency M :=
  Attempt2.mr4_is_the_diagnosis M

/-- **Attempt 3's diagnosis.** "Addable" and "distinguishable" are each other's negation at
this layer, so no tagging scheme — no basis, no generator count — satisfies MR7 and MR8
together. -/
theorem attempt3_diagnosis (dA dB : Dimension Attempt3.TaggedBase) :
    ¬ (Attempt3.Addable dA dB ∧ Attempt3.Distinguishable dA dB) :=
  Attempt3.tagging_dilemma dA dB

/-- **Attempt 3's tag carries no metrological content.** The projection that restores unit
semantics (`forget`) is precisely the one that identifies A's mass with B's — so the two
tagged dimensions are distinct, yet have one image, one scale factor, and one unit. A tag
that is invisible to unit conversion is not a dimension. -/
theorem attempt3_tag_is_not_a_dimension :
    Attempt3.massOf .A ≠ Attempt3.massOf .B
      ∧ Attempt3.forget (Attempt3.massOf .A) = Attempt3.forget (Attempt3.massOf .B) :=
  Attempt3.forget_collapses_the_tag

/-- **Attempt 3 cannot express the oscillator's solution.** The phase `ω_A · t`, the argument
of `cos`, is not dimensionless — so a tagged basis handles the oscillator's *parameters* and
not its *dynamics*. -/
theorem attempt3_phase_broken : Attempt3.angFreqOf .A * Attempt3.timeD ≠ 1 :=
  Attempt3.phase_not_dimensionless

/-! ## The resolution

Kind and object are independent axes, so the conjunction attempt 3 proved contradictory is
simply true. -/

/-- **Attempt 4 · the dilemma dissolved.** A's and B's masses are the *same kind* — which is
what `mass_extensive` licenses their sum by — and belong to *different objects*, which is
what makes them non-substitutable. One axis could not carry both; two can. -/
theorem attempt4_resolution :
    (Attempt4.mA.toIndividualProperty.kind = Attempt4.mB.toIndividualProperty.kind)
      ∧ (Attempt4.mA.toIndividualProperty.carrier
          ≠ Attempt4.mB.toIndividualProperty.carrier) :=
  Attempt4.no_dilemma

/-! ## Tier 2, which only attempt 4 reaches -/

/-- **MR4 · the rad/s trap.** One dimension, two kinds — the oscillator's instance of
`PropertyKindCalculus.dim_not_injective`. Attempts 1–3 all identify these. -/
theorem attempt4_ho4 :
    Attempt4.frequency.kind ≠ Attempt4.angularFrequency.kind
      ∧ Attempt4.frequency.toDimension = Attempt4.angularFrequency.toDimension :=
  Attempt4.mr4_capstone

/-- **MR5 · scale type.** One dimension, two scale types, opposite operator availability:
differences of absolute energies are licensed, ratios of them are not. -/
theorem attempt4_ho5 :
    Attempt4.absoluteEnergy.toDimension = Attempt4.energyDifference.toDimension
      ∧ ¬ Attempt4.absoluteEnergy.kind.IsRational
      ∧ Attempt4.energyDifference.kind.IsRational :=
  Attempt4.mr5_capstone

/-- **MR9 · whole-system quantities.** Three pairwise-distinct dedicated kinds over one
underlying kind — hence one dimension and one unit (rad/s). Substituting a bare frequency for
a normal-mode one is the bug this closes, and in the symmetric case it returns the right
number, so no test would have caught it. -/
theorem attempt4_ho9 :
    Attempt4.dkOmegaA ≠ Attempt4.dkOmegaB
      ∧ Attempt4.dkOmegaPlus ≠ Attempt4.dkOmegaA
      ∧ Attempt4.dkOmegaPlus ≠ Attempt4.dkOmegaB
      ∧ Attempt4.dkOmegaA.kind = Attempt4.dkOmegaB.kind
      ∧ Attempt4.dkOmegaPlus.kind = Attempt4.dkOmegaA.kind :=
  Attempt4.mr9_capstone

/-! ## Tier 4 — one formula, four authorings, one number

This is the comparison that cannot live in an attempt file, because it *is* the comparison.
Each attempt writes `V = m·ω²·x²` in its own idiom, in its own `Tier4` namespace, and the
four differ enormously in what has to be written and **not at all in what is computed**. The
theorems below prove exactly that: every attempt's definition produces the same magnitude as
attempt 1's one-liner, so the witnesses, the casts and the object parameters buy nothing at
the value level.

That is the right way to read MR11's ⚠️ for PKC. The cost is real and it is entirely at the
*type* level — which is where Tiers 2, 3, 5 and 6 are won, and where a reader of the source
pays for them.

| attempt | per-formula cost | per-model cost | operators visible |
|---|---|---|---|
| 1 · reals | none | none | yes |
| 2 · `WithDim` | **1 cast + 1 discharge per named result** | 0 | yes |
| 3 · tagged | 1 object parameter; result type unnameable | 0 | yes, type is the derivation |
| 4 · PKC, longhand | 4 witnesses | 3 kind declarations | **no** |
| 4 · PKC + table | **none** | 3 kind declarations + 4 table entries | **yes** |
-/

/-- **Attempt 2's cast buys nothing numerically.** -/
theorem mr11_withDim_same_value (m ω x : ℝ) :
    (Attempt2.Tier4.energyWithDim ⟨m⟩ ⟨ω⟩ ⟨x⟩).val = Attempt1.Tier4.energyReals m ω x := rfl

/-- **Attempt 3's object parameter buys nothing numerically.** -/
theorem mr11_tagged_same_value (o : Attempt3.Osc) (m ω x : ℝ) :
    (Attempt3.Tier4.energyTagged o ⟨m⟩ ⟨ω⟩ ⟨x⟩).val
      = Attempt1.Tier4.energyReals m ω x := rfl

/-- **Attempt 4's four witnesses and three intermediate kinds buy nothing numerically.** The
most verbose definition in the benchmark computes precisely the least verbose one. -/
theorem mr11_pkc_same_value (o : System) (m ω x : ℝ) :
    (Attempt4.Tier4.energyPkc o ⟨m⟩ ⟨ω⟩ ⟨x⟩).magnitude
      = Attempt1.Tier4.energyReals m ω x := rfl

/-- **And the ceremony is avoidable.** With `OperatorTable`'s curated instances extended to
the object-indexed layer, the PKC formula is written `m * (ω * ω) * (x * x)` —
character-identical to attempt 1's — and is the **same term** as the longhand version, so
nothing was weakened. This is what turns attempt 4's MR11 from ❌ to ⚠️: the per-formula cost
goes to zero and what remains is a one-time, per-model registration. -/
theorem mr11_operators_same_term (o : System)
    (m : IndividualQuantity o Attempt4.mass.kind ℝ)
    (ω : IndividualQuantity o Attempt4.angularFrequency.kind ℝ)
    (x : IndividualQuantity o Attempt4.Tier4.lengthK ℝ) :
    Attempt4.Tier4.energyPkcOperators o m ω x = Attempt4.Tier4.energyPkc o m ω x :=
  Attempt4.Tier4.energyPkcOperators_eq o m ω x

/-! ## Tier 5 — the carrier axis

MR12's evidence is `#guard_msgs`-pinned inside `Attempt4Pkc.lean` (a rendered string is not a
proposition this module could import), so what is collected here is Tier 5. -/

/-! **MR13 · carrier parametricity.** One `stiffness` definition, instantiated at `Float`,
*runs*: `m = 5`, `ω = 2` gives `k = 20`. Attempts 1–3 have no executable carrier at all —
attempt 1 has a *second copy* of the model, which is the failure rather than a workaround. -/
#guard (Attempt4.Tier5.stiffnessFloat ⟨5⟩ ⟨2⟩).magnitude == 20.0

/-- **MR13 · the law is proved once.** Additivity over an arbitrary `LawfulCarrier`, hence at
`ℝ` with no `ℝ`-specific proof. -/
theorem mr13_law_transfers (h : DifferenceKind Attempt4.Tier5.dl)
    (x y : Quantity Attempt4.Tier5.dl ℝ) :
    Quantity.add h x y = Quantity.add h y x :=
  Attempt4.Tier5.add_comm_real h x y

/-! **MR14 · complex-valued quantities.** The driven oscillator's mechanical impedance
`Z = 3 + 4i` as *one* kind at one dimension, squared through the ordinary kind-gated
`Quantity.mul`: `Z² = −7 + 24i`, computed. Attempts 2 and 3 can hold this value and cannot
square it. -/
#guard Attempt4.Tier5.ZSq.magnitude.re == -7.0
#guard Attempt4.Tier5.ZSq.magnitude.im == 24.0

/-- **MR14 · the component roles are a kind-layer fact.** Resistance and reactance — the
in-phase and quadrature components of one complex quantity — are distinct dedicated kinds at
one dimension and one unit. MR9's capstone, met again inside a single value. -/
theorem mr14_components_distinct :
    Attempt4.Tier5.resistance ≠ Attempt4.Tier5.reactance :=
  Attempt4.Tier5.resistance_ne_reactance

/-! ## Tier 6 — the geometric axis

The tier asks what happens when the same physics is written in a different coordinate system,
and it separates the attempts on a datum none of Tiers 1–5 needed: the **variance** of a
quantity — whether its components are invariant, turn with the frame, or turn on two indices.

The three theorems below are the three attempts' verdicts on one experiment. The rotation is
the same in all three (`cos θ = 3/5`, `sin θ = 4/5`), and it is applied to three quantities
that must be treated differently: a velocity, a pair of masses, and a frequency family. -/

/-- **Attempt 1 · ❌.** One type, `Fin 2 → ℝ`, and one rotation applicable to all three. The
contraction is correctly invariant; the masses and the frequencies are destroyed; nothing in
the attempt can express the difference. -/
theorem attempt1_ho19 :
    Attempt1.Tier6.dot (Attempt1.Tier6.turn Attempt1.Tier6.vA)
        (Attempt1.Tier6.turn Attempt1.Tier6.vA)
      = Attempt1.Tier6.dot Attempt1.Tier6.vA Attempt1.Tier6.vA
      ∧ Attempt1.Tier6.turn Attempt1.Tier6.masses 0 ≠ Attempt1.Tier6.masses 0
      ∧ Attempt1.Tier6.turn Attempt1.Tier6.omegas 0 ≠ Attempt1.Tier6.omegas 0 :=
  Attempt1.Tier6.mr19_capstone

/-- **Attempt 2 · ❌.** The dimension is carried through the rotation perfectly, which is the
point: the dimension was never the thing at risk. A rotation is dimension-blind, so a
dimension-generic `turnQ` applies to masses and frequency families alike. -/
theorem attempt2_ho19 :
    (Attempt2.Tier6.turnQ Attempt2.Tier6.masses).val 0 ≠ Attempt2.Tier6.masses.val 0
      ∧ (Attempt2.Tier6.turnQ Attempt2.Tier6.omegas).val 0 ≠ Attempt2.Tier6.omegas.val 0
      ∧ WithDim (Dim.length * Dim.time⁻¹) (Fin 2 → ℝ)
          = WithDim (Dim.length * Dim.time⁻¹) (Fin 2 → ℝ) :=
  Attempt2.Tier6.mr19_capstone

/-- **Attempt 3 · ❌, and instructively so.** The obvious response to Tier 6 is to add a
generator per frame, exactly as attempt 3 added one per oscillator. It fails twice: the three
quantities that must transform differently all belong to A and so share a tag exponent, and
the coupled pair's normal-mode coordinate carries both tags and is therefore neither
oscillator's. `tagging_dilemma` was never about objects — it is about free commutative
groups, and a frame is not an element of one. -/
theorem attempt3_ho19 :
    (Attempt3.massOf .A).exponent (.tag .A)
        = (Attempt3.angFreqOf .A).exponent (.tag .A)
      ∧ Attempt3.Tier6.normalModeDim ≠ Attempt3.lengthOf .A
      ∧ ¬ (Attempt3.Addable (Attempt3.massOf .A) (Attempt3.massOf .B)
            ∧ Attempt3.Distinguishable (Attempt3.massOf .A) (Attempt3.massOf .B)) :=
  Attempt3.Tier6.mr19_capstone

/-- **Attempt 4 · ✅ — MR18.** The scalar product is invariant under the change of frame and a
component is not, and both facts are about *one* quantity. This is what "a change of
representation does not change the physical equations" amounts to when it is discharged rather
than assumed: everything a mechanical model asserts is built from contractions, and
contractions do not move. -/
theorem attempt4_ho18 :
    (InFrame.normSq Attempt4.Tier6.vv Attempt4.Tier6.vRot).components
        = (InFrame.normSq Attempt4.Tier6.vv Attempt4.Tier6.vLab).components
      ∧ (Attempt4.Tier6.vRot.component 0).components
          ≠ (Attempt4.Tier6.vLab.component 0).components :=
  Attempt4.Tier6.mr18_capstone

/-- **Attempt 4 · ✅ — MR19.** And the frequency family is *not* a vector: turn the frame and
the anisotropic oscillator's stiffness matrix acquires an off-diagonal entry, so there is no
list of two frequencies in the rotated frame at all. The datum that separates it from a
velocity is the variance, which is exactly what attempts 1–3 have no place for. -/
theorem attempt4_ho19 :
    (InFrame.normSq Attempt4.Tier6.vv Attempt4.Tier6.vRot).components
        = (InFrame.normSq Attempt4.Tier6.vv Attempt4.Tier6.vLab).components
      ∧ (InFrame.toFrameRank2 Attempt4.Tier6.turn
          Attempt4.Tier6.stiffnessMatrix).components 0 1 ≠ 0 :=
  Attempt4.Tier6.mr19_capstone

/-- **Tier 6's diagnosis, and why it is a third axis rather than a finer basis.** Variance is
independent of dimension in both directions at once: a velocity and a frequency family have
*different* dimensions and are handed the *same* transformation by anything that dispatches on
the dimension, while a velocity and the same velocity read in another frame have the *same*
dimension and must not be interchanged. Both halves are attempt 2's
`withDim_discriminates_only_dimension`, on the axis Tier 6 introduces — so no refinement of
the dimension group reaches it, which is the same conclusion Tiers 2 and 3 reached about kind
and object, arrived at from the geometry. -/
theorem tier6_diagnosis :
    (Attempt2.Tier6.turnQ Attempt2.Tier6.omegas).val 0 ≠ Attempt2.Tier6.omegas.val 0
      ∧ WithDim (Dim.length * Dim.time⁻¹) (Fin 2 → ℝ)
          = WithDim (Dim.length * Dim.time⁻¹) (Fin 2 → ℝ) :=
  ⟨Attempt2.Tier6.rotating_frequencies_is_nonsense, rfl⟩

/-! ## The benchmark in one statement

Two quantities of the coupled pair — its total mass and its angular frequency — behave
identically at every layer below the kind: same syntax, same dimension arithmetic, same unit
covariance, same types. They differ in exactly one respect, extensivity, and that respect is
a property of the **kind**. A layer that cannot name kinds cannot see the difference, and the
harmonic oscillator is where that stops being an abstract observation. -/

/-- **The whole benchmark.** Attempt 2 accepts both sums, attempt 3 rejects both, attempt 4
distinguishes them — and attempt 4's dimension facts are attempt 2's, unchanged, because the
kind layer sits *above* the dimension layer rather than replacing it. -/
theorem the_benchmark :
    -- attempt 2 accepts the meaningless sum
    (Attempt2.frequencySum.val ≠ 5)
      -- attempt 3 rejects the meaningful one
      ∧ (¬ Attempt3.Addable (Attempt3.massOf .A) (Attempt3.massOf .B))
      -- attempt 4 licenses one and refuses the other
      ∧ Extensive Attempt4.mass.kind Attempt4.massMeasurement
      ∧ ¬ Extensive Attempt4.angularFrequency.kind Attempt4.angFreqMeasurement
      -- and keeps attempt 2's dimensional content verbatim
      ∧ Attempt4.action.toDimension
          / (Attempt4.mass.toDimension * Attempt4.angularFrequency.toDimension)
          = Attempt4.characteristicArea.toDimension :=
  ⟨Attempt2.frequencySum_is_not_a_normal_mode,
   Attempt3.attempt3_chose_distinguishable,
   Attempt4.mass_extensive,
   Attempt4.angFreq_not_extensive,
   Attempt4.xiSq_dimension⟩

/-! ## MR32 — appended: one family, three failures — and, since the lift landed, a sweep

Attempts 1–2 collapse the family into one type: the sum for free, the confusion for free.
Attempt 3 distinguishes it and loses the sum — its `tagging_dilemma`, transposed from
objects to specializations. Attempt 4, at first scoring, proved the lattice and stopped at
the sum — the absence that minted `PropertyKindCalculus.SpecializationLift`. With the lift
landed, attempt 4 holds both halves at once, and the two rejections that remain are
different *kinds* of failure, still worth recording: -/

/-- Attempt 3's obstruction is *structural* — the distinguishing tag provably carries no
physical content, yet cannot be removed without destroying what it bought. -/
theorem mr32_attempt3_structural :
    Attempt3.kineticDim .A ≠ Attempt3.potentialDim .A ∧
      Attempt3.forget (Attempt3.kineticDim .A) = Attempt3.forget (Attempt3.potentialDim .A) :=
  Attempt3.mr32_over_rejection

/-- Attempt 4's first-scoring obstruction was *absence* — and absence is repairable:
`Quantity.widen` and the `KindJoin` table now consume the lattice `mr32_comparable`
proves, so the kinds are distinct, mutually comparable, **and** the Hamiltonian is
writable at the join, erasing to the bare-real sum. The one cell of the appended row that
moved, and the benchmark working as intended: the ⚠️ named machinery, the machinery
landed, the probe flipped. -/
theorem mr32_attempt4_swept :
    Attempt4.kineticEnergy ≠ Attempt4.potentialEnergy
      ∧ MutuallyComparable Attempt4.EnergyEdge Attempt4.kineticEnergy Attempt4.potentialEnergy
      ∧ ∀ (T : Quantity Attempt4.kineticEnergy Float) (V : Quantity Attempt4.potentialEnergy Float),
          (Attempt4.hamiltonian T V).magnitude = T.magnitude + V.magnitude :=
  Attempt4.mr32_capstone

end PropertyKindCalculus.Examples.HarmonicOscillator.Scorecard

