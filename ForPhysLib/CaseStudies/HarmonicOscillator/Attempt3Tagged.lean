/-
# Attempt 3 — Buckingham-π object tagging

The third attempt is the one a dimensional analyst reaches for when attempt 2 fails MR7, and
it is a genuinely clever idea with a long pedigree: if `m_A` and `m_B` are indistinguishable
because they have the same dimension, then **give them different dimensions**. Extend the
base with one generator per oscillator and tag every quantity with the object it belongs to.
Variants of this trick — orientational analysis, per-object units, "directional" dimensions —
recur throughout the applied literature precisely because they do buy something real.

PhysLib supports this cleanly, and *because of this project's own contribution*: `Dimension B`
is parametric in its basis (issue #1441 → PR #1447), so a tagged basis is a first-class
citizen with the full dimensional algebra, not a hack. This attempt therefore gets the best
possible version of its own idea, on a substrate purpose-built to host it.

It **wins MR7** — the requirement attempt 2 could not touch — and it is important to say so
plainly. It then fails, in four separate ways that are all the same way:

  1. **MR8, by over-rejection.** `m_A + m_B` — the pair's total mass, a perfectly meaningful
     quantity — becomes inexpressible. MR8 is two-sided for exactly this reason.
  2. **MR2, by residue.** `ω_A / ω_B` is a pure number in physics, and here it carries a
     leftover tag. Worse, the *phase* `ω_A · t` — the argument of a cosine — is not
     dimensionless, so it cannot be fed to a transcendental function at all.
  3. **The decisive one: the Hamiltonian does not type-check.** A tag exponent counts *how
     many tagged factors* a quantity was built from, and physics reaches one quantity by
     routes with different multiplicities. Kinetic energy `m·v²` carries `⟨o⟩³`, potential
     energy `m·ω²·x²` carries `⟨o⟩⁵`, both are `M·L²·T⁻²`, both belong to the *same*
     oscillator — and they are not addable, so `H = T + V` cannot be written down
     (`kinetic_ne_potential`).
  4. **MR3, by loss.** `dimScale` is defined only over `LTMCTDimensionBase`, so a tagged
     basis has no unit semantics. It can be recovered — by a projection that forgets the tags,
     i.e. by exactly undoing the thing the basis was built to do.

The common cause is stated as `tagging_dilemma` at the end: `Dimension B` is a free
commutative group, so a tag is a *group element*, and a group element that distinguishes A
from B necessarily forbids their sum and fails to cancel in their ratio. Object identity is
not multiplicative.

Scored against `README.md`:
- MR1 ✅
- MR2 ⚠️
- MR3 ❌
- MR4 ❌
- MR5 ❌
- MR6 ⚠️
- MR7 ✅
- MR8 ❌
- MR9 ❌
- MR10 ✅
- MR11 ❌
- MR12 ❌
- MR13 ❌
- MR14 ❌
- MR15 ❌
- MR16 ❌
- MR17 ⚠️
- MR18 ❌
- MR19 ❌
- MR32 ❌ (appended)

The tag threads through every signature, the result types become derivations rather than names,
and the `ℝ`-only algebra is inherited from attempt 2 unchanged.
Tier 6 adds one finding specific to *this* idea: the tag is the wrong shape for a frame twice over,
since it neither varies with the choice of axes nor survives one.
-/

module

public import PropertyKindCalculus.Dimension
public import Physlib.Units.WithDim.Basic
public import Mathlib.Basic.Complex.Basic

public section -- pkc-blanket
@[expose] section -- pkc-blanket-expose

namespace PropertyKindCalculus.Examples.HarmonicOscillator.Attempt3

open PropertyKindCalculus Dimension

/-! ## The tagged basis

`LTMCTDimensionBase` plus one generator per oscillator. This is the parametric-basis API
doing precisely what it was upstreamed for. -/

/-- The two oscillators of the coupled pair. -/
inductive Osc
  /-- Oscillator A. -/
  | A
  /-- Oscillator B. -/
  | B
deriving DecidableEq, Repr

/-- PhysLib's five physical generators, extended with one *object tag* per oscillator. -/
inductive TaggedBase
  /-- A physical base dimension (length, time, mass, charge, temperature). -/
  | base (b : LTMCTDimensionBase)
  /-- An object tag, one per oscillator — the Buckingham-π move. -/
  | tag (o : Osc)
deriving DecidableEq

instance : DimensionBasis TaggedBase := DimensionBasis.pi _

/-- The physical generators embed injectively into the tagged basis. -/
theorem base_injective : Function.Injective TaggedBase.base := by
  intro a b h; cases h; rfl

/-- Lift a physical dimension into the tagged basis, faithfully (the embedding is injective,
so every exponent is preserved). -/
def phys (d : Dimension LTMCTDimensionBase) : Dimension TaggedBase :=
  Dimension.extend TaggedBase.base d

/-- The tag generator of an oscillator. -/
def tagD (o : Osc) : Dimension TaggedBase := Dimension.single (.tag o)

/-! ### The exponent facts everything below rests on -/

@[simp] theorem phys_exponent_base (d : Dimension LTMCTDimensionBase) (b : LTMCTDimensionBase) :
    (phys d).exponent (.base b) = d.exponent b :=
  Dimension.extend_exponent_apply base_injective d b

@[simp] theorem phys_exponent_tag (d : Dimension LTMCTDimensionBase) (o : Osc) :
    (phys d).exponent (.tag o) = 0 := by
  simp [phys, Dimension.extend]

@[simp] theorem tagD_exponent_tag (o o' : Osc) :
    (tagD o).exponent (.tag o') = if o' = o then 1 else 0 := by
  simp [tagD]

@[simp] theorem tagD_exponent_base (o : Osc) (b : LTMCTDimensionBase) :
    (tagD o).exponent (.base b) = 0 := by
  simp [tagD]

/-! ## The tagged quantities

Time is deliberately **not** tagged: it is a shared global coordinate, the same `t` for both
oscillators. That is the honest modelling choice, and it is what makes the phase problem
below bite. Tagging time instead only moves the failure. -/

/-- Oscillator `o`'s mass: `M · ⟨o⟩`. -/
def massOf (o : Osc) : Dimension TaggedBase := phys Dim.mass * tagD o
/-- Oscillator `o`'s angular frequency: `T⁻¹ · ⟨o⟩`. -/
def angFreqOf (o : Osc) : Dimension TaggedBase := phys Dim.time⁻¹ * tagD o
/-- Oscillator `o`'s displacement: `L · ⟨o⟩`. -/
def lengthOf (o : Osc) : Dimension TaggedBase := phys Dim.length * tagD o
/-- Time — untagged, shared by both oscillators. -/
def timeD : Dimension TaggedBase := phys Dim.time

/-! ## MR7 ✅ — object identity, won

This is the requirement attempt 2 could not touch, and attempt 3 takes it outright. A's mass
and B's mass have different dimensions, hence different types, so the mixed Hamiltonian is
rejected at elaboration rather than caught in review. Credit where it is due. -/

/-- A's mass and B's mass have **different dimensions** — the tag does not cancel against
`M`. -/
theorem massOf_ne : massOf .A ≠ massOf .B := by
  intro h
  have := congrArg (fun d => Dimension.exponent d (.tag .A)) h
  simp [massOf] at this

/-- A's and B's angular frequencies, likewise. -/
theorem angFreqOf_ne : angFreqOf .A ≠ angFreqOf .B := by
  intro h
  have := congrArg (fun d => Dimension.exponent d (.tag .A)) h
  simp [angFreqOf] at this

/-- The potential coefficient `½ m ω²`, now *parametric in the oscillator*: both arguments
must belong to the same object `o`, and the type says so. -/
noncomputable def potentialCoeff (o : Osc) (m : WithDim (massOf o) ℝ)
    (ω : WithDim (angFreqOf o) ℝ) : WithDim (massOf o * angFreqOf o * angFreqOf o) ℝ :=
  m * ω * ω

/-! **MR7 holds.** The mixed Hamiltonian — A's mass with B's angular frequency — is a type
error. Attempt 2 accepted this silently. -/
#check_failure (fun (mA : WithDim (massOf .A) ℝ) (ωB : WithDim (angFreqOf .B) ℝ) =>
  potentialCoeff .A mA ωB)

/-! **MR7 holds, symmetrically.** B's mass cannot stand in for A's. -/
#check_failure (fun (mB : WithDim (massOf .B) ℝ) => (mB : WithDim (massOf .A) ℝ))

/-! ## MR1 ✅, MR10 ✅ — inherited from attempt 2

The tagged basis is still a `Dimension`, so homogeneity and cross-boundary provenance are
unaffected: they were properties of `WithDim`, not of the choice of basis. -/

/-! **MR1 holds.** A mass plus a length, still rejected. -/
#check_failure (fun (m : WithDim (massOf .A) ℝ) (l : WithDim (lengthOf .A) ℝ) => m + l)

/-! ## MR8 ❌ — over-rejection: the total mass becomes inexpressible

Here is the price. `m_A + m_B` is the pair's total mass. It is meaningful, it is what
extensivity licenses, and attempt 1 and attempt 2 both compute it correctly (`3 + 5 = 8`).
Attempt 3 cannot express it at all, because `Add (WithDim d M)` is homogeneous in `d` and the
two masses no longer share a `d`.

MR8 is two-sided precisely to catch this: a scheme that rejects everything has not solved the
problem, it has relocated it. Attempt 2 accepted the meaningless frequency sum; attempt 3
rejects the meaningful mass sum. Neither *distinguishes* the two cases, which is what MR8
actually asks for. -/

/-! **MR8 fails, by over-rejection.** The pair's total mass — `3 + 5 = 8`, a quantity every
textbook computes — does not elaborate. -/
#check_failure (fun (mA : WithDim (massOf .A) ℝ) (mB : WithDim (massOf .B) ℝ) => mA + mB)

/-! And the tagging cannot be repaired by adding a third generator for the pair, because the
sum still has nothing to be formed *from*: `Add` is homogeneous, so a result at any target
dimension requires the two summands to already sit at that same dimension — which is to say
untagged again. Landing the sum at the plain physical `M` fails for the same reason. -/
#check_failure (fun (mA : WithDim (massOf .A) ℝ) (mB : WithDim (massOf .B) ℝ) =>
  (mA + mB : WithDim (phys Dim.mass) ℝ))

/-! ## MR2 ⚠️ — dimensionless numbers acquire a residue

A tag that distinguishes A from B necessarily fails to cancel between A and B. Two
consequences, both fatal to ordinary oscillator physics.

**The frequency ratio.** `ω_A / ω_B` is a pure number — it is *the* parameter of a coupled
two-oscillator system, the detuning. Here it comes out carrying `⟨A⟩/⟨B⟩`.

**The phase.** `ω_A · t` is the argument of a cosine. A transcendental function requires a
dimensionless argument; the tagged phase is not dimensionless, so `cos(ω_A t)` is not
expressible. This is the failure mode that makes tagged bases unusable for dynamics rather
than merely awkward. -/

/-- Tags do cancel against **themselves** — the scheme is not incoherent, just wrong. -/
theorem self_ratio_dimensionless (o : Osc) : angFreqOf o / angFreqOf o = 1 := div_self' _

/-- **MR2 fails (residue).** The frequency ratio of the two oscillators — the detuning, a
pure number — is not dimension one. -/
theorem detuning_not_dimensionless : angFreqOf .A / angFreqOf .B ≠ 1 :=
  fun h => angFreqOf_ne (div_eq_one.mp h)

/-- **MR2 fails (phase).** The argument of `cos(ω_A t)` is not dimensionless: it retains the
tag `⟨A⟩`. A tagged basis therefore cannot express the oscillator's *solution*, only its
parameters. -/
theorem phase_not_dimensionless : angFreqOf .A * timeD ≠ 1 := by
  intro h
  have := congrArg (fun d => Dimension.exponent d (.tag .A)) h
  simp [angFreqOf, timeD] at this

/-! **The phase failure, at the type level.** There is no way to obtain the dimensionless
number a transcendental function needs. -/
#check_failure (fun (ω : WithDim (angFreqOf .A) ℝ) (t : WithDim timeD ℝ) =>
  ((ω * t : WithDim (angFreqOf .A * timeD) ℝ) : WithDim (1 : Dimension TaggedBase) ℝ))

/-! ### The decisive case — the Hamiltonian does not type-check

The residue above is not merely inconvenient; it makes the oscillator's *own* energy
ill-formed. A tag exponent counts **how many tagged factors went into a quantity**, and two
physically equal quantities can be built from different numbers of them:

  * kinetic energy `T = m·v²` with `v = x/t` — the time is untagged, so `v` carries `⟨o⟩¹` and
    `T` carries `⟨o⟩¹⁺²  = ⟨o⟩³`;
  * potential energy `V = m·ω²·x²` — three tagged factors squared twice, so `V` carries
    `⟨o⟩¹⁺²⁺² = ⟨o⟩⁵`.

Both are `M·L²·T⁻²`. Both belong to the *same* oscillator. They are not addable, so
`H = T + V` — the object of the entire exercise — cannot be written down.

This is general, not an artefact of this encoding: any scheme that makes object identity a
*group element* makes it count multiplicities, and physics routinely reaches one quantity by
routes with different multiplicities. -/

/-- Oscillator `o`'s velocity, `L·T⁻¹·⟨o⟩` — the displacement over the *shared* time. -/
def velocityOf (o : Osc) : Dimension TaggedBase := lengthOf o / timeD

/-- Kinetic energy `m·v²` of oscillator `o`. -/
def kineticDim (o : Osc) : Dimension TaggedBase := massOf o * (velocityOf o * velocityOf o)

/-- Potential energy `m·ω²·x²` of oscillator `o`. -/
def potentialDim (o : Osc) : Dimension TaggedBase :=
  massOf o * (angFreqOf o * angFreqOf o) * (lengthOf o * lengthOf o)

/-- The **tag exponent** — how many tagged factors a quantity was built from. -/
def tagExp (d : Dimension TaggedBase) (o : Osc) : Dimension.Exponent := d.exponent (.tag o)

theorem tagExp_kinetic : tagExp (kineticDim .A) .A = 3 := by
  simp [tagExp, kineticDim, velocityOf, massOf, lengthOf, timeD]
  norm_num

theorem tagExp_potential : tagExp (potentialDim .A) .A = 5 := by
  simp [tagExp, potentialDim, massOf, angFreqOf, lengthOf]
  norm_num

/-- **The decisive failure.** Kinetic and potential energy *of the same oscillator* have
different tagged dimensions — `⟨A⟩³` against `⟨A⟩⁵` — because they are reached through
different numbers of tagged factors. -/
theorem kinetic_ne_potential : kineticDim .A ≠ potentialDim .A := by
  intro h
  have h35 : (3 : Dimension.Exponent) = 5 := by
    rw [← tagExp_kinetic, ← tagExp_potential, tagExp, tagExp, h]
  norm_num at h35

/-! That both *are* the physical energy `M·L²·T⁻²` — so the obstruction lives entirely in the
tag — is `kinetic_forget_eq_potential_forget` below, once the tag-forgetting projection has
been defined.

**The Hamiltonian is unwritable.** `T + V` for one oscillator has no `Add` instance. A
tagged basis cannot state the very equation the harmonic oscillator is defined by. -/
#check_failure (fun (T : WithDim (kineticDim .A) ℝ) (V : WithDim (potentialDim .A) ℝ) => T + V)

/-! ## MR3 ❌ — unit semantics is lost, and recovering it undoes the tagging

`LTMCTUnitChoices.dimScale` has type
`LTMCTUnitChoices → LTMCTUnitChoices → Dimension LTMCTDimensionBase →* ℝ≥0`. It is defined
over the five physical generators, and a tagged dimension is not one. Nor is this an
implementation gap that a future PR could close: a "unit for oscillator A's mass" distinct
from the unit for B's would mean the kilogram means something different for A, which is
exactly backwards.

Attempt 3's best defence is to project the tags away and take the unit semantics from the
image. That works — and the theorem below shows what it costs. -/

/-! **MR3 fails.** A tagged dimension has no scale factor: `dimScale` does not accept it. -/
#check_failure (fun (u₁ u₂ : LTMCTUnitChoices) => u₁.dimScale u₂ (massOf .A))

/-! **MR3 fails.** Nor does `WithDim` over a tagged basis carry `HasDim`, so `scaleUnit` — the
whole `UnitDependent` covariance story of attempt 2 — is unavailable. -/
#check_failure (fun (u₁ u₂ : LTMCTUnitChoices) (m : WithDim (massOf .A) ℝ) =>
  UnitDependent.scaleUnit u₁ u₂ m)

/-- **The defence: forget the tags.** Project a tagged dimension onto the physical basis by
keeping only the physical exponents. This is a monoid homomorphism, so it *does* restore
`dimScale`. -/
def forget (d : Dimension TaggedBase) : Dimension LTMCTDimensionBase :=
  Dimension.ofFunction fun b => d.exponent (.base b)

@[simp] theorem forget_exponent (d : Dimension TaggedBase) (b : LTMCTDimensionBase) :
    (forget d).exponent b = d.exponent (.base b) := by
  simp [forget]

theorem forget_mul (d₁ d₂ : Dimension TaggedBase) :
    forget (d₁ * d₂) = forget d₁ * forget d₂ := by
  ext b; simp

theorem forget_phys (d : Dimension LTMCTDimensionBase) : forget (phys d) = d := by
  ext b; simp

theorem forget_tagD (o : Osc) : forget (tagD o) = 1 := by
  ext b; simp

/-- The projection restores the expected physical dimension: a tagged mass forgets to `M`. -/
theorem forget_massOf (o : Osc) : forget (massOf o) = Dim.mass := by
  rw [massOf, forget_mul, forget_phys, forget_tagD, mul_one]

/-- **The Hamiltonian obstruction is purely the tag.** Kinetic and potential energy of one
oscillator are `⟨A⟩³` and `⟨A⟩⁵` apart (`kinetic_ne_potential`) and yet have the *same* image
under the tag-forgetting projection — both are `M·L²·T⁻²`, as physics says. So the thing that
made `T + V` unwritable carries no physical content whatsoever. -/
theorem kinetic_forget_eq_potential_forget :
    forget (kineticDim .A) = forget (potentialDim .A) := by
  ext b
  simp [kineticDim, potentialDim, velocityOf, massOf, angFreqOf, lengthOf, timeD]
  ring

/-- **The cost of the defence, as a theorem.** The projection that restores unit semantics
is *exactly* the one that destroys the object distinction: `m_A` and `m_B` are distinct
tagged dimensions (`massOf_ne`) with the *same* image under `forget`. So the unit-conversion
factor for A's mass and for B's mass are equal — as of course they must be, since both are
kilograms — and the tag was never a metrological distinction in the first place. -/
theorem forget_collapses_the_tag :
    massOf .A ≠ massOf .B ∧ forget (massOf .A) = forget (massOf .B) :=
  ⟨massOf_ne, by rw [forget_massOf, forget_massOf]⟩

/-- Read the other way round: **whatever the tag is, it is not a dimension.** It contributes
nothing to how the quantity responds to a change of units, which is the definition of a
dimension (`Physlib.Units.Basic`: "a dimension is a property of a quantity related to how it
changes with respect to a change in the unit"). Attempt 3 encodes object identity in a
structure whose entire semantics it is invisible to. -/
theorem tag_has_no_unit_content (o : Osc) (u₁ u₂ : LTMCTUnitChoices) :
    u₁.dimScale u₂ (forget (tagD o)) = 1 := by
  rw [forget_tagD]; exact map_one _

/-! ## MR4 ❌, MR5 ❌, MR6 ⚠️, MR9 ❌ — inherited, unimproved

Tagging addresses *object* identity. It does nothing about kinds that share a dimension
within one object, which is what Tier 2 asks about. -/

/-- **MR4 fails.** Frequency and angular frequency for the *same* oscillator carry the same
tag and the same physical dimension, so they are the same type — attempt 2's rad/s trap,
untouched. -/
theorem freq_trap_survives_tagging (o : Osc) :
    (phys Dim.time⁻¹ * tagD o) = angFreqOf o := rfl

/-- **MR6 fails.** Nothing distinguishes the degrees of freedom *within* one oscillator; a
second level of tagging would be needed, and would multiply every failure above. -/
example (o : Osc) (ω : Fin 2 → WithDim (angFreqOf o) ℝ) :
    WithDim (angFreqOf o * angFreqOf o) ℝ := ω 0 * ω 1

/-- **MR9 fails.** The pair's normal-mode frequency has to be tagged with *something*. Tag it
`A` and it is interchangeable with `ω_A` — the exact bug MR9 names. Tag it with a third
generator `pair` and it becomes unrelatable to `ω_A` and `ω_B` by any operation, so the
normal-mode formula `ω₊ = √((k + 2k_c)/m)` cannot be written down. -/
example : WithDim (angFreqOf .A) ℝ := ⟨5⟩

/-! ## The diagnosis — `tagging_dilemma`

Every failure above is one fact. `Dimension B` is a **free commutative group**, so a tag is a
group element; and within `WithDim`, a group element that distinguishes two quantities is
*by definition* one that forbids their sum.

The two capabilities MR7 and MR8 ask for are, at this layer, literally each other's negation:

  * "A's and B's masses can be added" is realized by `dA = dB`, because `Add (WithDim d M)`
    is homogeneous in `d` — witnessed by the `#check_failure` under MR8 and the
    same-dimension `example` under MR1;
  * "A's and B's masses are distinguishable" is realized by `dA ≠ dB`, because `WithDim`
    offers no discrimination beyond the dimension (attempt 2's
    `withDim_discriminates_only_dimension`) — witnessed by the `#check_failure` probes under
    MR7.

So the theorem is trivial, and its triviality *is* the content: there is no third thing to
vary. Any tagging scheme picks one of MR7 and MR8 and loses the other. -/

/-- "A's and B's masses can be added": the `Add` instance is homogeneous, so this is equality
of dimensions. -/
def Addable (dA dB : Dimension TaggedBase) : Prop := dA = dB

/-- "A's and B's masses are distinguishable": `WithDim` discriminates only by dimension, so
this is *dis*equality of dimensions. -/
def Distinguishable (dA dB : Dimension TaggedBase) : Prop := dA ≠ dB

/-- **The tagging dilemma.** No assignment of dimensions to the two masses is both addable
and distinguishing. MR7 and MR8 cannot both be satisfied by any choice of basis, tagging
scheme, or generator count — the obstruction is the group structure itself, not this
particular encoding.

To satisfy both, a layer must be able to say "these are the same *kind* (so they add) and
different *individuals* (so they do not substitute)". That is two independent axes. A
dimension is one axis. -/
theorem tagging_dilemma (dA dB : Dimension TaggedBase) :
    ¬ (Addable dA dB ∧ Distinguishable dA dB) :=
  fun ⟨hEq, hNe⟩ => hNe hEq

/-- Instantiated at the actual masses: attempt 3 chose `Distinguishable`, and `tagging_dilemma`
is why the total mass went with it. -/
theorem attempt3_chose_distinguishable : ¬ Addable (massOf .A) (massOf .B) := massOf_ne

/-! # Tier 4 — ergonomics (MR11 ❌, MR12 ❌)

Everything attempt 2 costs, plus the object parameter threaded through every argument, plus a
result type that **cannot be named at all**. -/

namespace Tier4

/-- **MR11 fails.** The potential energy `V = m·ω²·x²`, tagged. One extra parameter; zero
casts, *because none is possible*; and a return type that is the derivation rather than a
name. There is no `Dim.energy`-shaped target to cast to, because the tagged energy carries
`⟨o⟩⁵` and no physical name has a tag exponent.

And recall `kinetic_ne_potential`: this energy cannot be added to the *kinetic* energy of the
same oscillator, so the definition below cannot participate in a Hamiltonian at all. It is a
well-typed term for a quantity that cannot be used. -/
noncomputable def energyTagged (o : Osc)
    (m : WithDim (massOf o) ℝ) (ω : WithDim (angFreqOf o) ℝ)
    (x : WithDim (lengthOf o) ℝ) : WithDim (potentialDim o) ℝ :=
  m * (ω * ω) * (x * x)

/-! **MR12 fails**, and worse than attempt 2. What a reader gets back is the type
`WithDim (potentialDim o) ℝ` — which is to say, a name for a derivation — and unfolding it
gives an expression in `phys`, `tagD` and the group operations. Attempt 2's rendering carried
dimension noise; this carries dimension noise *plus* a tag algebra with no physical reading. -/

end Tier4

/-! # Tier 5 — computation (MR13 ❌, MR14 ❌, MR15 ❌)

Inherited from attempt 2 unchanged, and for attempt 2's reason: `WithDim`'s multiplicative
instances are declared at `M = ℝ`. Changing the *basis* does not touch the *carrier* axis —
they are orthogonal, and this attempt's whole idea lives on the basis. -/

namespace Tier5

/-! **MR13 fails.** No product at an executable carrier, tagged basis or not. -/
#check_failure (fun (m : WithDim (massOf .A) Float) (ω : WithDim (angFreqOf .A) Float) => m * ω)

/-! **MR14 fails.** Nor at a complex one — so the driven oscillator's impedance can be stored
and not squared, exactly as in attempt 2. -/
#check_failure (fun (a b : WithDim (massOf .A) ℂ) => a * b)

/-! **MR15 fails.** One usable carrier, so no exec/spec gap to name. -/

end Tier5

/-! # Tier 6 — geometry (MR16 ❌, MR17 ⚠️, MR18 ❌, MR19 ❌)

Attempt 3's idea was to make an *identity* into a dimension. Tier 6 asks it to make a *frame*
into one, and the answer is instructive: the attempt fails here twice, and the two failures
point in opposite directions, which is the clearest statement of why the basis is the wrong
place for either. -/

namespace Tier6

/-! ## MR16 ❌ — inherited, and now with tags to get wrong

A change of carrier is still a hand-written project-and-rewrap, and the dimension in the
re-wrap is still an annotation. The tagged basis adds a second thing to get wrong: the tag. -/

/-- **MR16 fails.** A's mass, re-carried into `ℂ` — and re-tagged as *B*'s on the way. Both
the dimension and the object identity are chosen afresh in the return type, so the axis this
attempt exists to protect is exactly the one a carrier change silently crosses. -/
noncomputable def massAtoComplexB (m : WithDim (massOf .A) ℝ) : WithDim (massOf .B) ℂ :=
  ⟨m.val⟩

/-- **MR16 fails, stated.** MR7 is won at the dimension layer and lost again at the carrier
boundary, because there is no operation there for the guarantee to attach to. -/
theorem carrier_change_crosses_the_tag :
    massOf .A ≠ massOf .B ∧ ∀ m : WithDim (massOf .A) ℝ, (massAtoComplexB m).val = ⟨m.val, 0⟩ :=
  ⟨massOf_ne, fun _ => rfl⟩

/-! ## MR17 ⚠️ — held, not combined

Identical to attempt 2: `WithDim d (Fin 2 → ℝ)` is well-formed and adds, and no product of any
kind is available at a non-`ℝ` carrier. The tag rides along without changing the verdict. -/

/-- A's velocity in the plane, tagged. -/
noncomputable def vA : WithDim (lengthOf .A / timeD) (Fin 2 → ℝ) := ⟨![3, 4]⟩

/-- It adds. -/
noncomputable example (u v : WithDim (lengthOf .A / timeD) (Fin 2 → ℝ)) :
    WithDim (lengthOf .A / timeD) (Fin 2 → ℝ) := u + v

/-! **MR17 fails on the combining half** — no `HMul` at an array carrier, so neither the
meaningless pointwise product nor the meaningful scalar product can be written. -/
#check_failure (fun (u v : WithDim (lengthOf .A / timeD) (Fin 2 → ℝ)) => u * v)

/-! **And the tag makes the scalar product's target unnameable even in principle.** A
contraction `v · v` of A's velocity would carry `⟨A⟩²` — the same multiplicity problem that
made `kinetic_ne_potential` — so A's speed squared and A's kinetic energy per unit mass, which
are the same quantity, would sit at different tag exponents. -/

/-- The dimension a contraction of A's velocity would land at, tag exponent `2`. -/
def speedSqDim : Dimension TaggedBase := (lengthOf .A / timeD) * (lengthOf .A / timeD)

/-- **MR17's tagged-specific failure.** The tag exponent of a squared velocity is `2`, so a
speed squared is not the same dimension as any quantity reached by a route with one factor of
A — the `kinetic_ne_potential` pathology, arriving in Tier 6 through the geometry rather than
through the energy. -/
theorem speedSq_tag_exponent : tagExp speedSqDim .A = 2 := by
  simp [tagExp, speedSqDim, lengthOf, timeD]
  decide

/-! ## MR18 ❌ — a frame is not a basis element, in two directions at once

This is the sharp result of the tier for attempt 3, and it is worth stating carefully because
the natural response to Tier 6 is "add a generator per frame", exactly as attempt 3 added one
per oscillator.

**It fails going out.** A change of frame must act on *components*, mixing them. A dimension
is an exponent vector and multiplication of dimensions adds exponents, so anything the basis
can express is a *scaling* — one factor per quantity, no mixing. There is no element of a free
commutative group whose action on a pair of numbers is a rotation.

**And it fails coming in.** Even the tag attempt 3 already has does not survive a rotation: a
rotation of the plane mixes A's coordinates with A's other coordinates, which is fine, but a
*coupled* pair's normal modes mix A's coordinates with **B's** — and the resulting quantity has
tag exponent in both, so it is neither A's nor B's. The normal-mode coordinate is exactly the
kind of thing this basis cannot name. -/

/-- The dimension of a normal-mode coordinate, `(x_A ± x_B)/√2` — a length carrying *both*
tags, because it was built from both oscillators' displacements. -/
def normalModeDim : Dimension TaggedBase := lengthOf .A * lengthOf .B

/-- **MR18 fails.** The normal-mode coordinate is not A's displacement and not B's, and the
reason is that a tag exponent counts factors rather than recording an identity. -/
theorem normalMode_is_neither : normalModeDim ≠ lengthOf .A ∧ normalModeDim ≠ lengthOf .B := by
  constructor
  · intro h
    have := congrArg (fun d => d.exponent (.tag .B)) h
    simp [normalModeDim, lengthOf] at this
  · intro h
    have := congrArg (fun d => d.exponent (.tag .A)) h
    simp [normalModeDim, lengthOf] at this

/-- **MR18 fails, the mixing half.** As in attempt 2, a rotation is a function on raw
components and the frame appears in no type, so readings in two frames add. The tag does not
help: two readings of *A's own* velocity in two frames have the same tagged dimension. -/
noncomputable def turn (v : Fin 2 → ℝ) : Fin 2 → ℝ :=
  ![3/5 * v 0 - 4/5 * v 1, 4/5 * v 0 + 3/5 * v 1]

noncomputable example : WithDim (lengthOf .A / timeD) (Fin 2 → ℝ) := vA + ⟨turn vA.val⟩

/-! ## MR19 ❌ — the tag distinguishes objects, never variances

`ω_A` and `x_A` now carry different dimensions — `T⁻¹·⟨A⟩` and `L·⟨A⟩` — which is more
separation than attempts 1 and 2 offered. It is still not MR19's separation, and the reason is
the one this whole attempt keeps running into: the tag is a claim about **whose** the quantity
is, and variance is a claim about **how it transforms**. Two quantities of one object can have
different variances, and two objects' quantities can share one. -/

/-- A's frequency family and A's displacement — same tag, different dimensions, and *both*
would be handed to the same rotation by anything that dispatches on the basis. -/
theorem tag_does_not_separate_variance :
    (massOf .A).exponent (.tag .A) = (angFreqOf .A).exponent (.tag .A)
      ∧ (lengthOf .A).exponent (.tag .A) = (angFreqOf .A).exponent (.tag .A) := by
  constructor <;> simp [massOf, angFreqOf, lengthOf]

/-- **MR19, the capstone — and Tier 6's verdict on the tagging idea.** The three quantities a
change of frame must treat differently — a mass (invariant), a velocity (turns), a frequency
family (rank-2) — all belong to oscillator A, so they carry the *same* tag exponent `1` and
are indistinguishable on the axis this attempt added. Meanwhile the one genuinely geometric
object of the coupled pair, the normal-mode coordinate, carries a tag exponent this basis
cannot interpret at all. Adding a generator per frame would repeat both halves exactly:
`tagging_dilemma` is not about objects, it is about free commutative groups. -/
theorem mr19_capstone :
    (massOf .A).exponent (.tag .A) = (angFreqOf .A).exponent (.tag .A)
      ∧ normalModeDim ≠ lengthOf .A
      ∧ ¬ (Addable (massOf .A) (massOf .B) ∧ Distinguishable (massOf .A) (massOf .B)) :=
  ⟨tag_does_not_separate_variance.1, normalMode_is_neither.1,
   tagging_dilemma (massOf .A) (massOf .B)⟩

end Tier6

/-! ## MR32 ❌ — specialization keeps kinds comparable (appended)

Appended after the first scoring pass; see `Attempt1Reals` for the occasion. This attempt
already carries the whole verdict, proved before the requirement was stated: the tagged
basis *does* distinguish the family — and forbids its sum. `kinetic_ne_potential` and the
`#check_failure` on `T + V` are the distinguishability side; `kinetic_forget_eq_potential_forget`
proves the obstruction carries no physical content. Scored ❌ by rule 3: over-rejection
counts as failure. The dilemma stated at `tagging_dilemma` for *objects* recurs here for
*specializations*, which is evidence it is structural. -/

/-- **MR32, the capstone** — restating the two halves already proved above: the family is
distinguished, and the distinction that forbids `H = T + V` has no dimensional content. -/
theorem mr32_over_rejection :
    kineticDim .A ≠ potentialDim .A ∧
      forget (kineticDim .A) = forget (potentialDim .A) :=
  ⟨kinetic_ne_potential, kinetic_forget_eq_potential_forget⟩

end PropertyKindCalculus.Examples.HarmonicOscillator.Attempt3

end -- pkc-blanket-expose
end -- pkc-blanket
