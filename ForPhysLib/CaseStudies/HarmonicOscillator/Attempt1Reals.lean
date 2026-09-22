/-
# Attempt 1 — plain reals in a bundle (the status quo)

The first honest attempt is the one PhysLib ships today:
`QuantumMechanics.HarmonicOscillator d` carries `m : ℝ` and `ω : Fin d → ℝ`, and every
derived quantity — the characteristic length `ξ`, the potential, the Hamiltonian — is
built from those bare reals.

This is not a strawman. It has a real defence, and this module states it in its strongest
form (§ *The bundling defence*): the `structure` **is** the object, so a quantity is only
ever reached by writing `Q.m`, and writing `Q₂.m` where `Q₁.m` was meant is a visible
authoring act rather than a silent coercion. Every guarantee attempt 1 offers rests on
that, and § *Where the defence ends* shows exactly where it stops holding — at the first
function boundary (**MR10**), after which nothing at all remains.

Scored against `README.md`:
- MR1 ❌
- MR2 ❌
- MR3 ❌
- MR4 ❌
- MR5 ❌
- MR6 ⚠️
- MR7 ⚠️
- MR8 ❌
- MR9 ❌
- MR10 ❌
- MR11 ✅
- MR12 ⚠️
- MR13 ❌
- MR14 ⚠️
- MR15 ❌
- MR16 ❌
- MR17 ❌
- MR18 ❌
- MR19 ❌
- MR32 ❌ (appended)

The one requirenent this attempt wins outright is **authoring ergonomics**, and it wins it permanently:
no scheme that adds safety will ever beat `m * ω * ω * x * x`.

That is the honest shape of the trade every other attempt is making.

The evidence in this file runs *opposite* to the other attempts':
here almost nothing is rejected, so a failure is witnessed by an `example` showing that a **nonsensical term elaborates anyway**.

Each one is a bug a reviewer would have to catch by reading.
-/

module

public import Mathlib.Analysis.SpecialFunctions.Sqrt
public import Mathlib.Analysis.Real.Pi.Bounds

public section -- pkc-blanket
@[expose] section -- pkc-blanket-expose

namespace PropertyKindCalculus.Examples.HarmonicOscillator.Attempt1

open Real

/-! ## The model, as PhysLib has it

Mirroring `Physlib/QuantumMechanics/HarmonicOscillator/Basic.lean`: a mass and a family of
natural frequencies indexed by the spatial degree of freedom, both bare reals. -/

/-- A `d`-dimensional harmonic oscillator, bare-real style. -/
structure Oscillator (d : ℕ) where
  /-- The mass. -/
  m : ℝ
  /-- The natural (angular) frequencies, one per degree of freedom. -/
  ω : Fin d → ℝ

namespace Oscillator

variable {d : ℕ} (Q : Oscillator d) (i : Fin d)

/-- Reduced Planck constant, as a bare real (PhysLib's `Constants.ℏ`). -/
noncomputable def hbar : ℝ := 1.054571817e-34

/-- The characteristic length `ξ i = √ℏ / (√m · √(ω i))`, exactly as PhysLib defines it. -/
noncomputable def ξ : ℝ := √hbar / (√Q.m * √(Q.ω i))

end Oscillator

/-! ## Two oscillators, coupled

`m_A = 3`, `m_B = 5`; `ω_A = 2`, `ω_B = 4`; the coupling `k_c` and the upper normal mode
`ω₊ = 5`. The magnitudes are the ones fixed in `README.md`. -/

/-- Oscillator A. -/
noncomputable def oscA : Oscillator 1 := ⟨3, fun _ => 2⟩
/-- Oscillator B. -/
noncomputable def oscB : Oscillator 1 := ⟨5, fun _ => 4⟩
/-- The coupling constant of the spring joining A to B. A property of *neither* oscillator. -/
noncomputable def kCoupling : ℝ := 6
/-- The upper normal-mode angular frequency of the coupled pair. Not `ω_A`, not `ω_B`,
not `ω_A + ω_B`. -/
noncomputable def ωPlus : ℝ := 5

/-! ## MR1 ❌ — dimensional homogeneity

A mass plus a length elaborates without complaint. There is no dimension to check. -/

/-- **MR1 fails.** Adding the mass of A to the characteristic length of A is a well-typed
`ℝ`. Nothing in the language objects. -/
noncomputable example : ℝ := oscA.m + oscA.ξ 0

/-- **MR1 fails, worse.** A mass, a frequency and a length summed together. Still an `ℝ`. -/
noncomputable example : ℝ := oscA.m + oscA.ω 0 + oscA.ξ 0 + kCoupling

/-! ## MR2 ❌ — derived dimensions are computed, not annotated

There is nothing to compute. `ξ` is an `ℝ` because every real-valued expression is, not
because `ℏ / (m·ω)` was found to be an area. The *type* of `ξ` carries no evidence that the
formula was even dimensionally sound, so a typo in the formula — dividing by `√m` where
`√(m·ω)` was meant — produces another perfectly good `ℝ`. -/

/-- **MR2 fails.** A deliberately wrong characteristic length (the frequency dropped from
the denominator) has *exactly the same type* as the right one. Both are `ℝ`; nothing
distinguishes them until someone reads the formula. -/
noncomputable def ξWrong (Q : Oscillator 1) : ℝ := √Oscillator.hbar / √Q.m

example : (ξWrong oscA : ℝ) = ξWrong oscA := rfl

/-! ## MR3 ❌ — unit-change covariance

There is no unit system to change from. A bare `ℝ` is not covariant in anything; the
numbers `3` and `5` above mean whatever the reader assumes they mean, and re-reading them
as grams rather than kilograms silently rescales every derived quantity by a different
power with no record anywhere. -/

/-! ## MR4 ❌ — the rad/s trap

`Oscillator.ω` is an *angular* frequency (rad/s). A user with an ordinary frequency in
hertz can hand it straight over: both are `ℝ`. The resulting `ξ`, spectrum and Hamiltonian
are wrong by the appropriate power of 2π, and every check in the file passes. -/

/-- An ordinary frequency ν in hertz — the same quantity A's `ω` measures, in the other of
the two ISO 80000-3 items that share the dimension `T⁻¹`. -/
noncomputable def nuA : ℝ := 2 / (2 * π)

/-- **MR4 fails.** An oscillator built from a frequency in hertz where an angular frequency
was required. It elaborates, and it is wrong by `2π`. -/
noncomputable def oscFromHz : Oscillator 1 := ⟨3, fun _ => nuA⟩

/-- And the two are *not* equal — the bug is real, not notional — yet the type system
sees no difference between them. -/
theorem hz_bug_is_real : oscFromHz.ω 0 ≠ oscA.ω 0 := by
  simp only [oscFromHz, oscA, nuA]
  intro h
  have hπ : (3:ℝ) < π := Real.pi_gt_three
  rw [div_eq_iff (by positivity)] at h
  nlinarith [hπ]

/-! ## MR5 ❌ — scale type

The energy of a Hamiltonian is fixed only up to the zero of the potential, so its *ratios*
are meaningless while its *differences* are not. A bare `ℝ` offers `/` unconditionally. -/

/-- Two energy levels of A, on some gauge. -/
noncomputable def energyLevel (n : ℕ) : ℝ := 2 * (n + 1/2)

/-- **MR5 fails.** The ratio of two gauge-dependent absolute energies elaborates and
evaluates. Shift the potential's zero and this number changes; nothing marks it as
unphysical. -/
noncomputable example : ℝ := energyLevel 1 / energyLevel 0

/-- The gauge-dependence, made concrete: offsetting every level by a constant changes the
ratio (from `3` to `2`), so the ratio was never a property of the oscillator. -/
theorem energy_ratio_gauge_dependent :
    energyLevel 1 / energyLevel 0 ≠ (energyLevel 1 + 2) / (energyLevel 0 + 2) := by
  norm_num [energyLevel]

/-! ## MR6 ⚠️ — degrees of freedom

`ω : Fin d → ℝ` distinguishes degrees of freedom *by an index*, which is better than
nothing: `Q.ω 0` and `Q.ω 1` are different terms. But the index is not part of the value's
type, so once either is used the distinction is gone. -/

/-- An anisotropic two-dimensional oscillator. -/
noncomputable def aniso : Oscillator 2 := ⟨1, ![2, 7]⟩

/-- **MR6 fails.** The characteristic length of degree of freedom 0 multiplied by the
angular frequency of degree of freedom 1 — a quantity of no physical standing — elaborates
without comment. -/
noncomputable example : ℝ := aniso.ξ 0 * aniso.ω 1

/-- Isotropy is at least *statable* here, as PhysLib's `IsIsotropic` states it: the
magnitudes agree. That much attempt 1 gets right, and it is the shape every later attempt
must preserve — a fact about numbers, never an identification of the two degrees of
freedom. -/
def IsIsotropic {d : ℕ} (Q : Oscillator d) : Prop := ∀ i j, Q.ω i = Q.ω j

theorem aniso_not_isotropic : ¬ IsIsotropic aniso := by
  intro h
  have := h 0 1
  simp [aniso] at this

/-! ## MR7 ⚠️ — object identity: *the bundling defence*

Here is attempt 1's best argument, stated as strongly as it can be. The `structure` **is**
the object. A mass is only ever obtained by writing `oscA.m`, so building a Hamiltonian
from A's mass and B's frequency requires the author to *write* `oscB.ω`, in plain sight,
next to an `oscA.m`. That is a visible authoring act. Reviewers catch those. -/

/-- The Hamiltonian's potential coefficient `½ m ω²`, taken from one oscillator. -/
noncomputable def potentialCoeff (Q : Oscillator 1) : ℝ := Q.m * (Q.ω 0)^2 / 2

/-- The defence holds *at the projection site*: this reads wrong, because both projections
are visible in one line. -/
noncomputable example : ℝ := oscA.m * (oscB.ω 0)^2 / 2

/-! ## MR10 ❌ — and where the defence ends

The defence is a claim about what the *author writes at the projection site*. It says
nothing about what happens one call deep, and the moment a quantity is passed as a
parameter it is a bare `ℝ` with no memory of where it came from. Every guarantee above
evaporates here, which is why MR6 and MR7 are scored ⚠️ (i.e. failed) rather than ✅. -/

/-- A perfectly ordinary helper — the shape any real development is full of. Its signature
is `ℝ → ℝ → ℝ`; it cannot ask which oscillator either argument belongs to, because that
information does not exist at this point. -/
noncomputable def zeroPointEnergy (m ω : ℝ) : ℝ := Oscillator.hbar * ω / 2 + 0 * m

/-- **MR10 fails.** The mixed call. There is no `oscA.`/`oscB.` juxtaposition to notice
here — the two values arrived as arguments — and there is nothing for the checker to
object to. -/
noncomputable example : ℝ := zeroPointEnergy oscA.m (oscB.ω 0)

/-- **MR10 fails, at the limit.** The arguments in the wrong order. Same type, same
elaboration, different physics. -/
noncomputable example : ℝ := zeroPointEnergy (oscA.ω 0) oscA.m

/-! ## MR8 ❌ — licensed aggregation, in both directions

MR8 is deliberately two-sided: the total mass of the pair *is* the sum of the parts, and
the pair's angular frequency *is not*. Attempt 1 accepts both, so it gets the mass right by
luck and the frequency wrong by the same luck. -/

/-- The total mass of the pair — genuinely `3 + 5 = 8`, and attempt 1 gets it. -/
theorem total_mass : oscA.m + oscB.m = 8 := by norm_num [oscA, oscB]

/-- **MR8 fails.** The same syntax produces `2 + 4 = 6` for the angular frequencies, which
is not the pair's normal-mode frequency (`ω₊ = 5`) nor anything else physical. The
expression that was right for mass is wrong for frequency, and the two are indistinguishable
to the checker. -/
theorem frequency_sum_is_meaningless : oscA.ω 0 + oscB.ω 0 ≠ ωPlus := by
  norm_num [oscA, oscB, ωPlus]

/-- The two lines above have **the same shape and the same type**. That is the whole of
MR8: extensivity is a property of the *kind*, and there is no kind here to carry it. -/
theorem mr8_the_point :
    oscA.m + oscB.m = 8 ∧ oscA.ω 0 + oscB.ω 0 ≠ ωPlus :=
  ⟨total_mass, frequency_sum_is_meaningless⟩

/-! ## MR9 ❌ — whole-system quantities

`kCoupling` is a property of the pair, through the pair of components `A↔B`. Attempt 1 has
nowhere to put it: it is a top-level `ℝ`, no more attached to the pair than to anything
else. And `ωPlus`, `oscA.ω 0` and `oscB.ω 0` are mutually substitutable. -/

/-- **MR9 fails.** The normal-mode frequency substituted for a bare one, inside the
oscillator constructor itself. Nothing to report. -/
noncomputable def oscAWithWrongOmega : Oscillator 1 := ⟨oscA.m, fun _ => ωPlus⟩

/-- The *lower* normal-mode angular frequency of the coupled pair. The normal modes interlace
the bare frequencies — `ω₋ ≤ min(ω_A, ω_B) ≤ max(ω_A, ω_B) ≤ ω₊` — so with `ω_A = 2`,
`ω_B = 4` we have `ω₋ = 1.5` and `ω₊ = 5`. -/
noncomputable def ωMinus : ℝ := 1.5

/-- **MR9 fails, and the failure is continuous.** Four quantities — the two bare frequencies
and the two normal modes — pairwise distinct in value, identical in type, and mutually
substitutable in every expression. What makes this the worst kind of bug is the *limit*: as
the coupling `k_c → 0` the normal modes converge on the bare frequencies, so a test run on a
weakly coupled system passes with the substitution in place, and the error grows only as the
coupling does. No dimension, no unit and no plain-real type records which of the four a value
is. -/
theorem four_frequencies_one_type :
    ωMinus ≠ oscA.ω 0 ∧ ωMinus ≠ oscB.ω 0 ∧ ωPlus ≠ oscA.ω 0 ∧ ωPlus ≠ oscB.ω 0 := by
  norm_num [ωMinus, ωPlus, oscA, oscB]

/-! # Tier 4 — ergonomics (MR11 ✅, MR12 ⚠️)

The one tier attempt 1 wins, and it is not a small win. -/

namespace Tier4

/-- **MR11 holds, and permanently.** The potential energy `V = m·ω²·x²` — the formula, and
nothing else. Zero extra arguments, zero casts, zero witnesses, zero declarations of setup.
This is the baseline every other attempt is measured against, and no scheme that adds safety
will beat it. Attempts 2, 3 and 4 all pay something here; the benchmark's job is to say what
they buy with it, not to pretend the payment is imaginary. -/
noncomputable def energyReals (m ω x : ℝ) : ℝ := m * (ω * ω) * (x * x)

/-! **MR12 is ⚠️, not ❌.** There is no rendering machinery — no attribute, no lift, no LaTeX —
so what a reader gets back is Lean's own pretty-printer. But what that prints *is* the formula,
because there is nothing else in the term: no cast, no dimension expression, no witness. So
attempt 1 renders acceptably by having nothing to hide rather than by having a pipeline, and
the distinction matters for exactly one reason — the moment any of the guarantees in Tiers 2–3
is added, the noise arrives with it. Attempts 2 and 3 are ❌ here for that reason. -/

end Tier4

/-! # Tier 5 — computation (MR13 ❌, MR14 ⚠️, MR15 ❌)

The carrier is not an axis here; it is a constant. `Oscillator` is `ℝ`-valued in its fields,
so "the same model at another carrier" is not a thing that can be asked for — it is a second
structure. -/

namespace Tier5

/-- **MR13 fails.** The executable model. Note what this is: a *second declaration* of the same
physics, sharing nothing with `Oscillator` but the author's intention. -/
structure OscillatorFloat (d : ℕ) where
  /-- The mass. -/
  m : Float
  /-- The natural (angular) frequencies. -/
  ω : Fin d → Float

/-- The stiffness `k = m·ω²`, over the specification carrier. -/
noncomputable def stiffnessReal (Q : Oscillator 1) : ℝ := Q.m * Q.ω 0 * Q.ω 0

/-- The stiffness again, over the executable carrier — **written twice**, because there is no
way to write it once. -/
def stiffnessFloat (Q : OscillatorFloat 1) : Float := Q.m * Q.ω 0 * Q.ω 0

/-! It runs, which is the only thing the duplication buys. -/
#guard (stiffnessFloat ⟨5, fun _ => 2⟩) == 20.0

/-! **MR13 fails.** Two definitions, no relation between them — and, decisively, *nothing in
either type records that they are the same model*. A change to one is not a compile error in
the other, so the thing that runs and the thing that was reasoned about drift apart silently,
which is precisely the failure MR13 names. Every law proved of `stiffnessReal` says nothing
whatsoever about `stiffnessFloat`. -/

/-! ## MR14 ⚠️ — complex-valued quantities

Attempt 1 scores ⚠️ rather than ❌ here, and the reason is worth being precise about: a bare
carrier can *hold* a complex value perfectly well, because a bare carrier constrains nothing.
What it cannot do is say that the value is one quantity of one kind. -/

/-- **MR14 is ⚠️.** The driven oscillator's mechanical impedance `Z = 3 + 4i` — expressible,
because `ℂ` is a type and attempt 1 accepts any type. -/
noncomputable def Z : ℂ := ⟨3, 4⟩

/-- And its squared modulus computes, `3² + 4² = 25`. This much works. -/
theorem Z_normSq : Complex.normSq Z = 25 := by
  simp [Z, Complex.normSq_apply]
  norm_num

/-- **MR14 fails at the metrological question.** The impedance's two components — the
mechanical resistance and the reactance, which IEC 80000-6's electrical twin lists as
*separate items* — are `Z.re` and `Z.im`, two bare reals of the same type as everything else
in this file. Nothing distinguishes them from each other, from a mass, or from the ratio of
two energy levels, and nothing records that a modulus is ratio-scale while an argument is
interval-scale. So the value is representable and the *quantity* is not. -/
noncomputable example : ℝ × ℝ := (Z.re, Z.im)

/-! ## MR15 ❌ — exec/spec agreement

With one carrier there is no exec/spec distinction, hence no bridge to build and no gap to
name. That is not a defence: it means the float arithmetic every consumer eventually runs sits
outside whatever was verified, and `stiffnessReal`/`stiffnessFloat` above are the two halves
of exactly that gap with nothing between them. -/

end Tier5

/-! # Tier 6 — geometry (MR16 ❌, MR17 ❌, MR18 ❌, MR19 ❌)

The oscillators move into a plane. Every failure below has the same form as the ones above —
a term that should not exist elaborates — and they are collected here because a plane is where
a reader's intuition that "it is only bookkeeping" is hardest to sustain. -/

namespace Tier6

/-! ## MR16 ❌ — a carrier morphism can change anything

A change of representation is, here, a function `ℝ → ℝ`. So is a change of unit. So is a
change of *quantity*. All three have the same type, and the type is the only thing a reader or
a checker has to go on. -/

/-- An honest representation change — rounding a mass to the nearest gram. -/
noncomputable def roundMass (m : ℝ) : ℝ := m

/-- A unit change wearing the same clothes: kilograms to grams. -/
noncomputable def kgToGrams (m : ℝ) : ℝ := 1000 * m

/-- And a change of *kind*, wearing them too: a mass to its rest energy. -/
noncomputable def massToEnergy (m : ℝ) : ℝ := m * 8.98755e16

/-- **MR16 fails.** All three have one type, so a pipeline that applies the third where the
first was meant is a well-typed program, and the value it produces is a mass according to
every check available. There is no `castCarrier` here whose signature could fix the kind,
because there is no kind. -/
theorem three_morphisms_one_type :
    (roundMass : ℝ → ℝ) = roundMass
      ∧ (kgToGrams : ℝ → ℝ) = kgToGrams
      ∧ (massToEnergy : ℝ → ℝ) = massToEnergy :=
  ⟨rfl, rfl, rfl⟩

/-! ## MR17 ❌ — a vector quantity is `n` unrelated numbers

ISO 80000-2 §18 asks for a numerical array under *one scalar unit*. Attempt 1 offers
`Fin 2 → ℝ`, which is that shape and no more — and, crucially, is also the shape of two
unrelated numbers, of a pair of masses, and of `ω`. -/

/-- A's velocity in the plane, `(3, 4)`. -/
noncomputable def vA : Fin 2 → ℝ := ![3, 4]
/-- B's velocity, `(1, 0)`. -/
noncomputable def vB : Fin 2 → ℝ := ![1, 0]

/-- **MR17 fails.** The componentwise product of two velocities — not a scalar product, not a
vector product, not any operation ISO 80000-2 §18 licenses — is a perfectly good `Fin 2 → ℝ`,
which is also the type of a velocity. So the result can be used wherever a velocity can. -/
noncomputable example : Fin 2 → ℝ := fun i => vA i * vB i

/-- **MR17 fails, the §18 half.** The per-coordinate reading the standard advises *against* —
each component carrying its own number and unit — is indistinguishable from the array reading
it advises *for*, because neither carries a unit at all. -/
noncomputable example : (ℝ × String) × (ℝ × String) := ((3, "m/s"), (4, "m/s"))

/-! ## MR18 ❌ — nothing is frame-relative, so everything rotates

A change of Cartesian frame is a matrix acting on components. Attempt 1 can *write* one; what
it cannot do is say which values it may be applied to. -/

/-- The Pythagorean rotation `cos θ = 3/5`, `sin θ = 4/5`, as a plain function. -/
noncomputable def turn (v : Fin 2 → ℝ) : Fin 2 → ℝ :=
  ![3/5 * v 0 - 4/5 * v 1, 4/5 * v 0 + 3/5 * v 1]

/-- The scalar product, likewise. -/
noncomputable def dot (u v : Fin 2 → ℝ) : ℝ := u 0 * v 0 + u 1 * v 1

/-- The invariance is *true* — `|v|²` really is `25` in both frames. Attempt 1's problem is
never that the arithmetic is wrong. -/
theorem speedSq_invariant : dot (turn vA) (turn vA) = dot vA vA := by
  simp [dot, turn, vA]
  ring

/-- **MR18 fails.** The frame is nowhere in any type, so components read in the laboratory
frame add to components read in the rotated frame without complaint. The sum is meaningless,
and it is `(3, 4) + (-7/5, 24/5)` — a plausible-looking pair of numbers no check will
question. -/
noncomputable example : Fin 2 → ℝ := fun i => vA i + turn vA i

/-- **MR18 fails, the dual.** `turn` accepts anything of the right shape, so a triple — here a
pair — of *masses* rotates into two numbers that are the masses of nothing. -/
noncomputable def masses : Fin 2 → ℝ := ![3, 5]

noncomputable example : Fin 2 → ℝ := turn masses

/-- And the "rotated masses" are not the masses: `3` has become `-11/5`. A quantity has been
silently destroyed by an operation that had no business touching it. -/
theorem rotating_masses_is_nonsense : turn masses 0 ≠ masses 0 := by
  simp [turn, masses]
  norm_num

/-! ## MR19 ❌ — `ω` and `x` are the same type

The requirement's whole content is that `ω : Fin d → ℝ` and a position `x : Fin d → ℝ` obey
different transformation laws while being written identically. Attempt 1 makes this maximally
sharp: they are not merely the same type, they are the same type *by construction*, since
`Oscillator.ω` is declared as `Fin d → ℝ` in the structure PhysLib ships. -/

/-- The anisotropic oscillator's frequencies, `(2, 7)` — `aniso.ω`, extracted. -/
noncomputable def omegas : Fin 2 → ℝ := aniso.ω

/-- **MR19 fails.** The frequency list rotates, because nothing says it is not a vector. The
result is `(-22/5, 29/5)`: two numbers that are not the frequencies of any oscillator, in any
frame. What has actually happened is that a diagonal rank-2 object was treated as rank-1, and
the off-diagonal information the rotation should have produced has been discarded rather than
computed. -/
theorem rotating_frequencies_is_nonsense : turn omegas 0 ≠ omegas 0 := by
  simp [turn, omegas, aniso]
  norm_num

/-- **MR19, the capstone — and the tier's.** One type, `Fin 2 → ℝ`, holding a velocity, a pair
of masses and a frequency list; one function, `turn`, applicable to all three; correct for the
first and destructive for the other two. Nothing in attempt 1 can express the difference,
because the difference is not in the numbers, the dimensions, the units or the shapes. -/
theorem mr19_capstone :
    dot (turn vA) (turn vA) = dot vA vA
      ∧ turn masses 0 ≠ masses 0
      ∧ turn omegas 0 ≠ omegas 0 :=
  ⟨speedSq_invariant, rotating_masses_is_nonsense, rotating_frequencies_is_nonsense⟩

end Tier6

/-! ## MR32 ❌ — specialization keeps kinds comparable (appended)

Appended after the first scoring pass, when the trace against PKC's own requirement
catalogue showed R2 (the specialization lattice) unexercised even though its subject
matter is on this very page: kinetic, potential and total energy are a specialization
family, and `H = T + V` appears in every attempt.

Here all three are `ℝ`. The sum side of the requirement is swept — trivially, because
*everything* is writable — and the distinguishability side fails the way MR4 fails: a
function expecting the potential accepts the kinetic. -/

section MR32

/-- `H = T + V`, for free — along with every other sum of every other pair of reals. -/
noncomputable example (T V : ℝ) : ℝ := T + V

/-- A consumer that means the *potential* energy… -/
def expectsPotential (V : ℝ) : ℝ := V

/-- …accepts the kinetic. Distinguishability fails before licensing is even a question. -/
example (T : ℝ) : ℝ := expectsPotential T

end MR32

end PropertyKindCalculus.Examples.HarmonicOscillator.Attempt1

end -- pkc-blanket-expose
end -- pkc-blanket
