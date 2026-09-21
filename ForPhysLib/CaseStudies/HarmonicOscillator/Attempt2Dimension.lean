/-
# Attempt 2 — PhysLib `Dimension` / `WithDim` (the PR #1579 proposal)

The second attempt is the one jstoobysmith suggested: carry the oscillator's quantities in
`WithDim d ℝ`, so the mass has dimension `M`, the angular frequency `T⁻¹`, and every derived
quantity's dimension is *computed* by the free commutative group `Dimension LTMCTDimensionBase`
rather than asserted.

It delivers, cleanly and completely, the whole of Tier 1 — **MR1, MR2, MR3** — and it fixes
attempt 1's worst structural failure, **MR10**: a quantity keeps its dimension across a
function boundary, so a helper taking a mass and an angular frequency cannot be called with
them swapped.

It fails every requirement in Tiers 2 and 3, and it fails them for one reason, which this
file makes explicit rather than merely observing: `Dimension B` is a **free commutative
group**. Two quantities are distinguishable exactly when their exponent vectors differ, and
`WithDim d ℝ` offers no discrimination beyond `d`. So when two quantities share a dimension —
frequency and angular frequency, oscillator A's mass and oscillator B's mass, a normal-mode
frequency and a bare one — they do not merely *behave alike*. They inhabit **the same type**,
by `rfl`. PhysLib says so itself, in `WithDim.scaleUnit_val_eq_scaleUnit_val_of_dim_eq`:
equal dimensions make two quantities interchangeable under unit scaling.

Scored against `README.md`:
- MR1 ✅
- MR2 ✅
- MR3 ✅
- MR4 ❌
- MR5 ❌
- MR6 ❌
- MR7 ❌
- MR8 ❌
- MR9 ❌
- MR10 ✅
- MR11 ⚠️
- MR12 ❌
- MR13 ❌
- MR14 ❌
- MR15 ❌
- MR16 ❌
- MR17 ⚠️
- MR18 ❌
- MR19 ❌
- MR32 ❌ (appended)

Tiers 5 and 6 have a second, independent cause worth naming here: `WithDim d M` is parametric
in `M` for the *additive* structure only — `HMul` and `HDiv` are declared at `M = ℝ` and
nowhere else — so the algebra a physical model is written in is `ℝ`-only, as
`Physlib/Units/Basic.lean` says of itself. A quantity can therefore be *held* at another
carrier and not *combined* there, which closes MR13, MR14 and MR15 at a stroke and leaves
MR17's vector arithmetic in the same position.
-/
import PropertyKindCalculus.Dimension
import PropertyKindCalculus.QuantityReal
import Physlib.Units.WithDim.Basic
import Mathlib.Basic.Complex.Basic

namespace PropertyKindCalculus.Examples.HarmonicOscillator.Attempt2

open PropertyKindCalculus Dimension

/-! ## The dimensions the oscillator needs

Expressed in PhysLib's generators, via PKC's named `Dim.*`. Nothing here is an annotation:
each is a product of powers, and the group decides what follows. -/

/-- Angular frequency ω, `T⁻¹` (rad/s). -/
def angularFrequency : Dimension LTMCTDimensionBase := Dim.time⁻¹

/-- Ordinary frequency ν, `T⁻¹` (Hz). ISO 80000-3 lists this as a *different item* from
angular frequency; the dimension group cannot tell, and `frequency = angularFrequency`
below is proved by `rfl`. -/
def frequency : Dimension LTMCTDimensionBase := Dim.time⁻¹

/-- Action, `M·L²·T⁻¹` — the dimension of `ℏ`. -/
def action : Dimension LTMCTDimensionBase := Dim.energy * Dim.time

/-- Spring constant, `M·T⁻²`. -/
def springConstant : Dimension LTMCTDimensionBase := Dim.mass * Dim.time⁻¹ * Dim.time⁻¹

/-! ## MR1 ✅ — dimensional homogeneity

`WithDim`'s `Add` instance is `Add (WithDim d M)`: homogeneous in `d` by construction. A sum
across dimensions has no instance to resolve, so it is rejected at elaboration. -/

/-! **MR1 holds.** A mass plus a length has no `Add` instance. This is attempt 1's first
failure, fixed. -/
#check_failure (fun (m : WithDim Dim.mass ℝ) (l : WithDim Dim.length ℝ) => m + l)

/-! **MR1 holds.** A mass plus an angular frequency: likewise rejected. -/
#check_failure (fun (m : WithDim Dim.mass ℝ) (ω : WithDim angularFrequency ℝ) => m + ω)

/-- Same-dimension addition, by contrast, elaborates — as it must. -/
noncomputable example (m₁ m₂ : WithDim Dim.mass ℝ) : WithDim Dim.mass ℝ := m₁ + m₂

/-! ## MR2 ✅ — derived dimensions are computed

PhysLib proves `HarmonicOscillator.ξ_sq : ξ i ^ 2 = ℏ / (m · ω i)`. Take that as the
defining relation and ask the group what `ξ²` is. The answer is `L²`, and it is a *computed*
answer: `decide` evaluates the exponent vectors of `M·L²·T⁻¹`, `M` and `T⁻¹` and checks the
result against `L²`. Nobody annotated anything.

(That this reduces at all is itself downstream of PR #1579: `Dimension.Exponent`'s reducible
rational arithmetic is what lets the kernel evaluate these.) -/

/-- **MR2 holds.** `ℏ / (m · ω)` has the dimension of an area — computed, not asserted. -/
theorem xiSq_dimension : action / (Dim.mass * angularFrequency) = Dim.area := by decide

/-- **MR2 holds, at the value level.** The characteristic length squared, built by the
`WithDim` division and multiplication instances, lands at the dimension the group computed —
so its type *is* the derivation. -/
noncomputable def xiSq (hbar : WithDim action ℝ) (m : WithDim Dim.mass ℝ)
    (ω : WithDim angularFrequency ℝ) : WithDim Dim.area ℝ :=
  WithDim.cast (hbar / (m * ω)) (by decide)

/-! **MR2 holds, and it catches a wrong formula.** Attempt 1's `ξWrong` — the frequency
dropped from the denominator — is *not* an area, so the same `cast` is rejected. This is the
requirement doing its job. -/
#check_failure (fun (hbar : WithDim action ℝ) (m : WithDim Dim.mass ℝ) =>
  (WithDim.cast (hbar / m) (by decide) : WithDim Dim.area ℝ))

/-! ## MR3 ✅ — unit-change covariance

`LTMCTUnitChoices.dimScale u₁ u₂` is a `MonoidHom (Dimension LTMCTDimensionBase) ℝ≥0`: the
scale factor is a *function of the dimension*, and it respects the dimensional algebra. That
is exactly the covariance MR3 asks for, and it is free. -/

/-- **MR3 holds (multiplicativity).** The scale factor of a product is the product of the
scale factors — so a derived quantity rescales consistently with the quantities it is
derived from. -/
theorem dimScale_mul (u₁ u₂ : LTMCTUnitChoices) (d₁ d₂ : Dimension LTMCTDimensionBase) :
    u₁.dimScale u₂ (d₁ * d₂) = u₁.dimScale u₂ d₁ * u₁.dimScale u₂ d₂ :=
  map_mul _ _ _

/-- **MR3 holds (unit).** A dimensionless quantity does not rescale. -/
theorem dimScale_one (u₁ u₂ : LTMCTUnitChoices) : u₁.dimScale u₂ 1 = 1 := map_one _

/-- **MR3 holds (identity).** Not changing units changes nothing. -/
theorem scaleUnit_id_withDim {d : Dimension LTMCTDimensionBase} (u : LTMCTUnitChoices)
    (m : WithDim d ℝ) : UnitDependent.scaleUnit u u m = m :=
  UnitDependent.scaleUnit_id u m

/-- **MR3 holds (composition).** Rescaling through an intermediate unit system agrees with
rescaling directly — the functoriality MR3 names. -/
theorem scaleUnit_trans_withDim {d : Dimension LTMCTDimensionBase}
    (u₁ u₂ u₃ : LTMCTUnitChoices) (m : WithDim d ℝ) :
    UnitDependent.scaleUnit u₂ u₃ (UnitDependent.scaleUnit u₁ u₂ m)
      = UnitDependent.scaleUnit u₁ u₃ m :=
  UnitDependent.scaleUnit_trans u₁ u₂ u₃ m

/-! ## MR10 ✅ — provenance survives a function boundary

Attempt 1's decisive failure, and attempt 2 fixes it outright: a helper's *signature* now
records what its arguments are, so the arguments cannot be supplied in the wrong order. This
is the genuine, permanent gain from adopting `Dimension`, and nothing below detracts from
it. -/

/-- The zero-point energy `½ℏω`, as a helper with a dimensioned signature. -/
noncomputable def zeroPointEnergy (hbar : WithDim action ℝ) (ω : WithDim angularFrequency ℝ) :
    WithDim Dim.energy ℝ :=
  WithDim.cast (hbar * ω) (by decide)

/-! **MR10 holds.** Attempt 1's swapped-argument call — a frequency where a mass was wanted —
is rejected here, because the two arguments no longer have the same type. -/
#check_failure (fun (hbar : WithDim action ℝ) (m : WithDim Dim.mass ℝ) =>
  zeroPointEnergy hbar m)

/-! ## MR4 ❌ — the rad/s trap

Frequency and angular frequency are the two ISO 80000-3 items that share `T⁻¹`. The dimension
group identifies them, so `WithDim frequency ℝ` and `WithDim angularFrequency ℝ` are not
similar types — they are **the same type**, definitionally. There is no discipline, no
convention, and no future lemma that can separate them at this layer. -/

/-- **MR4 fails, definitionally.** Frequency and angular frequency have the same dimension. -/
theorem frequency_eq_angularFrequency : frequency = angularFrequency := rfl

/-- **MR4 fails, at the type level.** The two quantity types are *literally identical*, so a
value in hertz is accepted wherever a value in rad/s is required — not by a coercion that
could be audited, but because there is nothing to coerce. -/
example : WithDim frequency ℝ = WithDim angularFrequency ℝ := rfl

/-- **MR4 fails, and the 2π is silently lost.** `zeroPointEnergy` accepts a frequency in
hertz. The result is well-dimensioned, unit-covariant, and wrong by `2π`. -/
noncomputable example (hbar : WithDim action ℝ) (ν : WithDim frequency ℝ) :
    WithDim Dim.energy ℝ := zeroPointEnergy hbar ν

/-! ## MR5 ❌ — scale type

The absolute energy of a Hamiltonian is gauge-dependent, so its ratios carry no physical
content; only its *differences* do. `WithDim` has a `HDiv` instance for every pair of
dimensions and no notion of scale type, so the meaningless ratio elaborates exactly as
readily as the meaningful one. -/

/-- **MR5 fails.** The ratio of two gauge-dependent absolute energies elaborates, and lands
at dimension one — which is the layer's way of saying "this is a pure number", precisely the
claim that is false here. -/
noncomputable example (E₁ E₀ : WithDim Dim.energy ℝ) :
    WithDim (Dim.energy * Dim.energy⁻¹) ℝ := E₁ / E₀

/-- The meaningful operation — a ratio of energy *differences* — has the same type as the
meaningless one, so the layer cannot prefer it. -/
noncomputable example (E₂ E₁ E₀ : WithDim Dim.energy ℝ) :
    WithDim (Dim.energy * Dim.energy⁻¹) ℝ := (E₂ - E₁) / (E₁ - E₀)

/-! ## MR6 ❌ — degrees of freedom

A dimensioned anisotropic oscillator indexes its frequencies by `Fin d`, exactly as attempt 1
does — the index is not part of the type, so `ω 0` and `ω 1` are interchangeable values of
one type. -/

/-- A `d`-dimensional oscillator with dimensioned fields — the PR #1579 rewrite of
`QuantumMechanics.HarmonicOscillator`. -/
structure DimOscillator (d : ℕ) where
  /-- The mass. -/
  m : WithDim Dim.mass ℝ
  /-- The natural angular frequencies, one per degree of freedom. -/
  ω : Fin d → WithDim angularFrequency ℝ

/-- **MR6 fails.** The characteristic length of one degree of freedom times the angular
frequency of another: still perfectly well-dimensioned, still meaningless. -/
noncomputable example (hbar : WithDim action ℝ) (Q : DimOscillator 2) :
    WithDim (Dim.area * angularFrequency) ℝ :=
  xiSq hbar Q.m (Q.ω 0) * Q.ω 1

/-! ## MR7 ❌ — object identity

Two oscillators' masses have the same dimension, hence the same type, hence are mutually
substitutable. The mixed Hamiltonian — A's mass with B's frequency — is well-typed. -/

/-- Oscillator A: `m = 3`, `ω = 2`. -/
noncomputable def oscA : DimOscillator 1 := ⟨⟨3⟩, fun _ => ⟨2⟩⟩
/-- Oscillator B: `m = 5`, `ω = 4`. -/
noncomputable def oscB : DimOscillator 1 := ⟨⟨5⟩, fun _ => ⟨4⟩⟩

/-- The Hamiltonian's potential coefficient `½ m ω²`. -/
noncomputable def potentialCoeff (m : WithDim Dim.mass ℝ) (ω : WithDim angularFrequency ℝ) :
    WithDim springConstant ℝ :=
  WithDim.cast (m * (ω * ω)) (by decide)

/-- **MR7 fails.** A's mass and B's angular frequency, combined. Dimensionally impeccable,
unit-covariant, and about no physical system whatsoever. -/
noncomputable example : WithDim springConstant ℝ := potentialCoeff oscA.m (oscB.ω 0)

/-- **MR7 fails, at the type level.** The two masses inhabit one type — the same
`rfl` that made MR4 fail. -/
example : (oscA.m : WithDim Dim.mass ℝ) = oscA.m ∧
    (oscB.m : WithDim Dim.mass ℝ) = oscB.m := ⟨rfl, rfl⟩

/-! ## MR8 ❌ — licensed aggregation

MR8 is two-sided: the total mass of the pair *is* `m_A + m_B`, and the pair's angular
frequency *is not* `ω_A + ω_B`. Attempt 2 accepts both, by the same `Add (WithDim d M)`
instance, because extensivity is not a property of a dimension. -/

/-- The total mass — correct, and accepted. -/
noncomputable def totalMass : WithDim Dim.mass ℝ := oscA.m + oscB.m

theorem totalMass_val : totalMass.val = 8 := by norm_num [totalMass, oscA, oscB]

/-- **MR8 fails.** The identical syntax at the identical instance produces the frequency
"sum", which is not the pair's normal-mode frequency (`ω₊ = 5`) nor anything else. -/
noncomputable def frequencySum : WithDim angularFrequency ℝ := oscA.ω 0 + oscB.ω 0

theorem frequencySum_is_not_a_normal_mode : frequencySum.val ≠ 5 := by
  norm_num [frequencySum, oscA, oscB]

/-- **The point of MR8, in one statement.** Two additions, one instance, one dimension
argument, one type — and one of them is physics while the other is noise. Nothing available
at this layer distinguishes them, because extensivity is a property of the *kind*, and there
is no kind here. -/
theorem mr8_the_point : totalMass.val = 8 ∧ frequencySum.val ≠ 5 :=
  ⟨totalMass_val, frequencySum_is_not_a_normal_mode⟩

/-! ## MR9 ❌ — whole-system quantities

The coupling constant belongs to the *pair*, through the component `A↔B`. It has the
dimension of a spring constant, so at this layer it is indistinguishable from either
oscillator's own spring constant. And the normal-mode frequencies share `T⁻¹` with the bare
ones. -/

/-- The coupling spring constant — a property of neither oscillator. -/
noncomputable def kCoupling : WithDim springConstant ℝ := ⟨6⟩
/-- The upper normal-mode angular frequency of the coupled pair. -/
noncomputable def ωPlus : WithDim angularFrequency ℝ := ⟨5⟩

/-- **MR9 fails.** The normal-mode frequency, substituted for a bare one, in a formula that
requires the bare one. Same type; nothing to report. -/
noncomputable example : WithDim springConstant ℝ := potentialCoeff oscA.m ωPlus

/-- **MR9 fails, symmetrically.** The coupling constant, substituted for oscillator A's own
spring constant. Same dimension `M·T⁻²`, same type. -/
noncomputable example : WithDim springConstant ℝ :=
  kCoupling + potentialCoeff oscA.m (oscA.ω 0)

/-! ## The diagnosis

Every Tier-2 and Tier-3 failure above is one fact seen from a different angle, and it is
worth stating as a theorem rather than as a remark: **`WithDim`'s only discrimination is
equality of dimensions.** When `d₁ = d₂`, the two quantity types are equal by `rfl`, so no
predicate, instance, coercion or future lemma can separate their inhabitants at this layer.
PhysLib itself records the consequence in
`WithDim.scaleUnit_val_eq_scaleUnit_val_of_dim_eq`: equal dimensions make two quantities
interchangeable under unit scaling.

This is not a defect. It is what a dimension *is* — the free commutative group on the base
quantities — and it is exactly what makes MR1–MR3 and MR10 come out so cleanly. The
conclusion is only that something has to sit above it. -/

/-- **The diagnosis, as a theorem.** Equal dimensions give equal quantity types, hence
mutual substitutability. Instantiate it at `frequency`/`angularFrequency` (MR4), at A's and
B's masses (MR7), or at a bare and a normal-mode frequency (MR9): one lemma, three
requirements failed. -/
theorem withDim_discriminates_only_dimension
    {d₁ d₂ : Dimension LTMCTDimensionBase} (h : d₁ = d₂) (M : Type) :
    WithDim d₁ M = WithDim d₂ M := by rw [h]

/-- Instantiated at the rad/s trap. -/
theorem mr4_is_the_diagnosis (M : Type) : WithDim frequency M = WithDim angularFrequency M :=
  withDim_discriminates_only_dimension rfl M

/-! # Tier 4 — ergonomics (MR11 ⚠️, MR12 ❌)

What the dimension index costs to write, and what a reader gets back. -/

namespace Tier4

/-! ## MR11 ⚠️ — three frictions, and a fourth found by writing this

  1. **No exponent.** `ω²` must be written `ω * ω`, because `HPow` on `WithDim` would have to
     compute `d ^ n` in the dimension index and there is no such instance.
  2. **A cast at every naming.** `HMul` lands the result at the *structural* dimension
     `Dim.mass * (angularFrequency * angularFrequency) * …`, never at the author's *named*
     dimension `Dim.energy`, so every definition that wants a named result type ends in a
     `WithDim.cast` whose obligation is discharged by a tactic.
  3. **The coefficient problem.** A leading `½` needs `(2⁻¹ : ℝ≥0) • _`, mixing a scalar
     action into an otherwise multiplicative expression.

The fourth was found by writing the file rather than by arguing about it: at five factors the
cast obligation **exceeds the elaborator's default heartbeat limit**, in both of the obvious
discharges (`by decide` and `WithDim.cast`'s own default `by ext <;> {simp; try ring}`). It
has to be hoisted into a named `def` for the dimension and a standalone lemma with the budget
raised. Discharging a dimension equation is not free at realistic formula sizes, and a real
model has expressions far larger than five factors.

Against all that: the signature now says what the arguments are, which is the MR10 win, and
the cost is one cast per *named result* rather than one per operation. -/

/-- The structural dimension of `m·ω²·x²`, named so the obligation can be discharged once. -/
def energyDim : Dimension LTMCTDimensionBase :=
  Dim.mass * (angularFrequency * angularFrequency) * (Dim.length * Dim.length)

set_option maxHeartbeats 1000000 in
/-- `M · T⁻² · L² = M·L²·T⁻²` — the energy dimension, computed. Needs a raised heartbeat
budget, which is the point of the note above. -/
theorem energyDim_eq : energyDim = Dim.energy := by decide

/-- **MR11 is ⚠️.** 1 named dimension + 1 lemma + 1 cast; `ω²` spelled out as `ω * ω`. The
operators survive, which is what keeps this from being ❌. -/
noncomputable def energyWithDim (m : WithDim Dim.mass ℝ)
    (ω : WithDim angularFrequency ℝ) (x : WithDim Dim.length ℝ) :
    WithDim Dim.energy ℝ :=
  WithDim.cast (m * (ω * ω) * (x * x)) energyDim_eq

/-! ## MR12 ❌ — rendering

There is no rendering machinery, so the reader gets Lean's pretty-printer — and unlike attempt
1, what it prints is not the formula. `WithDim.cast (m * (ω * ω) * (x * x)) energyDim_eq`
carries the cast and its proof term into the output, and the *type* carries a dimension
expression that is itself several lines. The noise grows with the safety, which is the exact
shape of the ergonomic objection the PR thread raises. -/

end Tier4

/-! # Tier 5 — computation (MR13 ❌, MR14 ❌, MR15 ❌)

`WithDim d M` *is* parametric in `M` — but only for the **additive** structure. The
multiplicative instances are declared at `M = ℝ` and nowhere else (`HMul (WithDim d₁ ℝ)
(WithDim d₂ ℝ) …`, `HDiv` likewise), and `dimScale` lands in `ℝ≥0`.

PhysLib states this itself in `Physlib/Units/Basic.lean`, without being asked, when comparing
itself to other Lean unit libraries: those "allow for or work in Floats, allowing computability
and the use of `#eval`. This is currently not possible with the more theoretical implementation
here in Physlib which is based exclusively on Reals." The probes below are that sentence,
mechanized. -/

namespace Tier5

/-- `WithDim` over `Float` *adds* — the additive instances are generic in the carrier. -/
example (a b : WithDim Dim.mass Float) : WithDim Dim.mass Float := a + b

/-! **MR13 fails.** But it does not *multiply*: `HMul` exists only at `ℝ`, so no derived
quantity — no `ξ`, no Hamiltonian coefficient, no impedance — can be formed over an executable
carrier. A model that cannot form a product is not a model. -/
#check_failure (fun (m : WithDim Dim.mass Float) (ω : WithDim angularFrequency Float) => m * ω)

/-! **MR13 fails.** Nor is there a unit-scale factor over a non-`ℝ` carrier, so the MR3 win
does not travel either. -/
#check_failure (fun (u₁ u₂ : LTMCTUnitChoices) (m : WithDim Dim.mass Float) =>
  UnitDependent.scaleUnit u₁ u₂ m)

/-! ## MR14 ❌ — complex-valued quantities

`WithDim d ℂ` can *hold* a complex value — the additive instances are generic — but cannot
*compute* with one, for exactly the reason `Float` failed. A complex impedance can be stored
and not combined. -/

/-- Held: the additive structure is carrier-generic. -/
noncomputable example (a b : WithDim Dim.mass ℂ) : WithDim Dim.mass ℂ := a + b

/-- The impedance `Z = 3 + 4i`, at its own dimension `M·T⁻¹`. Storing it is fine. -/
noncomputable def Z : WithDim springConstant ℂ := ⟨⟨3, 4⟩⟩

/-! **MR14 fails.** Not combined: there is no `HMul` at a complex carrier, so `Z²` — the first
thing anyone does with an impedance — cannot be formed. -/
#check_failure (fun (a b : WithDim Dim.mass ℂ) => a * b)

/-! ## MR15 ❌ — exec/spec agreement

With a single usable carrier there is no exec/spec distinction, hence no bridge to build and
no gap to name. As with attempt 1, that is not a defence. -/

end Tier5

/-! # Tier 6 — geometry (MR16 ❌, MR17 ⚠️, MR18 ❌, MR19 ❌)

This tier is where the dimension layer's structural limit is clearest, because the limit is
not an omission — it is what a dimension *is*. A `Dimension B` is an element of a free
commutative group on the base quantities. Everything it can distinguish is a difference of
exponent vectors, and none of the four requirements below is one. -/

namespace Tier6

/-! ## MR16 ❌ — a carrier morphism can change the dimension

`WithDim` has no `castCarrier`, so a change of representation is written by hand — projecting
`.val`, applying the function, and re-wrapping. The re-wrap is where the dimension is chosen,
and nothing connects it to the dimension that was projected out. -/

/-- An honest representation change: a mass in `ℝ`, embedded in `ℂ`. -/
noncomputable def massToComplex (m : WithDim Dim.mass ℝ) : WithDim Dim.mass ℂ := ⟨m.val⟩

/-- **MR16 fails.** The same hand-written shape, re-wrapped at a *different dimension*. This
is not a coercion that could be audited and it is not a cast with a proof obligation — it is
the only way `WithDim` offers to change a carrier, used with one character different. -/
noncomputable def massToComplexWrong (m : WithDim Dim.mass ℝ) : WithDim Dim.energy ℂ :=
  ⟨m.val⟩

/-- **MR16 fails, stated.** Both elaborate, and they differ only in the dimension the author
wrote in the return type — which is an annotation again, exactly the thing MR2 was won by
avoiding. The Tier-1 guarantee does not extend across a change of carrier because there is no
operation to attach it to. -/
theorem carrier_change_is_unconstrained (m : WithDim Dim.mass ℝ) :
    (massToComplex m).val = (massToComplexWrong m).val := rfl

/-! ## MR17 ⚠️ — a vector quantity, held but not combined

`WithDim d M` is generic in `M`, so `WithDim Dim.length (Fin 2 → ℝ)` is a well-formed type and
it is the right *shape* for ISO 80000-2 §18: a numerical array under one dimension. The
additive instances even work. That is genuinely more than attempt 1 offers, which is why this
is ⚠️ rather than ❌. -/

/-- **MR17, the half that works.** A velocity in the plane, `(3, 4)`, as one dimensioned
quantity over a numerical-array carrier. -/
noncomputable def vA : WithDim (Dim.length * Dim.time⁻¹) (Fin 2 → ℝ) := ⟨![3, 4]⟩

/-- And it adds, generically in the carrier. -/
noncomputable example (u v : WithDim (Dim.length * Dim.time⁻¹) (Fin 2 → ℝ)) :
    WithDim (Dim.length * Dim.time⁻¹) (Fin 2 → ℝ) := u + v

/-! **MR17 fails on the other half**, and for Tier 5's reason rather than a new one: `HMul` is
declared at `M = ℝ`, so *no* product of vector quantities can be formed at all — not the
pointwise one attempt 1 wrongly allowed, and not the scalar product either. The gate here is
accidental. It refuses the meaningless operation and the meaningful one together, by refusing
to multiply anything that is not a real number, which is over-rejection in the sense MR8's
two-sidedness was written to catch. -/
#check_failure (fun (u v : WithDim (Dim.length * Dim.time⁻¹) (Fin 2 → ℝ)) => u * v)

/-! And there is no scalar-product operation to reach for instead: a contraction takes two
array-carried quantities to a *scalar*-carried one at the product dimension, and `WithDim`
has no operation of that shape, at any carrier. -/

/-! ## MR18 ❌ — the frame is not a dimension

A change of frame acts on components and is **dimension-blind**: position, velocity, force and
field all turn by the same matrix, and their dimensions have no bearing on it. A unit change,
by contrast, is *computed from* the dimension — which is exactly why attempt 2 wins MR3 and
cannot even state MR18.

There is no index left to put a frame in. `WithDim d M` has two, and both are taken. -/

/-- The Pythagorean rotation, written the only way available: on the raw components. -/
noncomputable def turn (v : Fin 2 → ℝ) : Fin 2 → ℝ :=
  ![3/5 * v 0 - 4/5 * v 1, 4/5 * v 0 + 3/5 * v 1]

/-- Lifted to a dimensioned quantity — note that the dimension is carried along untouched,
which is correct, and that nothing else is. -/
noncomputable def turnQ {d : Dimension LTMCTDimensionBase}
    (v : WithDim d (Fin 2 → ℝ)) : WithDim d (Fin 2 → ℝ) := ⟨turn v.val⟩

/-- **MR18 fails.** `turnQ` is generic in `d` — as it must be, since a rotation does not care
about dimensions — and therefore applies to *every* array-carried quantity, including ones
that are not vectors at all. -/
noncomputable def masses : WithDim Dim.mass (Fin 2 → ℝ) := ⟨![3, 5]⟩

noncomputable example : WithDim Dim.mass (Fin 2 → ℝ) := turnQ masses

/-- And it destroys them: `3` becomes `-11/5`. The dimension `M` is preserved perfectly
throughout, which is the point — the dimension was never the thing at risk. -/
theorem rotating_masses_is_nonsense : (turnQ masses).val 0 ≠ masses.val 0 := by
  simp [turnQ, turn, masses]
  norm_num

/-- **MR18 fails, the mixing half.** Two readings of one velocity in two different frames have
the same dimension, hence the same type, hence add. This is
`withDim_discriminates_only_dimension` again, on a new axis: the frame is not a dimension, so
the layer cannot see it. -/
noncomputable example : WithDim (Dim.length * Dim.time⁻¹) (Fin 2 → ℝ) := vA + turnQ vA

/-! ## MR19 ❌ — an indexed family is not a vector

The two `Fin d → ℝ`s of `DimOscillator` — the frequency family and a position — now differ in
dimension, which is more than attempt 1 managed. It is still not the distinction MR19 asks
for, because the distinction MR19 asks for is between two *transformation laws*, and two
quantities of the same dimension can have different ones while two of different dimensions can
share one. -/

/-- The anisotropic oscillator's frequencies, `(2, 7)`, as one array-carried quantity. -/
noncomputable def omegas : WithDim angularFrequency (Fin 2 → ℝ) := ⟨![2, 7]⟩

/-- **MR19 fails.** `turnQ` applies, because it is generic in the dimension and a frequency
family has a dimension like anything else. The result is `(-22/5, 29/5)` — not the frequencies
of any oscillator in any frame, since what a rotation actually does to a diagonal rank-2 object
is produce off-diagonal terms, and there is nowhere here to put them. -/
theorem rotating_frequencies_is_nonsense : (turnQ omegas).val 0 ≠ omegas.val 0 := by
  simp [turnQ, turn, omegas]
  norm_num

/-- **MR19, the capstone — and the tier's diagnosis.** A velocity and a frequency family have
*different* dimensions and the *same* fate under `turnQ`; a velocity and a rotated velocity
have the *same* dimension and are not interchangeable. Both halves say the variance is
independent of the dimension, so no refinement of the dimension basis reaches it — which is
the Tier-6 form of `withDim_discriminates_only_dimension`, and the reason attempt 3's tagging
trick will not help here either. -/
theorem mr19_capstone :
    (turnQ masses).val 0 ≠ masses.val 0
      ∧ (turnQ omegas).val 0 ≠ omegas.val 0
      ∧ WithDim (Dim.length * Dim.time⁻¹) (Fin 2 → ℝ)
          = WithDim (Dim.length * Dim.time⁻¹) (Fin 2 → ℝ) :=
  ⟨rotating_masses_is_nonsense, rotating_frequencies_is_nonsense, rfl⟩

end Tier6

/-! ## MR32 ❌ — specialization keeps kinds comparable (appended)

Appended after the first scoring pass; see `Attempt1Reals` for the occasion. Dimension is
the only discrimination `WithDim` has, and the whole family shares `M·L²·T⁻²` — so kinetic,
potential and total energy inhabit *one type*, the sum is licensed for the wrong reason
(indistinguishability, not specialization), and a consumer of the potential accepts the
kinetic. The same verdict as MR4, landing on the requirement MR4 does not state: the family
is supposed to stay *comparable* while its members stay *apart*, and `WithDim` can only
have one or the other. -/

section MR32

/-- `H = T + V` — writable, but by collapse: both are `WithDim Dim.energy ℝ`. -/
noncomputable example (T V : WithDim Dim.energy ℝ) : WithDim Dim.energy ℝ := T + V

/-- A consumer that means the *potential* energy… -/
def expectsPotential (V : WithDim Dim.energy ℝ) : WithDim Dim.energy ℝ := V

/-- …accepts the kinetic, exactly as in Attempt 1. -/
example (T : WithDim Dim.energy ℝ) : WithDim Dim.energy ℝ := expectsPotential T

end MR32

end PropertyKindCalculus.Examples.HarmonicOscillator.Attempt2
