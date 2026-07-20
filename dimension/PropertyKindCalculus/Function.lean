/-
# The function calculus, dimensioned — coherence, the trigonometric algebra, and levels

`PropertyKindCalculus.QuantityFunction` (core) gives the carrier capability
(`MathCarrier`) and the kind-relations for functions, gated only on the ratio-scale
precondition the Mathlib-free core can express. This module adds the *dimensional*
content those relations carry — exactly as `Interaction` refines `ProductKind` with the
dimensional homomorphism:

  * the **ℝ instances** of `MathCarrier` / `MathCarrierExt` / `LawfulMathCarrier` — the
    proof carrier, where the function identities (`sin²+cos²=1`, `exp(a+b)=exp a·exp b`,
    …) actually hold;
  * **Family B (powers/roots):** the exponent-scaling certificate `dim k = (dim k₁)^p`,
    using PhysLib's `Pow Dimension ℚ` — `sqrt` of an area is a length, *checked*;
  * **Family C (transcendentals):** the argument and result are dimension one;
  * **Family D (trigonometric):** a *curated* algebra (`TrigAlgebra`, the unary analogue
    of `InteractionAlgebra`) keeping `sin` on angles only — `sin reflectivity` is a
    category error a dimension-only system cannot forbid, the dimension-1 disambiguation
    applied to functions;
  * **Family E (logarithmic levels):** `log` of a ratio demotes ratio-scale to
    interval-scale, so the multiplicative calculus *refuses* a level — the function layer
    meeting the scale layer;
  * a coda: the **ISO/IEC 80000-11 characteristic numbers** (Reynolds vs Mach) as
    distinct dimension-one *kinds* built from the existing `QuotientKind` — showing why a
    characteristic number is a kind, not a carrier constant like `pi`.

It builds on PhysLib (`lake build Dimension`); the core spine stays Mathlib-free.
-/
import PropertyKindCalculus.Dimension
import PropertyKindCalculus.Interaction
import PropertyKindCalculus.QuantityFunction
import PropertyKindCalculus.Complex
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Algebra.Order.Round

open Dimension

namespace PropertyKindCalculus

/-! ## The ℝ carrier — the proof representation for the function layer

The same `MathCarrier` surface, realized at `ℝ` with Mathlib's special functions. `ℝ`
is the carrier where the function *laws* hold, so it carries `LawfulMathCarrier` as well
— the function-layer analogue of `Quantity`'s lawful `ℝ` carrier in `QuantityReal`. -/

/-- `ℝ` is a function carrier (the proof representation). Noncomputable, like the real
special functions it forwards to. -/
noncomputable instance instMathCarrierReal : MathCarrier ℝ where
  exp := Real.exp
  log := Real.log
  sin := Real.sin
  cos := Real.cos
  sinh := Real.sinh
  cosh := Real.cosh
  tanh := Real.tanh
  sqrt := Real.sqrt
  abs := fun x => |x|
  pi := Real.pi

/-- `ℝ` supports the extended surface. `atan2` is the principal-branch `arctan (y/x)`
here (the spec carrier); the executable `Float` carrier supplies the true quadrant-aware
`atan2`. -/
noncomputable instance instMathCarrierExtReal : MathCarrierExt ℝ where
  toMathCarrier := instMathCarrierReal
  tan := Real.tan
  asin := Real.arcsin
  acos := Real.arccos
  atan := Real.arctan
  atan2 := fun y x => Real.arctan (y / x)
  cbrt := fun x => Real.rpow x (1 / 3)
  floor := fun x => (⌊x⌋ : ℝ)
  ceil := fun x => (⌈x⌉ : ℝ)
  round := fun x => ((round x : ℤ) : ℝ)
  rpow := fun x q => Real.rpow x (q : ℝ)

/-- **`ℝ` is a lawful function carrier.** The function identities are exactly the
Mathlib special-function lemmas, so a function-layer law proved over an arbitrary
`LawfulMathCarrier` holds verbatim at `ℝ`. The very carrier where these *fail* — an
executable float — is what the exec/spec refinement bridge exists to reconcile. -/
noncomputable instance instLawfulMathCarrierReal : LawfulMathCarrier ℝ where
  toMathCarrier := instMathCarrierReal
  exp_zero := Real.exp_zero
  exp_add := Real.exp_add
  log_exp := Real.log_exp
  sin_zero := Real.sin_zero
  cos_zero := Real.cos_zero
  sin_sq_add_cos_sq := fun a => by
    have h := Real.sin_sq_add_cos_sq a; rw [pow_two, pow_two] at h; exact h
  cosh_sq_sub_sinh_sq := fun a => by
    have h := Real.cosh_sq_sub_sinh_sq a; rw [pow_two, pow_two] at h; exact h
  sq_sqrt := fun _ h => by
    have h' := Real.sq_sqrt h; rw [pow_two] at h'; exact h'
  tanh_zero := Real.tanh_zero
  abs_zero := abs_zero

/-- **`ℝ` decides negativity** — the branch-cut capability of the complex carrier
(`Complex.NegTest`), at the proof representation. Classical (hence noncomputable), like
`ℝ`'s order: the principal complex square root branches on `sign(im)`, and at `ℝ` that
decision is the classical `x < 0`. The executable `Float` instance (computable) lives in
the core `Complex` module. -/
noncomputable instance instNegTestReal : Complex.NegTest ℝ where
  isNeg x := decide (x < 0)

/-! ## Family B — the power coherence (`dim k = (dim k₁)^p`)

The `Dimension`-level refinement of `PowerKind`: forgetting a power to the dimension
layer *scales* the dimension by the rational exponent. This is the one function family
that is dimensionful — and it is well-defined precisely because PhysLib's `Dimension`
carries ℚ exponents (`Pow Dimension ℚ`), so a half-power is a genuine group element. -/

/-- **The dimensional power law.** `b` is the `p`-th power of `a` at the dimension level:
its dimension is `a`'s scaled by `p`. The `Dimension`-layer strengthening of the core
`PowerKind`'s ratio-scale gate. -/
def DimPowerKind (p : Rat) (a b : DimensionedKind) : Prop :=
  b.dim = a.dim ^ p

/-- **Coherence.** A dimensional power forgets to the scaled dimension — the
function-layer analogue of `dim_homomorphism`. -/
theorem DimPowerKind.toDimension_eq {p : Rat} {a b : DimensionedKind}
    (h : DimPowerKind p a b) : b.toDimension = a.toDimension ^ p := h

/-- Area, a dimensionful ratio kind (`L²`) — the worked base for the half-power. -/
def areaK : DimensionedKind :=
  { kind := { id := "area", scale := .ratio }, dim := Dim.area }

/-- **`sqrt` of an area is a length — checked, not annotated.** The half-power of the
area dimension `L²` is the length dimension `L`: `dim(√area) = (dim area)^(1/2) = L`.
This is the certificate the core `Quantity.sqrt` carries, here discharged in the
`Dimension` group. -/
theorem sqrt_area_coherent : DimPowerKind (1 / 2) areaK lengthKind := by
  show lengthKind.dim = areaK.dim ^ (1 / 2 : Rat)
  ext b
  simp only [lengthKind, areaK, Dim.length, Dim.area, Dimension.qpow_exponent,
    Dimension.mul_exponent]
  ring

/-! ## Family C — transcendentals are dimension-one in, dimension-one out

`exp x = Σ xⁿ/n!` is dimensionally homogeneous only when `x` is a pure number, so a
transcendental takes a dimension-one argument and returns a dimension-one result. -/

/-- **The dimensional transcendental law.** A transcendental edge is coherent exactly
when argument and result are both dimension one. -/
def DimTranscendental (a b : DimensionedKind) : Prop :=
  a.toDimension = 1 ∧ b.toDimension = 1

/-- Loss tangent (`σ/ωε₀`), a dimension-one ratio kind — the kind of argument a
transcendental legitimately takes (the dipolar/conductive loss of a Debye dielectric). -/
def lossTangentK : DimensionedKind :=
  { kind := { id := "loss tangent", scale := .ratio }, dim := 1 }

/-- A pure number, dimension one — the result kind of a transcendental. -/
def numberK : DimensionedKind :=
  { kind := { id := "number", scale := .ratio }, dim := 1 }

/-- **`tanh` of a loss tangent is a number — both dimension one.** A worked
transcendental edge: the conductive-loss `tanh` argument is dimensionless and so is its
value. -/
theorem tanh_lossTangent_coherent : DimTranscendental lossTangentK numberK :=
  ⟨rfl, rfl⟩

/-! ## Family D — the curated trigonometric algebra (the function-layer disambiguation)

A plane angle is dimension one but a *distinct kind*. `sin` of an angle is sanctioned;
`sin` of a reflectivity is a category error. A dimension-only system calls both
arguments `dim = 1` and cannot tell them apart — so the discipline must be *curated*,
exactly like `InteractionAlgebra` curates the sanctioned products. This is the unary
analogue: a partial relation over `(function, argument-kind, result-kind)` with the
dimension-one coherence obligation. -/

/-- The trigonometric functions, as tags for the curated algebra. -/
inductive TrigFn
  | sin | cos | tan | asin | acos | atan
  deriving DecidableEq, Repr

/-- A curated **trigonometric algebra**: which `(f, argument-kind, result-kind)` edges
are sanctioned, with the R7-style obligation that every sanctioned edge is dimension one
on both sides. The unary, function-layer analogue of `InteractionAlgebra`. -/
structure TrigAlgebra where
  /-- The sanctioned trigonometric edges: `TFn f a b` reads "`f` maps a `a` to a `b`". -/
  TFn : TrigFn → DimensionedKind → DimensionedKind → Prop
  /-- **Coherence.** Every sanctioned trigonometric edge is dimension one on both sides
  (a transcendental takes and returns dimension one). -/
  tFn_coherent : ∀ {f a b}, TFn f a b → a.toDimension = 1 ∧ b.toDimension = 1

/-- The sanctioned trigonometric edges of SI: `sin`/`cos`/`tan` take a plane angle to a
number; `asin`/`acos`/`atan` take a number to a plane angle. *Absent* by construction:
`sin` of any non-angle dimension-one kind (a reflectivity, a loss tangent). -/
inductive SITrig : TrigFn → DimensionedKind → DimensionedKind → Prop
  /-- `sin : angle → number`. -/
  | sin  : SITrig .sin  angleKind numberK
  /-- `cos : angle → number`. -/
  | cos  : SITrig .cos  angleKind numberK
  /-- `tan : angle → number`. -/
  | tan  : SITrig .tan  angleKind numberK
  /-- `asin : number → angle`. -/
  | asin : SITrig .asin numberK angleKind
  /-- `acos : number → angle`. -/
  | acos : SITrig .acos numberK angleKind
  /-- `atan : number → angle`. -/
  | atan : SITrig .atan numberK angleKind

/-- Every sanctioned SI trigonometric edge is dimension one on both sides (R7). -/
theorem SITrig.coherent {f a b} (h : SITrig f a b) :
    a.toDimension = 1 ∧ b.toDimension = 1 := by
  cases h <;> exact ⟨rfl, rfl⟩

/-- The SI trigonometric algebra packaged as a coherent `TrigAlgebra`. -/
def siTrig : TrigAlgebra where
  TFn := SITrig
  tFn_coherent := SITrig.coherent

/-- **The dimension-1 disambiguation, for functions.** `sin` is sanctioned on a plane
angle and yields a number; angle and number are *distinct kinds* though both forget to
dimension one. A dimension-only type system identifies the two; the kind layer keeps
them apart, and the curated algebra is what makes `sin` accept the angle. -/
theorem sin_angle_is_number :
    siTrig.TFn .sin angleKind numberK
      ∧ angleKind.kind ≠ numberK.kind
      ∧ angleKind.toDimension = numberK.toDimension :=
  ⟨SITrig.sin, by decide, rfl⟩

/-- The argument of any sanctioned `sin` edge must be the plane-angle kind (the first
index is free here, so dependent elimination succeeds — unlike pinning it to a concrete
non-angle kind). -/
theorem SITrig.sin_arg {a b : DimensionedKind} (h : SITrig .sin a b) : a = angleKind := by
  cases h; rfl

/-- **The showpiece.** `sin` of a *reflectivity* is **not** sanctioned — a category
error — even though reflectivity is dimension one, exactly like an angle. This is the
forbidden application a dimension-only system would wave through; the curated trig
algebra refuses it by construction. -/
theorem sin_reflectivity_not_sanctioned :
    ¬ siTrig.TFn .sin reflectivity numberK := by
  intro h
  have h' : SITrig .sin reflectivity numberK := h
  have hk : reflectivity.kind = angleKind.kind :=
    congrArg DimensionedKind.kind (SITrig.sin_arg h')
  exact absurd hk (by decide)

/-! ## Family E — logarithmic levels (the function layer meets the scale layer)

A logarithmic level (decibel, neper, pH) is `log` of a ratio. It is dimension one, but
its *scale* is only interval, not ratio: you may subtract two levels (a dB difference)
but you may not multiply them. The multiplicative calculus must therefore *refuse* a
level — and it does, because `ProductKind`/`PowerKind` require every operand ratio-scale,
which a level is not. -/

/-- A sound pressure level (dB): dimension one, but **interval**-scale — `log` of a
pressure ratio. -/
def soundPressureLevelK : DimensionedKind :=
  { kind := { id := "sound pressure level", scale := .interval }, dim := 1 }

/-- A level is dimension one. -/
theorem level_dimensionless : soundPressureLevelK.toDimension = 1 := rfl

/-- ...yet **not ratio-scale** — `log` demoted it from the ratio-scale pressure ratio to
the interval-scale level. -/
theorem level_not_rational : ¬ soundPressureLevelK.kind.IsRational := by
  show ¬ soundPressureLevelK.kind.scale = ScaleType.ratio
  decide

/-- **The multiplicative calculus refuses a level.** There is no product kind with a
level as a factor: `ProductKind` requires every factor ratio-scale (Dybkær §13.3.5), and
a level is only interval-scale. (Levels may still be *added* — `Quantity.add` is
kind-gated, not scale-gated — which is exactly right: a dB difference is meaningful, a dB
product is not.) -/
theorem level_no_product {k₂ k : KindOfProperty} :
    ¬ ProductKind soundPressureLevelK.kind k₂ k :=
  fun h => level_not_rational h.ratio₁

/-- And no power either, for the same reason. -/
theorem level_no_power {p : Rat} {k : KindOfProperty} :
    ¬ PowerKind p soundPressureLevelK.kind k :=
  fun h => level_not_rational h.ratio₁

/-! ## Coda — ISO/IEC 80000-11 characteristic numbers are *kinds*, not constants

A carrier constant like `pi` is a fixed magnitude in the representation `R`, below the
kind layer. A *characteristic number* (Reynolds, Mach, …) is the opposite: a
dimension-one *kind of quantity*, formed by the quotient calculus from dimensioned
quantities so that the dimensions cancel to one. Two characteristic numbers are distinct
kinds even though both forget to dimension one — so a Reynolds number is never a Mach
number, the `vwc`/`gwc` disambiguation once more. Crucially this needs **no new
machinery**: it is built from the existing `QuotientKind`. -/

/-- Reynolds number — a dimension-one ratio kind (`ρvL/μ`, inertial over viscous
forces). -/
def reynoldsK : DimensionedKind :=
  { kind := { id := "Reynolds number", scale := .ratio }, dim := 1 }

/-- Mach number — a dimension-one ratio kind (flow speed over speed of sound). -/
def machK : DimensionedKind :=
  { kind := { id := "Mach number", scale := .ratio }, dim := 1 }

/-- **A characteristic number is a kind, not a constant.** Reynolds and Mach are
*distinct kinds* though both forget to dimension one — a dimension-only system identifies
them, the kind layer keeps them apart. Unlike `MathCarrier.pi` (a fixed magnitude in the
carrier), each is a variable quantity formed by the quotient calculus; the value of a
Reynolds number is whatever `ρvL/μ` produces in a given flow. -/
theorem reynolds_ne_mach_but_both_dimensionless :
    reynoldsK.kind ≠ machK.kind
      ∧ reynoldsK.toDimension = 1 ∧ machK.toDimension = 1 :=
  ⟨by decide, rfl, rfl⟩

end PropertyKindCalculus
