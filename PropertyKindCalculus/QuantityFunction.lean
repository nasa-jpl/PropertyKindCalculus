/-
# Functions on quantities — the kind-tracked function calculus (R12, function layer)

The product / quotient / reciprocal calculus (`QuantityClassification`) covers the
*algebraic* defining relations of the ISQ. Scientific models also apply *functions*
to quantities — roots, exponentials, logarithms, the trigonometric functions — and
each carries its own metrological discipline. This module adds that layer, reusing
the same three-part pattern (kind-relation · smart constructor · coherence) the
algebraic calculus uses, and grouping the functions into the six families that have
genuinely different kind signatures:

  * **A — kind-preserving** (`abs`, `neg`, `min`, `max`, `clamp`, `floor`, `ceil`,
    `round`): `k → k`. `|length|` is a length; `min`/`max`/`clamp` are *same-kind*
    binary, the gate being the shared kind index (exactly as for `Quantity.add`). No
    kind-relation is needed — the type *is* the certificate.
  * **B — powers / roots** (`sqrt`, `cbrt`, `x^(p/q)`): a `PowerKind p` relation; the
    dimension *scales* by `p` (`dim k = (dim k₁)^p`, certified in the `Dimension`
    layer, where PhysLib's `Pow Dimension ℚ` makes a half-power well-defined). The one
    family that is **not** dimension-one-in/out — the dimension-scaling extension of
    `mul`/`div`.
  * **C — dimensionless transcendentals** (`exp`, `log`, `sinh`, `cosh`, `tanh`): a
    `TranscendentalKind` relation; the argument must be of dimension one and so is the
    result (`exp x = Σ xⁿ/n!` is only homogeneous when `x` is a pure number).
  * **D — trigonometric** (`sin`/`cos`/`tan`, `asin`/`acos`/`atan`, `atan2`): the
    showcase. A plane angle is *dimension one but a distinct kind* — `sin` of an angle
    is fine, `sin` of a reflectivity is a category error a dimension-only system cannot
    forbid. The kind discipline is curated in the `Dimension` layer (an analogue of the
    interaction algebra); the core records the ratio-scale gate and the constructors.
  * **E — logarithmic levels** (dB, neper, pH): `log` of a ratio lands in an
    *interval-scale* kind, not a ratio-scale one (you can subtract decibels but not
    multiply them) — so the product/power calculus *correctly refuses* it. This is the
    family where the function layer talks to the **scale** layer (`ScaleType`), realized
    in the `Dimension` examples.
  * **F — re-expression against another reference** (degree/radian, metre/foot): a
    `ReferenceKind` relation. The one family that computes nothing — the quantity is
    unchanged and only the reference its number counts against moves, so the conversion
    is carried by one and the same quantity written in both references. Ratio-scale only:
    an interval scale's reference carries an offset a ratio cannot express.

## Carrier capability

The algebraic calculus rides on the toolchain classes `Mul`/`Div`/`Inv`. There is no
toolchain class for `exp`/`sin`/`sqrt`, so the one genuinely new artifact is a carrier
capability typeclass, mirroring `Carrier`/`LawfulCarrier` exactly:

  * `MathCarrier R` — the operation surface (deliberately the *same* surface as
    TorchLean's `MathFunctions`, so every carrier `MathFunctions` supports — `ℝ`,
    `Float`, `FP32`, `IEEE32Exec` — is a clean `MathCarrier`).
  * `MathCarrierExt R` — the richer surface (`tan`, the inverse trig, `atan2`, `cbrt`,
    rounding, rational `rpow`) that `ℝ` and `Float` support but the binary32 exec
    carrier need not — encoding that the executable carrier has a *smaller* function
    vocabulary than the specification carrier.
  * `LawfulMathCarrier R` — the operations *plus* the identities used in proofs
    (`sin²+cos²=1`, `exp(a+b)=exp a·exp b`, …). These hold at the `ℝ` proof carrier and
    **fail** in floating point, so — like `LawfulCarrier` — only the lawful carriers get
    this, and the gap is the same exec/spec refinement the R10 bridge closes.

The dimensional preconditions of families B–E (exponent scaling; argument dimension
one; the curated trigonometric algebra; the scale demotion of levels) are *dimensional*
statements, not expressible in the Mathlib-free core, so — exactly as `InteractionAlgebra`
refines `ProductKind` — they live in `PropertyKindCalculus.Function` in the `Dimension`
layer. Here the relations carry the ratio-scale gate, which *is* core-expressible.
-/

module

public import PropertyKindCalculus.QuantityClassification

public section Interface

namespace PropertyKindCalculus

/-! ## The function carrier (R10, function layer) -/

/-- **The function operation surface.** The transcendental and root operations a
kind-indexed magnitude needs, supplied once per representation type `R`. This is the
function-layer analogue of `Carrier`, and is deliberately the *same* surface as
TorchLean's `MathFunctions α`, so any carrier supporting `MathFunctions` (`ℝ`, `Float`,
binary32) instantiates it cleanly. -/
class MathCarrier (R : Type) where
  /-- Natural exponential. -/
  exp : R → R
  /-- Natural logarithm. -/
  log : R → R
  /-- Sine. -/
  sin : R → R
  /-- Cosine. -/
  cos : R → R
  /-- Hyperbolic sine. -/
  sinh : R → R
  /-- Hyperbolic cosine. -/
  cosh : R → R
  /-- Hyperbolic tangent. -/
  tanh : R → R
  /-- Square root. -/
  sqrt : R → R
  /-- Absolute value. -/
  abs : R → R
  /-- The constant `π`. -/
  pi : R

/-- **The extended function surface.** Operations the proof carrier `ℝ` and the run
carrier `Float` support, but which the binary32 *exec* carrier need not — its function
vocabulary is deliberately smaller. Bundling them in a separate class is what lets the
exec carrier be a `MathCarrier` without being a `MathCarrierExt`. -/
class MathCarrierExt (R : Type) extends MathCarrier R where
  /-- Tangent. -/
  tan : R → R
  /-- Inverse sine (principal value). -/
  asin : R → R
  /-- Inverse cosine (principal value). -/
  acos : R → R
  /-- Inverse tangent (principal value). -/
  atan : R → R
  /-- Two-argument inverse tangent — the angle of `(x, y)`; the two arguments share a
  kind so their ratio is dimensionless. -/
  atan2 : R → R → R
  /-- Cube root. -/
  cbrt : R → R
  /-- Floor. -/
  floor : R → R
  /-- Ceiling. -/
  ceil : R → R
  /-- Round to nearest. -/
  round : R → R
  /-- Rational power `x ^ (p : ℚ)`. -/
  rpow : R → Rat → R

/-- **A lawful function carrier.** A `MathCarrier` whose operations additionally obey
the algebraic identities used in proofs. These hold at `ℝ` (the proof carrier) and
*fail* in floating point (`sin² + cos² = 1` is not a floating-point identity), which is
why an executable carrier is a `MathCarrier` but not a `LawfulMathCarrier` — the same
exec/spec gap `LawfulCarrier` draws for `+`. The arithmetic classes are class
parameters because the identities are stated with the carrier's own `+`, `*`, `-`. -/
class LawfulMathCarrier (R : Type) [Add R] [Sub R] [Mul R] [Zero R] [One R] [LE R]
    extends MathCarrier R where
  /-- `exp 0 = 1`. -/
  exp_zero : exp 0 = 1
  /-- `exp` carries sums to products. -/
  exp_add : ∀ a b : R, exp (a + b) = exp a * exp b
  /-- `log` is a left inverse of `exp`. -/
  log_exp : ∀ a : R, log (exp a) = a
  /-- `sin 0 = 0`. -/
  sin_zero : sin 0 = 0
  /-- `cos 0 = 1`. -/
  cos_zero : cos 0 = 1
  /-- The Pythagorean identity. -/
  sin_sq_add_cos_sq : ∀ a : R, sin a * sin a + cos a * cos a = 1
  /-- The hyperbolic Pythagorean identity. -/
  cosh_sq_sub_sinh_sq : ∀ a : R, cosh a * cosh a - sinh a * sinh a = 1
  /-- `sqrt` is a right inverse of squaring on the nonnegative reals. -/
  sq_sqrt : ∀ a : R, (0 : R) ≤ a → sqrt a * sqrt a = a
  /-- `tanh 0 = 0`. -/
  tanh_zero : tanh 0 = 0
  /-- `abs 0 = 0`. -/
  abs_zero : abs 0 = 0

/-! ## Derived constants

`MathCarrier` carries only `pi` as a *primitive* constant — the one transcendental
constant carriers ship directly (it has no simpler closed form, and TorchLean's
`MathFunctions` provides exactly it). Every other mathematical constant is *derived*
from the operations, so it is a plain definition, not a class field: `e = exp 1`,
`ln 2 = log 2`, `√2 = sqrt 2`, and so on. Adding them as fields would be redundant
machinery — and would force every carrier to re-supply a value the operations already
determine.

This is a different thing entirely from the ISO/IEC 80000-11 *characteristic numbers*
(Reynolds, Mach, Prandtl, …). A constant like `pi` is a **fixed magnitude in the
carrier `R`** — it lives *below* the kind layer, in the representation, and is the same
number in every context. A characteristic number is **not a constant at all**: it is a
dimension-one *kind of quantity*, variable per physical situation, formed by the
quotient calculus from dimensioned quantities (Reynolds `Re = ρvL/μ`, the dimensions
cancelling to one). It lives *above* the carrier, in the kind layer — and, being a
distinct kind, a Reynolds number is never a Mach number even though both forget to
dimension one (the `vwc`/`gwc` disambiguation again). See the `Dimension` layer for the
worked Reynolds-vs-Mach example built entirely from the existing `QuotientKind`. -/

namespace MathCarrier

/-- **Euler's number**, `e = exp 1`. Derived from `exp`, not a primitive carrier field
the way `pi` is — there is no reason to make every carrier re-supply it. -/
def e {R : Type} [MathCarrier R] [One R] : R := MathCarrier.exp 1

end MathCarrier

/-! ## Family A — kind-preserving functions (`k → k`)

These preserve the kind: the result is classified the same as the input, so no
kind-relation is needed — the type `Quantity k R → Quantity k R` is itself the
certificate. `min`/`max`/`clamp` are *same-kind* binary, gated by the shared kind index
exactly as `Quantity.add`. -/

namespace Quantity

/-- Negation (kind-preserving). -/
@[expose] def neg {k : KindOfProperty} {R : Type} [Neg R] (a : Quantity k R) : Quantity k R :=
  ⟨-a.magnitude⟩

/-- Unary `-` on quantities (kind-preserving), the operator-instance counterpart of
`Quantity.neg` — completing the `Add`/`Sub`/`Neg` family begun in the core `Quantity`
module. -/
instance instNeg {k : KindOfProperty} {R : Type} [Neg R] : Neg (Quantity k R) := ⟨Quantity.neg⟩

/-- Absolute value (kind-preserving): `|length|` is a length. -/
@[expose] def abs {k : KindOfProperty} {R : Type} [MathCarrier R] (a : Quantity k R) : Quantity k R :=
  ⟨MathCarrier.abs a.magnitude⟩

/-- Same-kind minimum. -/
@[expose] def min {k : KindOfProperty} {R : Type} [Min R] (a b : Quantity k R) : Quantity k R :=
  ⟨Min.min a.magnitude b.magnitude⟩

/-- Same-kind maximum. -/
@[expose] def max {k : KindOfProperty} {R : Type} [Max R] (a b : Quantity k R) : Quantity k R :=
  ⟨Max.max a.magnitude b.magnitude⟩

/-- Clamp `a` into `[lo, hi]` (all of one kind): `max lo (min hi a)`. The kind index
forbids clamping a reflectivity against a permittivity bound. -/
@[expose] def clamp {k : KindOfProperty} {R : Type} [Min R] [Max R]
    (lo hi a : Quantity k R) : Quantity k R :=
  ⟨Max.max lo.magnitude (Min.min hi.magnitude a.magnitude)⟩

/-- Floor (kind-preserving). -/
@[expose] def floor {k : KindOfProperty} {R : Type} [MathCarrierExt R] (a : Quantity k R) : Quantity k R :=
  ⟨MathCarrierExt.floor a.magnitude⟩

/-- Ceiling (kind-preserving). -/
@[expose] def ceil {k : KindOfProperty} {R : Type} [MathCarrierExt R] (a : Quantity k R) : Quantity k R :=
  ⟨MathCarrierExt.ceil a.magnitude⟩

/-- Round to nearest (kind-preserving). -/
@[expose] def round {k : KindOfProperty} {R : Type} [MathCarrierExt R] (a : Quantity k R) : Quantity k R :=
  ⟨MathCarrierExt.round a.magnitude⟩

@[simp] theorem neg_magnitude {k : KindOfProperty} {R : Type} [Neg R] (a : Quantity k R) :
    (Quantity.neg a).magnitude = -a.magnitude := rfl

@[simp] theorem neg_op_magnitude {k : KindOfProperty} {R : Type} [Neg R] (a : Quantity k R) :
    (-a).magnitude = -a.magnitude := rfl

@[simp] theorem abs_magnitude {k : KindOfProperty} {R : Type} [MathCarrier R] (a : Quantity k R) :
    (Quantity.abs a).magnitude = MathCarrier.abs a.magnitude := rfl

@[simp] theorem clamp_magnitude {k : KindOfProperty} {R : Type} [Min R] [Max R]
    (lo hi a : Quantity k R) :
    (Quantity.clamp lo hi a).magnitude
      = Max.max lo.magnitude (Min.min hi.magnitude a.magnitude) := rfl

end Quantity

/-! ## Family B — powers and roots (`PowerKind p`)

A `PowerKind p k₁ k` records that raising a `k₁`-quantity to the rational power `p`
yields a `k`-quantity. In the core it carries the ratio-scale gate (only ratio
quantities have powers, Dybkær §13.3.5); the `Dimension` layer strengthens it with the
*exponent-scaling* certificate `dim k = (dim k₁)^p`, using PhysLib's `Pow Dimension ℚ`. -/

/-- **A kind-level power law.** `k` is the `p`-th power kind of `k₁` (`k = k₁^p`): both
ratio-scale. The `Dimension` layer strengthens this with `k.dim = (k₁.dim)^p`. -/
structure PowerKind (p : Rat) (k₁ k : KindOfProperty) : Prop where
  /-- The base is ratio-scale. -/
  ratio₁ : k₁.IsRational
  /-- The power is ratio-scale. -/
  ratioPow : k.IsRational

/-- **Smart constructor.** Build a power law `k = k₁^p` from two *named* ratio-scale kinds,
the ratio-scale gate discharged by `rfl` for any concrete kinds. -/
theorem PowerKind.ofRatio (p : Rat) (k₁ k : KindOfProperty)
    (h₁ : k₁.IsRational := by rfl) (h : k.IsRational := by rfl) : PowerKind p k₁ k := ⟨h₁, h⟩

namespace Quantity

/-- **Verified construction** of a rational power, licensed by the power law. -/
@[expose] def rpow {p : Rat} {k₁ k : KindOfProperty} {R : Type} [MathCarrierExt R]
    (_h : PowerKind p k₁ k) (a : Quantity k₁ R) : Quantity k R :=
  ⟨MathCarrierExt.rpow a.magnitude p⟩

/-- **Square root** — the half-power, available from the base `MathCarrier` (so it runs
even on the binary32 exec carrier). `sqrt` of an area is a length. -/
@[expose] def sqrt {k₁ k : KindOfProperty} {R : Type} [MathCarrier R]
    (_h : PowerKind (1 / 2) k₁ k) (a : Quantity k₁ R) : Quantity k R :=
  ⟨MathCarrier.sqrt a.magnitude⟩

/-- **Cube root** — the third-power root. -/
@[expose] def cbrt {k₁ k : KindOfProperty} {R : Type} [MathCarrierExt R]
    (_h : PowerKind (1 / 3) k₁ k) (a : Quantity k₁ R) : Quantity k R :=
  ⟨MathCarrierExt.cbrt a.magnitude⟩

@[simp] theorem sqrt_magnitude {k₁ k : KindOfProperty} {R : Type} [MathCarrier R]
    (h : PowerKind (1 / 2) k₁ k) (a : Quantity k₁ R) :
    (Quantity.sqrt h a).magnitude = MathCarrier.sqrt a.magnitude := rfl

@[simp] theorem rpow_magnitude {p : Rat} {k₁ k : KindOfProperty} {R : Type} [MathCarrierExt R]
    (h : PowerKind p k₁ k) (a : Quantity k₁ R) :
    (Quantity.rpow h a).magnitude = MathCarrierExt.rpow a.magnitude p := rfl

end Quantity

/-! ## Families C and D — transcendental and trigonometric functions (`TranscendentalKind`)

A `TranscendentalKind k₁ k` records that applying a transcendental function to a
`k₁`-quantity yields a `k`-quantity. The core content is the ratio-scale gate; the
*dimensional* content — the argument is dimension one (C), or is a plane angle and the
result a number, with the curation that forbids `sin reflectivity` (D) — lives in the
`Dimension` layer's curated function algebra. -/

/-- **A kind-level transcendental law.** Applying a transcendental to `k₁` yields `k`;
both ratio-scale. The `Dimension` layer strengthens this to `dim k₁ = dim k = 1` and,
for the trigonometric functions, curates exactly which `(k₁, k)` edges are sanctioned. -/
structure TranscendentalKind (k₁ k : KindOfProperty) : Prop where
  /-- The argument kind is ratio-scale. -/
  ratio₁ : k₁.IsRational
  /-- The result kind is ratio-scale. -/
  ratioResult : k.IsRational

namespace Quantity

/-- Exponential of a (dimensionless) quantity. -/
@[expose] def exp {k₁ k : KindOfProperty} {R : Type} [MathCarrier R]
    (_h : TranscendentalKind k₁ k) (a : Quantity k₁ R) : Quantity k R :=
  ⟨MathCarrier.exp a.magnitude⟩

/-- Natural logarithm of a (dimensionless) quantity. -/
@[expose] def log {k₁ k : KindOfProperty} {R : Type} [MathCarrier R]
    (_h : TranscendentalKind k₁ k) (a : Quantity k₁ R) : Quantity k R :=
  ⟨MathCarrier.log a.magnitude⟩

/-- Sine of a plane angle. -/
@[expose] def sin {k₁ k : KindOfProperty} {R : Type} [MathCarrier R]
    (_h : TranscendentalKind k₁ k) (a : Quantity k₁ R) : Quantity k R :=
  ⟨MathCarrier.sin a.magnitude⟩

/-- Cosine of a plane angle. -/
@[expose] def cos {k₁ k : KindOfProperty} {R : Type} [MathCarrier R]
    (_h : TranscendentalKind k₁ k) (a : Quantity k₁ R) : Quantity k R :=
  ⟨MathCarrier.cos a.magnitude⟩

/-- Hyperbolic sine. -/
@[expose] def sinh {k₁ k : KindOfProperty} {R : Type} [MathCarrier R]
    (_h : TranscendentalKind k₁ k) (a : Quantity k₁ R) : Quantity k R :=
  ⟨MathCarrier.sinh a.magnitude⟩

/-- Hyperbolic cosine. -/
@[expose] def cosh {k₁ k : KindOfProperty} {R : Type} [MathCarrier R]
    (_h : TranscendentalKind k₁ k) (a : Quantity k₁ R) : Quantity k R :=
  ⟨MathCarrier.cosh a.magnitude⟩

/-- Hyperbolic tangent. -/
@[expose] def tanh {k₁ k : KindOfProperty} {R : Type} [MathCarrier R]
    (_h : TranscendentalKind k₁ k) (a : Quantity k₁ R) : Quantity k R :=
  ⟨MathCarrier.tanh a.magnitude⟩

/-- Tangent of a plane angle. -/
@[expose] def tan {k₁ k : KindOfProperty} {R : Type} [MathCarrierExt R]
    (_h : TranscendentalKind k₁ k) (a : Quantity k₁ R) : Quantity k R :=
  ⟨MathCarrierExt.tan a.magnitude⟩

/-- Inverse sine — a number to a plane angle. -/
@[expose] def asin {k₁ k : KindOfProperty} {R : Type} [MathCarrierExt R]
    (_h : TranscendentalKind k₁ k) (a : Quantity k₁ R) : Quantity k R :=
  ⟨MathCarrierExt.asin a.magnitude⟩

/-- Inverse cosine — a number to a plane angle. -/
@[expose] def acos {k₁ k : KindOfProperty} {R : Type} [MathCarrierExt R]
    (_h : TranscendentalKind k₁ k) (a : Quantity k₁ R) : Quantity k R :=
  ⟨MathCarrierExt.acos a.magnitude⟩

/-- Inverse tangent — a number to a plane angle. -/
@[expose] def atan {k₁ k : KindOfProperty} {R : Type} [MathCarrierExt R]
    (_h : TranscendentalKind k₁ k) (a : Quantity k₁ R) : Quantity k R :=
  ⟨MathCarrierExt.atan a.magnitude⟩

/-- Two-argument inverse tangent — the angle of two *same-kind* quantities `(x, y)`
(their ratio is dimensionless, so the result is a plane angle). The shared kind index
`k₁` enforces that `y` and `x` are of one kind. -/
@[expose] def atan2 {k₁ k : KindOfProperty} {R : Type} [MathCarrierExt R]
    (_h : TranscendentalKind k₁ k) (y x : Quantity k₁ R) : Quantity k R :=
  ⟨MathCarrierExt.atan2 y.magnitude x.magnitude⟩

@[simp] theorem exp_magnitude {k₁ k : KindOfProperty} {R : Type} [MathCarrier R]
    (h : TranscendentalKind k₁ k) (a : Quantity k₁ R) :
    (Quantity.exp h a).magnitude = MathCarrier.exp a.magnitude := rfl

@[simp] theorem sin_magnitude {k₁ k : KindOfProperty} {R : Type} [MathCarrier R]
    (h : TranscendentalKind k₁ k) (a : Quantity k₁ R) :
    (Quantity.sin h a).magnitude = MathCarrier.sin a.magnitude := rfl

@[simp] theorem cos_magnitude {k₁ k : KindOfProperty} {R : Type} [MathCarrier R]
    (h : TranscendentalKind k₁ k) (a : Quantity k₁ R) :
    (Quantity.cos h a).magnitude = MathCarrier.cos a.magnitude := rfl

@[simp] theorem tanh_magnitude {k₁ k : KindOfProperty} {R : Type} [MathCarrier R]
    (h : TranscendentalKind k₁ k) (a : Quantity k₁ R) :
    (Quantity.tanh h a).magnitude = MathCarrier.tanh a.magnitude := rfl

end Quantity

/-! ## Family F — re-expression against another reference (`ReferenceKind`)

The families above all *compute* a new quantity. This one does not: it states the same
quantity against a different reference. Degree and radian, metre and foot, hectopascal
and millibar — the value is one quantity, and what changes is the reference the number
counts. `Unit` makes that thesis at the level of kinds and numerals (§13.3.3's
number-and-reference form, `quantity / unit = number` and `number × unit = quantity`);
here it acts on a carrier, so a model can convert without leaving the calculus.

The relation is between *kinds* because a system may choose to keep the two references
apart at the type level — an incidence angle in degrees and the same angle in radians as
distinct kinds, so that a routine expecting radians cannot be handed degrees. That is a
strengthening of the ISQ, exactly as family D's curation is: commensurable quantities
that a model deliberately refuses to confuse. A system that does *not* make that
distinction instantiates `k₁ = k` and the law is the identity.

The conversion is carried by two quantities rather than a bare factor: one and the same
quantity stated in both references — a half turn as `π` and as `180`, a foot as `0.3048`
and as `1`. That keeps the reference data inside the calculus (a bare factor would enter
a kinded result as an un-kinded flow, which is what the provenance reading draws in red),
and it is the ratio the definition of a metrological unit already names. -/

/-- **A kind-level re-expression law.** `k₁` and `k` carry one kind-of-property against
different references, so a `k₁`-quantity re-expresses as a `k`-quantity by the ratio of
those references; both ratio-scale. Only a ratio-scale kind converts by a ratio alone —
an interval scale's reference carries an offset too (Celsius and Fahrenheit), which this
relation deliberately does not license. -/
structure ReferenceKind (k₁ k : KindOfProperty) : Prop where
  /-- The source kind is ratio-scale. -/
  ratio₁ : k₁.IsRational
  /-- The target kind is ratio-scale. -/
  ratioResult : k.IsRational

/-- **Smart constructor.** Build a re-expression law between two *named* ratio-scale
kinds, the ratio-scale gate discharged by `rfl` for any concrete kinds. -/
theorem ReferenceKind.ofRatio (k₁ k : KindOfProperty)
    (h₁ : k₁.IsRational := by rfl) (h : k.IsRational := by rfl) : ReferenceKind k₁ k := ⟨h₁, h⟩

/-- A re-expression is reflexive: every kind carries itself against its own reference. -/
theorem ReferenceKind.refl {k : KindOfProperty} (h : k.IsRational) : ReferenceKind k k := ⟨h, h⟩

/-- A re-expression is symmetric: the references convert both ways, which is what makes
them references for one kind-of-property rather than a projection between two. -/
theorem ReferenceKind.symm {k₁ k : KindOfProperty} (h : ReferenceKind k₁ k) :
    ReferenceKind k k₁ := ⟨h.ratioResult, h.ratio₁⟩

namespace Quantity

/-- **Verified re-expression**, licensed by the re-expression law: `a` stated against the
reference `k` counts by, given one and the same quantity written in both references
(`ref` in `k`'s, `ref₁` in `k₁`'s). Degrees to radians is `reexpress h θ ⟨π⟩ ⟨180⟩` — a
half turn, twice.

The association is `(a · ref) / ref₁`, not `a · (ref / ref₁)`: the two differ in floating
point (they agree at 40° and disagree at 89°), and a conversion that quietly re-associates
would move every number downstream of it. -/
@[expose] def reexpress {k₁ k : KindOfProperty} {R : Type} [Mul R] [Div R]
    (_h : ReferenceKind k₁ k) (a : Quantity k₁ R) (ref : Quantity k R)
    (ref₁ : Quantity k₁ R) : Quantity k R :=
  ⟨a.magnitude * ref.magnitude / ref₁.magnitude⟩

@[simp] theorem reexpress_magnitude {k₁ k : KindOfProperty} {R : Type} [Mul R] [Div R]
    (h : ReferenceKind k₁ k) (a : Quantity k₁ R) (ref : Quantity k R)
    (ref₁ : Quantity k₁ R) :
    (Quantity.reexpress h a ref ref₁).magnitude
      = a.magnitude * ref.magnitude / ref₁.magnitude := rfl

end Quantity

/-! ## The executable carrier instances (`Float`)

`Float` supports the full extended surface (Lean core `Float.*`), so it is both a
`MathCarrier` and a `MathCarrierExt` — the run carrier. It is **not** a
`LawfulMathCarrier` (the identities fail in floating point). `Int` is deliberately *not*
a `MathCarrier`: it has no transcendental operations. -/

/-- `Float` is a function carrier — the executable representation. -/
instance instMathCarrierFloat : MathCarrier Float where
  exp := Float.exp
  log := Float.log
  sin := Float.sin
  cos := Float.cos
  sinh := Float.sinh
  cosh := Float.cosh
  tanh := Float.tanh
  sqrt := Float.sqrt
  abs := Float.abs
  pi := 3.141592653589793

/-- `Float` supports the extended surface too. `rpow` realizes the rational exponent
`p` as the float quotient of its numerator and denominator. -/
instance instMathCarrierExtFloat : MathCarrierExt Float where
  toMathCarrier := instMathCarrierFloat
  tan := Float.tan
  asin := Float.asin
  acos := Float.acos
  atan := Float.atan
  atan2 := Float.atan2
  cbrt := Float.cbrt
  floor := Float.floor
  ceil := Float.ceil
  round := Float.round
  rpow := fun x q => Float.pow x (Float.ofInt q.num / Float.ofNat q.den)

end PropertyKindCalculus

end Interface
