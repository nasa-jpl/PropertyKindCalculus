/-
# Complex-valued carriers — the fourth representation (R10): complexifying a carrier

A quantity carries a magnitude *in some numbers* (Dybkær §13.3.3); `Quantity k R`
makes *which numbers* an explicit carrier parameter `R` (R10). So far every carrier
has been a real one (`Int`, `ℝ`, `Float`, binary32). Many physical quantities,
however, take a **complex** value: the relative permittivity of a lossy dielectric
`ε = ε′ + jε″`, an electrical impedance, an AC phasor, a quantum amplitude. The key
point is metrological, not just numerical:

  * **Complex-ness is a property of the carrier, not of the kind.** A complex
    permittivity is *one* kind of quantity — a relative permittivity, dimension one,
    ratio-scale — whose *value* happens to be complex. It is not two real quantities
    (a "real part kind" and an "imaginary part kind"), and it is not a new dimension.
    In the two-index design (`k` = what is measured, `R` = in what numbers) it is
    exactly `Quantity k (Complex R)`: the *same* kind layer over a *complexified*
    carrier.

This module supplies that complexified carrier as a **functor on carriers**
`R ↦ Complex R`: given the real arithmetic of `R`, `Complex R` has the complex
arithmetic, so the *existing* kind calculus applies verbatim — `Quantity.mul`,
`Quantity.div`, `Quantity.add` over `Quantity k (Complex R)` are the same smart
constructors, now computing complex products and quotients, still gated by the same
`ProductKind`/`QuotientKind` witnesses. Nothing in the kind, scale, dimension, or
interaction layers changes; only the carrier does.

## The one operation with a branch

The algebraic operations (`+ − × ÷`) are total and single-valued, so they are plain
toolchain instances. The **principal square root** is the exception: it has a branch
cut along the negative real axis, and selecting the principal branch needs a single
sign decision (the sign of the imaginary part, with `sign 0 = +`, matching numpy's
`csqrt`). That lone comparison is the one carrier capability beyond the arithmetic,
isolated here as `NegTest` so the branch-free complex algebra needs only the
toolchain. The square root is then exposed as a **kind-tracked** `Quantity.csqrt`,
licensed by a `PowerKind (1/2)` exactly as the real `Quantity.sqrt` — a permittivity's
complex square root is a refractive index, a checked kind crossing.

`Complex` is deliberately *not* made a full `MathCarrier`: a complex `exp`/`log`/`sin`
suite drags in extra carrier capabilities (a quadrant-aware angle for `log`) and an
unprovable lawfulness story (branch cuts everywhere), none of which the metrology here
needs. The complex square root — the one transcendental the EM forward model uses — is
given directly and honestly as its own branch-tracked constructor.

## Why not Mathlib's `Complex` (`ℂ`)?

Reusing Mathlib's `ℂ` would seem natural, but `ℂ` cannot be *the carrier* here, for the
same two reasons `Quantity k R` is parametric over `R` at all rather than hardwiring `ℝ`:

  * **`ℂ` is noncomputable.** It is `{re im : ℝ}`, and `ℝ`-arithmetic does not reduce —
    `#eval (1 + 2 : ℂ).re` yields a stuck `Real.ofCauchy (sorry …)`, not a number, and no
    `ℂ`-valued program compiles. But the whole point of the representation axis (R10) is
    that the model *runs*: the executable carrier must be `Float`-backed (to build a
    lookup table, emit a native binary, bit-compare to a reference). `Complex Float` runs;
    `ℂ` cannot.
  * **`ℂ` is hardwired to `ℝ`, not carrier-parametric.** `Complex.re : ℂ → ℝ` is fixed;
    there is no "`ℂ` over `Float`" or "`ℂ` over binary32". The representation-parametric
    mission needs complex *over `Float`* (to run), *over a binary32 rounding spec* (to
    certify rounding), and *over `ℝ`* (to prove) — and `Complex R` supplies all three from
    one definition, where `ℂ` supplies only the `ℝ` one, the carrier we do **not** run on.
  * (Consequently `ℂ` is unavailable in this Mathlib-free core at all — importing it would
    drag Mathlib into the spine, defeating the executable-carrier goal above.)

This is the same call the calculus already makes for the reals: the carrier abstraction is
`Carrier` / `MathCarrier`, and Mathlib's `ℝ` is *one instance* of it (the proof carrier,
`instMathCarrierReal`) — not the universal carrier. Complex follows suit: `Complex R` is
the parametric carrier; Mathlib's `ℂ` is the natural *proof-carrier target*.

So the reuse of Mathlib's complex analysis (its field structure, `Complex.abs`, `exp`,
continuity, the fundamental theorem) belongs at the proof carrier `ℝ`, via a ring
isomorphism `Complex ℝ ≃+* ℂ`: any property of complex *quantities at `ℝ`* transports to
`ℂ` and borrows that library, while the executable side keeps running on `Complex Float`.
That bridge's home is the PhysLib-backed `Dimension` layer (where the `ℝ` carrier
instances already live), not this Mathlib-free core.

This file is **Mathlib-free** (toolchain arithmetic only), so the complex carrier is
available at the executable `Float` representation with no analysis import; the `ℝ`
`NegTest` instance (the proof carrier) lives in the PhysLib-backed `Dimension` layer
beside the other `ℝ` carrier instances.
-/
import PropertyKindCalculus.QuantityFunction

namespace PropertyKindCalculus

/-- **A complex number `(re, im)` over a carrier `R` — the complexification of `R`.**
The value type of a complex-valued quantity: `Quantity k (Complex R)` is a quantity of
kind `k` whose magnitude is complex. `R` ranges over any real carrier (`ℝ` to prove,
`Float` to run), so the same complex quantity elaborates at every representation. -/
structure Complex (R : Type) where
  /-- The real part. -/
  re : R
  /-- The imaginary part. -/
  im : R
deriving Repr

namespace Complex

variable {R : Type}

/-- Embed a real magnitude as a complex one (zero imaginary part) — the carrier-level
inclusion `R ↪ Complex R`. -/
def ofReal [Zero R] (a : R) : Complex R := ⟨a, 0⟩

/-! ## The toolchain arithmetic of `Complex R`

Each instance lifts the real operations of `R` to the standard complex formulas, so the
kind calculus' smart constructors (`Quantity.mul` over `[Mul R]`, `Quantity.div` over
`[Div R]`, …) work over `Complex R` with no further plumbing. -/

instance [Add R] : Add (Complex R) := ⟨fun z w => ⟨z.re + w.re, z.im + w.im⟩⟩
instance [Sub R] : Sub (Complex R) := ⟨fun z w => ⟨z.re - w.re, z.im - w.im⟩⟩
instance [Neg R] : Neg (Complex R) := ⟨fun z => ⟨-z.re, -z.im⟩⟩

/-- Complex multiplication `(a+bj)(c+dj) = (ac − bd) + (ad + bc)j`. -/
instance [Mul R] [Add R] [Sub R] : Mul (Complex R) :=
  ⟨fun z w => ⟨z.re * w.re - z.im * w.im, z.re * w.im + z.im * w.re⟩⟩

instance [Zero R] : Zero (Complex R) := ⟨⟨0, 0⟩⟩
instance [Zero R] [One R] : One (Complex R) := ⟨⟨1, 0⟩⟩

/-- The squared modulus `|z|² = re² + im²` — a *real* magnitude. -/
def abs2 [Mul R] [Add R] (z : Complex R) : R := z.re * z.re + z.im * z.im

/-- Complex division `z / w = z · conj w / |w|²`. -/
instance [Mul R] [Add R] [Sub R] [Div R] : Div (Complex R) :=
  ⟨fun z w =>
    let d := w.abs2
    ⟨(z.re * w.re + z.im * w.im) / d, (z.im * w.re - z.re * w.im) / d⟩⟩

/-- The modulus `|z| = √(re² + im²)` — a *real* magnitude (needs the carrier's `sqrt`). -/
def abs [Mul R] [Add R] [MathCarrier R] (z : Complex R) : R := MathCarrier.sqrt z.abs2

/-- `Complex R` is a `Carrier` (zero magnitude + addition) whenever `R` is, so the
kind-gated `Quantity.add`/`Quantity.zero` are available over complex quantities. -/
instance [Carrier R] : Carrier (Complex R) where
  zero := ⟨Carrier.zero, Carrier.zero⟩
  add z w := ⟨Carrier.add z.re w.re, Carrier.add z.im w.im⟩

/-- Extensionality for complex carriers: equal real and imaginary parts ⇒ equal. -/
@[ext] theorem ext {z w : Complex R} (hre : z.re = w.re) (him : z.im = w.im) : z = w := by
  cases z; cases w; cases hre; cases him; rfl

/-- **`Complex R` is a *lawful* carrier whenever `R` is** (the complex proof
representation). Complex addition is componentwise, so the additive-monoid laws lift
directly from `R`'s — making `Complex ℝ` / `Complex Int` lawful complex carriers, exactly
as the real ones, while `Complex Float` stays a `Carrier` but not a `LawfulCarrier`,
mirroring `Float`. This is what makes `Complex R` a *fourth* point on the R10 representation
axis (see the `Quantity` module): complex over `ℝ` to prove, over binary32 to certify
rounding, over `Float` to run. -/
instance [LawfulCarrier R] : LawfulCarrier (Complex R) where
  add_assoc a b c := by ext <;> exact LawfulCarrier.add_assoc _ _ _
  add_comm a b := by ext <;> exact LawfulCarrier.add_comm _ _
  zero_add a := by ext <;> exact LawfulCarrier.zero_add _
  add_zero a := by ext <;> exact LawfulCarrier.add_zero _

/-! ## The branch-cut capability and the principal square root -/

/-- **The lone comparison the principal complex square root needs.** `isNeg x` decides
`x < 0` as a `Bool`, with `isNeg 0 = false` — numpy's branch convention `sign 0 = +`.
Isolated as a one-field capability so the branch-*free* complex algebra above needs only
the toolchain, and only the square root pulls in a carrier comparison. (`Float` decides
`<` computably; `ℝ` decides it classically — its instance is the noncomputable one in the
`Dimension` layer, beside the other `ℝ` carrier instances.) -/
class NegTest (R : Type) where
  /-- Decide `x < 0` as a `Bool`, with `isNeg 0 = false`. -/
  isNeg : R → Bool

/-- `Float` decides negativity computably (the executable carrier). -/
instance : NegTest Float := ⟨fun x => x < 0⟩

/-- **The principal complex square root** (numpy's branch, `sign 0 = +`):
`√z = √((|z|+re)/2) + sign(im)·√((|z|−re)/2)·j`. The real and imaginary magnitudes are
two real square roots; the imaginary *sign* is the one branch decision, taken by
`NegTest`. The divisor `2` is `1 + 1` (toolchain), which at every real carrier is the
literal `2`. -/
def sqrt [One R] [Add R] [Sub R] [Mul R] [Div R] [Neg R] [MathCarrier R] [NegTest R]
    (z : Complex R) : Complex R :=
  let m := z.abs
  let two : R := 1 + 1
  let reOut := MathCarrier.sqrt ((m + z.re) / two)
  let imMag := MathCarrier.sqrt ((m - z.re) / two)
  let imOut := if NegTest.isNeg z.im then -imMag else imMag
  ⟨reOut, imOut⟩

/-! ## Projection lemmas (so `.re`/`.im` of every operation compute by `simp`/`rfl`) -/

@[simp] theorem ofReal_re [Zero R] (a : R) : (ofReal a : Complex R).re = a := rfl
@[simp] theorem ofReal_im [Zero R] (a : R) : (ofReal a : Complex R).im = 0 := rfl
@[simp] theorem add_re [Add R] (z w : Complex R) : (z + w).re = z.re + w.re := rfl
@[simp] theorem add_im [Add R] (z w : Complex R) : (z + w).im = z.im + w.im := rfl
@[simp] theorem sub_re [Sub R] (z w : Complex R) : (z - w).re = z.re - w.re := rfl
@[simp] theorem sub_im [Sub R] (z w : Complex R) : (z - w).im = z.im - w.im := rfl
@[simp] theorem neg_re [Neg R] (z : Complex R) : (-z).re = -z.re := rfl
@[simp] theorem neg_im [Neg R] (z : Complex R) : (-z).im = -z.im := rfl

@[simp] theorem mul_re [Mul R] [Add R] [Sub R] (z w : Complex R) :
    (z * w).re = z.re * w.re - z.im * w.im := rfl
@[simp] theorem mul_im [Mul R] [Add R] [Sub R] (z w : Complex R) :
    (z * w).im = z.re * w.im + z.im * w.re := rfl

@[simp] theorem div_re [Mul R] [Add R] [Sub R] [Div R] (z w : Complex R) :
    (z / w).re = (z.re * w.re + z.im * w.im) / w.abs2 := rfl
@[simp] theorem div_im [Mul R] [Add R] [Sub R] [Div R] (z w : Complex R) :
    (z / w).im = (z.im * w.re - z.re * w.im) / w.abs2 := rfl

@[simp] theorem abs2_eq [Mul R] [Add R] (z : Complex R) :
    z.abs2 = z.re * z.re + z.im * z.im := rfl
@[simp] theorem abs_eq [Mul R] [Add R] [MathCarrier R] (z : Complex R) :
    z.abs = MathCarrier.sqrt (z.re * z.re + z.im * z.im) := rfl

@[simp] theorem sqrt_re [One R] [Add R] [Sub R] [Mul R] [Div R] [Neg R] [MathCarrier R] [NegTest R]
    (z : Complex R) :
    (Complex.sqrt z).re = MathCarrier.sqrt ((z.abs + z.re) / (1 + 1)) := rfl
@[simp] theorem sqrt_im [One R] [Add R] [Sub R] [Mul R] [Div R] [Neg R] [MathCarrier R] [NegTest R]
    (z : Complex R) :
    (Complex.sqrt z).im =
      (if NegTest.isNeg z.im then -MathCarrier.sqrt ((z.abs - z.re) / (1 + 1))
       else MathCarrier.sqrt ((z.abs - z.re) / (1 + 1))) := rfl

end Complex

/-! ## The kind-tracked complex square root (function calculus, Family B)

The complexification leaves the kind layer untouched, so the *only* new kind-level
constructor is the square root — the one operation whose value type changes. It carries
the same `PowerKind (1/2)` certificate as the real `Quantity.sqrt`: the complex square
root of a (dimension-one) relative permittivity is a (dimension-one) refractive index, a
checked half-power crossing of kinds, the dimensional content discharged in the
`Dimension` layer exactly as for the real root. -/

/-- **Kind-tracked principal complex square root.** The complex analogue of
`Quantity.sqrt`, licensed by the same `PowerKind (1/2) k₁ k`: `√` carries a
`k₁`-quantity to a `k`-quantity, now over a complex carrier. Named `csqrt` because the
complex square root is a genuinely distinct operation — it has a branch cut — even though
its kind discipline is identical to the real half-power's. -/
def Quantity.csqrt {k₁ k : KindOfProperty} {R : Type}
    [One R] [Add R] [Sub R] [Mul R] [Div R] [Neg R] [MathCarrier R] [Complex.NegTest R]
    (_h : PowerKind (1 / 2) k₁ k) (a : Quantity k₁ (Complex R)) : Quantity k (Complex R) :=
  ⟨Complex.sqrt a.magnitude⟩

@[simp] theorem Quantity.csqrt_magnitude {k₁ k : KindOfProperty} {R : Type}
    [One R] [Add R] [Sub R] [Mul R] [Div R] [Neg R] [MathCarrier R] [Complex.NegTest R]
    (h : PowerKind (1 / 2) k₁ k) (a : Quantity k₁ (Complex R)) :
    (Quantity.csqrt h a).magnitude = Complex.sqrt a.magnitude := rfl

end PropertyKindCalculus
