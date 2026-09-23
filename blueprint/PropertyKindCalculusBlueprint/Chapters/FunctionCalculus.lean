import Verso
import VersoManual
import VersoBlueprint
-- The nodes below link real declarations, so this chapter imports the function-layer
-- core (`QuantityFunction`), its PhysLib-backed dimensional coherence (`Function`), and
-- the complex carrier (`Complex`).
import PropertyKindCalculus.QuantityFunction
import PropertyKindCalculus.Function
import PropertyKindCalculus.Complex

open Verso.Genre
open Verso.Genre.Manual
open Informal

#doc (Manual) "The Function Calculus and Complex-Valued Carriers (R12)" =>
%%%
tag := "function-calculus"
%%%

The product / quotient / reciprocal calculus covers the _algebraic_ defining relations of
the ISQ (area is length times length, speed is length over duration). Scientific models do
two further things the algebra alone does not reach: they apply _functions_ to quantities
(roots, exponentials, logarithms, the trigonometric functions), and they take _complex
values_ (the relative permittivity of a lossy dielectric, an impedance, a phasor). This
chapter adds the two carrier-level extensions that cover both — the *function calculus*
(a carrier _capability_, plus kind-relations for functions) and the *complex carrier* (a
carrier _construction_) — and the point of each is that the kind layer is left untouched:
only what a magnitude can _do_, or what numbers it lives _in_, changes.

# Functions on quantities

:::group "functions"
The algebraic calculus rides on the toolchain classes for multiplication, division, and
reciprocal. There is no toolchain class for `exp`, `sin`, or square root, so the one
genuinely new artifact is a carrier capability — the function-layer analogue of
{uses "def_carrier"}[the numeric carrier] — and a family of smart constructors that each
carry their own metrological discipline. The functions split into five families with
genuinely different kind signatures: kind-preserving (`abs`, `min`, `max`); powers and
roots (the dimension scales by the exponent); dimensionless transcendentals (`exp`, `log`
— pure number in, pure number out); the trigonometric functions (a plane angle in, a
number out — curated so that `sin` of a reflectivity stays a category error); and
logarithmic levels (dB, neper — where `log` of a ratio demotes the scale, so the product
calculus correctly refuses it).
:::

:::definition "def_mathCarrier" (parent := "functions") (lean := "PropertyKindCalculus.MathCarrier")
$`\mathrm{MathCarrier}\ R` is the *function operation surface* a kind-indexed magnitude
needs — $`\exp`, $`\log`, $`\sin`, $`\cos`, the hyperbolic functions, $`\sqrt{\,}`,
$`|\cdot|`, and the constant $`\pi` — supplied once per representation type $`R`. It is the
function-layer analogue of the numeric carrier `Carrier`, and is by construction the
_same_ surface as the underlying tensor toolchain's elementary functions, so every carrier
that supports them — $`\mathbb{R}`, `Float`, the binary32 carriers — is a clean
$`\mathrm{MathCarrier}`.
:::

:::proof "def_mathCarrier"
Realized as the `MathCarrier` class. The richer surface ($`\tan`, the inverse trig,
$`\operatorname{atan2}`, cube root, rounding, rational power) is split off into
`MathCarrierExt`, so the executable binary32 carrier — whose function vocabulary is
deliberately smaller — is a `MathCarrier` without being a `MathCarrierExt`. The algebraic
_identities_ ($`\sin^2+\cos^2=1`, $`\exp(a+b)=\exp a\cdot\exp b`) live in
`LawfulMathCarrier`, which holds at $`\mathbb{R}` and _fails_ in floating point — the same
exec/spec gap the lawful numeric carrier draws for $`+`. The `Float`
instance is computable (the run carrier); the $`\mathbb{R}` instance is the noncomputable
proof carrier in the PhysLib-backed `Dimension` layer.
:::

:::definition "def_powerKind" (parent := "functions") (lean := "PropertyKindCalculus.PowerKind")
$`\mathrm{PowerKind}\ p\ k_1\ k` records that raising a $`k_1`-quantity to the rational
power $`p` yields a $`k`-quantity ($`k = k_1^{\,p}`). In the core it carries only the
ratio-scale gate (Dybkær §13.3.5 — only ratio quantities have powers); the
{uses "def_dim"}[dimension] layer strengthens it to the exponent-scaling certificate
$`\dim k = (\dim k_1)^{p}`. This is the one function family that is _not_
dimension-one-in-out — the dimension-scaling extension of multiplication and division.
:::

:::proof "def_powerKind"
Realized as the `PowerKind` structure (two ratio-scale fields), with the smart constructors
{uses "def_quantity_sqrt"}[`Quantity.sqrt`] (the half-power), `Quantity.cbrt`, and
`Quantity.rpow`. The exponent-scaling refinement is `DimPowerKind`, well-defined because
PhysLib's `Dimension` carries $`\mathbb{Q}` exponents (`Pow Dimension ℚ`), making a
half-power a genuine group element.
:::

:::definition "def_quantity_sqrt" (parent := "functions") (lean := "PropertyKindCalculus.Quantity.sqrt") (tags := "proved")
$`\mathrm{Quantity.sqrt}` is the *verified half-power*, the canonical
{uses "def_powerKind"}[`PowerKind` $`(1/2)`] smart constructor: $`\sqrt{\,}` of a $`k_1`
yields a $`k`, its magnitude $`\sqrt{a}` taken in the carrier. It rides on the base
{uses "def_mathCarrier"}[`MathCarrier`] (not the extended surface), so it runs even on the
binary32 executable carrier.
:::

:::proof "def_quantity_sqrt"
Realized as `Quantity.sqrt`, taking a `PowerKind (1/2) k₁ k` and returning
$`⟨\mathrm{MathCarrier.sqrt}\ a.\mathrm{magnitude}⟩`; the projection
`sqrt_magnitude` is `rfl`, so an erased computation is exactly the carrier's
$`\sqrt{\,}`.
:::

:::theorem "thm_sqrt_area_coherent" (parent := "functions") (lean := "PropertyKindCalculus.sqrt_area_coherent") (tags := "proved") (effort := "small")
*The square root of an area is a length — checked, not annotated.* The half-power of the
area dimension $`\mathrm{L}^2` is the length dimension $`\mathrm{L}`:
$$`\dim(\sqrt{\mathrm{area}}) = (\dim \mathrm{area})^{1/2} = \mathrm{L}.`
The certificate {uses "def_quantity_sqrt"}[`Quantity.sqrt`] carries, here discharged in the
PhysLib `Dimension` group. Builds on {uses "def_powerKind"}[the power law].
:::

:::proof "thm_sqrt_area_coherent"
Proved in the `Function` module: `areaK` is declared with dimension $`\mathrm{L}^2` and the
goal `lengthKind.dim = areaK.dim ^ (1/2 : ℚ)` is closed component-wise by `norm_num` over
the rational exponents of the `Dimension` group.
:::

:::definition "def_transcendentalKind" (parent := "functions") (lean := "PropertyKindCalculus.TranscendentalKind")
$`\mathrm{TranscendentalKind}\ k_1\ k` licenses the smart constructors
{uses "def_quantity_sqrt"}[for] $`\exp`, $`\log`, the hyperbolic and trigonometric
functions. The core records the ratio-scale gate; the {uses "def_dim"}[dimension] layer
strengthens it to "argument and result are dimension one" (Families C), and — for the
trigonometric functions — to a _curated_ algebra (the unary analogue of
{uses "def_kMul"}[the interaction algebra]) that keeps $`\sin` on plane angles only. That a
plane angle is dimension one yet a distinct _kind_ is exactly why $`\sin` of an angle is
fine while $`\sin` of a reflectivity is the category error a dimension-only system cannot
forbid.
:::

:::proof "def_transcendentalKind"
Realized as `TranscendentalKind` with the constructors `Quantity.exp` / `log` / `sin` /
`cos` / `tanh` (base surface) and `tan` / `asin` / `acos` / `atan` / `atan2` (extended
surface). The dimensional strengthening is `DimTranscendental` (`tanh_lossTangent_coherent`
is the worked edge: the conductive-loss $`\tanh` argument is dimensionless and so is its
value), and the trigonometric curation is the `Dimension`-layer trig algebra.
:::

# Complex-valued carriers

:::group "complex"
A quantity carries a magnitude _in some numbers_; many physical quantities take that
magnitude in the _complex_ numbers. The key observation is metrological, not numerical:
*complex-ness is a property of the carrier, not of the kind*. A complex permittivity (a
real part plus _j_ times an imaginary part) is _one_ kind of quantity — a relative
permittivity, dimension one, ratio-scale — whose _value_ is complex. It is not two real
quantities, and not a new dimension. In the two-index design it is exactly
`Quantity k (Complex R)`: the _same_ kind layer over a _complexified_ carrier, so
{uses "def_kMul"}[the algebraic calculus] applies verbatim, now computing complex products
and quotients.
:::

:::definition "def_complex" (parent := "complex") (lean := "PropertyKindCalculus.Complex") (tags := "proved")
$`\mathrm{Complex}\ R` is the *complexification of a carrier* — the functor
$`R \mapsto \mathrm{Complex}\ R` that, given the real arithmetic of $`R`, equips
$`(\mathrm{re}, \mathrm{im})` with the complex arithmetic. A complex-valued quantity is
$`\mathrm{Quantity}\ k\ (\mathrm{Complex}\ R)`; the carrier varies
($`\mathbb{R}` to prove, `Float` to run) while the kind $`k` does not.

This is a *fourth* point on the representation axis (R10): the three scalar carriers
($`\mathbb{R}` to prove, a binary32 rounding spec to certify, `Float` to run) are all real,
and $`\mathrm{Complex}\ R` lifts each of them — $`\mathrm{Complex}\ \mathbb{R}` to prove,
$`\mathrm{Complex}\ (\mathrm{binary32})` to certify rounding, $`\mathrm{Complex}\ \mathrm{Float}`
to run. It is a `Carrier`, and a `LawfulCarrier` whenever $`R` is (complex addition is
componentwise, so the additivity laws lift for free); it carries a full field $`+\,-\,\times\,\div`
but is _unordered_, so — unlike the real carriers — it sits outside the
ordinal/interval/ratio carrier tower: complex magnitudes are compared by modulus, not ranked.
:::

:::proof "def_complex"
Realized as `Complex R` with the toolchain instances ($`+`, $`-`, $`\times`, $`\div`,
negation, zero, one), a `Carrier` instance, and $`|z|^2` / $`|z|`. Why parametric rather
than Mathlib's $`\mathbb{C}`? For the same reason the carrier is a parameter at all:
$`\mathbb{C}` is _noncomputable_ (its parts are $`\mathbb{R}`, which does not reduce — no
$`\mathbb{C}`-valued program runs or compiles, yet the executable carrier must be
`Float`-backed), and it is _hardwired to $`\mathbb{R}`_ (there is no "$`\mathbb{C}` over
`Float`"), whereas the representation axis needs complex over `Float`, over a binary32
rounding spec, and over $`\mathbb{R}` from one definition. As with the reals — where
$`\mathbb{R}` is _one instance_ of the carrier, not the universal one
— Mathlib's $`\mathbb{C}` is the natural _proof-carrier target_: a ring isomorphism
$`\mathrm{Complex}\ \mathbb{R} \simeq \mathbb{C}` (its home the `Dimension` layer) transports
any property of complex quantities at $`\mathbb{R}` to $`\mathbb{C}` and borrows its analysis
library, while the run side stays on $`\mathrm{Complex}\ \mathtt{Float}`.
:::

:::definition "def_complex_sqrt" (parent := "complex") (lean := "PropertyKindCalculus.Complex.sqrt") (tags := "proved")
The *principal complex square root*. The algebraic operations are total and
single-valued, so they are plain instances; the square root is the exception — it has a
branch cut along the negative real axis. Selecting the principal branch needs exactly one
sign decision (the sign of the imaginary part, with $`\operatorname{sign} 0 = +`),
isolated as the one-field capability `NegTest` so the branch-_free_ complex algebra needs
only the toolchain.
:::

:::proof "def_complex_sqrt"
Realized as `Complex.sqrt`:
$$`\sqrt{z} = \sqrt{\tfrac{|z|+\mathrm{re}}{2}} \;+\; \operatorname{sign}(\mathrm{im})\,\sqrt{\tfrac{|z|-\mathrm{re}}{2}}\,j,`
the real and imaginary magnitudes two real {uses "def_quantity_sqrt"}[square roots] and the
imaginary _sign_ the one `NegTest` decision (`Float` deciding it computably, $`\mathbb{R}`
classically). `Complex` is deliberately _not_ made a full `MathCarrier`: a complex
$`\exp`/$`\log`/$`\sin` suite would drag in a quadrant-aware angle and an unprovable
lawfulness story the metrology does not need — the one transcendental the electromagnetic
forward model uses is given directly and honestly as its own branch-tracked constructor.
:::

:::theorem "thm_quantity_csqrt" (parent := "complex") (lean := "PropertyKindCalculus.Quantity.csqrt") (tags := "proved") (effort := "small")
*The kind-tracked complex square root.* The complex analogue of
{uses "def_quantity_sqrt"}[`Quantity.sqrt`], licensed by the _same_
{uses "def_powerKind"}[`PowerKind` $`(1/2)`]: the complex square root of a (dimension-one)
relative permittivity is a (dimension-one) refractive index — a checked half-power crossing
of kinds, now over a complex carrier. The complexification leaves the kind layer untouched,
so this is the only new kind-level constructor the complex numbers require.
:::

:::proof "thm_quantity_csqrt"
Realized as `Quantity.csqrt`, the smart constructor wrapping {uses "def_complex_sqrt"}[the
principal complex square root] under the same `PowerKind (1/2)` certificate as the real
half-power; named `csqrt` because the complex root is a genuinely distinct operation (it
has a branch cut) even though its kind discipline is identical.
:::
