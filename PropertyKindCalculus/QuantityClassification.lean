/-
# Verified classification and instantiable kind-laws (R12)

A quantity's classification under a kind is, by default, a *tag*: `Quantity k R`
records the kind `k`, but its magnitude is an arbitrary `R`, so `⟨999⟩ :
Quantity area R` type-checks though `999` is no particular area. This module upgrades a
classification from an *assertion* to a *certificate*: a quantity is classified under a
kind by a proof that it stands in that kind's *defining relation* to quantities of the
kinds it is built from. The defining relations are the formalized ISO 80000 *Remarks*.

## The discipline (so kind-laws instantiate at the quantity level)

Every kind-law is stated as a *carrier-parametric universal over quantities* with the
kind-relation as a premise: `∀ {R} [structure R] (quantities) , (kind-law) → …`.
"Instantiating a kind-law at the quantity level" is then ordinary application. This is
the inter-kind generalization of the intra-kind `Quantity.laws_parametric` (R10).

## What is here — the product, quotient, and reciprocal families

The simplest defining relations — and a large fraction of the ISQ — are the **product**
(area = length · length, volume = area · length, energy = force · length, …), the
**quotient** (speed = length / duration, plane angle = arc / radius, …), and the
**reciprocal** (frequency = 1 / period, curvature = 1 / radius, repetency = 1 /
wavelength, …). Each is captured by the same three-part pattern:

  * `ProductKind k₁ k₂ k` / `QuotientKind k₁ k₂ k` / `ReciprocalKind k₁ k` — the
    kind-level law (`k = k₁ · k₂`, `k = k₁ / k₂`, `k = 1 / k₁`). In the core each
    carries the scale precondition (ratio-scale: only ratio quantities multiply,
    divide, or invert, Dybkær §13.3.5); the Dimension layer refines it with the
    dimensional certificate (`k.dim = k₁.dim * k₂.dim`, `… / …`, `(k₁.dim)⁻¹`).
  * `Quantity.mul` / `Quantity.div` / `Quantity.recip` — the smart constructors (the
    verified-by-construction paths).
  * `Quantity.IsProduct` / `IsQuotient` / `IsReciprocal` — the certificates (separate
    `Prop`s, carried when needed), with `_unique` / `eq_…_of_…` kind-laws stated to
    instantiate by application.

These use only the core arithmetic classes `Mul`, `Div`, `Inv` (all toolchain-level),
so the whole family stays Mathlib-free. Analysis-shaped defining relations (area as a
surface integral) follow the same discipline in the layers where their mathematics
lives.

## The trust model — witnesses are authored, not checked

What the type system enforces about a kind-law witness is *explicitness and
propagation*, not truth. `Quantity.mul`/`div`/`recip` refuse to operate without a
witness naming the full kind equation at the call site, and no mechanism — no
inference, no instance search, no coercion — can introduce one silently. But the smart
constructors are deliberately *liberal*: `ProductKind.ofRatio` signs **any** three
ratio-scale kinds it is handed. Whether `k` really is the product kind of `k₁` and `k₂`
is a metrological claim the type system cannot decide (the same dimension-one ratio can
legitimately land in different kinds by role); it is the *author's* claim.

So a wrong edge is not impossible — it is impossible to write *silently*. The
consequence, and the discipline downstream models build on: a model's kind algebra is
exactly the finite list of witnesses visible in its source. **A witness is to the kind
algebra what an axiom is to a proof**: the checker verifies everything *given* the
witnesses; their truth is a reviewed claim; and soundness is judged by enumerating them
— grep the witness constructors and the raw `⟨·⟩` tagging sites, exactly as
sorry-freeness is judged by `#print axioms`, never by the absence of warnings. Keep the
trusted base explicit, small, and enumerable; state the sanctioned edges next to each
kind declaration; certify the specifically-forbidden ones with `#check_failure` probes.
(A curated instance table — `OperatorTable`'s `KindMul`/`KindDiv` — narrows this
further at use sites that adopt it: at most one signed edge per operand pair.)
-/

module

public import PropertyKindCalculus.Quantity

public section -- pkc-blanket
@[expose] section -- pkc-blanket-expose

namespace PropertyKindCalculus

variable {R : Type}

/-- **A kind-level product law.** `k` is the *product kind* of `k₁` and `k₂`: all three
are ratio-scale (Dybkær §13.3.5 — only ratio quantities multiply), the precondition for
forming a product quantity. The Dimension layer strengthens this with the dimensional
equation `k.dim = k₁.dim * k₂.dim`; in the core it carries the scale precondition. -/
structure ProductKind (k₁ k₂ k : KindOfProperty) : Prop where
  /-- The first factor is ratio-scale. -/
  ratio₁ : k₁.IsRational
  /-- The second factor is ratio-scale. -/
  ratio₂ : k₂.IsRational
  /-- The product is ratio-scale. -/
  ratioProduct : k.IsRational

/-- **Smart constructor.** Build a product law from three *named* ratio-scale kinds, the
ratio-scale gate discharged by `rfl` for any concrete kinds. Reads as the kind equation it
stands for at the call site (`ProductKind.ofRatio k₁ k₂ k`), with the dimensional content
certified in the application's `Dimension` layer.

Deliberately liberal: it signs *any* ratio-scale triple — whether `k` truly is the product
kind of `k₁` and `k₂` is the author's claim, not a checked fact (the trust model in this
module's header). The guarantee is that the claim must be *written*, in full, where it is
used. -/
theorem ProductKind.ofRatio (k₁ k₂ k : KindOfProperty)
    (h₁ : k₁.IsRational := by rfl) (h₂ : k₂.IsRational := by rfl) (h : k.IsRational := by rfl) :
    ProductKind k₁ k₂ k := ⟨h₁, h₂, h⟩

/-- **Verified construction.** Build a `k`-quantity from a `k₁`- and a `k₂`-quantity,
licensed by the product law: the result is classified `k` *by construction*. -/
def Quantity.mul [Mul R] [ScalarCarrier R] {k₁ k₂ k : KindOfProperty}
    (_h : ProductKind k₁ k₂ k) (a : Quantity k₁ R) (b : Quantity k₂ R) : Quantity k R :=
  ⟨a.magnitude * b.magnitude⟩

@[simp] theorem Quantity.mul_magnitude [Mul R] [ScalarCarrier R] {k₁ k₂ k : KindOfProperty}
    (h : ProductKind k₁ k₂ k) (a : Quantity k₁ R) (b : Quantity k₂ R) :
    (Quantity.mul h a b).magnitude = a.magnitude * b.magnitude := rfl

/-- **The certificate.** `q` (of kind `k`) is the product of `a` (of `k₁`) and `b` (of
`k₂`): its magnitude is the product of theirs. A proof of this *certifies* `q`'s
classification as `k`, rather than merely asserting it. Kept a separate `Prop` so
`Quantity` stays a clean tag and certificates are carried only when needed. -/
def Quantity.IsProduct [Mul R] [ScalarCarrier R] {k₁ k₂ k : KindOfProperty}
    (_h : ProductKind k₁ k₂ k) (q : Quantity k R)
    (a : Quantity k₁ R) (b : Quantity k₂ R) : Prop :=
  q.magnitude = a.magnitude * b.magnitude

/-- The smart-constructed product satisfies the certificate **by construction**. -/
theorem Quantity.mul_isProduct [Mul R] [ScalarCarrier R] {k₁ k₂ k} (h : ProductKind k₁ k₂ k)
    (a : Quantity k₁ R) (b : Quantity k₂ R) :
    (Quantity.mul h a b).IsProduct h a b := rfl

/-- **A kind-law that instantiates at the quantity level.** A quantity certified as the
product of `a` and `b` is unique — supply any concrete `a`, `b` to get the
quantity-level fact by application. -/
theorem Quantity.isProduct_unique [Mul R] [ScalarCarrier R] {k₁ k₂ k} (h : ProductKind k₁ k₂ k)
    {q q' : Quantity k R} {a : Quantity k₁ R} {b : Quantity k₂ R}
    (hq : q.IsProduct h a b) (hq' : q'.IsProduct h a b) : q = q' := by
  cases q; cases q'
  simp only [Quantity.IsProduct] at hq hq'
  rw [hq, hq']

/-- **Canonicity.** Any quantity certified as the product of `a` and `b` *equals* the
smart-constructed product — the certificate determines the quantity. -/
theorem Quantity.eq_mul_of_isProduct [Mul R] [ScalarCarrier R] {k₁ k₂ k} (h : ProductKind k₁ k₂ k)
    {q : Quantity k R} {a : Quantity k₁ R} {b : Quantity k₂ R}
    (hq : q.IsProduct h a b) : q = Quantity.mul h a b :=
  Quantity.isProduct_unique h hq (Quantity.mul_isProduct h a b)

/-! ## The quotient family (`k = k₁ / k₂`)

Speed is path length divided by duration, a plane angle is an arc length divided by a
radius (so the lengths cancel and the angle is dimension one), repetency-like ratios,
and so on. The pattern mirrors the product family, over the core `Div` class. -/

/-- **A kind-level quotient law.** `k` is the *quotient kind* of `k₁` by `k₂`
(`k = k₁ / k₂`): all three are ratio-scale (the precondition for dividing quantities,
Dybkær §13.3.5). The Dimension layer strengthens this with `k.dim = k₁.dim / k₂.dim`. -/
structure QuotientKind (k₁ k₂ k : KindOfProperty) : Prop where
  /-- The dividend is ratio-scale. -/
  ratio₁ : k₁.IsRational
  /-- The divisor is ratio-scale. -/
  ratio₂ : k₂.IsRational
  /-- The quotient is ratio-scale. -/
  ratioQuotient : k.IsRational

/-- **Smart constructor.** Build a quotient law from three *named* ratio-scale kinds, the
ratio-scale gate discharged by `rfl` for any concrete kinds. -/
theorem QuotientKind.ofRatio (k₁ k₂ k : KindOfProperty)
    (h₁ : k₁.IsRational := by rfl) (h₂ : k₂.IsRational := by rfl) (h : k.IsRational := by rfl) :
    QuotientKind k₁ k₂ k := ⟨h₁, h₂, h⟩

/-- **Verified construction.** Build a `k`-quantity as the quotient of a `k₁`- by a
`k₂`-quantity, licensed by the quotient law: the result is classified `k` *by
construction*. -/
def Quantity.div [Div R] [ScalarCarrier R] {k₁ k₂ k : KindOfProperty}
    (_h : QuotientKind k₁ k₂ k) (a : Quantity k₁ R) (b : Quantity k₂ R) : Quantity k R :=
  ⟨a.magnitude / b.magnitude⟩

@[simp] theorem Quantity.div_magnitude [Div R] [ScalarCarrier R] {k₁ k₂ k : KindOfProperty}
    (h : QuotientKind k₁ k₂ k) (a : Quantity k₁ R) (b : Quantity k₂ R) :
    (Quantity.div h a b).magnitude = a.magnitude / b.magnitude := rfl

/-- **The certificate.** `q` (of kind `k`) is the quotient of `a` (of `k₁`) by `b` (of
`k₂`): its magnitude is the quotient of theirs. A proof *certifies* `q`'s classification
as `k`. -/
def Quantity.IsQuotient [Div R] [ScalarCarrier R] {k₁ k₂ k : KindOfProperty}
    (_h : QuotientKind k₁ k₂ k) (q : Quantity k R)
    (a : Quantity k₁ R) (b : Quantity k₂ R) : Prop :=
  q.magnitude = a.magnitude / b.magnitude

/-- The smart-constructed quotient satisfies the certificate **by construction**. -/
theorem Quantity.div_isQuotient [Div R] [ScalarCarrier R] {k₁ k₂ k} (h : QuotientKind k₁ k₂ k)
    (a : Quantity k₁ R) (b : Quantity k₂ R) :
    (Quantity.div h a b).IsQuotient h a b := rfl

/-- **A kind-law that instantiates at the quantity level.** A quantity certified as the
quotient of `a` by `b` is unique. -/
theorem Quantity.isQuotient_unique [Div R] [ScalarCarrier R] {k₁ k₂ k} (h : QuotientKind k₁ k₂ k)
    {q q' : Quantity k R} {a : Quantity k₁ R} {b : Quantity k₂ R}
    (hq : q.IsQuotient h a b) (hq' : q'.IsQuotient h a b) : q = q' := by
  cases q; cases q'
  simp only [Quantity.IsQuotient] at hq hq'
  rw [hq, hq']

/-- **Canonicity.** Any quantity certified as the quotient of `a` by `b` *equals* the
smart-constructed quotient. -/
theorem Quantity.eq_div_of_isQuotient [Div R] [ScalarCarrier R] {k₁ k₂ k} (h : QuotientKind k₁ k₂ k)
    {q : Quantity k R} {a : Quantity k₁ R} {b : Quantity k₂ R}
    (hq : q.IsQuotient h a b) : q = Quantity.div h a b :=
  Quantity.isQuotient_unique h hq (Quantity.div_isQuotient h a b)

/-- **Transposition.** A quotient law re-read as a product law: if `k = k₁ / k₂`, then
`k · k₂ = k₁` — multiplying a quotient back by its divisor recovers the dividend kind.
The ratio-scale fields permute; the *semantic* claim transposes with them (the same
trust model as the smart constructors: the author signed `k = k₁ / k₂`, and this is
that signature re-oriented, not a new edge). It lets a consumer that holds a quotient
witness build the dividend-kinded product — e.g. an uncertainty propagator forming
`|y| · u(b)` at the dividend kind from `y = a / b` — without registering a second,
independently-trusted law. -/
theorem QuotientKind.toProductKind {k₁ k₂ k : KindOfProperty}
    (h : QuotientKind k₁ k₂ k) : ProductKind k k₂ k₁ :=
  ⟨h.ratioQuotient, h.ratio₂, h.ratio₁⟩

/-! ## The reciprocal family (`k = 1 / k₁`)

Frequency is the reciprocal of period duration, curvature the reciprocal of the radius
of curvature, repetency the reciprocal of the wavelength. A unary special case of the
quotient, over the core `Inv` class. -/

/-- **A kind-level reciprocal law.** `k` is the *reciprocal kind* of `k₁`
(`k = 1 / k₁`): both ratio-scale (the precondition for inverting a quantity). The
Dimension layer strengthens this with `k.dim = (k₁.dim)⁻¹`. -/
structure ReciprocalKind (k₁ k : KindOfProperty) : Prop where
  /-- The base kind is ratio-scale. -/
  ratio₁ : k₁.IsRational
  /-- The reciprocal is ratio-scale. -/
  ratioReciprocal : k.IsRational

/-- **Verified construction.** Build a `k`-quantity as the reciprocal of a
`k₁`-quantity, licensed by the reciprocal law: classified `k` *by construction*. -/
def Quantity.recip [Inv R] {k₁ k : KindOfProperty}
    (_h : ReciprocalKind k₁ k) (a : Quantity k₁ R) : Quantity k R :=
  ⟨a.magnitude⁻¹⟩

/-- **The certificate.** `q` (of kind `k`) is the reciprocal of `a` (of `k₁`): its
magnitude is the inverse of `a`'s. A proof *certifies* `q`'s classification as `k`. -/
def Quantity.IsReciprocal [Inv R] {k₁ k : KindOfProperty}
    (_h : ReciprocalKind k₁ k) (q : Quantity k R) (a : Quantity k₁ R) : Prop :=
  q.magnitude = a.magnitude⁻¹

/-- The smart-constructed reciprocal satisfies the certificate **by construction**. -/
theorem Quantity.recip_isReciprocal [Inv R] {k₁ k} (h : ReciprocalKind k₁ k)
    (a : Quantity k₁ R) : (Quantity.recip h a).IsReciprocal h a := rfl

/-- **A kind-law that instantiates at the quantity level.** A quantity certified as the
reciprocal of `a` is unique. -/
theorem Quantity.isReciprocal_unique [Inv R] {k₁ k} (h : ReciprocalKind k₁ k)
    {q q' : Quantity k R} {a : Quantity k₁ R}
    (hq : q.IsReciprocal h a) (hq' : q'.IsReciprocal h a) : q = q' := by
  cases q; cases q'
  simp only [Quantity.IsReciprocal] at hq hq'
  rw [hq, hq']

/-- **Canonicity.** Any quantity certified as the reciprocal of `a` *equals* the
smart-constructed reciprocal. -/
theorem Quantity.eq_recip_of_isReciprocal [Inv R] {k₁ k} (h : ReciprocalKind k₁ k)
    {q : Quantity k R} {a : Quantity k₁ R}
    (hq : q.IsReciprocal h a) : q = Quantity.recip h a :=
  Quantity.isReciprocal_unique h hq (Quantity.recip_isReciprocal h a)

end PropertyKindCalculus

end -- pkc-blanket-expose
end -- pkc-blanket
