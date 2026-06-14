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

## What is here — the product family (the canonical R12 pattern)

The simplest defining relation — and a large fraction of the ISQ (area = length ·
length, volume = area · length, energy = force · length, …) — is the **product**.

  * `ProductKind k₁ k₂ k` — the kind-level law that `k` is the product of `k₁`, `k₂`.
    In the core it carries the scale precondition (all three ratio-scale: only ratio
    quantities multiply, Dybkær §13.3.5); the Dimension layer refines it with the
    dimensional certificate `k.dim = k₁.dim * k₂.dim`.
  * `Quantity.mul` — the smart constructor (verified-by-construction path).
  * `Quantity.IsProduct` — the certificate (a separate `Prop`, carried when needed).
  * `mul_isProduct`, `isProduct_unique`, `eq_mul_of_isProduct` — kind-laws stated to
    instantiate by application.

Analysis-shaped defining relations (area as a surface integral, speed as a derivative)
follow the same discipline in the layers where their mathematics lives.
-/

import PropertyKindCalculus.Quantity

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

/-- **Verified construction.** Build a `k`-quantity from a `k₁`- and a `k₂`-quantity,
licensed by the product law: the result is classified `k` *by construction*. -/
def Quantity.mul [Mul R] {k₁ k₂ k : KindOfProperty}
    (_h : ProductKind k₁ k₂ k) (a : Quantity k₁ R) (b : Quantity k₂ R) : Quantity k R :=
  ⟨a.magnitude * b.magnitude⟩

/-- **The certificate.** `q` (of kind `k`) is the product of `a` (of `k₁`) and `b` (of
`k₂`): its magnitude is the product of theirs. A proof of this *certifies* `q`'s
classification as `k`, rather than merely asserting it. Kept a separate `Prop` so
`Quantity` stays a clean tag and certificates are carried only when needed. -/
def Quantity.IsProduct [Mul R] {k₁ k₂ k : KindOfProperty}
    (_h : ProductKind k₁ k₂ k) (q : Quantity k R)
    (a : Quantity k₁ R) (b : Quantity k₂ R) : Prop :=
  q.magnitude = a.magnitude * b.magnitude

/-- The smart-constructed product satisfies the certificate **by construction**. -/
theorem Quantity.mul_isProduct [Mul R] {k₁ k₂ k} (h : ProductKind k₁ k₂ k)
    (a : Quantity k₁ R) (b : Quantity k₂ R) :
    (Quantity.mul h a b).IsProduct h a b := rfl

/-- **A kind-law that instantiates at the quantity level.** A quantity certified as the
product of `a` and `b` is unique — supply any concrete `a`, `b` to get the
quantity-level fact by application. -/
theorem Quantity.isProduct_unique [Mul R] {k₁ k₂ k} (h : ProductKind k₁ k₂ k)
    {q q' : Quantity k R} {a : Quantity k₁ R} {b : Quantity k₂ R}
    (hq : q.IsProduct h a b) (hq' : q'.IsProduct h a b) : q = q' := by
  cases q; cases q'
  simp only [Quantity.IsProduct] at hq hq'
  rw [hq, hq']

/-- **Canonicity.** Any quantity certified as the product of `a` and `b` *equals* the
smart-constructed product — the certificate determines the quantity. -/
theorem Quantity.eq_mul_of_isProduct [Mul R] {k₁ k₂ k} (h : ProductKind k₁ k₂ k)
    {q : Quantity k R} {a : Quantity k₁ R} {b : Quantity k₂ R}
    (hq : q.IsProduct h a b) : q = Quantity.mul h a b :=
  Quantity.isProduct_unique h hq (Quantity.mul_isProduct h a b)

end PropertyKindCalculus
