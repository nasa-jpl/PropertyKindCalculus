/-
`paradigm.fused_kinds` — **the kind layer over the fused forms** (`FusedExp`, Layer 1).

`FusedExp.scaledProdExp c x y` (`paradigm.batch_carrier`) is the carrier's bit-exact
single-op replacement for the hot composed shape `exp((c·x)·y)` — domain-neutral, and
metrologically naked: `x` and `y` are bare `C s`, so a call with the two batch operands
swapped type-checks and silently computes the role-swapped exponent. The *composed*
spelling of the same shape, written through the kind calculus
(`Quantity.mul`/`Quantity.exp`), already refuses that swap; the fused spelling should
not be the one place in a kinded model where the discipline lapses.

This module supplies the kinded form. `Quantity.scaledProdExp` carries the *same three
kind-law witnesses the composed spelling would* — one `ProductKind` per product node of
the left-associated exponent `(c·x)·y`, then the `TranscendentalKind` gating `exp` —
so the fused op and the composed kinded op have identical kind signatures, and a model
can swap one for the other (where the carrier offers the fused kernel, or falls back)
without touching its kind structure. The magnitudes are untouched:
`(Quantity.scaledProdExp …).magnitude` is *definitionally* the naked
`FusedExp.scaledProdExp` call (the `rfl` erasure lemma below), so the kinded form is
eligible to be the authored source and the naked call its derived erasure.

The scalar coefficient `c` rides `Quantity kc Float` — a *kinded host scalar* (the
fused interface takes the scale factor as a host `Float`, not a batch), so a science
constant like a Beer–Lambert two-way `−2` keeps its kind while staying a plain float
underneath. Domain readings of the coefficient (which `−2`, for what path) belong to
the downstream science model, exactly as for the naked form.
-/
import PropertyKindCalculus.Torch.Paradigm.BatchCarrier
import PropertyKindCalculus.QuantityFunction

open Spec
open PropertyKindCalculus.Paradigm (FusedExp)

namespace PropertyKindCalculus

/-- **The kinded scaled product exponential** `exp((c·x)·y)` as the carrier's single
fused op. The three witnesses mirror the composed form's kind structure node-for-node:
`hcx` classifies the scalar–batch product `c·x` (kind `kp`), `hcxy` the full exponent
`(c·x)·y` (kind `kE`), and `hexp` gates `exp : kE → k` (the Dimension layer pins `kE`
to dimension one). Swapping the batch operands `x`/`y` is a type error whenever their
kinds differ — the compile-time guarantee the naked `FusedExp.scaledProdExp` cannot
give. Bit-exact with the naked form by construction (`scaledProdExp_magnitude` is
`rfl`). -/
@[inline] def Quantity.scaledProdExp {C : Shape → Type} [FusedExp C] {s : Shape}
    {kc k₁ kp k₂ kE k : KindOfProperty}
    (_hcx : ProductKind kc k₁ kp) (_hcxy : ProductKind kp k₂ kE)
    (_hexp : TranscendentalKind kE k)
    (c : Quantity kc Float) (x : Quantity k₁ (C s)) (y : Quantity k₂ (C s)) :
    Quantity k (C s) :=
  ⟨FusedExp.scaledProdExp c.magnitude x.magnitude y.magnitude⟩

/-- **Erasure is definitional**: the kinded fused op *is* the naked fused op on
magnitudes — the lemma a downstream model uses to flip authorship (kinded form authored,
naked call derived) with zero bit- or op-order change. -/
@[simp] theorem Quantity.scaledProdExp_magnitude {C : Shape → Type} [FusedExp C]
    {s : Shape} {kc k₁ kp k₂ kE k : KindOfProperty}
    (hcx : ProductKind kc k₁ kp) (hcxy : ProductKind kp k₂ kE)
    (hexp : TranscendentalKind kE k)
    (c : Quantity kc Float) (x : Quantity k₁ (C s)) (y : Quantity k₂ (C s)) :
    (Quantity.scaledProdExp hcx hcxy hexp c x y).magnitude
      = FusedExp.scaledProdExp c.magnitude x.magnitude y.magnitude := rfl

end PropertyKindCalculus
