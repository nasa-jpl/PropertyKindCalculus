/-
# The measurand — VIM's "quantity intended to be measured", as a kinded interface

VIM 2.3 defines the **measurand**; GUM builds on it: a measurement of a measurand
returns **indications**, and its result is a **best estimate** with a **standard
uncertainty**. The `Uncertainty` library already speaks this vocabulary throughout —
`Budget.lean`'s combination laws, `EvidenceKinds.lean`'s "quantities of the measurand's
own kind", `UncertainQuantity`'s value-plus-descriptor — but the noun itself was never a
type. This module mints it, in the Mathlib-free core, as the *model-level* face of that
stack: a measurand is what a model exposes to be measured, before any particular
evaluation (Type A sampling, a budget, a distribution) produces numbers for it.

The interface is deliberately small, and each field is a piece of metrological
discipline rather than a bare function:

  * `estimate : S → Quantity k R` — the best estimate *in a state* of the carrying
    system `S`, at the measurand's kind. What `S` is belongs to the model (a quantum
    state, a sample, a configuration); the kind does not move.
  * `variance : S → Quantity k₂ R` — the second moment lives at the *squared* kind, and
    the structure carries the authored `ProductKind k k k₂` edge (`square`) as its
    license: a measurand exists only where the model's kind algebra has sanctioned the
    square. (`Budget.lean` keeps its transient squared kind an erasure detail inside one
    combination step; here the variance is exposed API, so the edge is explicit.)
  * `IsIndication : Quantity k R → Prop` — the values a measurement can return, carrying
    the measurand's kind. For an operator model this is the spectrum; for a discrete
    model, a range.

`sigma` — the standard uncertainty — is then *derived*, once, for every model: the root
of the variance, back at the measurand's kind. Roots are not a kind operation
(the radicand-first rule), so the crossing is attested here, one place, rather than at
every model. `upper`/`lower` give the `estimate ± σ` bounds through the scale-gated
`Quantity.add`/`sub` — the same-kind sum GUM's coverage interval is built from, and the
reason σ must cross back down from `k₂` at all.

What this module does *not* say: how estimate and variance are computed (the model's
job), or how an uncertainty is evaluated and propagated (`Uncertainty`'s job — an
evaluated measurand is what `UncertainQuantity` then carries as value plus descriptor).
R14's ladder attaches exactly at `sigma`.
-/

import PropertyKindCalculus.QuantityFunction

namespace PropertyKindCalculus

/-- **A measurand (VIM 2.3), at its kind.** A quantity of kind `k` a model exposes to
be measured on a system/state `S`, carried at `R`: best estimate, variance at the
squared kind `k₂` (licensed by the authored edge `square`), and the indication
predicate. The kind indices are the data the prose tradition has nowhere to put. -/
structure Measurand (k k₂ : KindOfProperty) (S R : Type) where
  /-- The authored square edge — a measurand exists only where the model's kind
  algebra has sanctioned `k · k`. -/
  square : ProductKind k k k₂
  /-- GUM's best estimate, in a state, at the measurand's kind. -/
  estimate : S → Quantity k R
  /-- The second moment about the estimate, at the squared kind. -/
  variance : S → Quantity k₂ R
  /-- The values a measurement can return, carrying the measurand's kind. -/
  IsIndication : Quantity k R → Prop

namespace Measurand

variable {k k₂ : KindOfProperty} {S R : Type}

/-- **The standard uncertainty σ — one attested root back to the measurand's kind**,
derived once for every model (radicand-first: the variance is the registered object,
the root is the crossing). R14's uncertainty ladder attaches here. -/
def sigma [MathCarrier R] (M : Measurand k k₂ S R) (s : S) : Quantity k R :=
  Quantity.attest "the root of the variance — roots are not a kind operation"
    (MathCarrier.sqrt (M.variance s).magnitude)

@[simp] theorem sigma_magnitude [MathCarrier R] (M : Measurand k k₂ S R) (s : S) :
    (M.sigma s).magnitude = MathCarrier.sqrt (M.variance s).magnitude := rfl

/-- The upper `estimate + σ` bound — a same-kind, scale-gated sum: the coverage
interval's endpoint lives at the measurand's kind, which is the whole reason σ crosses
back down from `k₂`. -/
def upper [Carrier R] [MathCarrier R] (h : DifferenceKind k)
    (M : Measurand k k₂ S R) (s : S) : Quantity k R :=
  Quantity.add h (M.estimate s) (M.sigma s)

/-- The lower `estimate − σ` bound, through the scale-gated difference. -/
def lower [Sub R] [MathCarrier R] (h : DifferenceKind k)
    (M : Measurand k k₂ S R) (s : S) : Quantity k R :=
  Quantity.sub h (M.estimate s) (M.sigma s)

end Measurand

end PropertyKindCalculus
