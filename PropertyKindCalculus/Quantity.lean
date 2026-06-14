/-
# Quantity — a kind-indexed magnitude, parametric in its numeric carrier (R10)

Dybkær (2009) §13.3.3 (a unitary kind value is "a reference quantity multiplied
by a *number*") fixes that a quantity carries a magnitude *in some numbers*. This
module specifies *which* numbers as an explicit type parameter, so the kind layer
is written once and reused at every numeric representation.

A `Quantity k R` is a magnitude of a fixed kind `k`, carried at a *representation
type* `R` (requirement R10). Two indices, two jobs:

  * `k : KindOfProperty` fixes *what is measured*. Because the kind is a type
    index, a `Quantity k₁ R` and a `Quantity k₂ R` are *different types* when
    `k₁ ≠ k₂` — even if both kinds are dimension one — so the dimension-1
    conflation (vwc vs gwc) is a type error, and same-kind addition is the only
    addition that type-checks (R4).
  * `R : Type` fixes *in what numbers*. The arithmetic `R` must support is bundled
    into a `Carrier` typeclass, so the *same* `Quantity` source elaborates at
    whichever `R` a task needs: `Int`/`ℝ` to prove, `Float` to run.

This is the architecture TorchLean already runs for tensors: a model is written
against a `Context α` typeclass (the arithmetic an element type must provide) and
instantiated at `α := ℝ` for the specification, at a finite rounding model, and at
an executable IEEE-754 kernel — the same source at three carriers. `Carrier` here
plays the role of TorchLean's `Context`; the kind index `k` is the layer *above*
the carrier that TorchLean does not have. The two indices compose.

The split into `Carrier` (operations) and `LawfulCarrier` (operations *plus* the
algebraic laws) is deliberate and is the whole point of R10: a law proved once
over `LawfulCarrier R` transfers to *every* lawful carrier (`Int`, `ℝ`), while an
executable float is a `Carrier` but **not** a `LawfulCarrier` — floating-point
addition is not associative — so the laws are *unavailable* at the float that
runs. Closing that gap is the exec/spec *refinement* bridge (still planned): the
executable result is the rounding of the real result, which lets an `ℝ`-proved law
descend to the run with a bounded error.
-/

import PropertyKindCalculus.Kind

namespace PropertyKindCalculus

/-- **The numeric carrier of a quantity (R10).** The minimal arithmetic a
kind-indexed magnitude needs, supplied once per representation type `R`. This is
the role TorchLean's `Context α` plays for tensor element types: the kind, scale,
dimension, interaction, and extensivity layers are all written *against* this
class, and so are reused verbatim at every `R`. -/
class Carrier (R : Type) where
  /-- The additive unit (a zero magnitude). -/
  zero : R
  /-- Addition of magnitudes (the operation a same-kind sum is built from). -/
  add : R → R → R

/-- **A lawful numeric carrier.** A `Carrier` whose addition additionally obeys
the additive-monoid laws (associative, commutative, with `zero` a unit). These
are exactly the laws that hold over `ℝ` (the proof carrier) and `Int`, and that
*fail* over an executable float — which is why a float is only a `Carrier`. A
quantity law proved over `LawfulCarrier R` is proved for every lawful `R` at
once. -/
class LawfulCarrier (R : Type) extends Carrier R where
  /-- Addition is associative. -/
  add_assoc : ∀ a b c : R, add (add a b) c = add a (add b c)
  /-- Addition is commutative. -/
  add_comm : ∀ a b : R, add a b = add b a
  /-- `zero` is a left unit. -/
  zero_add : ∀ a : R, add zero a = a
  /-- `zero` is a right unit. -/
  add_zero : ∀ a : R, add a zero = a

/-- **A quantity (R10).** A magnitude of a fixed kind `k`, carried at a
representation type `R`. Indexed by `k`, so the type system forbids forming or
comparing a `Quantity k₁ R` with a `Quantity k₂ R` when `k₁ ≠ k₂`; indexed by
`R`, so the same value type is instantiated at whichever numbers the task needs.
This indexing *is* the fix for the dimension-1 conflation. -/
structure Quantity (k : KindOfProperty) (R : Type) where
  /-- §13.3.3 — the magnitude (the *number* of the reference-times-number form),
  carried at the representation type `R`. -/
  magnitude : R

namespace Quantity

variable {k : KindOfProperty} {R : Type}

/-- The zero quantity of a kind (needs only a `Carrier`). -/
def zero [Carrier R] : Quantity k R := ⟨Carrier.zero⟩

/-- **Kind-gated addition (R4).** Addition of two quantities of the *same* kind
`k`. The type `Quantity k R → Quantity k R → Quantity k R` is itself the gate:
both summands must share the kind, so `Width + Width` type-checks while
`Width + Height` — and `Torque + Energy`, dimensions notwithstanding — does not. -/
def add [Carrier R] (x y : Quantity k R) : Quantity k R :=
  ⟨Carrier.add x.magnitude y.magnitude⟩

/-- Addition is commutative over any lawful carrier — proved once, for every `R`. -/
protected theorem add_comm [LawfulCarrier R] (x y : Quantity k R) :
    Quantity.add x y = Quantity.add y x := by
  unfold Quantity.add
  rw [LawfulCarrier.add_comm]

/-- Addition is associative over any lawful carrier — proved once, for every `R`. -/
protected theorem add_assoc [LawfulCarrier R] (x y z : Quantity k R) :
    Quantity.add (Quantity.add x y) z = Quantity.add x (Quantity.add y z) := by
  unfold Quantity.add
  rw [LawfulCarrier.add_assoc]

/-- The zero quantity is a left unit over any lawful carrier. -/
protected theorem zero_add [LawfulCarrier R] (x : Quantity k R) :
    Quantity.add Quantity.zero x = x := by
  unfold Quantity.add Quantity.zero
  rw [LawfulCarrier.zero_add]

/-- The zero quantity is a right unit over any lawful carrier. -/
protected theorem add_zero [LawfulCarrier R] (x : Quantity k R) :
    Quantity.add x Quantity.zero = x := by
  unfold Quantity.add Quantity.zero
  rw [LawfulCarrier.add_zero]

/-- **Representation-parametric additivity (R10).** The additivity laws hold over
*any* lawful carrier, established by a single proof and so available at every `R`
at once (`ℝ` for proofs, `Int`, …). The very `R` where these laws are absent —
an executable float, a `Carrier` but not a `LawfulCarrier` — is what the planned
exec/spec refinement bridge exists to reconcile. -/
theorem laws_parametric [LawfulCarrier R] (x y z : Quantity k R) :
    Quantity.add x y = Quantity.add y x
      ∧ Quantity.add (Quantity.add x y) z = Quantity.add x (Quantity.add y z)
      ∧ Quantity.add Quantity.zero x = x ∧ Quantity.add x Quantity.zero = x :=
  ⟨Quantity.add_comm x y, Quantity.add_assoc x y z,
    Quantity.zero_add x, Quantity.add_zero x⟩

end Quantity

/-! ## Concrete carriers

The same `Quantity` layer above, instantiated at three representation types. Two
are *lawful* (the additivity laws hold); the third runs but is deliberately not. -/

/-- `Int` is a numeric carrier. -/
instance instCarrierInt : Carrier Int where
  zero := 0
  add := (· + ·)

/-- `Int` is a *lawful* carrier: its additive-monoid laws come straight from the
core integer lemmas, so every `Quantity.add_*` law holds at `R := Int`. -/
instance : LawfulCarrier Int where
  toCarrier := instCarrierInt
  add_assoc := Int.add_assoc
  add_comm := Int.add_comm
  zero_add := Int.zero_add
  add_zero := Int.add_zero

/-- `Float` is a numeric carrier — the *executable* representation. A
`Quantity k Float` runs (`#eval` reduces its magnitude), which is what code
generation needs. It is **not** made a `LawfulCarrier`: floating-point addition is
not associative, so the additivity laws are intentionally unavailable here. That
absence is the gap the (planned) exec/spec refinement bridge closes — by relating
each float operation to the rounding of its real-number specification. -/
instance instCarrierFloat : Carrier Float where
  zero := 0.0
  add := (· + ·)

end PropertyKindCalculus
