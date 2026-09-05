/-
# ISO 80000-2 — *Mathematics*: the items this library's carriers realize

Part 2 of the series is a table of **mathematical signs and symbols** — 239 numbered items
across logic, sets, operations, functions, complex numbers, matrices, coordinate systems,
vectors and tensors. It defines no quantities and assigns no dimensions, so a catalogue in
the shape of `Part3` … `Part13` would be a category error, and this module does not attempt
one. Neither does it transcribe the table: a symbol list restated in Lean would be a second
copy of a document, checked by nothing.

What it records instead is the **intersection that carries weight for this library**: the
items whose mathematical objects `PropertyKindCalculus` actually instantiates, keyed by
item number, each with the declaration that realizes it. Three groups:

  * **§7, standard number sets and intervals.** `Quantity k R` is parametric in its numeric
    carrier (R10), and the carriers this library supplies are the standard's own sets — the
    natural numbers (2-7.1), the integers (2-7.2), the reals (2-7.4) and the complex numbers
    (2-7.5) — plus one that is *not* in the standard's table at all. `Float` is a finite set
    of dyadic rationals, and it is exactly the carrier that instantiates `Carrier` without
    `LawfulCarrier`: the arithmetic runs, the laws do not hold. Recording that against §7 is
    R15's premise stated at its source. The closed interval (2-7.7) is `IccQ`, with its
    endpoints role-typed so that a swapped construction is a type error.
  * **§15, complex numbers.** The complexified carrier `Complex R` (R10's fourth
    representation): complex-ness is a property of the carrier, not of the kind, so the
    imaginary unit (2-15.1), real and imaginary part (2-15.2, 2-15.3) and modulus (2-15.4)
    live under the carrier and leave the kind layer untouched.
  * **§18, scalars, vectors and tensors.** The clause this library's R11 requirement is
    drawn from: a vector quantity is a numerical vector times *one* scalar unit. The sum of
    two vectors is componentwise (2-18.2) — the pointwise carrier — and the product of a
    number and a vector (2-18.3) is `Quantity.smulK`, which is componentwise on the numbers
    and a licensed kind change on the kinds. The second half is what §18 leaves to the
    quantity layer and what this library adds.

Everything outside those three groups is deliberately absent, and that is a scoping
decision rather than an omission: this library realizes no part of §5 (mathematical logic),
§9 (elementary geometry), §11 (combinatorics), §17 (coordinate systems), §19 (transforms) or
§20 (special functions), so it has nothing to check against them.

No normative text from the licensed standard is reproduced; the items are restated in this
work's own formalism.
-/

import PropertyKindCalculus.Bounds
import PropertyKindCalculus.Complex
import PropertyKindCalculus.QuantityVector
import PropertyKindCalculus.Iso80000.References
import PropertyKindCalculus.QuantityReal

namespace PropertyKindCalculus.Iso80000.Part2

open PropertyKindCalculus

/-- The source: ISO 80000-2, the *Mathematics* part of the series. -/
def source : StandardRef := iso80000_2

/-! ## §7 — Standard number sets, as the carriers of `Quantity`

The clause names ℕ, ℤ, ℚ, ℝ, ℂ and the intervals. `Quantity k R` takes its numbers from a
carrier `R` (R10), so the clause's sets appear here as the carrier instances this library
supplies. The separation that matters is between `Carrier` — the arithmetic exists — and
`LawfulCarrier` — the arithmetic obeys the additivity laws the quantity layer proves once
and transports. -/

namespace Section7

/-- **2-7.1, ℕ.** The natural numbers carry the arithmetic and the laws. -/
example : LawfulCarrier Nat := inferInstance

/-- **2-7.2, ℤ.** The integers likewise — the exact carrier the Mathlib-free examples use. -/
example : LawfulCarrier Int := inferInstance

/-- **2-7.4, ℝ.** The reals are this library's specification carrier: every law about
magnitudes is proved here and transported down. -/
noncomputable example : LawfulCarrier ℝ := inferInstance

/-- **2-7.5, ℂ.** The complex numbers arrive as a *functor on carriers*: complexifying a
lawful carrier is lawful, so the kind layer applies verbatim over `Complex ℝ`. -/
noncomputable example : LawfulCarrier (Complex ℝ) := inferInstance

/-- **The carrier the clause does not list.** `Float` is a finite set of dyadic rationals,
not one of §7's sets. It carries the arithmetic — quantities over it run and `#eval` —
and it is the one carrier in this library for which no `LawfulCarrier` instance exists,
because the laws are false of it. The gap between the two instances is where numerical
adequacy (R15) begins. -/
example : Carrier Float := inferInstance

/-- **2-7.7, the closed interval `[a, b]`.** The kind-indexed counterpart, with the
endpoints carried as *roles* rather than as a pair of magnitudes, so that a swapped
construction does not typecheck. -/
example (k : KindOfProperty) : IccQ k Int → LowerBound k Int := IccQ.lo

end Section7

/-! ## §15 — Complex numbers, as a carrier and not as a kind

The clause's complex objects sit entirely below the kind layer. A complex-valued
permittivity is *one* kind — dimension one, ratio-scale — whose magnitude happens to be
complex; it is not two real kinds and not a new dimension. -/

namespace Section15

/-- **2-15.1 … 2-15.4 live under the carrier.** The complexified carrier is built from the
real one, so a quantity of *any* kind can take a complex magnitude without the kind, scale,
dimension or interaction layers changing. -/
noncomputable example : Carrier (Complex ℝ) := inferInstance

/-- The kind is untouched by the carrier: one kind reads at a real carrier and at the
complexified one, and the two quantity types are distinct types over the *same* kind. -/
example (k : KindOfProperty) : (Quantity k Int) × (Quantity k (Complex Int)) → KindOfProperty :=
  fun _ => k

end Section15

/-! ## §18 — Scalars, vectors and tensors

The clause this library's R11 is drawn from: units are scalar, so a vector quantity is a
numerical vector times one scalar unit. Its two elementary operations are componentwise on
the numbers; what the quantity layer adds is the kind side, which the clause does not
speak to. -/

namespace Section18

variable {ι : Type} {R : Type} [LawfulCarrier R]

/-- **2-18.2, the sum of two vectors** — componentwise, and lawful componentwise: the
pointwise carrier is a `LawfulCarrier` whenever its scalars are, so the additivity laws the
quantity layer proves once transport to vector quantities with no vector-specific proof. -/
example : LawfulCarrier (ι → R) := inferInstance

/-- **2-18.3, the product of a number and a vector** — componentwise on the numbers, and on
the kinds a *licensed* change: `Quantity.smulK` takes the same `ProductKind` law that the
homogeneous product takes, so scaling a vector quantity by a scalar quantity lands at a kind
the law names rather than at whichever kind the call site assumed. -/
example {V : Type} [SMul R V] [ScalarCarrier R] {k₁ k₂ k : KindOfProperty}
    (h : ProductKind k₁ k₂ k) (a : Quantity k₁ R) (b : Quantity k₂ V) :
    (Quantity.smulK h a b).magnitude = a.magnitude • b.magnitude :=
  Quantity.smulK_magnitude h a b

/-- **The scalar action is certified, not asserted** (R12): the smart-constructed product
satisfies its own classification certificate by construction. -/
example {V : Type} [SMul R V] [ScalarCarrier R] {k₁ k₂ k : KindOfProperty}
    (h : ProductKind k₁ k₂ k) (a : Quantity k₁ R) (b : Quantity k₂ V) :
    (Quantity.smulK h a b).IsSMul h a b :=
  Quantity.smulK_isSMul h a b

end Section18

end PropertyKindCalculus.Iso80000.Part2
