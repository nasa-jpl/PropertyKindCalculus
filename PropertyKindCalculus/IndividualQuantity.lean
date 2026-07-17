/-
# Individual quantity — a quantity that characterizes an object

Dybkær, *An Ontology on Property for Physical, Chemical, and Biological Systems*
(2009), Chapter 3 (system/object) and the instance layer.

`Quantity k R` (R10) records a magnitude of a *kind* `k`, but nothing about *whose*
quantity it is. Yet a measured quantity is always the property of some **object**: "the
length of *this* rectangle", "the glucose concentration of *this* plasma sample". Dybkær's
`IndividualProperty` (Kind.lean) captures that an individual property *instantiates* a kind
and *characterizes* an object — but carries no magnitude.

`IndividualQuantity o k R` is that instance layer made **quantitative**: an individual
property (kind `k` characterizing object `o`) that additionally bears a magnitude at
representation `R`. Crucially the object `o` rides in the *type*, exactly as the kind `k`
does. So the metrology gate the plain numeric model lacks becomes a *compile-time* fact:

  * two quantities combine with `mul` only when they **characterize the same object** — the
    length and the width must be *of the same rectangle*; multiplying a length of `R1` by a
    width of `R2` does not type-check; and
  * two quantities add with `add` only when they share **both** the object and the kind.

This is the first-class form of the object identity the `DedicatedKind` (Ch. 20) construct
expresses at the kind level, now available on quantities without tagging kinds by hand.
Whether two individual quantities of one object are *equal in magnitude* (e.g. a square's
length and width) remains, by contrast, a fact about the magnitudes — a theorem, never a
type-check.
-/
import PropertyKindCalculus.Foundations
import PropertyKindCalculus.Quantity
import PropertyKindCalculus.QuantityClassification

namespace PropertyKindCalculus

/-- **An individual quantity.** A magnitude of kind `k`, at representation `R`, that
**characterizes the object** `o` (Dybkær Ch. 3). Indexed by `o` as well as by `k`, so the
type system forbids combining quantities of *different objects* — the object-aware refinement
of `Quantity k R`, and the quantitative form of `IndividualProperty`. -/
structure IndividualQuantity (o : Object) (k : KindOfProperty) (R : Type) where
  /-- The magnitude, carried at the representation `R`. -/
  magnitude : R

namespace IndividualQuantity

variable {o : Object} {k : KindOfProperty} {R : Type}

/-- **Extensionality.** Two individual quantities of the same object, kind, and carrier are
equal exactly when their magnitudes are. -/
@[ext] theorem ext {x y : IndividualQuantity o k R} (h : x.magnitude = y.magnitude) : x = y := by
  cases x; cases y; cases h; rfl

/-- Forget the magnitude: the underlying **individual property** (kind `k` characterizing the
object `o`), tying this layer back to Dybkær's instance layer (`Kind.lean`). -/
def toIndividualProperty (_a : IndividualQuantity o k R) : IndividualProperty := ⟨k, o⟩

/-- Forget the object: the plain kind-indexed `Quantity k R`, so every `Quantity` law can be
reused on an individual quantity by projection. -/
def toQuantity (a : IndividualQuantity o k R) : Quantity k R := ⟨a.magnitude⟩

@[simp] theorem toQuantity_magnitude (a : IndividualQuantity o k R) :
    a.toQuantity.magnitude = a.magnitude := rfl

/-! ## Object- and kind-gated addition (R4, with object identity) -/

/-- **Same-object, same-kind addition.** Adds two quantities that characterize the *same*
object `o` and share the kind `k`, over the additive `Carrier`. Three gates, all in the type:
the object `o`, the kind `k`, and the `DifferenceKind k` scale witness. Adding a length of one
object to a length of another does not type-check. -/
def add [Carrier R] (_h : DifferenceKind k) (x y : IndividualQuantity o k R) :
    IndividualQuantity o k R :=
  ⟨Carrier.add x.magnitude y.magnitude⟩

@[simp] theorem add_magnitude [Carrier R] (h : DifferenceKind k)
    (x y : IndividualQuantity o k R) :
    (add h x y).magnitude = Carrier.add x.magnitude y.magnitude := rfl

/-- Addition commutes with the forgetful map to `Quantity`, so `Quantity`'s additivity laws
transfer verbatim. -/
theorem toQuantity_add [Carrier R] (h : DifferenceKind k) (x y : IndividualQuantity o k R) :
    (add h x y).toQuantity = Quantity.add h x.toQuantity y.toQuantity := rfl

/-! ## Object-gated, kind-licensed product (R5/R12, with object identity) -/

/-- **Same-object, kind-licensed product.** Multiplies a `k₁`- and a `k₂`-quantity that
characterize the *same* object `o`, licensed by the product kind-law `ProductKind k₁ k₂ k`,
yielding a `k`-quantity of that object. The shared `o` is the gate a dimensionless numeric
model cannot express: the two factors must be *of the same object*. -/
def mul [Mul R] {k₁ k₂ k : KindOfProperty} (_h : ProductKind k₁ k₂ k)
    (a : IndividualQuantity o k₁ R) (b : IndividualQuantity o k₂ R) : IndividualQuantity o k R :=
  ⟨a.magnitude * b.magnitude⟩

@[simp] theorem mul_magnitude [Mul R] {k₁ k₂ k : KindOfProperty} (h : ProductKind k₁ k₂ k)
    (a : IndividualQuantity o k₁ R) (b : IndividualQuantity o k₂ R) :
    (mul h a b).magnitude = a.magnitude * b.magnitude := rfl

/-- The product commutes with the forgetful map to `Quantity`. -/
theorem toQuantity_mul [Mul R] {k₁ k₂ k : KindOfProperty} (h : ProductKind k₁ k₂ k)
    (a : IndividualQuantity o k₁ R) (b : IndividualQuantity o k₂ R) :
    (mul h a b).toQuantity = Quantity.mul h a.toQuantity b.toQuantity := rfl

/-- **The product certificate.** `q` (kind `k`, object `o`) is the product of `a` and `b`: its
magnitude is the product of theirs. A proof *certifies* `q`'s classification, rather than
merely asserting it (R12). -/
def IsProduct [Mul R] {k₁ k₂ k : KindOfProperty} (_h : ProductKind k₁ k₂ k)
    (q : IndividualQuantity o k R) (a : IndividualQuantity o k₁ R) (b : IndividualQuantity o k₂ R) :
    Prop :=
  q.magnitude = a.magnitude * b.magnitude

/-- The smart-constructed product satisfies the certificate **by construction**. -/
theorem mul_isProduct [Mul R] {k₁ k₂ k : KindOfProperty} (h : ProductKind k₁ k₂ k)
    (a : IndividualQuantity o k₁ R) (b : IndividualQuantity o k₂ R) :
    (mul h a b).IsProduct h a b := rfl

/-! ## Object-gated, kind-licensed quotient (`k = k₁ / k₂`) -/

/-- **Same-object, kind-licensed quotient.** Divides a `k₁`- by a `k₂`-quantity that
characterize the *same* object `o`, licensed by the quotient kind-law. Dividing across objects
does not type-check. -/
def div [Div R] {k₁ k₂ k : KindOfProperty} (_h : QuotientKind k₁ k₂ k)
    (a : IndividualQuantity o k₁ R) (b : IndividualQuantity o k₂ R) : IndividualQuantity o k R :=
  ⟨a.magnitude / b.magnitude⟩

@[simp] theorem div_magnitude [Div R] {k₁ k₂ k : KindOfProperty} (h : QuotientKind k₁ k₂ k)
    (a : IndividualQuantity o k₁ R) (b : IndividualQuantity o k₂ R) :
    (div h a b).magnitude = a.magnitude / b.magnitude := rfl

/-- The quotient commutes with the forgetful map to `Quantity`. -/
theorem toQuantity_div [Div R] {k₁ k₂ k : KindOfProperty} (h : QuotientKind k₁ k₂ k)
    (a : IndividualQuantity o k₁ R) (b : IndividualQuantity o k₂ R) :
    (div h a b).toQuantity = Quantity.div h a.toQuantity b.toQuantity := rfl

/-- **The quotient certificate** (R12): `q` (kind `k`, object `o`) is the quotient of `a` by `b`. -/
def IsQuotient [Div R] {k₁ k₂ k : KindOfProperty} (_h : QuotientKind k₁ k₂ k)
    (q : IndividualQuantity o k R) (a : IndividualQuantity o k₁ R) (b : IndividualQuantity o k₂ R) :
    Prop :=
  q.magnitude = a.magnitude / b.magnitude

/-- The smart-constructed quotient satisfies the certificate **by construction**. -/
theorem div_isQuotient [Div R] {k₁ k₂ k : KindOfProperty} (h : QuotientKind k₁ k₂ k)
    (a : IndividualQuantity o k₁ R) (b : IndividualQuantity o k₂ R) :
    (div h a b).IsQuotient h a b := rfl

/-! ## Object-carried reciprocal (`k = 1 / k₁`) -/

/-- **Reciprocal, on one object.** The reciprocal of a `k₁`-quantity characterizing object `o`,
licensed by the reciprocal kind-law; it characterizes the *same* object `o`. -/
def recip [Inv R] {k₁ k : KindOfProperty} (_h : ReciprocalKind k₁ k)
    (a : IndividualQuantity o k₁ R) : IndividualQuantity o k R :=
  ⟨a.magnitude⁻¹⟩

@[simp] theorem recip_magnitude [Inv R] {k₁ k : KindOfProperty} (h : ReciprocalKind k₁ k)
    (a : IndividualQuantity o k₁ R) : (recip h a).magnitude = a.magnitude⁻¹ := rfl

/-- The reciprocal commutes with the forgetful map to `Quantity`. -/
theorem toQuantity_recip [Inv R] {k₁ k : KindOfProperty} (h : ReciprocalKind k₁ k)
    (a : IndividualQuantity o k₁ R) :
    (recip h a).toQuantity = Quantity.recip h a.toQuantity := rfl

/-- **The reciprocal certificate** (R12): `q` (kind `k`, object `o`) is the reciprocal of `a`. -/
def IsReciprocal [Inv R] {k₁ k : KindOfProperty} (_h : ReciprocalKind k₁ k)
    (q : IndividualQuantity o k R) (a : IndividualQuantity o k₁ R) : Prop :=
  q.magnitude = a.magnitude⁻¹

/-- The smart-constructed reciprocal satisfies the certificate **by construction**. -/
theorem recip_isReciprocal [Inv R] {k₁ k : KindOfProperty} (h : ReciprocalKind k₁ k)
    (a : IndividualQuantity o k₁ R) : (recip h a).IsReciprocal h a := rfl

end IndividualQuantity

end PropertyKindCalculus
