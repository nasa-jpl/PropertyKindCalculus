/-
# The kind-indexed operator table — curated `*` / `/` on quantities

`Quantity.mul` / `Quantity.div` (`QuantityClassification`) are the verified constructors:
every application names its kind-law witness (`ProductKind k₁ k₂ k` / `QuotientKind`), so
the result is classified *by construction*. That discipline is the point of R12 — and,
spelled at every node of a large kernel, it is also why downstream models end up keeping
a naked duplicate: a five-term forward model written as nested
`Quantity.mul (ProductKind.ofRatio …) (Quantity.mul (ProductKind.ofRatio …) …) …`
does not read next to `a * ndvi + (att * c) * r + d`, so the readable naked form
survives as the authored one and the kinded form decays into an overlay.

This module closes the ergonomics gap **without weakening the discipline**. Two moves:

  * **`KindMul k₁ k₂ k` / `KindDiv k₁ k₂ k` — the curated table.** A typeclass whose
    instances an application registers *once*, next to its kind declarations: "the
    product of `k₁` and `k₂` is sanctioned and lands in `k`", witnessed by the same
    `ProductKind` / `QuotientKind` law the named constructor takes. The result kind is
    an `outParam`, so instance search *computes* `k` from the operand kinds — the piece
    autoParam spellings cannot supply for the interior kinds of a chained product.
    This is the core-spine, Prop-level counterpart of the Dimension layer's curated
    interaction algebra (`InteractionAlgebra.KMul`, Flater App. C): same curation idea,
    but resolvable by instance search and available Mathlib-free.
  * **Scoped `HMul` / `HDiv` instances.** Inside `open scoped
    PropertyKindCalculus.OperatorTable`, `x * y` elaborates through the table: the
    witness is carried by the instance, not the call site, and where no table entry
    exists the product **fails to elaborate** — exactly the compile error a naked
    magnitude cannot give. `HMul`/`HDiv` are `infixl`, so a chain `a * b * c` groups
    left — the same association as the corresponding naked-magnitude expression, so a
    kinded kernel and its `.magnitude` erasure are the *same* expression tree (this is
    load-bearing for bit-exact, `rfl`-provable erasure on `Float` and for op order on a
    tape carrier). The instances come in pairs — one for `Quantity`, one for the
    object-indexed `IndividualQuantity` — reading the *same* table, so an application
    registers its algebra once and authors with operators at either layer. On the instance
    layer the object index rides through untouched, so the shared-object gate is enforced by
    instance resolution failing to unify rather than by anything the author writes.

Discipline for table curation (the instances are the algebra, so curate them):

  * **At most one instance per operand pair `(k₁, k₂)`.** The `outParam` means instance
    search *silently picks* the registered result kind; a second instance for the same
    pair would make resolution order-dependent. Registering a pair twice is a design
    error, guarded by result-kind pin `example`s in the application's probe files.
  * **Scoped, opt-in.** The instances live in the `OperatorTable` namespace, so a file
    states `open scoped PropertyKindCalculus.OperatorTable` to author with operators.
    There is still — deliberately — no `Mul`/`Div` instance on `Quantity` itself, and
    no unscoped operator: an unconstrained instance would erase the witness discipline.
  * **The named forms remain primary for laws.** `x * y` *is* `Quantity.mul` of the
    table's witness (`hmul_eq_mul`), so every certificate and kind-law of the named
    calculus applies to operator-built terms by rewriting one `rfl` lemma.

For a one-off product not worth a table entry, `Quantity.mulK` / `Quantity.divK` below
name the result kind explicitly and discharge the ratio-scale gate by autoParam —
midway between the full witness spelling and a table registration.
-/

module

public import PropertyKindCalculus.QuantityClassification
public import PropertyKindCalculus.IndividualQuantity
-- Private scope only: the proofs below reduce through bodies sealed in `PropertyKindCalculus.IndividualQuantity`; `import all`
-- gives this module the reduction without exposing them to every consumer.
import all PropertyKindCalculus.IndividualQuantity

public section -- pkc-blanket

namespace PropertyKindCalculus

universe u

/-- **A curated product-table entry.** The product of a `k₁`- and a `k₂`-quantity is
sanctioned and lands in `k`, witnessed by the same kind-level law `Quantity.mul` takes.
`k` is an `outParam`: instance search computes the result kind from the operand kinds, so
a chained product finds its interior kinds without annotation. Applications register
instances next to their kind declarations — at most one per `(k₁, k₂)` pair. -/
class KindMul (k₁ k₂ : KindOfProperty) (k : outParam KindOfProperty) : Prop where
  /-- The kind-level product law backing this table entry. -/
  law : ProductKind k₁ k₂ k

/-- **A curated quotient-table entry.** The quotient of a `k₁`- by a `k₂`-quantity is
sanctioned and lands in `k`, witnessed by the `QuotientKind` law. Same curation
discipline as `KindMul`. -/
class KindDiv (k₁ k₂ : KindOfProperty) (k : outParam KindOfProperty) : Prop where
  /-- The kind-level quotient law backing this table entry. -/
  law : QuotientKind k₁ k₂ k

namespace OperatorTable

variable {R : Type} {k₁ k₂ k : KindOfProperty}

/-- `x * y` through the curated table: `Quantity.mul` of the registered witness. Scoped —
`open scoped PropertyKindCalculus.OperatorTable` opts a file in. -/
scoped instance instHMulQuantity [Mul R] [ScalarCarrier R] [KindMul k₁ k₂ k] :
    HMul (Quantity k₁ R) (Quantity k₂ R) (Quantity k R) :=
  ⟨fun x y => Quantity.mul KindMul.law x y⟩

/-- `x / y` through the curated table: `Quantity.div` of the registered witness. -/
scoped instance instHDivQuantity [Div R] [ScalarCarrier R] [KindDiv k₁ k₂ k] :
    HDiv (Quantity k₁ R) (Quantity k₂ R) (Quantity k R) :=
  ⟨fun x y => Quantity.div KindDiv.law x y⟩

/-- The table operator **is** the named verified constructor, witness supplied by the
instance — the one `rfl` that transports every certificate and kind-law of the named
calculus to operator-built terms. -/
theorem hmul_eq_mul [Mul R] [ScalarCarrier R] [KindMul k₁ k₂ k] (x : Quantity k₁ R) (y : Quantity k₂ R) :
    x * y = Quantity.mul (KindMul.law (k₁ := k₁) (k₂ := k₂) (k := k)) x y := rfl

/-- The division dual of `hmul_eq_mul`. -/
theorem hdiv_eq_div [Div R] [ScalarCarrier R] [KindDiv k₁ k₂ k] (x : Quantity k₁ R) (y : Quantity k₂ R) :
    x / y = Quantity.div (KindDiv.law (k₁ := k₁) (k₂ := k₂) (k := k)) x y := rfl

@[simp] theorem hmul_magnitude [Mul R] [ScalarCarrier R] [KindMul k₁ k₂ k]
    (x : Quantity k₁ R) (y : Quantity k₂ R) :
    (x * y).magnitude = x.magnitude * y.magnitude := rfl

@[simp] theorem hdiv_magnitude [Div R] [ScalarCarrier R] [KindDiv k₁ k₂ k]
    (x : Quantity k₁ R) (y : Quantity k₂ R) :
    (x / y).magnitude = x.magnitude / y.magnitude := rfl

/-- An operator-built product satisfies the product **certificate** of the table's
witness — classification by construction survives the sugar. -/
theorem hmul_isProduct [Mul R] [ScalarCarrier R] [KindMul k₁ k₂ k] (x : Quantity k₁ R) (y : Quantity k₂ R) :
    (x * y).IsProduct KindMul.law x y := rfl

/-- An operator-built quotient satisfies the quotient certificate of the table's
witness. -/
theorem hdiv_isQuotient [Div R] [ScalarCarrier R] [KindDiv k₁ k₂ k] (x : Quantity k₁ R) (y : Quantity k₂ R) :
    (x / y).IsQuotient KindDiv.law x y := rfl

/-! ## The same table, on object-indexed quantities

`IndividualQuantity o k R` (the instance layer) gates every operation on a *shared object* `o`
as well as on the kinds, so a product of two quantities belonging to different objects does not
type-check. That gate is worth nothing if the layer is unusable to write in, and the ceremony
the table removes for `Quantity` is if anything heavier here: an object-indexed model is where
the interior kinds of a chained product are most tedious to name.

The instances below read the **same** `KindMul` / `KindDiv` table — an application registers its
algebra once and gets operators at both layers. The object rides through untouched: it is the
same `o` on both operands and on the result, so instance resolution simply fails to unify when
the operands belong to different objects, and the object gate is enforced exactly as before,
without the author writing anything. Curation is likewise unchanged: an unregistered operand
pair has no entry and the product does not elaborate. -/

variable {O : Type u} {o : O}

/-- `x * y` on object-indexed quantities, through the curated table:
`IndividualQuantity.mul` of the registered witness, on the shared object `o`. Scoped, like its
`Quantity` twin. -/
scoped instance instHMulIndividualQuantity [Mul R] [ScalarCarrier R] [KindMul k₁ k₂ k] :
    HMul (IndividualQuantity o k₁ R) (IndividualQuantity o k₂ R) (IndividualQuantity o k R) :=
  ⟨fun x y => IndividualQuantity.mul KindMul.law x y⟩

/-- `x / y` on object-indexed quantities, through the curated table. -/
scoped instance instHDivIndividualQuantity [Div R] [ScalarCarrier R] [KindDiv k₁ k₂ k] :
    HDiv (IndividualQuantity o k₁ R) (IndividualQuantity o k₂ R) (IndividualQuantity o k R) :=
  ⟨fun x y => IndividualQuantity.div KindDiv.law x y⟩

/-- The table operator **is** the named verified constructor at the instance layer too — the
`rfl` that transports every certificate and kind-law of `IndividualQuantity` to operator-built
terms, and the reason the operator sugar is invisible to anything downstream that reads the
elaborated term (the `@[pkc_math]` renderer included). -/
theorem hmul_eq_mul_individual [Mul R] [ScalarCarrier R] [KindMul k₁ k₂ k]
    (x : IndividualQuantity o k₁ R) (y : IndividualQuantity o k₂ R) :
    x * y = IndividualQuantity.mul (KindMul.law (k₁ := k₁) (k₂ := k₂) (k := k)) x y := rfl

/-- The quotient twin of `hmul_eq_mul_individual`. -/
theorem hdiv_eq_div_individual [Div R] [ScalarCarrier R] [KindDiv k₁ k₂ k]
    (x : IndividualQuantity o k₁ R) (y : IndividualQuantity o k₂ R) :
    x / y = IndividualQuantity.div (KindDiv.law (k₁ := k₁) (k₂ := k₂) (k := k)) x y := rfl

@[simp] theorem hmul_magnitude_individual [Mul R] [ScalarCarrier R] [KindMul k₁ k₂ k]
    (x : IndividualQuantity o k₁ R) (y : IndividualQuantity o k₂ R) :
    (x * y).magnitude = x.magnitude * y.magnitude := by
  rw [hmul_eq_mul_individual, IndividualQuantity.mul]

@[simp] theorem hdiv_magnitude_individual [Div R] [ScalarCarrier R] [KindDiv k₁ k₂ k]
    (x : IndividualQuantity o k₁ R) (y : IndividualQuantity o k₂ R) :
    (x / y).magnitude = x.magnitude / y.magnitude := by
  rw [hdiv_eq_div_individual, IndividualQuantity.div]

/-- An operator-built product of object-indexed quantities satisfies the product certificate of
the table's witness — classification by construction survives the sugar at this layer too. -/
theorem hmul_isProduct_individual [Mul R] [ScalarCarrier R] [KindMul k₁ k₂ k]
    (x : IndividualQuantity o k₁ R) (y : IndividualQuantity o k₂ R) :
    (x * y).IsProduct KindMul.law x y := by
  rw [hmul_eq_mul_individual]
  exact IndividualQuantity.mul_isProduct KindMul.law x y

/-- The quotient certificate, likewise. -/
theorem hdiv_isQuotient_individual [Div R] [ScalarCarrier R] [KindDiv k₁ k₂ k]
    (x : IndividualQuantity o k₁ R) (y : IndividualQuantity o k₂ R) :
    (x / y).IsQuotient KindDiv.law x y := by
  rw [hdiv_eq_div_individual]
  exact IndividualQuantity.div_isQuotient KindDiv.law x y

/-- **The operator sugar does not cross objects.** Forgetting an operator-built product to the
plain `Quantity` layer is the plain layer's operator-built product of the forgotten operands, so
the object index is carried and dropped coherently rather than being quietly discarded. -/
theorem toQuantity_hmul_individual [Mul R] [ScalarCarrier R] [KindMul k₁ k₂ k]
    (x : IndividualQuantity o k₁ R) (y : IndividualQuantity o k₂ R) :
    (x * y).toQuantity = Quantity.mul KindMul.law x.toQuantity y.toQuantity := by
  rw [hmul_eq_mul_individual]
  exact IndividualQuantity.toQuantity_mul KindMul.law x y

end OperatorTable

/-- **One-off product, result kind named at the call site.** For a product not worth a
table entry: `Quantity.mulK area w h` reads as the kind equation it stands for, with the
ratio-scale gate discharged by autoParam for concrete kinds (exactly
`ProductKind.ofRatio`'s own defaults). -/
@[expose] def Quantity.mulK {R : Type} [Mul R] [ScalarCarrier R] {k₁ k₂ : KindOfProperty} (k : KindOfProperty)
    (a : Quantity k₁ R) (b : Quantity k₂ R)
    (h : ProductKind k₁ k₂ k := by exact ProductKind.ofRatio _ _ _) : Quantity k R :=
  Quantity.mul h a b

/-- **One-off quotient, result kind named at the call site** — the division dual of
`Quantity.mulK`. -/
@[expose] def Quantity.divK {R : Type} [Div R] [ScalarCarrier R] {k₁ k₂ : KindOfProperty} (k : KindOfProperty)
    (a : Quantity k₁ R) (b : Quantity k₂ R)
    (h : QuotientKind k₁ k₂ k := by exact QuotientKind.ofRatio _ _ _) : Quantity k R :=
  Quantity.div h a b

@[simp] theorem Quantity.mulK_magnitude {R : Type} [Mul R] [ScalarCarrier R] {k₁ k₂ : KindOfProperty}
    (k : KindOfProperty) (a : Quantity k₁ R) (b : Quantity k₂ R) (h : ProductKind k₁ k₂ k) :
    (Quantity.mulK k a b h).magnitude = a.magnitude * b.magnitude := rfl

@[simp] theorem Quantity.divK_magnitude {R : Type} [Div R] [ScalarCarrier R] {k₁ k₂ : KindOfProperty}
    (k : KindOfProperty) (a : Quantity k₁ R) (b : Quantity k₂ R) (h : QuotientKind k₁ k₂ k) :
    (Quantity.divK k a b h).magnitude = a.magnitude / b.magnitude := rfl

end PropertyKindCalculus

end -- pkc-blanket
