/-
# Validation probes — the kind-indexed operator table

Inhabitation, boundary, and axiom-profile probes for `KindMul`/`KindDiv` and the scoped
`HMul`/`HDiv` instances (`PropertyKindCalculus.OperatorTable`). The probes check the
three properties the module's discipline rests on:

  * a registered pair elaborates through the table, with the result kind *computed* by
    instance search (the `outParam`), and computes the right magnitude;
  * an *unregistered* pair fails to elaborate — the table is a real gate, not a
    formality (and neither `Quantity` nor the operand kinds leak an unconstrained
    `Mul`);
  * the operator **is** the named verified constructor (`hmul_eq_mul` is `rfl`), so
    the certificates of the named calculus transport to operator-built terms.
-/

module

public import PropertyKindCalculus

public section -- pkc-blanket
@[expose] section -- pkc-blanket-expose

namespace PropertyKindCalculus.Tests.OperatorTable

open PropertyKindCalculus
open scoped PropertyKindCalculus.OperatorTable

/-- Length, a ratio kind. -/
def lengthK : KindOfProperty := { id := "length", scale := .ratio }
/-- Area, a ratio kind — the sanctioned product of two lengths. -/
def areaK : KindOfProperty := { id := "area", scale := .ratio }
/-- Colour, a nominal kind — sanctioned in no product. -/
def colourK : KindOfProperty := { id := "colour", scale := .nominal }

/-- The one curated entry: length × length = area. -/
instance : KindMul lengthK lengthK areaK := ⟨ProductKind.ofRatio _ _ _⟩
/-- Its quotient dual: area / length = length. -/
instance : KindDiv areaK lengthK lengthK := ⟨QuotientKind.ofRatio _ _ _⟩

-- Inhabitation: a registered pair elaborates through the table and computes — `3 * 4 = 12`
-- over the lawful carrier `Int`, with the result kind found by instance search.
example : ((⟨3⟩ : Quantity lengthK Int) * (⟨4⟩ : Quantity lengthK Int)).magnitude = 12 := rfl
example : ((⟨12⟩ : Quantity areaK Int) / (⟨4⟩ : Quantity lengthK Int)).magnitude = 3 := rfl

-- Result-kind pin (the curation guard): the product of two lengths *is* an area — a second,
-- conflicting table entry for the pair `(lengthK, lengthK)` would break this `rfl`, so a
-- silent `outParam` redirection cannot land unnoticed.
example : ((⟨3⟩ : Quantity lengthK Int) * (⟨4⟩ : Quantity lengthK Int))
    = (⟨12⟩ : Quantity areaK Int) := rfl

-- The operator is the named constructor, witness supplied by the instance — certificates
-- transport by this one `rfl`.
example (x y : Quantity lengthK Int) :
    x * y = Quantity.mul (ProductKind.ofRatio lengthK lengthK areaK) x y := rfl
example (x y : Quantity lengthK Int) :
    (x * y).IsProduct (KindMul.law (k := areaK)) x y := OperatorTable.hmul_isProduct x y

-- Boundary (Rule 2): an *unregistered* pair does not elaborate — there is no
-- `KindMul colourK lengthK ?k` entry (and no unconstrained `Mul` on `Quantity` to fall
-- back to), so the product of a colour and a length is a compile error, exactly the
-- error a naked magnitude cannot give.
#check_failure ((⟨1⟩ : Quantity colourK Int) * (⟨2⟩ : Quantity lengthK Int))

-- Boundary: same-kind multiplication is *also* gated — `lengthK * areaK` has no entry, so
-- even ratio-scale operands do not multiply without curation.
#check_failure ((⟨1⟩ : Quantity lengthK Int) * (⟨2⟩ : Quantity areaK Int))

-- The one-off helpers name the result kind at the call site, ratio gate by autoParam.
example : (Quantity.mulK areaK (⟨3⟩ : Quantity lengthK Int)
    (⟨4⟩ : Quantity lengthK Int)).magnitude = 12 := rfl
example : (Quantity.divK lengthK (⟨12⟩ : Quantity areaK Int)
    (⟨4⟩ : Quantity lengthK Int)).magnitude = 3 := rfl

/-- info: 'PropertyKindCalculus.OperatorTable.hmul_eq_mul' does not depend on any axioms -/
#guard_msgs in #print axioms OperatorTable.hmul_eq_mul

/-- info: 'PropertyKindCalculus.OperatorTable.hmul_magnitude' does not depend on any axioms -/
#guard_msgs in #print axioms OperatorTable.hmul_magnitude

/-- info: 'PropertyKindCalculus.OperatorTable.hdiv_magnitude' does not depend on any axioms -/
#guard_msgs in #print axioms OperatorTable.hdiv_magnitude

end PropertyKindCalculus.Tests.OperatorTable

end -- pkc-blanket-expose
end -- pkc-blanket
