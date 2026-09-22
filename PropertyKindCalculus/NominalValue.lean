/-
# NominalValue — the type-indexed nominal property value (Dybkær §12.4, §13.2.1)

The nominal counterpart of `Quantity`. A `Quantity k R` carries a *magnitude* and is
therefore meaningful only for kinds-of-quantity (§13.3.1; `nominal_not_quantity` proves a
nominal kind has no magnitude to carry). But nominal kinds-of-property are first-class in
the ontology (§13.2.1: comparable for equality, nothing else), and value-level data of
nominal kind flows through APIs constantly — file contents, field keys, paths, provenance
labels — almost always as the SAME representation type (`String`), which is exactly the
argument-swap hole the kind index exists to close: a `/proc/meminfo` dump and the field
key to look up in it are both `String`s, and a call that swaps them type-checks today
while being a parse error by construction.

`NominalValue k R` is the fix, mirroring `Quantity` point for point:

  * type-indexed by the kind, so cross-kind confusion is a compile error, not a runtime
    surprise;
  * carrier-polymorphic in `R` (usually `String`, but a designation can ride any
    identity-comparable representation);
  * the ONLY operator instance is `==` — the nominal scale licenses equality and nothing
    else (§13.2.1), so there is deliberately no order, no arithmetic, and no analogue of
    the product/quotient laws;
  * like `Quantity`, the structure does not *enforce* `k.IsNominal` — scale licensing
    lives on the operations and the declaring module's discipline, not on a proof
    obligation at every literal.

Ingest and erasure mirror the quantity story: a mint `⟨s⟩` is the boundary where raw text
becomes kinded (license it where the provenance is — e.g. adjacent to the file path that
was read), and `.value` is the erasure back into lexical processing.
-/

module

public import PropertyKindCalculus.Kind

public section -- pkc-blanket

namespace PropertyKindCalculus

/-- **§12.4 nominal property value**, type-indexed. A designation of the fixed nominal
kind `k`, carried at representation `R`. The nominal dual of `Quantity`: same indexing
discipline, no magnitude — see the module header. -/
structure NominalValue (k : KindOfProperty) (R : Type) where
  /-- The designation (text, label, category id). `.value` is the erasure boundary. -/
  value : R

namespace NominalValue

variable {k : KindOfProperty} {R : Type}

/-- **The reviewed nominal mint** — `Quantity.attest`'s analogue at the nominal carrier:
semantically the constructor, but the reason is harvested by the boundary audit (a built-in
attestor, like `Quantity.attest`), so a designation that enters by authored classification
lands in the reviewed column rather than the raw one. -/
@[inline] def attest (_why : String) (v : R) : NominalValue k R := ⟨v⟩

/-- Same-kind `==` — the ONE operation the nominal scale licenses (§13.2.1). Cross-kind
equality is already a type error. -/
instance instBEq [BEq R] : BEq (NominalValue k R) := ⟨fun a b => a.value == b.value⟩

instance instDecidableEq [DecidableEq R] : DecidableEq (NominalValue k R) :=
  fun a b => match a, b with
    | ⟨x⟩, ⟨y⟩ =>
      if h : x = y then .isTrue (by simp [h]) else .isFalse (by simp [h])

/-- Render as the designation (the kind rides the type, not the print). -/
instance instRepr [Repr R] : Repr (NominalValue k R) := ⟨fun v p => reprPrec v.value p⟩

@[simp] theorem beq_iff [BEq R] (a b : NominalValue k R) :
    (a == b) = (a.value == b.value) := rfl

@[simp] theorem mk_value (x : R) : (⟨x⟩ : NominalValue k R).value = x := rfl

end NominalValue

end PropertyKindCalculus

end -- pkc-blanket
