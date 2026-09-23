/-
# The specialization lift — widening along `Specializes`, and the licensed sum at the join

`Specialization` proves the lattice-side facts: `Specializes E` is a preorder, and two kinds
are `MutuallyComparable` when they share a super-kind. What it did not provide — and what the
ForPhysLib harmonic-oscillator benchmark (MR32) exposed as owed — is a **quantity-level**
operation that consumes those proofs. With kinetic and potential energy kept distinct (they
answer different examination principles), `H = T + V` must still be writable: not at either
sub-kind, but at the kind both provably specialize. Until this module, nothing consumed a
`Specializes` proof, so distinguishing the energy family made the Hamiltonian unwritable —
over-rejection, the failure mode this calculus exists to avoid charging to its users.

This module supplies the lift, in the house discipline:

  * **`Quantity.widen` — the verified constructor.** Re-classify a `k`-quantity at a
    super-kind `p`, licensed by a `Specializes E k p` proof; the magnitude is untouched.
    Widening along `refl` is the identity and widening composes along `trans`
    (`widen_widen`), so the lift is functorial on the specialization preorder. The dual
    direction — *narrowing* a `p`-quantity to a sub-kind — is deliberately absent: a
    general energy is not thereby a kinetic one.
  * **`Quantity.addAt` / `Quantity.leAt` — the sum and the comparison at the join.** The
    two operations VIM comparability licenses, in named-witness form. The sum of two
    quantities of comparable kinds lands **at the join** — gated, as every sum is, by
    `DifferenceKind`, at the join — and the comparison is gated by `OrderKind` at the
    join. Neither is available at either sub-kind: comparability, not identity.
  * **`KindJoin` — the curated table**, the specialization twin of `KindMul`. An
    application registers, once, next to its edge relation, that `k₁` and `k₂` join at
    `p` — witnessed by the same two `Specializes` proofs `addAt` takes, plus the
    `DifferenceKind p` gate — and the scoped `HAdd` instances then elaborate `T + V` with
    the witnesses carried by the instance rather than the call site. An unregistered pair
    fails to elaborate. The curation discipline is the same as the operator table: at most
    one instance per operand pair, scoped and opt-in, named forms primary for laws.

This is the specialization twin of the licensed aggregation in `Extensivity`: there, a
whole's value may be the sum of its parts' only where the kind licenses it; here, values
of *different* kinds may meet in a sum only where their kinds provably meet.
-/

module

public import PropertyKindCalculus.Specialization
public import PropertyKindCalculus.Bounds
public import PropertyKindCalculus.OperatorTable
-- Private scope only: the proofs below reduce through bodies sealed in
-- `PropertyKindCalculus.IndividualQuantity`; `import all` gives this module the reduction
-- without exposing them to every consumer.
import all PropertyKindCalculus.IndividualQuantity

public section Interface

namespace PropertyKindCalculus

universe u

variable {R : Type} {E : KindOfProperty → KindOfProperty → Prop}
variable {k k₁ k₂ p p' : KindOfProperty}

/-! ## Widening — the verified constructor -/

/-- **Verified re-classification.** View a `k`-quantity at a super-kind `p`, licensed by a
`Specializes E k p` proof: a kinetic energy *is* an energy. The magnitude is untouched —
only the classification index moves, and only upward along a proved specialization. -/
@[expose] def Quantity.widen (_h : Specializes E k p) (x : Quantity k R) : Quantity p R :=
  ⟨x.magnitude⟩

@[simp] theorem Quantity.widen_magnitude (h : Specializes E k p) (x : Quantity k R) :
    (x.widen h).magnitude = x.magnitude := by rw [Quantity.widen]

/-- Widening along reflexivity is the identity — viewing a quantity at its own kind is not
an operation. -/
theorem Quantity.widen_refl (x : Quantity k R) :
    x.widen (Specializes.refl (E := E) k) = x := by rw [Quantity.widen]

/-- Widening composes along transitivity: two steps up the lattice are one step along the
composite proof. Together with `widen_refl`, the lift is functorial on the specialization
preorder. -/
theorem Quantity.widen_widen (h₁ : Specializes E k p) (h₂ : Specializes E p p')
    (x : Quantity k R) :
    (x.widen h₁).widen h₂ = x.widen (h₁.trans h₂) := by rw [Quantity.widen]; rfl

/-- **The certificate.** `y` (of the super-kind `p`) *is the widening* of `x` (of `k`):
same magnitude, re-classified along a proved specialization. A separate `Prop`, carried
only when needed — uniform with `Quantity.IsProduct`. -/
def Quantity.IsWidening (_h : Specializes E k p) (y : Quantity p R) (x : Quantity k R) :
    Prop :=
  y.magnitude = x.magnitude

/-- The smart-constructed widening satisfies the certificate **by construction**. -/
theorem Quantity.widen_isWidening (h : Specializes E k p) (x : Quantity k R) :
    (x.widen h).IsWidening h x := by rw [Quantity.widen, Quantity.IsWidening]

/-! ## Widening at the instance layer

The object index rides through untouched: oscillator A's kinetic energy, viewed as an
energy, is still oscillator A's. -/

variable {O : Type u} {o : O}

/-- Widening on an object-indexed quantity: the kind index moves up the lattice, the
object index is carried unchanged. -/
@[expose] def IndividualQuantity.widen (_h : Specializes E k p) (x : IndividualQuantity o k R) :
    IndividualQuantity o p R :=
  ⟨x.magnitude⟩

@[simp] theorem IndividualQuantity.widen_magnitude (h : Specializes E k p)
    (x : IndividualQuantity o k R) :
    (x.widen h).magnitude = x.magnitude := by rw [IndividualQuantity.widen]

/-- Widening commutes with forgetting the object — the two lifts are coherent. -/
theorem IndividualQuantity.toQuantity_widen (h : Specializes E k p)
    (x : IndividualQuantity o k R) :
    (x.widen h).toQuantity = x.toQuantity.widen h := by
  rw [IndividualQuantity.widen, Quantity.widen, IndividualQuantity.toQuantity]; rfl

/-! ## The sum and the comparison at the join — named-witness forms -/

/-- **The licensed sum at the join.** `T + V` with the kinds kept distinct: both terms are
widened along their `Specializes` proofs and added *at the join* `p`, under the same
`DifferenceKind` scale gate every sum carries — discharged at the join, where the sum
lives. The result is classified `p` by construction; it is *not* available at either
sub-kind. -/
@[expose] def Quantity.addAt [Carrier R] (h₁ : Specializes E k₁ p) (h₂ : Specializes E k₂ p)
    (hd : DifferenceKind p) (x : Quantity k₁ R) (y : Quantity k₂ R) : Quantity p R :=
  Quantity.add hd (x.widen h₁) (y.widen h₂)

@[simp] theorem Quantity.addAt_magnitude [Carrier R]
    (h₁ : Specializes E k₁ p) (h₂ : Specializes E k₂ p) (hd : DifferenceKind p)
    (x : Quantity k₁ R) (y : Quantity k₂ R) :
    (Quantity.addAt h₁ h₂ hd x y).magnitude = Carrier.add x.magnitude y.magnitude := by
  rw [Quantity.addAt, Quantity.widen, Quantity.add]; rfl

/-- The sum at the join is commutative over any lawful carrier — `T + V = V + T`, with the
witnesses swapped along with the operands. -/
theorem Quantity.addAt_comm [LawfulCarrier R]
    (h₁ : Specializes E k₁ p) (h₂ : Specializes E k₂ p) (hd : DifferenceKind p)
    (x : Quantity k₁ R) (y : Quantity k₂ R) :
    Quantity.addAt h₁ h₂ hd x y = Quantity.addAt h₂ h₁ hd y x :=
  Quantity.add_comm hd _ _

/-- The sum at the join is not a new addition: it is `Quantity.add`, same-kind at the
join, after the lift. -/
theorem Quantity.addAt_eq_add_widen [Carrier R]
    (h₁ : Specializes E k₁ p) (h₂ : Specializes E k₂ p) (hd : DifferenceKind p)
    (x : Quantity k₁ R) (y : Quantity k₂ R) :
    Quantity.addAt h₁ h₂ hd x y = Quantity.add hd (x.widen h₁) (y.widen h₂) := by
  rw [Quantity.addAt]

/-- **The comparison at the join.** Quantities of comparable kinds are compared where
their kinds meet — gated by `OrderKind` at the join (ordinal or richer, Dybkær §12.16):
"is the kinetic energy larger than the potential?" is a question about energies. Stated on
the magnitudes, licensed by the lattice. -/
def Quantity.leAt [LE R] (_h₁ : Specializes E k₁ p) (_h₂ : Specializes E k₂ p)
    (_ho : OrderKind p) (x : Quantity k₁ R) (y : Quantity k₂ R) : Prop :=
  x.magnitude ≤ y.magnitude

/-! ## The curated join table -/

/-- **A curated join-table entry** — the specialization twin of `KindMul`. Registered once
per application, next to the edge relation it cites: `k₁` and `k₂` are comparable and
their sum lands at `p`, witnessed by the two `Specializes` proofs `addAt` takes plus the
`DifferenceKind` gate at the join. `E` and `p` are `outParam`s: instance search computes,
from the operand kinds alone, which family's lattice licenses the sum and where it lands.

Curation discipline, as for `KindMul`: at most one instance per operand pair `(k₁, k₂)` —
register the symmetric pair explicitly (or via `KindJoin.symm`) if `V + T` is wanted too —
and do **not** register the diagonal `(k, k)`: same-kind addition is `Quantity.add`'s job,
and a diagonal entry would shadow it with a join. -/
class KindJoin (E : outParam (KindOfProperty → KindOfProperty → Prop))
    (k₁ k₂ : KindOfProperty) (p : outParam KindOfProperty) : Prop where
  /-- The left operand's kind specializes the join. -/
  left : Specializes E k₁ p
  /-- The right operand's kind specializes the join. -/
  right : Specializes E k₂ p
  /-- The join's scale licenses `+`/`−` — the same gate every sum carries. -/
  diff : DifferenceKind p

/-- A registered join makes its operand kinds mutually comparable — the table entry *is*
the VIM comparability fact, witnessed. -/
theorem KindJoin.comparable (j : KindJoin E k₁ k₂ p) : MutuallyComparable E k₁ k₂ :=
  ⟨p, j.left, j.right⟩

/-- The symmetric entry, from a registered one — how an application gets `V + T` from its
`T + V` registration without restating the witnesses. -/
theorem KindJoin.symm (j : KindJoin E k₁ k₂ p) : KindJoin E k₂ k₁ p :=
  ⟨j.right, j.left, j.diff⟩

namespace OperatorTable

/-- `x + y` across comparable kinds, through the curated join table: `Quantity.addAt` of
the registered witnesses, landing at the join. Scoped, like the `KindMul` operators —
`open scoped PropertyKindCalculus.OperatorTable` opts a file in, and an unregistered kind
pair fails to elaborate. -/
scoped instance instHAddQuantityJoin [Carrier R] [j : KindJoin E k₁ k₂ p] :
    HAdd (Quantity k₁ R) (Quantity k₂ R) (Quantity p R) :=
  ⟨fun x y => Quantity.addAt j.left j.right j.diff x y⟩

/-- The join operator **is** the named verified constructor, witnesses supplied by the
instance — the `rfl` that transports every law of `addAt` to operator-built sums. -/
theorem hadd_eq_addAt [Carrier R] [j : KindJoin E k₁ k₂ p]
    (x : Quantity k₁ R) (y : Quantity k₂ R) :
    x + y = Quantity.addAt j.left j.right j.diff x y := rfl

@[simp] theorem hadd_magnitude_join [Carrier R] [KindJoin E k₁ k₂ p]
    (x : Quantity k₁ R) (y : Quantity k₂ R) :
    (x + y : Quantity p R).magnitude = Carrier.add x.magnitude y.magnitude := by
  rw [hadd_eq_addAt, Quantity.addAt, Quantity.widen, Quantity.widen, Quantity.add]

/-- `x + y` across comparable kinds at the instance layer: the same join table, on the
shared object `o`. The object gate is enforced by instance resolution failing to unify
when the operands belong to different objects — a cross-object `T + V` does not
elaborate, exactly as a cross-object product does not. -/
scoped instance instHAddIndividualQuantityJoin [Carrier R] [j : KindJoin E k₁ k₂ p] :
    HAdd (IndividualQuantity o k₁ R) (IndividualQuantity o k₂ R)
      (IndividualQuantity o p R) :=
  ⟨fun x y => IndividualQuantity.add j.diff (x.widen j.left) (y.widen j.right)⟩

/-- The instance-layer join operator is the named form — widen both operands, add
same-kind at the join, on the shared object. -/
theorem hadd_eq_add_widen_individual [Carrier R] [j : KindJoin E k₁ k₂ p]
    (x : IndividualQuantity o k₁ R) (y : IndividualQuantity o k₂ R) :
    x + y = IndividualQuantity.add j.diff (x.widen j.left) (y.widen j.right) := rfl

@[simp] theorem hadd_magnitude_join_individual [Carrier R] [KindJoin E k₁ k₂ p]
    (x : IndividualQuantity o k₁ R) (y : IndividualQuantity o k₂ R) :
    (x + y : IndividualQuantity o p R).magnitude
      = Carrier.add x.magnitude y.magnitude := by
  rw [hadd_eq_add_widen_individual, IndividualQuantity.add, IndividualQuantity.widen,
    IndividualQuantity.widen]

/-- **The join sum does not cross objects silently.** Forgetting an operator-built join
sum to the plain `Quantity` layer is the plain layer's join sum of the forgotten
operands. -/
theorem toQuantity_hadd_join [Carrier R] [j : KindJoin E k₁ k₂ p]
    (x : IndividualQuantity o k₁ R) (y : IndividualQuantity o k₂ R) :
    (x + y : IndividualQuantity o p R).toQuantity
      = x.toQuantity + y.toQuantity := by
  rw [hadd_eq_add_widen_individual, IndividualQuantity.add, IndividualQuantity.widen,
    IndividualQuantity.widen, IndividualQuantity.toQuantity, IndividualQuantity.toQuantity,
    IndividualQuantity.toQuantity, hadd_eq_addAt, Quantity.addAt, Quantity.widen,
    Quantity.widen, Quantity.add]

end OperatorTable

end PropertyKindCalculus

end Interface
