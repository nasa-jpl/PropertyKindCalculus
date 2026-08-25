/-
# QuantityVector — vector/tensor quantities as a numerical array × one scalar unit

ISO 80000-2:2019 §18 (scalars, vectors and tensors) prescribes how a *vector* (or
tensor) quantity is represented: **not** as a collection of per-coordinate quantity
values (each a number × unit), but as a *numerical* vector multiplied by a single
unit — and "all units are scalars". The vector quantity itself is independent of
the choice of coordinate system; only its numerical components depend on that
choice.

That is exactly the shape R10's `Quantity k R` already has, once the carrier `R` is
allowed to be a numerical array. A function space `ι → R` is a `Carrier` whenever
`R` is — zero and addition are pointwise — so:

  * `Quantity k (Fin n → R)` is a single kind-`k` quantity whose magnitude is a
    numerical `n`-vector (the "numerical vector"), and
  * its unit is the *scalar* `MetrologicalUnit` of the kind `k` (one unit for the
    whole vector), and
  * the additivity laws transfer to the vector carrier by the *same* parametric
    proof used for scalars (`Quantity.add_comm`, `Quantity.laws_parametric`).

So this module realizes the ISO 80000-2 §18 reading structurally, with no new core
machinery — the carrier-parametricity of R10 is precisely what makes it free. This
contrasts a representation-rooted model that attaches a unit to each coordinate
value (the per-coordinate `(number × unit)` reading §18 advises against).

In plain engineering terms: a vector quantity is *one* typed array of numbers with
*one* unit on it, not a bag of separately-united numbers.

The *executable* array carrier additionally gets the one honest default — the empty
table (`Inhabited (Quantity k (Array α))`, and its capacity-hinted spelling
`Quantity.emptyWithCapacity`), the well-typed fallback array-indexing idioms demand.
Scalar quantities stay uninhabited on purpose: a default scalar would be a fabricated
magnitude.
-/

import PropertyKindCalculus.Quantity

namespace PropertyKindCalculus

/-- A function space `ι → R` is a numeric carrier whenever `R` is: `zero` and `add`
are **pointwise**. With `ι := Fin n` this is the *numerical vector* carrier — the
representation a vector quantity takes under ISO 80000-2 §18 (a numerical array,
the unit kept scalar on the kind). -/
instance instCarrierPi {ι : Type} {R : Type} [Carrier R] : Carrier (ι → R) where
  zero := fun _ => Carrier.zero
  add f g := fun i => Carrier.add (f i) (g i)

/-- The pointwise carrier is **lawful** whenever `R` is — the additive-monoid laws
hold coordinatewise (`funext` + the laws on `R`). Hence the quantity additivity
laws transfer to vector (and, with nested function spaces, tensor) carriers by the
same parametric proof, with no per-carrier argument. -/
instance instLawfulCarrierPi {ι : Type} {R : Type} [LawfulCarrier R] :
    LawfulCarrier (ι → R) where
  toCarrier := instCarrierPi
  add_assoc a b c := by funext i; exact LawfulCarrier.add_assoc (a i) (b i) (c i)
  add_comm a b := by funext i; exact LawfulCarrier.add_comm (a i) (b i)
  zero_add a := by funext i; exact LawfulCarrier.zero_add (a i)
  add_zero a := by funext i; exact LawfulCarrier.add_zero (a i)

/-- **The empty table — the one `Inhabited` quantity.** At the *executable* array carrier a
vector quantity defaults to the empty numerical array: it has no components, so it asserts no
magnitude at `k` — every index read misses, and a validity domain over it is empty. That makes
it the honest well-typed fallback the array-indexing idioms demand (`xs[i]!` on an array *of*
vector quantities needs `Inhabited` for its panic branch) **without** licensing a default
*value*: scalar carriers stay uninhabited on purpose, because a default scalar quantity would
be a fabricated magnitude — a mint the boundary audit never sees. -/
instance instInhabitedQuantityArray {k : KindOfProperty} {α : Type} :
    Inhabited (Quantity k (Array α)) := ⟨⟨#[]⟩⟩

/-- **Component access — a component of a vector quantity is a quantity of the table's own
kind** (the §18 reading: the numerical array holds components; the kind — and unit — is the
whole vector's, so reading one component *keeps* it). Kind-preserving *by parametricity*: `k`
flows from the table to the component and nothing can change it — the array-carrier analogue of
`castCarrier`, and the licensed alternative to erasing with `.magnitude` and re-minting `⟨…⟩`
around every element read. The carrier is any `Nat`-indexed collection (`GetElem?`), so the
boxed `Array R` and the packed executable columns (`FloatArray`, `ByteArray`) read through the
same licensed form — a packed representation is a representation choice, not a different
metrological object. The index stays bare `Nat` — index space is the documented erasure
boundary, not a quantity — and the panic fallback inhabits the *element carrier*
(`default : Elem`), not the quantity, so the header's doctrine stands: scalar quantities stay
uninhabited. -/
def Quantity.get! {k : KindOfProperty} {R Elem : Type} {valid : R → Nat → Prop}
    [GetElem? R Nat Elem valid] [Inhabited Elem]
    (v : Quantity k R) (i : Nat) : Quantity k Elem :=
  ⟨v.magnitude[i]!⟩

@[simp] theorem Quantity.get!_magnitude {k : KindOfProperty} {R Elem : Type}
    {valid : R → Nat → Prop} [GetElem? R Nat Elem valid] [Inhabited Elem]
    (v : Quantity k R) (i : Nat) :
    (v.get! i).magnitude = v.magnitude[i]! := rfl

/-- **Component append — the write dual of `Quantity.get!`.** Extending a table with a value
*of its own kind* keeps the kind by parametricity: `k` flows from both the table and the new
component, and nothing can change it. This is the licensed accumulator idiom — build a vector
quantity by pushing kinded components — replacing the pattern of collecting bare magnitudes in
an `Array Float` and re-minting the finished table with `⟨…⟩`. The §18 reading again: pushing
a component changes the *extent* of the numerical array, not the kind (or unit) of the vector
quantity. -/
def Quantity.push {k : KindOfProperty} {R : Type}
    (v : Quantity k (Array R)) (x : Quantity k R) : Quantity k (Array R) :=
  ⟨v.magnitude.push x.magnitude⟩

@[simp] theorem Quantity.push_magnitude {k : KindOfProperty} {R : Type}
    (v : Quantity k (Array R)) (x : Quantity k R) :
    (v.push x).magnitude = v.magnitude.push x.magnitude := rfl

/-- The empty table with reserved storage — `default` plus a capacity hint. Capacity is pure
representation (how much the array *can* hold, never what it does hold), so this asserts
exactly what `Inhabited`'s default does: nothing, at any kind. The natural seed for a
`Quantity.push` accumulation loop of known extent. -/
def Quantity.emptyWithCapacity {k : KindOfProperty} {R : Type} (n : Nat) :
    Quantity k (Array R) := ⟨Array.emptyWithCapacity n⟩

@[simp] theorem Quantity.emptyWithCapacity_magnitude {k : KindOfProperty} {R : Type}
    (n : Nat) :
    (Quantity.emptyWithCapacity (k := k) (R := R) n).magnitude = Array.emptyWithCapacity n :=
  rfl

/-- **Extent.** The component count of a vector quantity's numerical array — bare `Nat` by
design: an extent is structural (how many components the representation holds), not a magnitude
at `k`, so it leaves the calculus the way an index enters it. -/
def Quantity.size {k : KindOfProperty} {R : Type} (v : Quantity k (Array R)) : Nat :=
  v.magnitude.size

@[simp] theorem Quantity.size_eq {k : KindOfProperty} {R : Type}
    (v : Quantity k (Array R)) : v.size = v.magnitude.size := rfl

end PropertyKindCalculus
