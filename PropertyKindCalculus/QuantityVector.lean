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
table (`Inhabited (Quantity k (Array α))`), the well-typed fallback array-indexing
idioms demand. Scalar quantities stay uninhabited on purpose: a default scalar would
be a fabricated magnitude.
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

end PropertyKindCalculus
