/-
`PropertyKindCalculus.Uncertainty.Roles` — **an estimate and its dispersion are not the same
sort of thing**, and at a kind alone nothing says so.

`Evidence`'s own docstring has always said it: "`stdUnc` is the GUM's `u`: a *dispersion*, and
therefore a quantity of the measurand's own kind (the uncertainty of a length is a length)". The
parenthesis is exactly the problem. Because `u(x)` is at the kind of `x`, the two are the same
type, they sit next to each other in every evidence record and every constructor call, and
swapping them type-checks.

That is not a hypothetical. A margin read as a coverage factor is `g/u`; with the two exchanged
it is `u/g`, and a deployment record whose band reads **42 u** — a systematic the model does not
carry, which must never be tightened — reads instead as `1/42` of a `u`, which is a coverage
statement so tight that every conformity rule would happily shrink it. One transposition turns
the single most important diagnosis this library makes into its exact opposite, in the safe-
looking direction, with no type error and no test failure unless somebody wrote the test for
that specific pair.

## What the roles are

Three things live at kind `k` and are not interchangeable.

  * A **value** — `Quantity k R`, the thing itself. Also a difference of estimates, a correction,
    a margin: anything whose claim is a location or a displacement on the measurand's scale.
  * An **estimate** — `Estimate k R`, a value *offered as* the measurand's. The distinction from
    a plain value is not pedantry: only an estimate has a dispersion, and only an estimate is
    what a coverage interval is centred on.
  * A **dispersion** — `Dispersion k R`, the GUM's `u`: the standard deviation of the
    distribution that could reasonably be attributed to the measurand (GUM 3.3.1). At `k`, and
    never a value of `k`.

## The algebra, and the one operation that is missing on purpose

The content of the distinction is in which operations exist.

  * Dispersions **do not add**. There is no `Add (Dispersion k R)` here and none is coming: `u₁ +
    u₂` is not how uncertainties combine, and a type that permitted it would permit the error at
    every site. They combine in **quadrature**, `u_c = √(Σ uᵢ²)`, which is `combine` — and
    `combine` on a `List` rather than a binary operator, because the GUM's law is over a model's
    whole contributor set and a fold would invite the reader to think of it as repeated addition.
  * Estimates **do not add either**, for a different reason: the sum of two estimates is an
    estimate of a different measurand, which is a model, not an operation. What an estimate
    admits is a *correction* (`corrected`) and a *comparison* (`deviation`), and the second
    returns a plain value — the difference of two estimates is a displacement, not an estimate.
  * A dispersion **divides** a value to give a coverage factor (`factorOf`) and **multiplies** by
    one to give an expanded uncertainty (`expanded`). Both directions go through
    `EvidenceKinds`' laws, so a coverage factor is arrived at rather than re-stamped.
  * An estimate and its expanded uncertainty give the endpoints of a coverage interval — and
    those come back as `LowerBound`/`UpperBound`, so the whole role-directed apparatus in
    `Decimal` applies to them without anything further being said.

## What this does not do

It does not make `Estimate` and `Dispersion` different *kinds*. They are the same kind and must
be: `u(x)` is comparable with `x`, the GUM's arithmetic depends on it, and a library that made
them incomparable would have to unwrap at every step and would be worse than none. The
separation is at the **role** layer, which is where `Bounds` puts the identical distinction for
endpoints, and for the identical reason.
-/

module

public import PropertyKindCalculus.Bounds
public import PropertyKindCalculus.Uncertainty.EvidenceKinds
public import PropertyKindCalculus.Uncertainty.Carriers

public section -- pkc-blanket
@[expose] section -- pkc-blanket-expose

namespace PropertyKindCalculus.Uncertainty

open PropertyKindCalculus

variable {k : KindOfProperty} {R : Type}

/-! ## The two roles -/

/-- **A value offered as the measurand's** — GUM 3.1.2's *result of a measurement*.

A one-field wrapper, like `LowerBound`, and for the same reason: what it adds is not data but
the refusal to be used where a value of another role belongs. The wrapped `Quantity` is
reachable as `q` when the arithmetic genuinely is the measurand's. -/
structure Estimate (k : KindOfProperty) (R : Type) where
  /-- The estimate, as a quantity of the measurand's kind. -/
  q : Quantity k R
deriving Repr

/-- **The standard uncertainty of an estimate** — GUM 3.3.1's `u`, the standard deviation of the
distribution of values that could reasonably be attributed to the measurand.

At the measurand's own kind, because the uncertainty of a length is a length; and *not* a value
of the measurand, because it is a width rather than a location. It has no `+` (see the module
header), which is the whole of what this type contributes. -/
structure Dispersion (k : KindOfProperty) (R : Type) where
  /-- The dispersion, as a quantity of the measurand's kind. -/
  q : Quantity k R
deriving Repr

/-- The estimate's magnitude. Provided so that a role wrapper costs nothing at a read site: the
guard against transposition is at construction, where the mistake is made. -/
def Estimate.magnitude (e : Estimate k R) : R := e.q.magnitude

/-- The dispersion's magnitude — the counterpart of `Estimate.magnitude`. -/
def Dispersion.magnitude (d : Dispersion k R) : R := d.q.magnitude

instance [BEq R] : BEq (Estimate k R) where beq a b := a.magnitude == b.magnitude
instance [BEq R] : BEq (Dispersion k R) where beq a b := a.magnitude == b.magnitude

/-! ## What an estimate admits

Not `+`. The sum of two estimates is an estimate of a *different measurand*, which is a
measurement model and not an arithmetic operation on this one — `Budget`'s contributor
machinery is where that belongs. -/

/-- **An estimate moved by a correction** (GUM 3.2.3): still an estimate of the same measurand,
which is exactly what a correction is for. The correction is a plain `Quantity` because it is a
displacement and not a location — a bias, a calibration offset, a known systematic. -/
def Estimate.corrected [Add R] (e : Estimate k R) (correction : Quantity k R) : Estimate k R :=
  ⟨⟨e.magnitude + correction.magnitude⟩⟩

/-- **The displacement between two estimates**, as a plain value.

Deliberately not an `Estimate`: two estimates of one measurand differ by a quantity of that kind,
and that difference is a deviation to be compared against a dispersion — it is not itself
anything's estimate. This is the operation a conformity assessment performs when it asks how far
a deployed coefficient sits from the fit it came out of. -/
def Estimate.deviation [Sub R] (a b : Estimate k R) : Quantity k R :=
  ⟨a.magnitude - b.magnitude⟩

/-! ## What a dispersion admits -/

/-- **The GUM's combination law**, `u_c = √(Σ uᵢ²)` (GUM 5.1.2, uncorrelated contributors).

A `List` and not a binary operator, and no `Add` instance anywhere near it. Uncertainties do not
add; they combine in quadrature, and the difference is not small — two equal contributors give
`√2 u` and not `2 u`, so a fold written as a sum over-states by 41 % at two terms and grows from
there. Stating the law over the whole contributor set is also the honest shape: it is a property
of a *model*, evaluated once, rather than something accumulated pairwise. -/
def Dispersion.combine [MathCarrier R] [Zero R] [Add R] [Mul R]
    (us : List (Dispersion k R)) : Dispersion k R :=
  ⟨⟨MathCarrier.sqrt ((us.map (fun u => u.magnitude * u.magnitude)).foldl (· + ·) 0)⟩⟩

/-- **The expanded uncertainty** `U = k·u` (GUM 2.3.5).

Through `expansionLaw`, so the product of a coverage factor and a dispersion is *constructed* at
`k` rather than re-stamped there — and the result is a `Dispersion` again, because `U` is still a
width and not a location. `k.IsRational` is what licenses the whole thing, and it is the same
precondition `Evidence` carries. -/
def Dispersion.expanded [Mul R] [ScalarCarrier R] (u : Dispersion k R)
    (factor : Quantity coverageFactor R)
    (hk : k.IsRational := by rfl) : Dispersion k R :=
  ⟨Quantity.mul (expansionLaw k hk) factor u.q⟩

/-- **How many standard uncertainties a value amounts to** — the `g/u` of a band reading (GUM
2.3.6 read backwards), through `bandReadingLaw`.

`none` at a dispersion of zero, which is a refusal and not a division by zero dressed up: a
margin measured against no dispersion is not a large coverage factor, it is a factor that has no
meaning, and the two must not produce the same answer. The numerator is a plain `Quantity`
because what gets divided is a margin or a deviation — a displacement, never an estimate, and
the type now says so. -/
def Dispersion.factorOf [Div R] [ScalarCarrier R] [Zero R] [BEq R] (u : Dispersion k R) (g : Quantity k R)
    (hk : k.IsRational := by rfl) : Option (Quantity coverageFactor R) :=
  if u.magnitude == (0 : R) then none
  else some (Quantity.div (bandReadingLaw k hk) g u.q)

/-! ## Where the two roles meet the bounds

The endpoints of a coverage interval. Returned at their **roles** rather than as two quantities
called lo and hi, so that what `Bounds` says about an endpoint — that a comparison against it
cannot be written backwards — applies to them unchanged.

One thing does *not* come free, and the distinction is worth carrying here because this is the
module that produces the endpoints. A coverage interval is **asserted**: it claims the measurand
lies inside, so shortening either endpoint outward keeps the claim true and gives coverage away,
which is `Decimal`'s `roundedDown`/`roundedUp` pair. A **tolerance** or acceptance limit
(`Conformity.Tolerance`) is imposed, and wants the opposite pair. Both are `LowerBound` /
`UpperBound`; the geometric role is the same and the safe rounding is inverted, so the reading
has to be supplied by whoever knows why the bound exists. -/

/-- **The lower endpoint of the coverage interval** `y − U`, as a lower bound. -/
def Estimate.minus [Sub R] (y : Estimate k R) (u : Dispersion k R) : LowerBound k R :=
  ⟨⟨y.magnitude - u.magnitude⟩⟩

/-- **The upper endpoint of the coverage interval** `y + U`, as an upper bound. -/
def Estimate.plus [Add R] (y : Estimate k R) (u : Dispersion k R) : UpperBound k R :=
  ⟨⟨y.magnitude + u.magnitude⟩⟩

/-! ## Laws -/

/-- **Combining nothing is nothing.** The empty model has no contributors and therefore no
combined uncertainty, which is `0` and not undefined — the sum over an empty set. -/
@[simp] theorem Dispersion.combine_nil [MathCarrier R] [Zero R] [Add R] [Mul R] :
    (Dispersion.combine (k := k) (R := R) []).magnitude = MathCarrier.sqrt 0 := rfl

/-- **A single contributor combines to its own square root of square.** Stated in the form the
carrier can discharge — on an exact carrier `√(u²) = |u|`, and this library does not assume the
host `Float` gets that exactly, which is precisely the sort of claim `Adequacy` exists to
police. -/
@[simp] theorem Dispersion.combine_singleton [MathCarrier R] [Zero R] [Add R] [Mul R]
    (u : Dispersion k R) :
    (Dispersion.combine [u]).magnitude
      = MathCarrier.sqrt (0 + u.magnitude * u.magnitude) := rfl

/-- **The interval's endpoints are the estimate displaced by the expanded uncertainty**, and
each arrives already carrying its role. Definitional, and stated so that the pairing of `minus`
with `LowerBound` (rather than the other way round) is a fact in the file and not a convention a
reader has to trust. -/
@[simp] theorem Estimate.minus_magnitude [Sub R] (y : Estimate k R) (u : Dispersion k R) :
    (y.minus u).q.magnitude = y.magnitude - u.magnitude := rfl

/-- The dual of `Estimate.minus_magnitude`. -/
@[simp] theorem Estimate.plus_magnitude [Add R] (y : Estimate k R) (u : Dispersion k R) :
    (y.plus u).q.magnitude = y.magnitude + u.magnitude := rfl

/-- **A factor is refused at a dispersion of zero**, never computed. The statement that a
consumer relies on when it treats `none` as "unreadable" rather than as "unavailable for some
other reason". -/
theorem Dispersion.factorOf_eq_none [Div R] [ScalarCarrier R] [Zero R] [BEq R] (u : Dispersion k R)
    (g : Quantity k R)
    (hk : k.IsRational) (h : u.magnitude == (0 : R)) :
    u.factorOf g hk = none := by
  unfold Dispersion.factorOf; rw [ite_eq_left h]

/-- **A correction moves an estimate by exactly the correction.** The law that makes `corrected`
usable in a budget: the displacement introduced is the one that was asked for, so a bias
correction's own uncertainty can be accounted separately rather than being entangled with it. -/
@[simp] theorem Estimate.corrected_magnitude [Add R] (e : Estimate k R) (c : Quantity k R) :
    (e.corrected c).magnitude = e.magnitude + c.magnitude := rfl

/-- **The deviation between an estimate and itself is zero** — at whatever `Sub` means on the
carrier, which on a host float is exact for finite values and is `NaN` for a `NaN`. Stated in the
definitional form for that reason. -/
@[simp] theorem Estimate.deviation_self [Sub R] (e : Estimate k R) :
    (e.deviation e).magnitude = e.magnitude - e.magnitude := rfl

end PropertyKindCalculus.Uncertainty

end -- pkc-blanket-expose
end -- pkc-blanket
