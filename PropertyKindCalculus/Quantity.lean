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

**Four representations, not three.** Those three carriers are all *real*. Many
physical quantities take a *complex* value (the relative permittivity of a lossy
dielectric `ε = ε′ + jε″`, an impedance, an AC phasor), so there is a fourth
representation: the **complexification** `Complex R` of any of the first three
(`PropertyKindCalculus.Complex`, a *functor on carriers* `R ↦ Complex R`). Complex-
ness is a property of the *carrier*, not of the kind — `Quantity k (Complex R)` is
the *same* kind layer over a complexified carrier — so it is genuinely a fourth point
on the representation axis, giving `Complex ℝ` to prove, `Complex (binary32)` to
certify rounding, and `Complex Float` to run. `Complex R` is a `Carrier` (and a
`LawfulCarrier` whenever `R` is — complex addition is componentwise, so the
additivity laws lift for free), and it carries the full `+ − × ÷` of a field; but it
is *unordered* (there is no `≤` on `ℂ`), so it sits **outside** the
ordinal/interval/ratio carrier tower below — complex magnitudes are compared by
modulus, not ranked. See the `Complex` module.

The split into `Carrier` (operations) and `LawfulCarrier` (operations *plus* the
algebraic laws) is deliberate and is the whole point of R10: a law proved once
over `LawfulCarrier R` transfers to *every* lawful carrier (`Int`, `ℝ`), while an
executable float is a `Carrier` but **not** a `LawfulCarrier` — floating-point
addition is not associative — so the laws are *unavailable* at the float that
runs. That gap is closed for `+` by the exec/spec *refinement* bridge
(`QuantityRefinement`): `CarrierRefinement E S` states that the executable result,
forgotten to the spec carrier, is the rounding of the spec result, and
`Quantity.add_refines` lifts it along the kind index. `Torch.Fp32` instantiates it
at genuine IEEE binary32, so the descent is realized and not merely specified.

**What the bridge covers, precisely.** `CarrierRefinement` carries two laws —
`toSpec_zero` and `toSpec_add` — so the descent is available for aggregation and
*not* for the multiplicative operations. A model whose formulas are products
(`k = m·ω²`, a scalar product, an impedance squared) has no `mul_refines` to appeal
to. The forward-error story for a whole expression tree, products and quotients
included, exists in a different shape and a different layer:
`Uncertainty.Adequacy.DagBound`'s `dag_fp32_error_bound` accumulates per-node
half-ulp budgets over an `add`/`sub`/`mul`/`div` DAG, grounded in TorchLean's own
`FP32.{mul,div}_abs_error`. Whether that soundness should route *through*
`CarrierRefinement` or stay direct is the open item recorded in `UNCERTAINTY.md` §7
("`CarrierRefinement` consolidation"), and it is the reason this paragraph names the
boundary rather than claiming the whole of it.
-/

module

public import PropertyKindCalculus.Kind

public section Interface

namespace PropertyKindCalculus

/-- **The numeric carrier of a quantity (R10).** The minimal *additive* structure a
kind-indexed magnitude needs in order to *aggregate*: a zero and an addition, supplied once
per representation type `R`. This is the role TorchLean's `Context α` plays for tensor element
types — the kind, scale, dimension, interaction, and extensivity layers are all written
*against* this class and reused verbatim at every `R`.

**Why a bespoke `zero`/`add` rather than extending Lean's `Zero`/`Add`?** Three reasons, all
deliberate:

  * **It is the home of additivity (extensivity §13.5, R10), nothing more.** `Carrier` carries
    *exactly* the operation whose laws the extensivity capstone is about. It is intentionally
    *not* a field/ring: multiplication and division change the *kind* (length × length = area),
    so they are cross-kind operations gated by `ProductKind`/`QuotientKind` witnesses, not
    carrier methods (see `QuantityClassification`); subtraction and the transcendentals ride
    Lean's own `Sub`/`MathCarrier` at their use sites. Which operations are even *meaningful*
    is a property of a kind's *scale* (`Scale.lean`: `AllowsOrder`/`AllowsDifference`/
    `AllowsRatio`), not of the carrier — so the carrier stays minimal and the licensing lives
    on the kind.
  * **It keeps the core Mathlib-free and self-contained.** Because `add`/`zero` are bespoke
    methods, derived carriers — `Carrier (ι → R)` (`QuantityVector`) and `Carrier (Complex R)`
    (`Complex`) — are built *directly* from `R`'s `Carrier`, with no need for Mathlib's
    `Pi`/`Complex` algebra instances and with no risk of *instance diamonds* against them in
    the Mathlib-backed `dimension` layer.
  * **It draws the R10 line sharply** (see `LawfulCarrier`).

For ergonomic *computation*, the same-kind operator `+` is also available over Lean's `Add`
(see the "Two additions" note below); on any carrier that is both a `Carrier` and an `Add`,
the two coincide. -/
class Carrier (R : Type) where
  /-- The additive unit (a zero magnitude). -/
  zero : R
  /-- Addition of magnitudes — the operation extensive aggregation (§13.5) is built from. -/
  add : R → R → R

/-- **Generic carrier from the ambient algebra.** A `Carrier` for any type that already has a
`Zero` and an `Add` — the one-liner that admits a *non-numeric* carrier (an operator, a
matrix, a function space) to the quantity layer. A definition, not an instance: which types
join the curated carrier vocabulary stays a per-application decision (the R10 line), so an
application registers `instance : Carrier X := Carrier.ofZeroAdd X` for the `X` it means. -/
@[instance_reducible, expose] def Carrier.ofZeroAdd (R : Type) [Zero R] [Add R] : Carrier R :=
  ⟨0, (· + ·)⟩

/-- **A lawful numeric carrier (the R10 line).** A `Carrier` whose addition additionally obeys
the additive-monoid laws (associative, commutative, with `zero` a unit). These are exactly the
laws that hold over `ℝ` (the proof carrier) and `Int`, and that *fail* over an executable
float (float `+` is not associative) — which is why `Float` is a `Carrier` but **not** a
`LawfulCarrier`. A quantity law proved over `LawfulCarrier R` is proved for *every* lawful `R`
at once (R10); the gap to the unlawful executable carrier is what the planned exec/spec
refinement bridge (`QuantityRefinement`) reconciles, by relating each float operation to the
rounding of its real-number specification. -/
class LawfulCarrier (R : Type) extends Carrier R where
  /-- Addition is associative. -/
  add_assoc : ∀ a b c : R, add (add a b) c = add a (add b c)
  /-- Addition is commutative. -/
  add_comm : ∀ a b : R, add a b = add b a
  /-- `zero` is a left unit. -/
  zero_add : ∀ a : R, add zero a = a
  /-- `zero` is a right unit. -/
  add_zero : ∀ a : R, add a zero = a

/-- **A quantity (R10).** A magnitude of a fixed kind `k`, carried at a representation type `R`.

Indexed by `k`, so the type system forbids forming or comparing a `Quantity k₁ R` with a
`Quantity k₂ R` when `k₁ ≠ k₂`; indexed by `R`, so the same value type is instantiated at whichever
numbers the task needs. This indexing *is* the fix for the dimension-1 conflation. -/
structure Quantity (k : KindOfProperty) (R : Type) where
  /-- §13.3.3 — the magnitude (the *number* of the reference-times-number form),
  carried at the representation type `R`. -/
  magnitude : R

/-- **A kind-level difference law (the additive analogue of `ProductKind`).** A witness that
`k`'s scale *allows differences* — i.e. is interval or ratio (Dybkær §12.19, `Scale.lean`'s
`AllowsDifference`), the precondition for forming a same-kind sum or difference. It is to the
*named*, scale-checked `Quantity.add` / `Quantity.sub` what `ProductKind`/`QuotientKind` are to
`Quantity.mul` / `Quantity.div`: the metrology gate, recorded in the type. (You cannot
meaningfully add two *nominal* or *ordinal* quantities; this rules that out.) -/
structure DifferenceKind (k : KindOfProperty) : Prop where
  /-- `k`'s scale licenses `+`/`−` (interval or ratio). -/
  allowsDifference : k.scale.AllowsDifference

/-- **Smart constructor.** A difference law for any kind whose scale concretely allows
differences (interval or ratio); the gate is discharged by `trivial` for a concrete kind. -/
theorem DifferenceKind.ofScale {k : KindOfProperty} (h : k.scale.AllowsDifference := by trivial) :
    DifferenceKind k := ⟨h⟩

namespace Quantity

variable {k : KindOfProperty} {R : Type}

/-- **Extensionality.** Two quantities of the same kind and carrier are equal exactly when
their magnitudes are — `Quantity` is a one-field wrapper, so equality is decided on the
magnitude. Registered with `@[ext]` so the `ext` tactic reduces a quantity goal to its
magnitude. -/
@[ext] theorem ext {x y : Quantity k R} (h : x.magnitude = y.magnitude) : x = y := by
  cases x; cases y; cases h; rfl

/-- The zero quantity of a kind (needs only a `Carrier`). -/
@[expose] def zero [Carrier R] : Quantity k R := ⟨Carrier.zero⟩

/-- **Kind- and scale-gated addition (R4, the named/lawful form).** Adds two quantities of the
*same* kind `k`, over the additive `Carrier`. Two gates, both in the type: the kind index `k`
(so `Width + Width` type-checks but `Width + Height` does not), and the `DifferenceKind k`
witness (so the kind's scale must license `+`). This is the *disciplined* counterpart of the
ergonomic operator `+` — uniform with `Quantity.mul`/`Quantity.div`, which likewise carry their
kind-law witness — and the operation the R10 additivity laws below are stated about. -/
@[expose] def add [Carrier R] (_h : DifferenceKind k) (x y : Quantity k R) : Quantity k R :=
  ⟨Carrier.add x.magnitude y.magnitude⟩

/-- Addition is commutative over any lawful carrier — proved once, for every `R`. -/
protected theorem add_comm [LawfulCarrier R] (h : DifferenceKind k) (x y : Quantity k R) :
    Quantity.add h x y = Quantity.add h y x := by
  unfold Quantity.add
  rw [LawfulCarrier.add_comm]

/-- Addition is associative over any lawful carrier — proved once, for every `R`. -/
protected theorem add_assoc [LawfulCarrier R] (h : DifferenceKind k) (x y z : Quantity k R) :
    Quantity.add h (Quantity.add h x y) z = Quantity.add h x (Quantity.add h y z) := by
  unfold Quantity.add
  rw [LawfulCarrier.add_assoc]

/-- The zero quantity is a left unit over any lawful carrier. -/
protected theorem zero_add [LawfulCarrier R] (h : DifferenceKind k) (x : Quantity k R) :
    Quantity.add h Quantity.zero x = x := by
  unfold Quantity.add Quantity.zero
  rw [LawfulCarrier.zero_add]

/-- The zero quantity is a right unit over any lawful carrier. -/
protected theorem add_zero [LawfulCarrier R] (h : DifferenceKind k) (x : Quantity k R) :
    Quantity.add h x Quantity.zero = x := by
  unfold Quantity.add Quantity.zero
  rw [LawfulCarrier.add_zero]

/-- **Representation-parametric additivity (R10).** The additivity laws hold over *any* lawful
carrier, established by a single proof and so available at every `R` at once (`ℝ` for proofs,
`Int`, …). The very `R` where these laws are absent — an executable float, a `Carrier` but not
a `LawfulCarrier` — is what the planned exec/spec refinement bridge exists to reconcile. -/
theorem laws_parametric [LawfulCarrier R] (h : DifferenceKind k) (x y z : Quantity k R) :
    Quantity.add h x y = Quantity.add h y x
      ∧ Quantity.add h (Quantity.add h x y) z = Quantity.add h x (Quantity.add h y z)
      ∧ Quantity.add h Quantity.zero x = x ∧ Quantity.add h x Quantity.zero = x :=
  ⟨Quantity.add_comm h x y, Quantity.add_assoc h x y z,
    Quantity.zero_add h x, Quantity.add_zero h x⟩

/-! ### Two additions, two worlds — `Quantity.add` vs `+`

PropertyKindCalculus offers same-kind addition in **two** spellings, for two different jobs.
Pick by *which world you are in*; on the concrete leaf carriers (`Int`, `ℝ`, `Float`) they
compute the same value, so it never matters there — the distinction is about *what is in
scope* and *what you are proving*.

  * **`Quantity.add (h : DifferenceKind k)` — the lawful / metrology world.** Defined over the
    bespoke `Carrier` (`Carrier.add`), it carries the R10 additivity laws (`LawfulCarrier`)
    and works over carriers Lean's `Add` cannot reach Mathlib-free — the derived
    `Carrier (ι → R)` and `Carrier (Complex R)`. It is **scale-gated** (the `DifferenceKind`
    witness), so it is the operation to use in proofs and in generic code that must be sound
    across every representation. Uniform with `Quantity.mul`/`Quantity.div`.

  * **`x + y` (the `Add` instance) — the computational world.** Defined over Lean's standard
    `Add R` (`x.magnitude + y.magnitude`), it needs *no* `Carrier` instance, so it is available
    over carriers that only supply Lean's `+` — e.g. TorchLean's `Context` — and reads as
    ordinary arithmetic in an executable kernel (the Mironov forward in `sm-smap-nisar-lean`
    uses it). It is kind-gated (different kinds are different types) but **not** scale-gated:
    an operator instance has nowhere to carry the `DifferenceKind` witness, exactly as there is
    deliberately no `Mul` instance (multiplication is cross-kind). Reach for the named
    `Quantity.add` when you want that gate enforced.

The subtraction/negation operators `-` / unary `-` mirror `+` (computational world, over
Lean's `Sub`/`Neg`); their scale-gated named form is `Quantity.sub` below (and `Quantity.neg`
in the function-calculus module, alongside `abs`/`min`/`max`). -/

/-- **Kind- and scale-gated subtraction (the named form).** The disciplined counterpart of the
`-` operator: a same-kind difference over Lean's `Sub`, gated by `DifferenceKind k`. (Defined
over `Sub` rather than `Carrier` because subtraction is not part of the additive-aggregation
carrier; it is the interval-scale difference.) -/
@[expose] def sub [Sub R] (_h : DifferenceKind k) (x y : Quantity k R) : Quantity k R :=
  ⟨x.magnitude - y.magnitude⟩

/-- Same-kind `+` over any `Add` carrier (kind-gated, ergonomic; the computational-world
addition — see the "Two additions" note). -/
instance instAdd [Add R] : Add (Quantity k R) := ⟨fun x y => ⟨x.magnitude + y.magnitude⟩⟩
/-- Same-kind `-` over any `Sub` carrier (kind-gated, ergonomic). -/
instance instSub [Sub R] : Sub (Quantity k R) := ⟨fun x y => ⟨x.magnitude - y.magnitude⟩⟩

@[simp] theorem add_magnitude [Add R] (x y : Quantity k R) :
    (x + y).magnitude = x.magnitude + y.magnitude := rfl
@[simp] theorem sub_magnitude [Sub R] (x y : Quantity k R) :
    (x - y).magnitude = x.magnitude - y.magnitude := rfl

/-! ### Same-kind comparison — the computational world, continued

Equality and order never mix kinds (the type index already forbids comparing a
`Quantity k₁ R` with a `Quantity k₂ R`), so — like `+`/`-` above — they get plain
operator instances delegating to the carrier. Whether an order is *meaningful* is a
scale question (`ScaleType.AllowsOrder`, ordinal and above); these instances are the
kind-gated computational face, exactly as `+` is to `Quantity.add`. -/

/-- Same-kind `==` over the carrier's `BEq` (kind-gated: cross-kind `==` is a type error). -/
instance instBEq [BEq R] : BEq (Quantity k R) := ⟨fun x y => x.magnitude == y.magnitude⟩
/-- Same-kind `≤` over the carrier's order (kind-gated). -/
instance instLE [LE R] : LE (Quantity k R) := ⟨fun x y => x.magnitude ≤ y.magnitude⟩
/-- Same-kind `<` over the carrier's order (kind-gated). -/
instance instLT [LT R] : LT (Quantity k R) := ⟨fun x y => x.magnitude < y.magnitude⟩

instance instDecidableLE [LE R] [DecidableLE R] (x y : Quantity k R) : Decidable (x ≤ y) :=
  inferInstanceAs (Decidable (x.magnitude ≤ y.magnitude))
instance instDecidableLT [LT R] [DecidableLT R] (x y : Quantity k R) : Decidable (x < y) :=
  inferInstanceAs (Decidable (x.magnitude < y.magnitude))

@[simp] theorem beq_iff [BEq R] (x y : Quantity k R) :
    (x == y) = (x.magnitude == y.magnitude) := rfl
@[simp] theorem le_iff [LE R] (x y : Quantity k R) :
    (x ≤ y) ↔ (x.magnitude ≤ y.magnitude) := Iff.rfl
@[simp] theorem lt_iff [LT R] (x y : Quantity k R) :
    (x < y) ↔ (x.magnitude < y.magnitude) := Iff.rfl

/-- Render as the magnitude (a `Quantity` in a log line or `Repr` dump shows its number;
the kind is carried by the type, not re-printed). -/
instance instRepr [Repr R] : Repr (Quantity k R) := ⟨fun q p => reprPrec q.magnitude p⟩

/-- **Kind-preserving representation change.** Apply a carrier map `f : R → S` to the
magnitude, keeping the kind fixed: rounding (`Float.ceil` then truncation), widening
(`Nat.toFloat`), and narrowing casts are *representation* operations — the quantity they
carry is the same kind throughout, so this is deliberately **not** a kind conversion
(there is no way to change `k` with it). The disciplined alternative to erasing with
`.magnitude` and re-minting `⟨…⟩` around every numeric cast. -/
@[expose] def castCarrier {S : Type} (f : R → S) (q : Quantity k R) : Quantity k S := ⟨f q.magnitude⟩

@[simp] theorem castCarrier_magnitude {S : Type} (f : R → S) (q : Quantity k R) :
    (q.castCarrier f).magnitude = f q.magnitude := rfl

/-- **An authored mint, on the record.** Wrap a raw magnitude at kind `k`, stating the reason.
Semantically this *is* `⟨m⟩` — nothing is checked — but the assertion becomes *enumerable*: the
boundary audit recognizes registered attestors (`@[kindAttest]`; this one is built in) and
reports every call site with its harvested `why`, so each surviving authored mint is a one-line
review artifact rather than an anonymous `⟨…⟩` a declaration-level tier tag silently covers.

The discipline (`BoundaryAudit`'s header): `attest` is the *last* resort, for a classification
with no machine-checkable evidence — `why` should say why no check applies. Where evidence
exists, take the licensed route instead: a `CertifiedIngest`/`KindAdmissible` check at ingest, a
`ProductKind`/`QuotientKind` witness edge (`Quantity.mul`/`div`), `castCarrier` for a
representation change, `Quantity.get!` for component access, the empty-array `default` for a
missing table. -/
@[inline, expose] def attest (_why : String) (m : R) : Quantity k R := ⟨m⟩

@[simp] theorem attest_magnitude (why : String) (m : R) :
    (attest (k := k) why m).magnitude = m := rfl

/-! ### The integer ↔ real round-trip, named in both directions

An affine model over integer resources (`bytes(P) = fixed + perElement·P`) computes
through a real-valued slope and must land back on an integer, so every such computation
widens and then narrows. The narrowing has TWO correct answers and picking the wrong one
is a resource error, not a rounding wart — which is the whole reason these are named
definitions rather than a lambda written afresh at each site. -/

/-- Widen a `Nat`-carried magnitude to `Float`: the entry half of the round-trip, and the
harmless half — no information is lost and no decision rides on it. -/
def asFloat (q : Quantity k Nat) : Quantity k Float := q.castCarrier Nat.toFloat

/-- Narrow back to `Nat`, rounding **up**. For a *demand* — bytes that must be allocated,
work that must be scheduled: understating it is what an out-of-memory kill is made of, so
the fractional part is charged in full. -/
def ceilToNat (q : Quantity k Float) : Quantity k Nat :=
  q.castCarrier (fun x => x.ceil.toUInt64.toNat)

/-- Narrow back to `Nat`, rounding **down**. The dual of `ceilToNat` and the other half of
its argument: for an *allowance* — how many elements a budget sustains, how many shards
fit — overstating it authorizes exactly the excess the solver exists to prevent. -/
def floorToNat (q : Quantity k Float) : Quantity k Nat :=
  q.castCarrier (fun x => x.floor.toUInt64.toNat)

end Quantity

/-! ## Concrete carriers

The same `Quantity` layer above, instantiated at four representation types. Three
are *lawful* (the additivity laws hold); the last runs but is deliberately not. -/

/-- **`Nat` is a numeric carrier** — the representation a *count* is held in. A count is the
canonical dimension-one ratio-scale quantity, and a counting pipeline accumulates one the way
any other quantity is accumulated: from a zero and by repeated same-kind addition. Without the
instance neither former is available at `Nat`, so a counter has to start life as an anonymous
`⟨0⟩` and grow by bare arithmetic under it — a mint and an unkinded fold standing in for the two
operations the kind already licenses. The absence is what makes counts the last thing in a model
to get kinded, which is backwards: they are the values a positional swap is easiest to hide in. -/
instance instCarrierNat : Carrier Nat where
  zero := 0
  add := (· + ·)

/-- `Nat` is a *lawful* carrier: `Nat` addition is an associative, commutative monoid with `0`
as its unit, so every `Quantity.add_*` law holds at `R := Nat`. Counts differ from `Int` only in
having no additive inverse, which the additive-monoid laws do not ask for. -/
instance : LawfulCarrier Nat where
  toCarrier := instCarrierNat
  add_assoc := Nat.add_assoc
  add_comm := Nat.add_comm
  zero_add := Nat.zero_add
  add_zero := Nat.add_zero

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

/-! ## The carrier tower — representations mirroring Dybkær's scale lattice (R-scale ↔ carrier)

`Carrier` above is the *additive-aggregation* carrier — exactly what the extensivity/R10 story
needs, no more. Dybkær's scale lattice (`Scale.lean`) records, on the *kind* side, which
operations a kind's scale licenses: order at ordinal, `+`/`−` at interval, `×`/`÷` at ratio.
The marker classes below mirror that lattice on the *carrier* side. Each bundles exactly the
standard-Lean arithmetic a representation `R` must supply to carry a quantity of the matching
scale, and the `extends` chain reproduces the lattice order `ordinal ⊏ interval ⊏ ratio`
(`ScaleType.le`). They **require** Lean's classes (`LE`/`Add`/`Sub`/`Mul`/…) rather than
redefining them, so they compose with the field operations the rest of the library already
rides — `Quantity.mul` over `[Mul R] [ScalarCarrier R]`, `Quantity.sqrt` over `MathCarrier`
— and add no instance diamonds.

Two complementary gates, then: a *kind*'s scale says an operation is **meaningful**
(`DifferenceKind`, `ProductKind`, … on the kind index); a *carrier*'s tier says the
representation can **compute** it (`IntervalCarrier`, `RatioCarrier`, … on `R`). A sound
quantity operation needs both.

`ScalarCarrier`, at the end of this section, is the third gate the first two leave open:
supplying `×` is not the same as supplying *the* `×`, and a numerical-array carrier
supplies a pointwise one. -/

/-- **Ordinal carrier** — a representation that can be *ordered* (`<`, `>`), the least a
non-nominal magnitude needs. Mirrors `ScaleType.ordinal`. -/
class OrdinalCarrier (R : Type) [LE R] [LT R] : Prop

/-- **Interval carrier** — additionally supplies `0`, `+`, `−` (and unary `−`): differences
are representable. Mirrors `ScaleType.interval`; the carrier-side companion of `DifferenceKind`
(which is the *kind*-side gate for the same `+`/`−`). -/
class IntervalCarrier (R : Type) [LE R] [LT R] [Zero R] [Add R] [Sub R] [Neg R] : Prop
    extends OrdinalCarrier R

/-- **Ratio carrier** — additionally supplies `1`, `×`, `÷`: an absolute zero and full field
arithmetic. Mirrors `ScaleType.ratio`; the carrier-side companion of `ProductKind` /
`QuotientKind`. The concrete representations the library runs on — `Int`, `ℝ`, `Float` — are
all ratio carriers. -/
class RatioCarrier (R : Type) [LE R] [LT R] [Zero R] [One R] [Add R] [Sub R] [Neg R] [Mul R]
    [Div R] : Prop extends IntervalCarrier R

/-- `Int` is a ratio carrier (the proof carrier with exact arithmetic). -/
instance : RatioCarrier Int := {}
/-- `Float` is a ratio carrier (the executable representation). -/
instance : RatioCarrier Float := {}

/-- **The carrier tower reproduces the scale order.** Every ratio carrier is in particular an
interval carrier — the carrier-side image of `interval ⊏ ratio` (`ScaleType.allows_mono`). -/
theorem ratioCarrier_isIntervalCarrier {R : Type}
    [LE R] [LT R] [Zero R] [One R] [Add R] [Sub R] [Neg R] [Mul R] [Div R] [RatioCarrier R] :
    IntervalCarrier R := inferInstance

/-- And every interval carrier is an ordinal carrier — the image of `ordinal ⊏ interval`. -/
theorem intervalCarrier_isOrdinalCarrier {R : Type}
    [LE R] [LT R] [Zero R] [Add R] [Sub R] [Neg R] [IntervalCarrier R] :
    OrdinalCarrier R := inferInstance

/-! ## The scalar gate — whose `×` is the multiplication of magnitudes

The tower above says how *much* arithmetic a representation supplies. It does not say
whether that arithmetic **is** the arithmetic of magnitudes, and for the product and
quotient families that is the load-bearing question.

A numerical-array carrier — `QuantityVector`'s `ι → R`, the ISO 80000-2 §18
representation of a vector quantity — carries a perfectly good `Mul`: Lean's pointwise
one. The componentwise product of two position vectors is not a physical quantity of any
kind. Left ungated, `Quantity.mul` signs it anyway, because the `ProductKind` witness
licenses `length × length = area` on the *kind* side and the *carrier* then silently
chooses the operation. What comes out is a `Quantity area (Fin 3 → R)` holding a Hadamard
product: correctly kinded, correctly dimensioned, and not a thing.

`ScalarCarrier` is the missing half of this module's own doctrine — *a kind's scale says
an operation is meaningful; a carrier's tier says the representation can compute it; a
sound quantity operation needs both* — finally applied to `×` and `÷`.
`Quantity.mul`/`Quantity.div` require it, so a vector carrier **fails to synthesize**
rather than quietly multiplying componentwise.

**Why this cannot be a structural test.** The same Lean type `ι → R` is a scalar carrier
under one reading and not under another, and no property of the type decides which:

  * a **batch** carrier holds `N` independent samples *of one scalar quantity* — the
    Stage-4 propagators' whole design — and there elementwise `×` is exactly right;
  * a **vector** carrier holds `n` components *of one quantity* — and there elementwise
    `×` is meaningless.

So membership is a claim about what the representation *represents*, which is why this is
a marker class in the manner of `RatioCarrier` above and `ProductKind.ofRatio` in
`QuantityClassification`: nothing stops someone writing `ScalarCarrier (Fin 3 → ℝ)`. The
guarantee is this library's trust model throughout — **the default is refusal, and the
claim must be written, in full, where it is made.**

**Why it carries no law.** The obvious separating law is absence of zero divisors, and it
is wrong here: it holds at `ℝ` and at `Complex ℝ` and *fails* at `Float`, where two
nonzero magnitudes underflow to a zero product. A law-bearing class would exclude the
executable carrier the whole representation axis exists to keep.

The operations a vector carrier *does* license — the scalar product and the vector product
of ISO 80000-2 §18 — are not pointwise and do not have the `Quantity.mul` shape at all:
their operands and their result sit at different *variances*. Those belong to
`PropertyKindCalculus.Frame`. -/
class ScalarCarrier (R : Type) : Prop

/-- `Nat` is scalar: a count is one number. -/
instance instScalarCarrierNat : ScalarCarrier Nat := ⟨⟩
/-- `Int` is scalar. -/
instance instScalarCarrierInt : ScalarCarrier Int := ⟨⟩
/-- `Float` is scalar — the executable representation of a single magnitude. -/
instance instScalarCarrierFloat : ScalarCarrier Float := ⟨⟩

end PropertyKindCalculus

end Interface
