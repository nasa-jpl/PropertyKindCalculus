/-
# Frame — the structural half of value representation (coordinate frames and variance)

`QuantityVector` realizes ISO 80000-2 §18's *numerical* reading of a vector quantity: one
kind, one scalar unit, an indexed array of numbers. That reading is deliberately silent on
the sentence §18 puts next to it — **the quantity is independent of the choice of
coordinate system while its numerical components are not.** Independence of a choice is
not a property an array has; it is a property of how the array behaves when the choice
changes, and nothing in `Quantity k (Fin n → R)` records that a choice was made at all.

This module supplies the missing structure: which frame components were read in, how they
respond when the frame changes, and which quantities survive the change unaltered.

## The four words, since they all get used loosely

  * A **frame** is a choice of basis. It is not data the module computes with — it is the
    thing coefficients are stated *relative to*, so `Frame` carries an identity and nothing
    else, and two frames differ by being different choices.
  * A vector quantity's numbers are **coefficients in that basis**: `v = Σᵢ vᵢ eᵢ`. The
    quantity is one thing; the list `(v₀, …, vₙ₋₁)` is what it looks like against one choice
    of `eᵢ`. This is ISO 80000-2 §18's "the quantity is independent of the coordinate system
    while its numerical components are not", read literally.
  * A **change of frame** `FrameChange n R f g` is the transition matrix `C` between two such
    choices. It is **orthonormal** when its columns are an orthonormal set (`Cᵀ C = I`) —
    equivalently, when the two bases are both orthonormal and `C⁻¹ = Cᵀ`. Rotations and
    reflections qualify; a general linear change does not, and is still expressible.
  * The **variance** is how many basis indices a quantity's coefficients carry, hence how
    many copies of `C` act on them. It is the datum that distinguishes a velocity from a
    stiffness matrix when both are held as `Fin n → …` over the same kind and dimension.

**What is invariant, and why.** A contraction `x · y = Σᵢ xᵢ yᵢ` sums over the basis index,
and under an orthonormal change the frame's entries collect into `Σᵢ C i j · C i l = δⱼₗ` and
cancel — so the sum is a property of the two quantities and not of the basis. A single
coefficient `xᵢ` has no such sum: it *is* the projection onto the `i`-th basis vector, and
replacing that basis vector changes it by definition. So the invariance is not a general fact
about scalars that components happen to violate; it is a fact about *contractions*, and a
coefficient is simply not one. `FrameReal` proves both halves, the second with a witness.

## What goes wrong without it

Two position vectors of one system, at the same kind, the same dimension, the same unit and
the same carrier, expressed in different frames, add without complaint. The sum is
meaningless and there is nothing anywhere below this module to say so — a dimension check
passes, a kind check passes, an object-identity check passes, and the numbers are all
plausible. Rigid-body work is made of this error: a body-frame inertia contracted with a
lab-frame angular velocity is dimensionally perfect and wrong.

The dual error is applying a frame change to something that is not frame-relative. A triple
of masses is a `Fin 3 → R` exactly as a position is; rotating it produces three numbers that
are not masses of anything.

## Frames are not units, and the difference is the point

`UnitConversion` handles the other change of representation, and the two factor
differently:

  * a **unit** change acts *through the dimension* — the factor `d ↦ dimScale u₁ u₂ d` is
    computed from the quantity's dimension, so the kind layer already knows it, and a
    dimensioned scheme can state unit covariance without any further apparatus;
  * a **frame** change acts *through the carrier* and is **dimension-blind** — position,
    velocity, force and field all turn by the same matrix, and their dimensions have no
    bearing on it.

So a scheme with only a dimension axis can express the first and is structurally silent on
the second. That is why this is a separate axis rather than a second kind of unit, and why
a frame — unlike a unit, which the kind determines a canonical choice of — is carried as an
*index*: there is no canonical frame to fall back on, and mixing two of them is invisible
to every other check in the library.

## Scope: orthonormal changes, and what that defers

The transformations here are linear changes of Cartesian frame. Under an **orthonormal**
change the covariant and contravariant transformation laws coincide (`C⁻¹ = Cᵀ`), so this
module carries one `vector` variance rather than the covector/vector pair. That is exactly
the setting Cartesian coordinates put you in, and it is not the general one: the
covariant/contravariant split, curvilinear coordinates, bound-versus-free vectors, and
affine frames (an origin as well as a basis, which positions need and velocities do not)
are **not** provided here. `IsOrthonormal` is a hypothesis on the theorems that need it,
never a field, so the definitions stay usable for a general linear change while the
invariance results state their price.

## Where the laws are

The definitions below are carrier-parametric and Mathlib-free, so a change of frame runs at
`Float` and specifies at `ℝ` — the representation axis applies to the frame axis like any
other. Proving anything about a sum of products needs ring laws the core does not carry, so
the invariance theorems live in `PropertyKindCalculus.FrameReal` (the `Dimension` library),
exactly as `Quantity`'s laws relate to `QuantityReal`'s carrier.
-/

import PropertyKindCalculus.QuantityVector
import PropertyKindCalculus.QuantityClassification

namespace PropertyKindCalculus

/-! ## Frames -/

/-- **A coordinate frame** — an identified choice of basis. The identity is the whole
content: what a frame *is* numerically never enters, because a frame is exactly the thing
components are relative *to*, and two frames differ by being different choices.

Anchoring is by name (`"lab"`, `"body frame of oscillator A"`, `"principal axes"`), the
same way `System` and `Component` carry their identity. -/
structure Frame where
  /-- The frame's identity. -/
  id : String
deriving DecidableEq, Repr

/-- **How a quantity's coefficients respond to a change of frame** — how many basis indices
they carry, and therefore how many copies of the transition matrix act on them.

Not a property of the kind and not a property of the carrier: two quantities of the same kind
cannot differ here, but a mass and a position have the same carrier `Fin 3 → R` under
different laws, and this is the only place the difference can be written.

**`scalar` means "no basis index", not "does not depend on the basis".** The distinction
matters and is the one readers get wrong. A mass carries no index and is genuinely the same
number in every frame. A *coefficient* of a vector quantity also carries no index once it has
been extracted — there is nothing left for a matrix to act on — and it is emphatically not
frame-independent, because it was defined as the coefficient along a basis vector the change
of frame replaced. `InFrame.component` therefore lands at `scalar` variance with **no**
invariance theorem attached, and `FrameReal.component_not_invariant` exhibits the witness. -/
inductive Variance
  /-- No basis index: nothing for the transition matrix to act on. A mass or an energy is
  frame-independent for this reason; an extracted coefficient is *not*, and shares this tag
  only because it too has no index left. -/
  | scalar
  /-- One basis index, transforming once: `v ↦ C v` (position, velocity, force). -/
  | vector
  /-- Two basis indices, transforming once each: `M ↦ C M Cᵀ` (an inertia tensor, a stiffness
  matrix). -/
  | rank2
deriving DecidableEq, Repr

/-- **Components read in a frame, at a stated variance** — a role wrapper over `Quantity`,
in the manner of `Axis`'s `Extent`/`Position` and `Bounds`' endpoints, with the same field
name `q`.

The three indices do three different jobs and none substitutes for another: `k` says what
property this is, `var` says how it behaves under a change of frame, and `f` says which
frame these particular numbers were read in. Adding two of these requires all three to
agree, which is the guarantee the module exists for. -/
structure InFrame (f : Frame) (var : Variance) (k : KindOfProperty) (R : Type) where
  /-- The quantity whose magnitude holds the components. -/
  q : Quantity k R

namespace InFrame

variable {f g : Frame} {var : Variance} {k : KindOfProperty} {R : Type}

/-- The components, as the carrier holds them. -/
def components (x : InFrame f var k R) : R := x.q.magnitude

@[simp] theorem components_mk (q : Quantity k R) :
    (InFrame.mk (f := f) (var := var) q).components = q.magnitude := rfl

/-- **Same frame, same variance, same kind** — the only shape addition takes. Two readings
in different frames have different types, so their sum is not a wrong answer to write; it
is not writable. -/
def add (h : DifferenceKind k) (x y : InFrame f var k R) [Carrier R] : InFrame f var k R :=
  ⟨Quantity.add h x.q y.q⟩

@[simp] theorem add_components [Carrier R] (h : DifferenceKind k) (x y : InFrame f var k R) :
    (x.add h y).components = Carrier.add x.components y.components := rfl

end InFrame

/-! ## Changes of frame -/

/-- **A change of frame from `f` to `g`**, as the matrix of the transition in `n`
dimensions over the carrier `R`. `entry i j` is row `i`, column `j`.

The frames appear as *phantom* indices — they constrain which readings this may be applied
to without contributing to the data, which is what makes a change of frame composable in
one direction only and non-applicable to a reading in some third frame. -/
structure FrameChange (n : Nat) (R : Type) (f g : Frame) where
  /-- The transition matrix: `entry i j` is the `i`-th row, `j`-th column. -/
  entry : Fin n → Fin n → R

/-- **The sum of an indexed family of carrier values.** Written by recursion so it needs
only `Zero` and `Add` — no `Fintype`, no Mathlib — which is what keeps a change of frame
executable at `Float`. `FrameReal` proves it agrees with `∑ i, f i`. -/
def sumFin {R : Type} [Zero R] [Add R] : {n : Nat} → (Fin n → R) → R
  | 0, _ => 0
  | _ + 1, v => v 0 + sumFin (fun i => v i.succ)

@[simp] theorem sumFin_zero {R : Type} [Zero R] [Add R] (v : Fin 0 → R) :
    sumFin v = 0 := rfl

@[simp] theorem sumFin_succ {R : Type} [Zero R] [Add R] {n : Nat} (v : Fin (n + 1) → R) :
    sumFin v = v 0 + sumFin (fun i => v i.succ) := rfl

namespace FrameChange

variable {n : Nat} {R : Type} {f g h : Frame}

/-- The matrix acting on a numerical vector: `(C v) i = Σⱼ C i j · v j`. -/
def mulVec [Zero R] [Add R] [Mul R] (c : FrameChange n R f g) (v : Fin n → R) : Fin n → R :=
  fun i => sumFin (fun j => c.entry i j * v j)

/-- The transpose — for an orthonormal change, its inverse. -/
def transpose (c : FrameChange n R f g) : FrameChange n R g f :=
  ⟨fun i j => c.entry j i⟩

/-- The matrix acting on both indices of a rank-2 array: `(C M Cᵀ) i j = Σₖ Σₗ C i k · M k l · C j l`. -/
def conj [Zero R] [Add R] [Mul R] (c : FrameChange n R f g) (m : Fin n → Fin n → R) :
    Fin n → Fin n → R :=
  fun i j => sumFin (fun k => sumFin (fun l => c.entry i k * m k l * c.entry j l))

/-- **Staying put.** The identity change of frame — the diagonal matrix. -/
def id (n : Nat) (R : Type) [Zero R] [One R] (f : Frame) : FrameChange n R f f :=
  ⟨fun i j => if i = j then 1 else 0⟩

/-- **Composition**, as the matrix product. Note the direction: a change `f → g` followed by
a change `g → h` is a change `f → h`, and the frames make any other pairing a type error. -/
def comp [Zero R] [Add R] [Mul R] (c₂ : FrameChange n R g h) (c₁ : FrameChange n R f g) :
    FrameChange n R f h :=
  ⟨fun i j => sumFin (fun m => c₂.entry i m * c₁.entry m j)⟩

/-- **Orthonormality** — the columns are an orthonormal set, i.e. `Cᵀ C = I`. Carried as a
`Prop` on the change rather than as a field of it, in the manner of `ProductKind`: the
definitions above are meaningful for any linear change, and the theorems that genuinely need
`C⁻¹ = Cᵀ` say so in their statements. A rotation satisfies it; a rotation composed with a
reflection satisfies it too, which is why this is orthonormality and not "is a rotation". -/
def IsOrthonormal [Zero R] [One R] [Add R] [Mul R] (c : FrameChange n R f g) : Prop :=
  ∀ i j : Fin n, sumFin (fun m => c.entry m i * c.entry m j) = if i = j then 1 else 0

end FrameChange

/-! ## Acting on readings

Three actions, one per variance, each typed so that it accepts only the variance whose law
it implements. There is no dispatch and no default: applying the vector law to a scalar
reading is not a runtime decision that goes the wrong way, it is an expression that does not
elaborate. -/

namespace InFrame

variable {f g : Frame} {k k₁ k₂ : KindOfProperty} {R : Type} {n : Nat}

/-- **A scalar reads the same in every frame.** The action is the identity on the value, and
the *only* thing that changes is the index — which is the content of "invariant": not that
the number happens to agree, but that no matrix was consulted to obtain it. -/
def toFrameScalar (x : InFrame f .scalar k R) : InFrame g .scalar k R := ⟨x.q⟩

@[simp] theorem toFrameScalar_components (x : InFrame f .scalar k R) :
    (toFrameScalar (g := g) x).components = x.components := rfl

/-- **A vector's components turn with the frame**: `v ↦ C v`. -/
def toFrameVector [Zero R] [Add R] [Mul R] (c : FrameChange n R f g)
    (x : InFrame f .vector k (Fin n → R)) : InFrame g .vector k (Fin n → R) :=
  ⟨⟨c.mulVec x.components⟩⟩

@[simp] theorem toFrameVector_components [Zero R] [Add R] [Mul R] (c : FrameChange n R f g)
    (x : InFrame f .vector k (Fin n → R)) :
    (toFrameVector c x).components = c.mulVec x.components := rfl

/-- **A rank-2 array turns on both indices**: `M ↦ C M Cᵀ`. This is the law that makes a
diagonal matrix stop being diagonal, which is the whole reason a per-axis list of numbers
is not a vector. -/
def toFrameRank2 [Zero R] [Add R] [Mul R] (c : FrameChange n R f g)
    (x : InFrame f .rank2 k (Fin n → Fin n → R)) :
    InFrame g .rank2 k (Fin n → Fin n → R) :=
  ⟨⟨c.conj x.components⟩⟩

@[simp] theorem toFrameRank2_components [Zero R] [Add R] [Mul R] (c : FrameChange n R f g)
    (x : InFrame f .rank2 k (Fin n → Fin n → R)) :
    (toFrameRank2 c x).components = c.conj x.components := rfl

/-! ## The scalar product — the licensed way back to a scalar carrier

`Quantity.mul` is unavailable at a numerical-array carrier by construction
(`ScalarCarrier`, in `Quantity`): the pointwise product Lean would supply is not a physical
operation. The scalar product is what §18 licenses in its place, and it has a different
shape in three respects — both operands must be read in the **same frame**, both must be at
**vector** variance, and the result lands at **scalar** variance on the **scalar carrier**
`R`, where `Quantity.mul` and the rest of the ratio-scale arithmetic become available again.

The kind law is the ordinary `ProductKind`: a scalar product of a length by a length is an
area, and the kind layer neither knows nor needs to know that the route went through
components. -/

/-- **The scalar product** `x · y = Σᵢ xᵢ yᵢ`, at the product kind, in the shared frame.

The shared frame `f` is the gate: two readings taken in different frames have different
types and there is no contraction of them to write. That is the same device the object
index uses for individual quantities, on the axis where it is otherwise undetectable. -/
def dot [Zero R] [Add R] [Mul R] [ScalarCarrier R] {k : KindOfProperty}
    (_h : ProductKind k₁ k₂ k)
    (x : InFrame f .vector k₁ (Fin n → R)) (y : InFrame f .vector k₂ (Fin n → R)) :
    InFrame f .scalar k R :=
  ⟨⟨sumFin (fun i => x.components i * y.components i)⟩⟩

@[simp] theorem dot_components [Zero R] [Add R] [Mul R] [ScalarCarrier R]
    {k : KindOfProperty} (h : ProductKind k₁ k₂ k)
    (x : InFrame f .vector k₁ (Fin n → R)) (y : InFrame f .vector k₂ (Fin n → R)) :
    (dot h x y).components = sumFin (fun i => x.components i * y.components i) := rfl

/-- **The squared magnitude** `|x|² = x · x` — the scalar product's diagonal, named because
it is what kinetic energy, potential energy and every modulus are built from. -/
def normSq [Zero R] [Add R] [Mul R] [ScalarCarrier R] {k : KindOfProperty}
    (h : ProductKind k₁ k₁ k) (x : InFrame f .vector k₁ (Fin n → R)) :
    InFrame f .scalar k R :=
  dot h x x

@[simp] theorem normSq_components [Zero R] [Add R] [Mul R] [ScalarCarrier R]
    {k : KindOfProperty} (h : ProductKind k₁ k₁ k)
    (x : InFrame f .vector k₁ (Fin n → R)) :
    (normSq h x).components = sumFin (fun i => x.components i * x.components i) := rfl

/-- **Reading a coefficient.** A component of a vector quantity is a quantity of the *same*
kind (§18: the unit belongs to the whole vector), and it is **frame-relative** — which is the
difference between this and `Quantity.get!`, whose result carries no frame because a table's
rows are not a basis.

The variance drops to `scalar` because there is no basis index left for the transition matrix
to act on. That is *not* the same as being frame-independent: `x.component i` is the
projection of `x` onto the `i`-th basis vector of `f`, so a change of frame changes it by
definition. The frame index `f` is retained for exactly this reason, and no invariance theorem
is attached — `FrameReal.component_not_invariant` supplies the witness that none could be. -/
def component [Zero R] (x : InFrame f .vector k (Fin n → R)) (i : Fin n) :
    InFrame f .scalar k R :=
  ⟨⟨x.components i⟩⟩

@[simp] theorem component_components [Zero R] (x : InFrame f .vector k (Fin n → R))
    (i : Fin n) : (x.component i).components = x.components i := rfl

end InFrame

end PropertyKindCalculus
