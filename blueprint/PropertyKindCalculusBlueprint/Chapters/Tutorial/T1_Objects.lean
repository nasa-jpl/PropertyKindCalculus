import Verso
import VersoManual
import VersoBlueprint
import PropertyKindCalculusBlueprint.References

-- A tutorial chapter: no nodes, no `{deftech}`. The code blocks are SubVerso anchors quoted
-- live from `examples/Tutorial/HarmonicOscillatorSquare.lean` (the `Tutorial` library); the
-- blueprint build refuses a block whose text no longer matches the anchored region.

open Verso.Genre
open Verso.Genre.Manual
open Informal
open Verso.Code.External

set_option verso.exampleProject ".."
set_option verso.exampleModule "Tutorial.HarmonicOscillatorSquare"

#doc (Manual) "T1 — What is measured: objects, sorts, and parts" =>
%%%
tag := "tutorial-objects"
%%%

Start at the bottom-left of the square, with the things that bear the properties. The
oscillator has two bodies and three springs, so two object types, each a plain inductive
with decidable equality:

```anchor objects
inductive Body | A | B
deriving DecidableEq, Repr

inductive Spring | kA | kC | kB
deriving DecidableEq, Repr
```

Each object has a _sort_, the kind of system it is: a point mass, a linear spring, and, for
the pair the bodies and springs make up, a coupled oscillator pair. Two further sorts,
springs in parallel and springs in series, are declared now and earn their keep in T6:

```anchor sorts
def bodyS : SortOfSystem := ⟨"point mass"⟩
def springS : SortOfSystem := ⟨"linear spring"⟩
def pairS : SortOfSystem := ⟨"coupled oscillator pair"⟩
def parallelS : SortOfSystem := ⟨"springs in parallel"⟩
def seriesS : SortOfSystem := ⟨"springs in series"⟩
```

The left edge of the square, _instantiated by_, is one instance per object type, declared
once and never derived:

```anchor sorted
/-- Left edge, *instantiated by*: every body is a point mass. Declared once, never derived. -/
instance : Sorted Body := ⟨fun _ => bodyS⟩
/-- Every spring is a linear spring. -/
instance : Sorted Spring := ⟨fun _ => springS⟩
```

A designation is what lets a quantity name its bearer in words; injectivity is decided:

```anchor designated
/-- Designation (so `toIndividualProperty` can name a body); injectivity by `decide`. -/
instance : Designated Body where
  designation
    | .A => ⟨"body A"⟩
    | .B => ⟨"body B"⟩
  designation_inj {x y} h := by
    cases x <;> cases y <;> first | rfl | exact absurd (System.mk.inj h) (by decide)

instance : Designated Spring where
  designation
    | .kA => ⟨"spring A"⟩
    | .kC => ⟨"spring C"⟩
    | .kB => ⟨"spring B"⟩
  designation_inj {x y} h := by
    cases x <;> cases y <;> first | rfl | exact absurd (System.mk.inj h) (by decide)
```

The quantities written over the objects are one line each. They are the individual
quantities T3 explains, and they are needed now so that the refusals below have something
to refuse; the kinds `massK` and `stiffnessK` they name are T2's subject:

```anchor modes
def mA : IndividualQuantity Body.A massK Int := ⟨3⟩
def mB : IndividualQuantity Body.B massK Int := ⟨5⟩
def kA : IndividualQuantity Spring.kA stiffnessK Int := ⟨6⟩
def kC : IndividualQuantity Spring.kC stiffnessK Int := ⟨2⟩
def kB : IndividualQuantity Spring.kB stiffnessK Int := ⟨3⟩
```

What this buys is checked by the compiler: every body is a point mass by `rfl`, the two
bodies share a sort, and a quantity reads back its two indices as an individual property
that names the kind and the bearer:

```anchor edges
/-- Left edge: a substance instantiates its kind (sort). -/
example : Sorted.sortOf Body.A = bodyS := rfl
example : Sorted.sortOf Spring.kC = springS := rfl
theorem bodies_one_sort : Sorted.sortOf Body.A = Sorted.sortOf Body.B := rfl

/-- Bottom + right edges: the two type indices of a mode, read back as an individual
property — the mode characterizes body A and instantiates mass. -/
example : mA.toIndividualProperty = ⟨massK, ⟨"body A"⟩⟩ := rfl
```

What it refuses is the first value proposition of the object axis. The masses of two bodies
do not add, nor the stiffnesses of two springs, and B's mass cannot stand in for A's, each
with the error that says why — an error that names the object:

```anchor bottomEdge
/- Bottom edge: masses of two bodies do not add. -/
/--
error: Application type mismatch: The argument
  mB
has type
  IndividualQuantity Body.B massK Int
but is expected to have type
  IndividualQuantity Body.A massK Int
in the application
  IndividualQuantity.add ⋯ mA mB
-/
#guard_msgs in
example := IndividualQuantity.add DifferenceKind.ofScale mA mB
/- Nor stiffnesses of two springs. -/
/--
error: Application type mismatch: The argument
  kC
has type
  IndividualQuantity Spring.kC stiffnessK Int
but is expected to have type
  IndividualQuantity Spring.kA stiffnessK Int
in the application
  IndividualQuantity.add ⋯ kA kC
-/
#guard_msgs in
example := IndividualQuantity.add DifferenceKind.ofScale kA kC
/- B's mass cannot stand in for A's. -/
/--
error: Type mismatch
  mB
has type
  IndividualQuantity Body.B massK Int
but is expected to have type
  IndividualQuantity Body.A massK Int
-/
#guard_msgs in
example : IndividualQuantity Body.A massK Int := mB
```

The case study types the same oscillator with nominal objects, a name such as
`⟨"oscillator A"⟩` and no sort. One line shows what that costs. `dedicatedFor`, T2's
construct, reaches the catalogue entry dedicated to an object _through the object's sort_,
and an object with no sort has no way up; the first line of the error is the whole story:

```anchor noSort
/-! The case study's objects are nominal `System`s and know no sort, so they cannot reach
the top edge through `dedicatedFor` at all — the refusal that says why the tutorial needs
an object type with a `Sorted` instance. -/
/--
error: failed to synthesize instance of type class
  Sorted System

Hint: Type class instance resolution failures can be inspected with the `set_option trace.Meta.synthInstance true` command.
-/
#guard_msgs in
example := massK.dedicatedFor (⟨"oscillator A"⟩ : Object) whole
```

A dimension-and-units library has no object axis at all: `mA + mB` is a sum of two masses
and nothing more can be said. Tagging the object into the type by hand recovers the refusal
and loses the sum (T0's third row); declaring the object as an index of the quantity keeps
both, as T3 shows.

Reference: {ref "object-types"}[The object type] for `Sorted`, `Designated`, and the
individual quantity; {ref "foundations"}[Foundations] for the square this part walks.
