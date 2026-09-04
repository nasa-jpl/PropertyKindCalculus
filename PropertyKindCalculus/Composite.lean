/-
# Composite objects and licensed assembly (Dybkær §3.3 mereology, §13.5 extensivity)

`Extensivity.lean` states the §13.5 law over `PropertyValue` numerals: for an extensive
kind, the value on a whole is the sum over the leaves of a `Decomposition`. That is the
law. This module is the *arithmetic* the law licenses — aggregation at the
`IndividualQuantity` layer, where the object rides in the type and therefore where a sum
over parts has to say which object it lands on.

Two things are needed, and neither existed before.

**An object type with a whole in it.** Object-gated addition refuses `p.mass + q.mass` for
distinct parts `p` and `q`, which is right — and it equally refuses the *legitimate* total
mass of the assembly, because the total characterizes an object the parts' type does not
contain. The whole and its parts must inhabit **one** object type or the arithmetic cannot
relate them. `Composite P` is that type when the host library has none of its own; a host
that does (a `System` with a naming convention, an index type with a distinguished top) can
use its own, since the eliminator below takes the whole and the part-injection as
arguments rather than fixing them.

`PartWhole.lean` does not answer this: its `Part`/`Whole` are role wrappers over
*quantities of one kind*, which is what stops a call site handing a portion and a total to
a fraction the wrong way round. The question here is which *object* a sum characterizes,
and roles over quantities cannot say.

**A license.** Aggregation is not available for the asking. Mass assembles; angular
velocity does not, and the failure of a library that sums it anyway is silent. `Assembles`
is the curation entry, carrying the scale gate as its content, and
`assemble_eq_measured` below is where the entry meets §13.5: for a kind that is
*actually* extensive under a measurement, the assembled magnitude **is** the measured
value of the whole. The class is the author's claim; that theorem is what the claim buys.
-/

import PropertyKindCalculus.Extensivity
import PropertyKindCalculus.IndividualQuantity

namespace PropertyKindCalculus

universe u v

/-! ## The composite object type -/

/-- **The object type of a composite** — the whole, or one of its parts.

The construct `MR22` asks for and the one a structural object type (physlib's particles, a
mesh's cells) does not supply on its own: a particle type contains particles and no
assembly, so a total mass has nowhere to live. `Composite P` adds exactly one inhabitant,
and it is *distinct as a term* from every part, which is the whole mechanism — a
whole-system quantity and a part quantity do not add, definitionally, with nothing to
prove and nothing to enforce. -/
inductive Composite (P : Type u) where
  /-- The assembly itself — the bearer of whole-composite quantities. -/
  | whole
  /-- One part of the assembly. -/
  | part (p : P)
deriving DecidableEq, Repr

/-- A part reads as itself where a composite object is expected. This does **not** elide the
object index of a quantity type (`IndividualQuantity`'s object argument determines its own
object type, so there is nothing to coerce *to*); it is for the explicit positions — the
part-injection handed to `assemble`, a predicate over composite objects. -/
instance {P : Type u} : CoeHead P (Composite P) := ⟨Composite.part⟩

/-- **Naming a composite** — a `Designated` structure for `Composite P`, given a name for
the whole and the proof that no part already answers to it.

A *definition*, not an instance, and the disjointness hypothesis is why: which nominal
system an assembly is called is a terminological commitment its author makes, not something
instance search can find, and a whole silently sharing a part's name would break the
injectivity `Designated` exists to guarantee. -/
@[instance_reducible]
def Composite.designated {P : Type u} [Designated P] (w : Object)
    (hw : ∀ p : P, Designated.designation p ≠ w) : Designated (Composite P) where
  designation
    | .whole => w
    | .part p => Designated.designation p
  designation_inj {x y} h := by
    cases x <;> cases y <;> simp only at h
    · rfl
    · exact absurd h.symm (hw _)
    · exact absurd h (hw _)
    · exact congrArg Composite.part (Designated.designation_inj h)

/-! ## The license -/

/-- **The aggregation license (§13.5, curated).** A kind whose quantities may be summed over
the parts of a composite to give the quantity of the whole. Mass carries it; angular
velocity deliberately does not, and the sum of the parts' angular velocities is then not a
term anyone can write.

Registration is opt-in — an unregistered kind has no instance and `assemble` does not
elaborate — and the entry is not a formality: its `diff` field is the same scale gate
`Quantity.add` demands, so a nominal or ordinal kind cannot be licensed at all. What the
class does *not* prove is that the sum is the physics; that is a fact about a measurement,
and `assemble_eq_measured` is where an author discharges it. -/
class Assembles (k : KindOfProperty) : Prop where
  /-- `k`'s scale licenses the sum the assembly is built from — interval or ratio. -/
  diff : DifferenceKind k

/-! ## The eliminator -/

variable {O : Type u} {P : Type v} {k : KindOfProperty} {R : Type}

/-- **Assembly — the quantity of the whole from the quantities of its parts.**

The whole `whole` and the part-injection `part` are arguments, so this serves a bespoke
`Composite P` (`assemble .whole .part`) and equally a host library's own object type with
its own naming of parts (`assemble rover (partOf rover)`). `f` is *dependent*: the quantity
supplied for `p` must characterize `part p`, which is the gate — a part's quantity cannot
be smuggled in under another part's name.

The traversal is `Decomposition.fold`, the same one `leafSum` uses, so the arithmetic here
and the §13.5 law are one recursion read at two carriers rather than two that agree. -/
def assemble [Carrier R] [Assembles k] (whole : O) (part : P → O) (d : Decomposition P)
    (f : (p : P) → IndividualQuantity (part p) k R) : IndividualQuantity whole k R :=
  ⟨d.fold (fun p => (f p).magnitude) Carrier.add⟩

@[simp] theorem assemble_magnitude [Carrier R] [Assembles k] (whole : O) (part : P → O)
    (d : Decomposition P) (f : (p : P) → IndividualQuantity (part p) k R) :
    (assemble whole part d f).magnitude
      = d.fold (fun p => (f p).magnitude) Carrier.add := rfl

/-- **The license, cashed (§13.5).** When the kind really is extensive under a measurement
`m`, the assembled magnitude over any decomposition **is** the value `m` reports for the
whole — the quantity-level eliminator and Dybkær's aggregation law computing the same
number, by `extensive_additive`.

This is what makes `Assembles` a claim about the world rather than a permission slip: the
class licenses the sum to be *written*, and this theorem is what an author shows to say the
sum is *right*. Its absence is exactly the volume-on-mixing case — `volMix` has no
`Extensive` witness, so no instance of this theorem exists for it. -/
theorem assemble_eq_measured [Assembles k] (whole : O) (part : P → O)
    {m : Measurement P} (h : Extensive k m) (d : Decomposition P) :
    (assemble (k := k) whole part d (fun p => ⟨(m (.atom p)).numeral⟩)).magnitude
      = (m d).numeral :=
  (extensive_additive h d).symm

end PropertyKindCalculus
