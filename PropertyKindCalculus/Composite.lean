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
value of the whole. The class is the author's claim; that theorem is what the claim buys —
and `assemble_ne_measured` is what it costs to claim it wrongly: for a *whole-proper* kind
the same term still elaborates, and reports a number the whole does not have.

**Whole, but not one.** Those two halves are Marmodoro's two kinds of structure. A
`Decomposition` *unites*: it makes a whole out of parts and, being one carving among many,
brings no count principle with it — "physical structure unites; while metaphysical structure
unifies … But wholes are not always unities" (*Whole, but not One*, 2018, §3). What makes
the many *one* is not found among the parts: it is the sort `σ`, declared once by a model —
unification "under the individuation principle of the sortal", and Dybkær's sort of system
is that sortal under another name. Hence the three design decisions of this module. The
whole is *added* rather than derived, because no carving yields it. The same parts under two
sorts are two object types with two sets of licenses, because the statue and the lump are
two wholes. And the license is indexed by the sort rather than by the kind alone, because
how parts make a whole is settled by what the whole is — which is exactly the claim the
parts cannot make on their own behalf.
-/

import PropertyKindCalculus.Extensivity
import PropertyKindCalculus.IndividualQuantity

namespace PropertyKindCalculus

universe u v w

/-! ## The composite object type -/

/-- **The object type of a composite** — the whole, or one of its parts.

The construct `MR22` asks for and the one a structural object type (physlib's particles, a
mesh's cells) does not supply on its own: a particle type contains particles and no
assembly, so a total mass has nowhere to live. `Composite P` adds exactly one inhabitant,
and it is *distinct as a term* from every part, which is the whole mechanism — a
whole-system quantity and a part quantity do not add, definitionally, with nothing to
prove and nothing to enforce. -/
inductive Composite (σ : SortOfSystem) (P : Type u) where
  /-- The assembly itself — the bearer of whole-composite quantities. -/
  | whole
  /-- One part of the assembly, *read as composing this sort of whole*. The bare `p` (at the
  object type `P` itself) remains the part simpliciter; `Composite.part p` is the part in its
  compositional role, which is why the sort reaches it. -/
  | part (p : P)
deriving DecidableEq, Repr

/-- A part reads as itself where a composite object is expected — a `CoeTail`, since the
sort of the composite comes from the expected type. This does **not** elide the object index
of a quantity type (`IndividualQuantity`'s object argument determines its own object type, so
there is nothing to coerce *to*); it is for the explicit positions — the part-injection handed
to `assemble`, a predicate over composite objects. -/
instance {σ : SortOfSystem} {P : Type u} : CoeTail P (Composite σ P) := ⟨Composite.part⟩

/-- **Naming a composite** — a `Designated` structure for `Composite σ P`, given a name for
the whole and the proof that no part already answers to it.

A *definition*, not an instance, and the disjointness hypothesis is why: which nominal
system an assembly is called is a terminological commitment its author makes, not something
instance search can find, and a whole silently sharing a part's name would break the
injectivity `Designated` exists to guarantee. -/
@[instance_reducible]
def Composite.designated {σ : SortOfSystem} {P : Type u} [Designated P] (w : Object)
    (hw : ∀ p : P, Designated.designation p ≠ w) : Designated (Composite σ P) where
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

/-- **The aggregation license (§13.5, curated) — keyed by the sort of the whole.** A kind
whose quantities may be summed over the parts of a composite *of the given sort* to give the
quantity of the whole. Mass carries it for every sort a mechanical model declares; angular
velocity deliberately carries it for none, and the sum of the parts' angular velocities is
then not a term anyone can write.

The sort index is not decoration, and the library's own counterexample is why: **volume**.
Over the parts of a rigid assembly, volume aggregates; over the parts of a mixture it
contracts (`mixing_subadditive` — 50 mL of ethanol and 50 mL of water make 96 mL), and both
facts are facts about *volume*. A registry keyed by the kind alone must either license the
mixture or refuse the assembly, and either answer is wrong. Keyed by the sort, both answers
are right at once — which is the neo-Aristotelian point that how parts unify into a whole is
dictated by the *sort* of the whole, not by the attribute being summed and not by the parts.

Registration is opt-in — an unregistered pair has no instance and `assemble` does not
elaborate — and the entry is not a formality: its `diff` field is the same scale gate
`Quantity.add` demands, so a nominal or ordinal kind cannot be licensed at all. What the
class does *not* prove is that the sum is the physics; that is a fact about a measurement,
and `assemble_eq_measured` is where an author discharges it, per sort. -/
class Assembles (σ : SortOfSystem) (k : KindOfProperty) : Prop where
  /-- `k`'s scale licenses the sum the assembly is built from — interval or ratio. -/
  diff : DifferenceKind k

/-! ## Joint objects

A quantity can characterize an *ordered pair* of objects rather than one: a flow from a
source to a sink, a torque delivered across a coupling, the force one body exerts on another.
Under the parameterization that needs no construct at all — the object type is `O₁ × O₂`, and
the ordering gate falls out of the pair's own equality, so a quantity of `(a, b)` and one of
`(b, a)` do not combine.

What the shape does need is its one *meaningful* re-indexing. Everything else about a joint
object is ordinary. -/

/-- **The transpose of a joint quantity** — the same magnitude, read as a quantity of the
reversed pair.

This is the equal-and-opposite reading, and it is the only re-indexing of an individual
quantity this library offers. There is deliberately no general `reindex`: moving a magnitude
from one object to another is exactly what the object index exists to prevent, and an
operation that did it on request would return the layer to a naming convention. The transpose
is safe because it is not a move — the pair `(a, b)` and the pair `(b, a)` are the same
coupling read from its two ends, and which end is *source* is the whole content of a law like
Newton's third.

Its value is that the law becomes a type. A "reverse" that negates a magnitude and forgets to
exchange the endpoints has the untransposed type, so it does not elaborate where a reversed
force is expected. -/
def IndividualQuantity.transpose {O₁ : Type u} {O₂ : Type v} {a : O₁} {b : O₂}
    {k : KindOfProperty} {R : Type} (q : IndividualQuantity (a, b) k R) :
    IndividualQuantity (b, a) k R :=
  ⟨q.magnitude⟩

@[simp] theorem IndividualQuantity.transpose_magnitude {O₁ : Type u} {O₂ : Type v} {a : O₁}
    {b : O₂} {k : KindOfProperty} {R : Type} (q : IndividualQuantity (a, b) k R) :
    q.transpose.magnitude = q.magnitude := rfl

/-- **The transpose is an involution** — reading a coupling from the far end twice is reading
it from the near end, with nothing lost. -/
@[simp] theorem IndividualQuantity.transpose_transpose {O₁ : Type u} {O₂ : Type v} {a : O₁}
    {b : O₂} {k : KindOfProperty} {R : Type} (q : IndividualQuantity (a, b) k R) :
    q.transpose.transpose = q := rfl

/-! ## The eliminator -/

variable {O : Type u} {P : Type v} {k : KindOfProperty} {R : Type}

/-- **Assembly — the quantity of the whole from the quantities of its parts, as a sort of
whole.**

The sort `σ` says *what kind of whole* is being composed, and it is the index the license is
looked up at — assembling the same parts as a different sort of whole is a different act, with
its own licenses (rigid assembly versus mixture is the canonical split). The whole `whole` and
the part-injection `part` are arguments, so this serves a bespoke `Composite P`
(`assemble σ .whole .part`) and equally a host library's own object type with its own
naming of parts (`assemble σ rover (partOf rover)`). `f` is *dependent*: the quantity
supplied for `p` must characterize `part p`, which is the gate — a part's quantity cannot
be smuggled in under another part's name.

The traversal is `Decomposition.fold`, the same one `leafSum` uses, so the arithmetic here
and the §13.5 law are one recursion read at two carriers rather than two that agree. -/
def assemble [Carrier R] (σ : SortOfSystem) [Assembles σ k] (whole : O) (part : P → O)
    (d : Decomposition P) (f : (p : P) → IndividualQuantity (part p) k R) :
    IndividualQuantity whole k R :=
  ⟨d.fold (fun p => (f p).magnitude) Carrier.add⟩

@[simp] theorem assemble_magnitude [Carrier R] (σ : SortOfSystem) [Assembles σ k]
    (whole : O) (part : P → O)
    (d : Decomposition P) (f : (p : P) → IndividualQuantity (part p) k R) :
    (assemble σ whole part d f).magnitude
      = d.fold (fun p => (f p).magnitude) Carrier.add := rfl

/-- **The license, cashed (§13.5).** When the kind really is extensive under a measurement
`m`, the assembled magnitude over any decomposition **is** the value `m` reports for the
whole — the quantity-level eliminator and Dybkær's aggregation law computing the same
number, by `extensive_additive`.

This is what makes `Assembles` a claim about the world rather than a permission slip: the
class licenses the sum to be *written*, and this theorem is what an author shows to say the
sum is *right*. Its absence is exactly the volume-on-mixing case — `volMix` has no
`Extensive` witness, so no instance of this theorem exists for it. -/
theorem assemble_eq_measured (σ : SortOfSystem) [Assembles σ k] (whole : O) (part : P → O)
    {m : Measurement P} (h : Extensive k m) (d : Decomposition P) :
    (assemble (k := k) σ whole part d (fun p => ⟨(m (.atom p)).numeral⟩)).magnitude
      = (m d).numeral :=
  (extensive_additive h d).symm

/-- **The license refused.** For a *whole-proper* kind — one whose
value the parts do not determine, in either of the two ways they could — there is a carving
on which the assembled magnitude is **not** the value the whole has. Not merely unjustified:
wrong, on an exhibited pair of parts.

The `[Assembles σ k]` instance is still required, and that is the finding. The class licenses
the sum to be *written*; nothing about writing it makes it true, so an author who registers a
whole-proper kind gets a term that elaborates and a number that is not the physics. This is
the negative counterpart of `assemble_eq_measured` — same eliminator, same measurement, the
`Extensive` hypothesis replaced by its refutation — and it is why the registry is opt-in and
its entries are curated per sort. -/
theorem assemble_ne_measured (σ : SortOfSystem) [Assembles σ k] (whole : O)
    (part : P → O) {m : Measurement P} (h : WholeProper k m) :
    ∃ d : Decomposition P,
      (assemble (k := k) (R := Int) σ whole part d
        (fun p => ⟨(m (.atom p)).numeral⟩)).magnitude ≠ (m d).numeral := by
  obtain ⟨p, q, hpq⟩ := h.notAdditive
  refine ⟨.union (.atom p) (.atom q), fun he => hpq ?_⟩
  have hfold : (assemble (k := k) (R := Int) σ whole part (.union (.atom p) (.atom q))
      (fun p => ⟨(m (.atom p)).numeral⟩)).magnitude
        = (m (.atom p)).numeral + (m (.atom q)).numeral := rfl
  exact (hfold.symm.trans he).symm

end PropertyKindCalculus
