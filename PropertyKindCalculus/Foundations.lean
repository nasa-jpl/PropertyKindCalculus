/-
# Foundations — system and object

Dybkær, *An Ontology on Property for Physical, Chemical, and Biological Systems*
(2009), Chapter 3.
-/

module

public section -- pkc-blanket
@[expose] section -- pkc-blanket-expose

namespace PropertyKindCalculus

universe u v

/-- **§3.3 system** — "part or phenomenon of the perceivable or conceivable
world consisting of a demarcated arrangement of a set of elements and a set of
relationships or processes between these elements."

Specified abstractly by identity here; the mereological structure needed for
extensivity (§13.5) is added in a later module. -/
structure System where
  /-- Terminological identity of the system/object (mirrors the OML `id`). -/
  id : String
deriving DecidableEq, Repr

/-- **§3.3 Note 6** — 'object' is given as a synonym of 'system'. We keep the
synonym so that the *instance* layer can read as "characterizes an object". -/
abbrev Object := System

/-! ## What an object type has to supply

`System` above is the **nominal** object type: an object *is* its terminological identity,
so naming one and telling two apart are the same act. That is the right reading for a
sample, an instrument, a rover — and it is not the only reading a host library offers. A
particle of a mechanical system, a cell of a mesh, a pixel of a scene are objects whose
identity is a *position in a structure*, with no name stored anywhere.

The instance layer (`IndividualQuantity`) is therefore parameterized over the object type,
and the parameterization splits its obligations in two:

  * **discrimination** — telling two objects apart. Every type in Lean already does this,
    definitionally, which is why the object *gate* needs no class and costs nothing to
    carry to a foreign object type.
  * **designation** — naming an object in the terminological vocabulary, which is what
    `IndividualProperty` (Ch. 3) consumes. This is *not* free, and `Designated` below is
    where an object type supplies it. (The §20 dedicated kind consumes the object's
    *sort*, not its name — that half is `Sorted`'s.)

The nominal type supplies both; a structural one supplies only the first, and honestly
saying so is the point of separating them. -/

/-- **An object type with terminological identity.** A map from the object type into the
nominal `Object`, so an individual property can name the object it characterizes (§3.3)
whatever the object type is.

The injectivity field is the whole content of the class. Without it, an author facing a
structural object type — physlib's particles, a mesh cell — can always satisfy the class by
sending every object to one constant name, and the resulting designation is *worse than
none*: it type-checks, it renders, and it silently reports two distinct objects as the same
system. With it, a type whose objects carry no identity simply has no instance, which is
the true answer and is the one a reader should get. -/
class Designated (O : Type u) where
  /-- The nominal designation of an object. -/
  designation : O → Object
  /-- **Distinct objects are distinctly named.** A designation that collapses two objects
  is not a designation; this is what makes the instance a claim rather than a formality. -/
  designation_inj : ∀ {x y : O}, designation x = designation y → x = y

/-- **The nominal object type designates itself** — the existing API is the instance, and
`Object` is one inhabitant of the parameterization rather than the only object type there
is. Injectivity is reflexivity: for a nominal object, the name *is* the identity. -/
instance : Designated Object where
  designation o := o
  designation_inj h := h

/-- **§20 sort of system** — the *sort* an object belongs to, as distinct from the object
itself: *plasma* as against this plasma sample, *rover* as against rover 1, *point-particle
system* as against this system of five particles. Dybkær's dedicated kind-of-property is
defined over exactly this — "kind-of-property with given **sort of** system and any pertinent
component" — and the neo-Aristotelian reading says why the distinction earns a carrier of its
own: what parts a whole has, how they unify, and which of its quantities aggregate are facts
about the *sort*, not about the individual. The mereological registry (`Composite.Assembles`)
is keyed by it for that reason: volume aggregates over the parts of a rigid assembly and
contracts over the parts of a mixture, and a registry keyed by the kind-of-property alone
cannot say so.

Specified abstractly by identity, exactly as `System` is — the two are the same shape at two
ontological levels. In Lowe's four-category ontology (*The Four-Category Ontology*, 2005,
Fig. 7.1) the correspondence is exact: `SortOfSystem` is the **substantial universal**, his
*Kinds* corner, and `System` the **substantial particular**, his *Substances*. The other
column of the square is `KindOfProperty` (his *Attributes*) over `IndividualQuantity` (his
*Modes*), and the calculus carries the square's edges as well as its corners: `Sorted.sortOf`
below is the left *instantiated by* edge, and the other three edges live where the corners
they join are defined (`IndividualQuantity`, `DedicatedKind`).

The sort is also what answers a question the mereology cannot. A decomposition of a system
makes a whole out of parts without settling how many entities that whole *is*; the count
comes with the sortal, under whose "individuation principle" — Marmodoro, *Whole, but not
One* (2018), §4, whence "[e]very science individuates its own individual subjects or
substances" — a plurality is one thing of a kind. `SortOfSystem` is where a model states its
own such principle, and `Composite` (with `Assembles`) is where the statement does work. -/
structure SortOfSystem where
  /-- Terminological identity of the sort. -/
  id : String
deriving DecidableEq, Repr

/-- **An object type whose objects know their sort** — the instantiation arrow from the
particular to its universal, Lowe's left edge (*Kinds* instantiated by *Substances*,
Fig. 7.1): every object of `O` is of some sort, and `sortOf` says which.

A class, but never derived: what sort a model's objects instantiate is the model's claim, made
once. There is deliberately no blanket instance for `Object` — a nominal identity string does
not know its sort, and guessing one is how *rover 1* and *the rover fleet* end up interchangeable. -/
class Sorted (O : Type u) where
  /-- The sort each object instantiates. -/
  sortOf : O → SortOfSystem

/-! ### Composing object types

Object types compose the way types compose, and the calculus needs nothing per shape: a
composite object type, a pair of object types, an index family are all ordinary type
formations, and the *gate* on each of them is the definitional equality their terms already
have. What does not come free is designation, and these are the two combinators that carry
it — one general, one for the shape where the general one is hardest to satisfy.

Neither is an `instance`. Designating a derived object type is a terminological commitment
(which name does the assembly answer to? how are two names joined into one?), and instance
search guessing it is precisely the failure mode `designation_inj` exists to prevent. -/

/-- **Designation travels along an injection.** An object type that injects into a designated
one is designated: name each object by the name of its image. This is the composition
principle for the whole census of object shapes — an index family, a structural object with a
key, a sub-selection of a named set — and it is the only one most cases need.

The injectivity hypothesis is the *author's* claim about `f`, and for a concrete finite object
type it is discharged by `decide`. -/
@[instance_reducible]
def Designated.ofInjective {O : Type u} {P : Type v} [Designated P] (f : O → P)
    (hf : ∀ {x y : O}, f x = f y → x = y) : Designated O where
  designation o := Designated.designation (f o)
  designation_inj h := hf (Designated.designation_inj h)

/-- **Designating a joint object** — a quantity that characterizes an ordered *pair* of
objects (a flow, a transfer, a torque across a coupling) needs the two names joined into one,
and `join` is that choice.

The library states the obligation and does not make the choice, for a reason the exhibits
check: the encoding an author reaches for first — concatenate with a separator — is **not**
injective, because the separator can occur inside a name, and the resulting designation
reports two different couplings as one system. A `join` over a *concrete* finite object type
discharges `hjoin` by `decide`; over arbitrary names it needs an escaping convention, which is
the author's to pick and to prove. -/
@[instance_reducible]
def Designated.prod {O₁ : Type u} {O₂ : Type v} [Designated O₁] [Designated O₂]
    (join : Object → Object → Object)
    (hjoin : ∀ {a b c d : Object}, join a b = join c d → a = c ∧ b = d) :
    Designated (O₁ × O₂) where
  designation x := join (Designated.designation x.1) (Designated.designation x.2)
  designation_inj {x y} h := by
    obtain ⟨h₁, h₂⟩ := hjoin h
    cases x; cases y
    simp only [Prod.mk.injEq]
    exact ⟨Designated.designation_inj h₁, Designated.designation_inj h₂⟩

end PropertyKindCalculus

end -- pkc-blanket-expose
end -- pkc-blanket
