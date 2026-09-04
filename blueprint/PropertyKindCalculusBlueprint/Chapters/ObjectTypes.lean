import Verso
import VersoManual
import VersoBlueprint
-- The nodes below link real declarations, so this chapter imports the object layer it
-- documents: the core (`Designated`, `IndividualQuantity`, `Composite`) and the Mathlib-tier
-- assembly over a finite index.
import PropertyKindCalculus
import PropertyKindCalculus.CompositeReal

open Verso.Genre
open Verso.Genre.Manual
open Informal

#doc (Manual) "The object type" =>

A measured quantity is always the property of some object — the length of _this_
pencil, the glucose concentration of _this_ plasma sample — and R19 puts that object
in the type. What kind of thing an object may _be_ is a separate question, and this
chapter is its answer: the object is drawn from an arbitrary type, and the
consequences of that decision are not symmetric.

Two things are wanted of an object, and they turn out to have different prices.

_Discrimination_ — telling two objects apart — is what the gate needs, and it is
free. It is definitional equality of a type index, a mechanism every type in Lean
already has. The evidence is a measurement of the instance layer itself: of the
declarations in `IndividualQuantity`, *exactly one reads its object*. `add`,
`mul`, `div`, `recip` and all three classification certificates carry `o` and never
inspect it. What stops a length of `R1` multiplying a width of `R2` is that the two
types differ, and nothing else.

_Designation_ — naming an object in the terminological vocabulary — is what
Dybkær's instance layer and the Chapter 20 dedicated kind consume, and it is not
free. It is supplied by `Designated`, and an object type that has no identity of its
own has no instance.

The asymmetry is the point. A host library's own objects — the particles of a
mechanical system, the cells of a mesh, the pixels of a scene — can be _gated_ with
nothing supplied, on their own types, without that library changing. They cannot be
_named_, and the layer says so rather than inventing a name that is not there.

# What an object type supplies

:::group "object_types"
The object of an individual quantity ranges over an arbitrary type. The gate needs
nothing from it; the designation needs `Designated`, whose injectivity field is what
distinguishes a designation from a formality.
:::

:::definition "def_individualQuantity" (parent := "object_types") (lean := "PropertyKindCalculus.IndividualQuantity")
An _individual quantity_ is a magnitude of a {uses "def_kindOfProperty"}[kind-of-property] that _characterizes an object_ (Ch. 3), with the object carried in the type alongside the kind. Its object is drawn from an arbitrary type, so a nominal {uses "def_system"}[system] and a host library's own structural object are both admissible indices.
:::

:::proof "def_individualQuantity"
A one-field structure `IndividualQuantity {O : Type u} (o : O) (k : KindOfProperty) (R : Type)`. `add` is gated on the object, the kind, and a `DifferenceKind` scale witness; `mul`, `div` and `recip` on the object and a kind law. None of these reads `o`, which is why the generalization from `Object` to an arbitrary `O` changed no proof.
:::

:::definition "def_designated" (parent := "object_types") (lean := "PropertyKindCalculus.Designated")
A _designated_ object type carries a map into the nominal {uses "def_system"}[system] type, injectively, so an individual quantity of such an object can name it. The nominal type designates itself; a type whose objects are positions in a structure has no instance.
:::

:::proof "def_designated"
A two-field class: `designation : O → Object` and `designation_inj`. The injectivity field is the whole content. Without it, any object type is satisfiable by the constant map, and the resulting designation reports two distinct objects as one system — silently, wherever it is rendered. With it, the absence of an instance is a true report about the type.
:::

# The census of object types

The useful distinction is not between objects this calculus defines and objects a
host library defines. It is how an object carries its identity, crossed with whether
its type is primitive or derived from another. Six shapes arise, and each is
exhibited — acceptances as `example`, refusals as `#check_failure` — in the
`MiniObjectTypes` module of the `Examples` library.

_Nominal._ Identity *is* the name: `System`, a terminological id and nothing else.
Naming and telling apart are one act, so both questions are answered at once. This is
the reading the layer shipped with, and the right one for a sample, an instrument, a
rover.

_Structural._ Identity is a *position*: a particle of a mechanical system, a cell of
a mesh. Gated for free — the exhibit states this at an arbitrary type variable, about
which nothing whatever is assumed — and not designatable, because there is no name
anywhere to designate with.

_Indexed._ The position *determines* a name: a pixel, a spectral band, a layer.
Between the two — gated like a structural object, designatable like a nominal one, with
the injectivity discharged rather than assumed.

_Composite._ Derived: the parts of an assembly *and the whole they compose*, in one
type. The construct aggregation needs, below.

_Joint._ Derived: an ordered pair, for a quantity that characterizes a *coupling*
rather than a system — a flow, a transfer, a torque across an interface. The gate falls
out with nothing added, so an interface quantity is an instance of the scheme rather
than a construct of its own. Designation is where this shape instructs: the obvious
nominal encoding, concatenating the two names with a separator, is _not_ injective,
because the separator can occur inside a name. The exhibit gives the two couplings that
collide, and that counterexample is the argument for the injectivity field.

_Singleton._ One object, `Unit`. Worth naming because it bounds the cost: a model with
nothing to disambiguate pays nothing for the object layer, since there is exactly one
term to write.

A seventh shape suggests itself and is not one. An object _at a time_ — the same
apparatus examined on Tuesday — is not a new object type: the time dependence belongs
to the quantity, which is a function of time, and the difference between two occasions
is an _examination_. Whether a sample drawn at one moment is a
different system from the sample drawn at the next is a modeling decision about the
system, not something the parameterization settles.

# Assembly over a composite

Gating on the object refuses a sum across two objects, which is what it is for — and
it refuses, with equal correctness, the _total_ mass of an assembly, because the total
characterizes an object the part type does not contain. Aggregation therefore needs an
eliminator, and the eliminator is where the §13.5 license enters.

:::definition "def_composite" (parent := "object_types") (lean := "PropertyKindCalculus.Composite")
The _composite_ object type over a part type: the whole, or one of its parts. The whole and the parts must inhabit one type or their quantities cannot be related at all; the whole is a distinct term from every part, so a whole-assembly quantity and a part quantity do not combine.
:::

:::proof "def_composite"
A two-constructor inductive with `DecidableEq` and `Repr`. Naming a composite is a definition rather than an instance, taking the whole's name and the proof that no part already answers to it — a terminological commitment instance search has no business guessing.
:::

:::definition "def_assembles" (parent := "object_types") (lean := "PropertyKindCalculus.Assembles")
The _assembly license_: the kinds whose part quantities may be summed into the quantity of the whole. Registration is opt-in, so an unlicensed kind has no aggregation, and the entry carries the same scale gate addition demands, so a nominal or ordinal kind cannot be licensed at all.
:::

:::proof "def_assembles"
A `Prop`-valued class with one field, a `DifferenceKind` witness for the licensed kind. Mass and momentum are registered in the applications; angular velocity and displacement deliberately are not, and the sums that would be wrong are then not terms anyone can write.
:::

:::definition "def_assemble" (parent := "object_types") (lean := "PropertyKindCalculus.assemble")
_Assembly_: the quantity of the whole, folded from the quantities of the parts over a {uses "def_extensiveKind"}[decomposition]. The whole and the part injection are arguments rather than fixed, so the eliminator serves a {uses "def_composite"}[composite] and equally a host library's own object type with its own naming of parts. Its part function is dependent — the quantity supplied for a part must characterize _that_ part — which is the gate.
:::

:::proof "def_assemble"
`Decomposition.fold` of the parts' magnitudes under `Carrier.add`: the same traversal `leafSum` uses, so the quantity-level arithmetic and the §13.5 law are one recursion read at two carriers. The counterpart over a finite index (`assembleOver`, `assembleAll`) sums a `Finset` instead, which is the shape a host library's own aggregate is written in — a `Finset.sum`, recovered by `rfl` rather than by a rewriting lemma.
:::

:::theorem "thm_assemble_eq_measured" (parent := "object_types") (lean := "PropertyKindCalculus.assemble_eq_measured") (tags := "capstone, proved") (effort := "medium")
*The license, cashed.* For a kind that is genuinely {uses "def_extensiveKind"}[extensive] under a measurement, the assembled magnitude over any decomposition *is* the value that measurement reports for the whole. This is what makes the license a claim about the world rather than a permission slip: the class licenses the sum to be written, and this theorem is what shows the sum is right. Volume on mixing has no `Extensive` witness, so it has no instance of this.
:::

:::proof "thm_assemble_eq_measured"
`extensive_additive` applied to the decomposition, symmetrized: the assembled magnitude is `leafSum` by definitional unfolding of the shared fold, and `leafSum` is the whole's measured numeral by the aggregation capstone.
:::
