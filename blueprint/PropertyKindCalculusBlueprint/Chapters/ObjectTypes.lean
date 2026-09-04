import Verso
import VersoManual
import VersoBlueprint
-- The nodes below link real declarations, so this chapter imports the object layer it
-- documents: the core (`Designated`, `IndividualQuantity`, `Composite`) and the Mathlib-tier
-- assembly over a finite index.
import PropertyKindCalculus
import PropertyKindCalculus.CompositeReal
-- The four-category correspondence below cites Lowe, so the chapter imports the
-- blueprint's `References`.
import PropertyKindCalculusBlueprint.References

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
Dybkær's instance layer consumes, and it is not free. It is supplied by
`Designated`, and an object type that has no identity of its own has no instance.
(The Chapter 20 dedicated kind consumes the object's _sort_, not its name — that
half is `Sorted`'s.)

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

# The generality of the paradigm

It is tempting to read the census as a taxonomy the calculus provides — six kinds of object,
pick one. It is the opposite. *PKC contributes no taxonomy of objects; it contributes the fact
that it needs none.*

What a metrology layer must have of an object is discrimination, and discrimination is what a
type *is*. So every entry in the census is either a type the host library already has
(nominal, structural, indexed, singleton) or an ordinary type former applied to such types
(composite, joint) — and the *gate* on all of them is definitional equality, which comes with
the type and costs nothing to carry.

That is why the shapes compose without any provision being made for it. A quantity of *this
instrument*, at *this pixel*, of *that particle* is a quantity of the triple
`Object × Cell × Particle`, and its gate is the triple's own equality: differ in any one
factor and the sum is refused. Nothing in the library knows that this combination exists.

## What the library ships, and what it refuses to ship

Exactly two things do not come from the type former:

_The one object type a host cannot have._ A whole is not one of its parts, so a part type
does not contain the assembly, so the total has nowhere to live. The _composite_ is that type, and it is the only object *construction* this library ships.

_Closure of designation._ Naming a derived object is a terminological commitment, not a
derivation, and the library states the obligation instead of guessing the convention. The
composition principle is that a designation travels along an injection; the injectivity is
the author's claim, `decide` for a finite object type and a lemma otherwise.

The refusal is the substantive half. An automatic designation for pairs would have to join two
names into one, and the encoding an author reaches for first — concatenate with a separator —
is not injective, because the separator can occur inside a name. Two different couplings, one
name, silently. The `Examples` library carries that counterexample as a compiled fact; it is
the reason `Designated` carries an injectivity field rather than a docstring.

:::definition "def_designatedOfInjective" (parent := "object_types") (lean := "PropertyKindCalculus.Designated.ofInjective")
_Designation travels along an injection._ An object type that injects into a {uses "def_designated"}[designated] one is designated: name each object by the name of its image. This is the composition principle for the whole census — an index family, a combination of factors, a sub-selection of a named set — and the only one most models need.
:::

:::proof "def_designatedOfInjective"
Compose the two maps and the two injectivity proofs. A *definition*, not an instance: which naming a model uses is the model's decision, and instance search finding one by accident is the failure `designation_inj` exists to prevent. `Designated.prod` is its specialization to a pair, taking the join of two names and the proof that the join is injective.
:::

# Operations the object index changes

Two operations look ordinary until the object is in the type, and then say something they
could not say before.

:::definition "def_smulK" (parent := "object_types") (lean := "PropertyKindCalculus.IndividualQuantity.smulK")
_The kind-licensed scalar action._ A scalar quantity of an object scaling a vector quantity *of the same object*, licensed by the same product law the homogeneous product takes. `p = m·v` and `F = m·a` have this shape, and the homogeneous product cannot express them: it wants one carrier for both operands, and here one side is a number and the other a numerical vector.
:::

:::proof "def_smulK"
The carrier's own `SMul` on the magnitudes, with `ScalarCarrier` demanded of the *acting* side — a vector carrier is deliberately not a `ScalarCarrier`, so this cannot be misread as a componentwise product of two vectors. The object gate is as much the point as the kind law: one particle's mass scaling another's acceleration is exactly the substitution an object-blind model has no way to refuse, and it is the shape of an ordinary copy-paste error. Without this operation an application has to mint an unlicensed action and attest it at the interface tier, which is where the kind stops being checked.
:::

:::definition "def_transpose" (parent := "object_types") (lean := "PropertyKindCalculus.IndividualQuantity.transpose")
_The transpose of a joint quantity._ The same magnitude, read as a quantity of the reversed pair — the equal-and-opposite reading, and the *only* re-indexing of an individual quantity the library offers. Its value is that a law becomes a type: a "reverse" that negates a magnitude and forgets to exchange the endpoints has the untransposed type and does not elaborate where a reversed quantity is expected.
:::

:::proof "def_transpose"
The magnitude, at the swapped index; the involution is `rfl`. There is deliberately no general re-indexing: moving a magnitude from one object to another is what the object index exists to prevent, and an operation that did it on request would return the layer to a naming convention. The transpose is safe because it is not a move — `(a, b)` and `(b, a)` are one coupling read from its two ends, and which end is the source is the content of a law like Newton's third.
:::

# Assembly over a composite

Gating on the object refuses a sum across two objects, which is what it is for — and
it refuses, with equal correctness, the _total_ mass of an assembly, because the total
characterizes an object the part type does not contain. Aggregation therefore needs an
eliminator, and the eliminator is where the §13.5 license enters.

:::definition "def_sortOfSystem" (parent := "object_types") (lean := "PropertyKindCalculus.SortOfSystem")
The _sort of system_ — the substantial *universal* as against the substantial *particular*: _plasma_ as against this sample, _rover_ as against rover 1. Dybkær's dedicated kind-of-property is defined over exactly this — "kind-of-property with given *sort of* system and any pertinent component" (Ch. 20, quoted from the source's own definition) — and the mereological registry is keyed by it, because how parts unify into a whole is dictated by the sort of the whole.
:::

:::proof "def_sortOfSystem"
A one-field structure with `DecidableEq`, mirroring the {uses "def_system"}[system] carrier one ontological level up. `Sorted O` is the instantiation arrow from an object type to its sorts (`sortOf : O → SortOfSystem`), declared per model and never derived. With these, the calculus carries all four corners of Lowe's ontological square (the four-category analysis; the correspondence is spelled out edge by edge below) — of which three were already present and the fourth was being played, by convention, by the particular. `DedicatedKind.sort` stores exactly what the quoted definition asks for, and `dedicatedFor` closes the square: dedicating a kind through an object contributes the object's sort, so two objects of one sort instantiate one catalogue entry while their quantities stay apart by type.
:::

The correspondence with Lowe's four-category ontology
({Manual.citep lowe_four_category_ontology}[], Fig. 7.1 — the ontological square) is
worth stating edge by edge, because the calculus
carries the *relations* of the square and not only its corners. The corners: `SortOfSystem`
is his _Kinds_ (the substantial universal), the object index his _Substances_ (the
substantial particular), `KindOfProperty` his _Attributes_ (the non-substantial universal),
`IndividualQuantity` his _Modes_. The edges: `Sorted.sortOf` is the left _instantiated by_
edge — substances instantiate kinds. The right _instantiated by_ edge — modes instantiate
attributes — is the kind index of an individual quantity, and the bottom _characterized by_
edge — substances characterized by modes — is its object index: both edges into the mode
are *type indices*, which is exactly why they gate arithmetic. The top _characterized by_
edge — kinds characterized by attributes — is the dedicated kind, refined by Dybkær's
pertinent component, a refinement the square itself does not carry.

The diagonal is a structural agreement rather than a construct. Lowe's _exemplified by_ —
a substance exemplifying an attribute — is derivative for him, factoring through either
path around the square, and the calculus likewise has no primitive object-to-kind-of-property
construct: the dispositional route (up the left edge, then across the top) is
`dedicatedFor`, and the occurrent route (across the bottom, then up the right) is an
inhabitant of `IndividualQuantity o k R`. The reading is not idiosyncratic: surveying the
square's grounding relations, Simons states the occurrent half as a definition — an object
exemplifies an attribute "when a mode which instantiates an attribute characterizes an
object" — and counts exemplification "definable in terms of instantiation, characterization,
and some logic" {Manual.citep simons_basis_of_categorial_distinctions}[]. Where the
calculus narrows Lowe: the attributes here are kinds-of-property specifically — quantitative
attributes carrying a scale and an examination — not attributes at large.

One stance the implementation takes silently is worth making explicit. The calculus's
universals are catalogue *entries*: a `SortOfSystem` and a `KindOfProperty` are data,
declared by a model, and a sort no object instantiates is idle data rather than a Platonic
surplus. That is the immanentist reading Lowe himself settled on — universals as
"abstractions from, or invariants across, particulars", incapable of existing
uninstantiated (Lowe 2012, quoted in Heil
{Manual.citep heil_existents_and_universals}[]) — and it is the only reading a
terminological ontology in Dybkær's style needs.

A second correspondence runs alongside Lowe's and settles a different question: not what
the four categories are, but why a whole needs a sort at all. Marmodoro distinguishes two
kinds of structure — "physical structure unites; while metaphysical structure unifies. The
former brings about wholes, the latter unities. But wholes are not always unities"
{Manual.citep marmodoro_whole_but_not_one}[]. The extensivity layer is the first of those:
a decomposition unites parts into a whole and, being one carving among many, brings no
count principle with it. The second is what a model supplies when it declares a sort and
instantiates a composite — unification "under the individuation principle of the sortal",
and Dybkær's _sort of system_ is that sortal under another name. Three decisions of this
chapter follow from taking the distinction seriously. The whole is _added_ rather than
derived, because no carving yields it. The same parts under two sorts are two object types
with two sets of licenses, because the statue and the lump are two wholes. And the license
is indexed by the sort rather than by the kind alone, because how parts make a whole is
settled by what the whole is — the one claim the parts cannot make on their own behalf.
Her further distinction between structural and substantial powers lands in the extensivity
chapter, where a whole-proper kind is one no aggregation produces.

:::definition "def_composite" (parent := "object_types") (lean := "PropertyKindCalculus.Composite")
The _composite_ object type over a part type, *as a {uses "def_sortOfSystem"}[sort] of whole*: the whole, or one of its parts. The whole and the parts must inhabit one type or their quantities cannot be related at all; the whole is a distinct term from every part, so a whole-assembly quantity and a part quantity do not combine. The sort index is what lets two wholes stand over one part type — the statue and the lump over the same clay — and their quantities do not combine either, because the types differ. Extensionality about objects is not assumed.
:::

:::proof "def_composite"
A two-constructor inductive with `DecidableEq` and `Repr`, indexed by the sort and the part type. Naming a composite is a definition rather than an instance, taking the whole's name and the proof that no part already answers to it — a terminological commitment instance search has no business guessing.
:::

:::definition "def_assembles" (parent := "object_types") (lean := "PropertyKindCalculus.Assembles")
The _assembly license_, keyed by the {uses "def_sortOfSystem"}[sort of the whole] and the kind: which kinds' part quantities may be summed into a quantity of *that sort of* whole. Registration is opt-in, and the entry carries the same scale gate addition demands, so a nominal or ordinal kind cannot be licensed at all.
:::

:::proof "def_assembles"
A `Prop`-valued class with one field, a `DifferenceKind` witness. The sort index is forced by the library's own counterexample: volume aggregates over the parts of a rigid assembly and contracts over the parts of a mixture (`mixing_subadditive`), and both facts are facts about volume — a registry keyed by the kind alone must either license the mixture or refuse the assembly, and either answer is wrong. The validation suite carries both verdicts side by side, each backed by its witness: an `Extensive` measurement for the rigid sort, the ethanol/water contraction for the mixture.
:::

:::definition "def_assemble" (parent := "object_types") (lean := "PropertyKindCalculus.assemble")
_Assembly_: the quantity of the whole, folded from the quantities of the parts over a {uses "def_extensiveKind"}[decomposition]. The whole and the part injection are arguments rather than fixed, so the eliminator serves a {uses "def_composite"}[composite] and equally a host library's own object type with its own naming of parts. Its part function is dependent — the quantity supplied for a part must characterize _that_ part — which is the gate.
:::

:::proof "def_assemble"
`Decomposition.fold` of the parts' magnitudes under `Carrier.add`: the same traversal `leafSum` uses, so the quantity-level arithmetic and the §13.5 law are one recursion read at two carriers. The counterpart over a finite index (`assembleOver`, `assembleAll`) sums a `Finset` instead, which is the shape a host library's own aggregate is written in — a `Finset.sum`, recovered by `rfl` rather than by a rewriting lemma.
:::

:::theorem "thm_assemble_ne_measured" (parent := "object_types") (lean := "PropertyKindCalculus.assemble_ne_measured") (tags := "proved") (effort := "small")
_The license refused._ For a whole-proper kind — one whose value the parts do not determine, in either of the two ways they could — there is a carving on which the assembled magnitude is _not_ the value the whole has. Not merely unjustified: wrong, on an exhibited pair of parts. Uses {uses "def_assemble"}[assembly].
:::

:::proof "thm_assemble_ne_measured"
The `Assembles` instance is still required, and that is the finding: the class licenses the sum to be _written_, and nothing about writing it makes it true, so an author who registers a whole-proper kind gets a term that elaborates and a number that is not the physics. The witness's own non-additive pair supplies the carving; the negative twin of `assemble_eq_measured`, same eliminator and same measurement, with the extensivity hypothesis replaced by its refutation. This is why the registry is opt-in and curated per sort rather than derived.
:::

## Two sums, and only the object tells them apart

A sum of quantities appears in applied models in two shapes that are identical on the page.

A _resultant_ combines several quantities *of one object and one kind* into one of the same
object and kind: the forces acting on a particle, the currents into a node. Nothing about the
object changes, so nothing beyond the scale gate addition already demands is needed.

An _assembly_ combines the quantities of the *parts* into a quantity of the *whole*. The
object changes, and whether that is meaningful at all is a fact about the kind — which is what
the _license_ records.

Summing the particles' velocities is refused because it is an assembly of an unlicensed kind.
Summing the forces on one particle must not be refused, because it is not an assembly. A layer
that indexes quantities only by kind writes both with the same `∑` at the same type and can
refuse neither; this is the clearest single thing the object index buys, and the
`PointParticle` case study scores four designs on exactly it.

:::theorem "thm_assemble_eq_measured" (parent := "object_types") (lean := "PropertyKindCalculus.assemble_eq_measured") (tags := "capstone, proved") (effort := "medium")
*The license, cashed.* For a kind that is genuinely {uses "def_extensiveKind"}[extensive] under a measurement, the assembled magnitude over any decomposition *is* the value that measurement reports for the whole. This is what makes the license a claim about the world rather than a permission slip: the class licenses the sum to be written, and this theorem is what shows the sum is right. Volume on mixing has no `Extensive` witness, so it has no instance of this.
:::

:::proof "thm_assemble_eq_measured"
`extensive_additive` applied to the decomposition, symmetrized: the assembled magnitude is `leafSum` by definitional unfolding of the shared fold, and `leafSum` is the whole's measured numeral by the aggregation capstone.
:::
