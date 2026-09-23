import Verso
import VersoManual
import VersoBlueprint
-- The nodes below link real declarations, so this chapter imports the core layer it
-- documents: `System`, `SortOfSystem`, `IndividualQuantity`, `Designated`,
-- `Decomposition`, and the `Part`/`Whole` roles.
import PropertyKindCalculus
-- The foundation cites Dybkær, Lowe, Simons, Heil, and Marmodoro, so the chapter
-- imports the blueprint's `References`.
import PropertyKindCalculusBlueprint.References

open Verso.Genre
open Verso.Genre.Manual
open Informal

#doc (Manual) "Foundations: system, part, and the ontological square" =>
%%%
tag := "foundations"
%%%

PKC's foundation is a combination of two sources. Dybkær's ontology on property
{Manual.citep dybkaer_ontology_on_property}[] supplies the metrological content — system,
component, property, kind-of-property, scale, examination — and the discipline that every
construct be a terminological commitment a model states rather than a convention a reader
infers. Lowe's four-category ontology {Manual.citep lowe_four_category_ontology}[]
supplies the categorial frame: which of those constructs is a universal and which a
particular, and along which relations they meet. The combination is load-bearing, and
this chapter says where: Dybkær's text runs part–whole structure at two levels, in two
vocabularies, without ever relating them, and the square is what relates them. A kind is
ultimately a kind *of* some system — in the universal or the particular sense — and which
sense a construct consumes decides what may be summed, what may be counted, and what a
whole even is. Those decisions are made here, before the first aggregate, rather than
discovered mid-proof.

# The mereology Dybkær implies

The word _mereology_ does not occur in Dybkær's text. The structure does, at two levels,
and the levels never meet.

At the level of *concepts*, the vehicle is the _partitive relation_ that ISO 704 and
ISO 1087-1 provide and Fig. 2.1 (item 2) sets in notation: a _comprehensive concept_
over its _partitive concepts_, beside the generic and associative relations. Dybkær puts
it to work as a relation among universals. The quantity taxonomy itself is drawn with
partitive rather than generic edges (Fig. 6.9); the representation of a unitary quantity
value has the numerical value and the metrological unit as coordinate concepts in
partitive relation to it (Fig. 9.25); a property-value scale stands in partitive
relation to ⟨property value⟩ (§11.8). And he *rules* with it: ⟨property⟩ over
⟨property value⟩ cannot be comprehensive-over-partitive, because a property value is not
a detachable piece of a property (§9.13.2).

At the level of *systems*, the vocabulary is plain part-talk, and it is load-bearing
from the opening of Chapter 3. ⟨system⟩ was adopted "to accommodate any partition into
components" (§3.2, where Bunge is quoted: "there are no simple structureless entities").
The definition itself is mereological — a system is a "demarcated arrangement of a set
of elements and a set of relationships or processes between these elements" (§3.3), an
element being "any definable part except a relationship or a process" (§3.3 Note 3) —
and its worked examples are a six-deep chain of parts: a human being, the blood of that
human being, the leukocytes of that blood, a single leukocyte among them, the DNA of
that leukocyte, a given gene in that DNA. ⟨component⟩ is then defined as "part of a
system" outright (§3.4), with the complementary part — the chemist's _matrix_ — named
beside it (§3.4 Note 2), and the improper case, system and component "designated
identically", admitted (§3.4 Note 3). Fig. 3.5 splits ⟨object⟩ into composite and
non-composite. The relation even carries definitional weight one level up: the minimal
definition of ⟨property⟩ — "inherent feature of a system" — is available exactly because
"a relevant component is a part of a system and therefore might not need special
mention" (§5.5.1).

Two further facts fix how these two levels must be read, and both are Dybkær's own.
First, they are genuinely two: the partitive relation holds between concepts —
universals — while a component is part of a particular system, and nothing in the text
identifies the two relations or maps one onto the other. Second, at the one point where
the levels could have been collapsed, he refuses. Asked whether ⟨object⟩ stands in a
partitive relation to its properties — whether properties are the parts objects are made
of — §2.23.3 answers that "the description of a biological object by a set of all its
properties hardly means that a duplicate instance can be created by putting the
properties together", and the object–property relation is fixed as associative (§3.1,
Fig. 2.25). That is a refusal of the bundle theory in one sentence: properties
*characterize* objects, they do not *compose* them. What is needed, then, is a frame
that keeps properties and their bearers in distinct categories related by
characterization rather than parthood, distinguishes universals from particulars on both
sides, and leaves room for a part–whole relation among the particulars and another among
the universals without confusing either with instantiation. That frame exists, and it is
Lowe's.

# The ontological square

:::group "foundations_square"
The four corners of Lowe's square, as the calculus carries them: the system (substantial
particular), its sort (substantial universal), the kind-of-property (non-substantial
universal, from the spine), and the individual quantity (mode). The identity discipline
`Designated` is what makes naming a corner a claim.
:::

:::definition "def_system" (parent := "foundations_square") (lean := "PropertyKindCalculus.System")
A _system_ (Dybkær §3.3) is a demarcated arrangement of elements and their
relationships; _object_ (§3.3 Note 6) is given as a synonym. Specified abstractly by
identity: what parts a system has is deliberately not a field, because Dybkær's own
Note 5 makes the parts observer-relative — "the extent and structure of a system is
essentially defined by the observer for some purpose" — so parthood arrives as a
_carving_, below, rather than as stored structure.
:::

:::proof "def_system"
A one-field `structure` with `DecidableEq`; nothing to prove. The synonym
`Object := System` keeps the instance layer reading as "characterizes an
object".
:::

:::definition "def_sortOfSystem" (parent := "foundations_square") (lean := "PropertyKindCalculus.SortOfSystem")
The _sort of system_ — the substantial *universal* as against the substantial
*particular*: _plasma_ as against this sample, _rover_ as against rover 1. Dybkær's
dedicated kind-of-property is defined over exactly this — "kind-of-property with given
*sort of* system and any pertinent component" (Ch. 20, quoted from the source's own
definition) — and the mereological registry is keyed by it, because how parts unify into
a whole is dictated by the sort of the whole.
:::

:::proof "def_sortOfSystem"
A one-field structure with `DecidableEq`, mirroring the {uses "def_system"}[system] carrier one ontological level up. `Sorted O` is the instantiation arrow from an object type to its sorts (`sortOf : O → SortOfSystem`), declared per model and never derived. With these, the calculus carries all four corners of Lowe's ontological square (the correspondence is spelled out edge by edge below) — of which three were already present and the fourth was being played, by convention, by the particular. `DedicatedKind.sort` stores exactly what the quoted definition asks for, and `dedicatedFor` closes the square: dedicating a kind through an object contributes the object's sort, so two objects of one sort instantiate one catalogue entry while their quantities stay apart by type.
:::

:::definition "def_individualQuantity" (parent := "foundations_square") (lean := "PropertyKindCalculus.IndividualQuantity")
An _individual quantity_ is a magnitude of a {uses "def_kindOfProperty"}[kind-of-property] that _characterizes an object_ (Ch. 3), with the object carried in the type alongside the kind. Its object is drawn from an arbitrary type, so a nominal {uses "def_system"}[system] and a host library's own structural object are both admissible indices — the census of admissible shapes is the object-type chapter's subject.
:::

:::proof "def_individualQuantity"
A one-field structure `IndividualQuantity {O : Type u} (o : O) (k : KindOfProperty) (R : Type)`. `add` is gated on the object, the kind, and a `DifferenceKind` scale witness; `mul`, `div` and `recip` on the object and a kind law. None of these reads `o`, which is why the generalization from `Object` to an arbitrary `O` changed no proof.
:::

:::definition "def_designated" (parent := "foundations_square") (lean := "PropertyKindCalculus.Designated")
A _designated_ object type carries a map into the nominal {uses "def_system"}[system] type, injectively, so an individual quantity of such an object can name it. The nominal type designates itself; a type whose objects are positions in a structure has no instance.
:::

:::proof "def_designated"
A two-field class: `designation : O → Object` and `designation_inj`. The injectivity field is the whole content. Without it, any object type is satisfiable by the constant map, and the resulting designation reports two distinct objects as one system — silently, wherever it is rendered. With it, the absence of an instance is a true report about the type.
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
edge — kinds characterized by attributes — is the dedicated kind (the dedicated-kinds
chapter), refined by Dybkær's pertinent component, a refinement the square itself does not
carry.

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

# The carving — mereology as data, wholes by sortal

With the square in place, the two levels of Dybkær's implied mereology get one carrier
each, and the flexibility both sources demand is a theorem-shaped commitment rather than
a mood. Marmodoro's distinction says why flexibility is forced: "physical structure
unites; while metaphysical structure unifies. The former brings about wholes, the latter
unities. But wholes are not always unities" — and a physical structure is "numberless",
bringing no count principle with it: "Alternative carvings of the world deliver
alternative numbers of entities" {Manual.citep marmodoro_whole_but_not_one}[].
The particular-side mereology is therefore *data*, quantified over: a carving of a
system, never the carving. Unification — being one whole of a sort, with a license to
aggregate — is a separate act, supplied when a model declares a sort and instantiates
a composite (the object-type chapter),
"under the individuation principle of the sortal"; Dybkær's _sort of system_ is that
sortal under another name. The host library this work targets confirms the design from
the other side: its rigid body is a single mass functional whose parts occur only as
bound points inside integrands, so a foundation that made the parts of a system a stored
fact would misdescribe the very objects it aims at.

:::group "foundations_carving"
The particular-side mereology as data: the carving (a description of a whole into
parts, one among many) and the part/whole roles a single portion-total pair carries.
:::

:::definition "def_decomposition" (parent := "foundations_carving") (lean := "PropertyKindCalculus.Decomposition")
A _carving_ of a whole into parts drawn from an arbitrary type — a
{uses "def_system"}[system]'s subsystems, a host library's own particles — as a binary
tree of joins. Deliberately not a census: nothing in a carving claims the parts are
disjoint, exhaustive, or all there are, and nothing fixes how many parts a system has.
It is Dybkær's §3.2 "partition into components" with §3.3 Note 5's observer-relativity
taken at face value: the carving is the observer's act, so every law that consumes one
is quantified over all of them.
:::

:::proof "def_decomposition"
A two-constructor inductive `Decomposition O` — `atom` and `union` — with `fold` as its
one eliminator, realized in the Mathlib-free core as the `Mereology` module, which
imports nothing at all: the carving is pure structure, and the laws that consume it
(the `Extensivity` module) import it rather than housing it. The abstinence is
load-bearing: `coalesce_count_ne` and
`count_sortal_ne` (the extensivity chapter) prove that a part count is not a function of
the whole, which is exactly what a carving-as-census would wrongly supply.
:::

:::definition "def_partWhole" (parent := "foundations_carving") (lean := "PropertyKindCalculus.Part")
_Part and whole as roles._ A portion of a thing is a quantity of the *same*
{uses "def_kindOfProperty"}[kind] as the thing — which is what leaves an interface
taking a portion and its total open to a silent argument swap. `Part k R` and
`Whole k R` put the two mereological roles into the type; `Part.WithinWhole` — the
portion does not exceed its total — is the only relation between them, stated with the
part on the left, where the mereology puts it, so the reversed reading is unwritable
rather than merely wrong. Dybkær's improper case (§3.4 Note 3, system and component
"designated identically") is the pair wrapping one quantity.
:::

:::proof "def_partWhole"
One-field role wrappers over `Quantity k R`, with `castCarrier` on each so a pair born
as counts crosses to a float carrier in its roles. The eliminator `Part.fractionOf`
writes the portion-over-total division once, in the only order the roles admit, and its
result is deliberately a *different* kind, licensed by a quotient kind-law — dividing a
portion by its total is what mints the "fraction of total" role. The roles claim no
partition: exhaustiveness and disjointness are further commitments, and the kernels this
serves do not make them.
:::

Where the foundation does work downstream: the extensivity chapter states Dybkær's
§13.5 aggregation modes as laws quantified over all carvings; the object-type chapter
adds the whole a carving cannot supply (`Composite`, one sort at a time) and keys the
license to aggregate by that sort (`Assembles`); the dedicated-kinds chapter consumes
the sort as Dybkær's Ch. 20 asks; and the count — the SI's "count of a specified
elementary entity" — is keyed by a sortal, because the refutations above leave it
nowhere else to live.
