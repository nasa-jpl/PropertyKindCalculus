import Verso
import VersoManual
import VersoBlueprint
-- The extensivity nodes below now link real declarations, so this chapter imports
-- the (Mathlib-free, core) `Extensivity` module.
import PropertyKindCalculus.Extensivity
-- The carving/oneness discussion below cites Marmodoro, so the chapter imports the
-- blueprint's `References`.
import PropertyKindCalculusBlueprint.References

open Verso.Genre
open Verso.Genre.Manual
open Informal

#doc (Manual) "Extensivity" =>

Dybkær §13.5 divides kinds-of-quantity "according to physical (and arithmetic)
additivity", presenting Bunge's four types: _unconditionally extensive_ (§13.5.1, the
value for the total equals the arithmetic sum over the parts), _quasiextensive_
(§13.5.2, approximately equal — an uncertainty question, not a mereological one),
_conditionally extensive_ (§13.5.3, the addition exists but the total may differ "due
to the respective internal and environmental conditions" — volume on mixing), and
_intensive_ (§13.5.4, no physical addition, the value "invariant with the extent of a
system of constant composition"). These are quantified arithmetic laws over the
mereology of systems — again something a description logic cannot state — and they are
_realized_, sorry-free, in the Mathlib-free `Extensivity` module: the decomposition
mereology, the predicates, the two inductions that lift a single split to the whole
tree, and a checked witness for each — mass, density, and the volume-on-mixing
counterexample. One further case, which Bunge's four do not name, is added: a value the
parts do not determine at all.

# Extensive and conditionally-extensive kinds (Dybkær §13.5)

:::group "extensivity"
Mass is extensive: the mass of a whole is the sum of the masses of its parts.
Volume on mixing is not: ethanol and water mix sub-additively. Tracking which
kinds are extensive is a precondition for soundly aggregating measurements.
:::

:::definition "def_extensiveKind" (parent := "extensivity") (lean := "PropertyKindCalculus.Extensive")
A kind is _extensive_ when, for any partition of a {uses "def_system"}[system]
into disjoint parts, the quantity of the whole equals the sum over the parts.
This requires the mereological structure deferred from the foundations chapter.
:::

:::proof "def_extensiveKind"
Realized as `Extensive k m`, a predicate over a kind `k` and a measurement `m`
(the property value observed on each node of a `Decomposition`): it asserts that
every part is measured as a value of kind `k`, and that the numeral on a disjoint
union is the sum of the numerals on its two parts.
:::

:::theorem "thm_extensive_additive" (parent := "extensivity") (lean := "PropertyKindCalculus.extensive_additive") (tags := "capstone, proved") (effort := "medium")
*Extensive aggregation.* For an extensive kind $`k` and a system decomposed into
parts $`s_1, \dots, s_n`,
$$`\mathrm{value}_k\Bigl(\bigsqcup_i s_i\Bigr) = \sum_i \mathrm{value}_k(s_i).`
The $`\forall`-quantified additivity law itself — not a single instance — is the
deliverable, and it is exactly what OWL2 has no vocabulary for. Builds on {uses "def_extensiveKind"}[extensive kinds].
:::

:::proof "thm_extensive_additive"
Proved in the `Extensivity` module by induction on the `Decomposition`: at a leaf
the law is reflexivity; at a union the single-split `additive` field plus the two
induction hypotheses give the numeral of the whole as the sum of the leaf sums.
:::

:::theorem "thm_mixing_subadditive" (parent := "extensivity") (lean := "PropertyKindCalculus.mixing_subadditive") (tags := "proved") (effort := "small")
*Counterexample — volume on mixing is not extensive.* Volume fails the additivity
law for a water/ethanol mixture: the volume of the mixture is strictly less than
the sum of the component volumes. Stating the negation keeps the extensive
predicate honest. Uses {uses "def_extensiveKind"}[extensive kinds].
:::

:::proof "thm_mixing_subadditive"
Proved in the `Extensivity` module. 50 mL of water and 50 mL of ethanol measure
96 mL when mixed; the strict inequality $`96 < 50 + 50` is `by decide`, and the
same `volMix` measurement witnesses $`\neg\,\mathrm{Extensive}\ \mathrm{volume}` by
refuting its `additive` field on that two-part decomposition.
:::

# Intensity, whole-properness, and what a carving cannot say

A `Decomposition` is a _carving_ and not a census. Nothing in it fixes how many parts a
system has, and every law of this chapter is quantified over all carvings rather than
stated for one — which is why the $`\forall`-quantified form is the deliverable: a total
that depends on how the whole was cut is not a total. That is Marmodoro's point about
physical structure, which "unites" without bringing a count principle with it, so that
"It is an open question how many entities a physical structure is"
{Manual.citep marmodoro_whole_but_not_one}[]. What a carving therefore cannot supply is
the _whole_; that arrives with a sort of system and its aggregation license, in the
object-type chapter.

Additivity is one answer to what composition does to a value, and the alternatives are not
the absence of an answer. Both below are stated against the same measurement, so a model that
claims one is claiming something refutable.

:::definition "def_intensiveKind" (parent := "extensivity") (lean := "PropertyKindCalculus.Intensive")
A kind is _intensive_ (§13.5.4) when composing two parts *that already agree* leaves the
value where it was: temperature, density, the angular velocity of a rigid body. The
hypothesis is Dybkær's own, read literally — his definition asks that the value be
"invariant with the extent of a system of constant composition", and _of constant
composition_ is the clause a shorter phrasing drops. Without it the law would assert that
mixing water at 20 °C with water at 80 °C leaves either reading intact.
:::

:::proof "def_intensiveKind"
Realized as `Intensive k m`, the same shape as {uses "def_extensiveKind"}[extensivity] with
the additivity field replaced by a conditional constancy field. What the structure says
about parts that _disagree_ is nothing at all: an intensive kind licenses no reading of the
whole from unequal parts, which is a narrower claim than a total law and an honest one.
:::

:::theorem "thm_intensive_uniform" (parent := "extensivity") (lean := "PropertyKindCalculus.intensive_uniform") (tags := "capstone, proved") (effort := "medium")
*Intensive aggregation.* For an intensive kind, a whole all of whose atomic parts read
$`v` reads $`v` itself, over any carving and to any depth. Builds on {uses "def_intensiveKind"}[intensive kinds].
:::

:::proof "thm_intensive_uniform"
By induction on the decomposition, exactly as the extensive capstone: at a leaf the
hypothesis is the conclusion; at a union the two induction hypotheses make the parts agree,
which is what the conditional constancy field consumes. The leaf-wise quantifier is
`Decomposition.Forall` — extensivity reaches its leaves through arithmetic (`leafSum`) and
intensivity has no arithmetic to reach them with.
:::

:::theorem "thm_not_extensive_of_intensive" (parent := "extensivity") (lean := "PropertyKindCalculus.not_extensive_of_intensive") (tags := "proved") (effort := "small")
*The branches exclude each other.* An intensive kind is not extensive as soon as two parts
agree on a *nonzero* value: additivity doubles it, constancy keeps it, and only
$`0 = 0 + 0` satisfies both. Uses {uses "def_intensiveKind"}[intensive kinds] and
{uses "def_extensiveKind"}[extensive kinds].
:::

:::proof "thm_not_extensive_of_intensive"
Cancellation on $`v + v = v + 0`. The nonzero hypothesis is stated rather than assumed
away, because a kind whose every reading is zero really does satisfy both laws, vacuously.
The library's witness is density: two parcels of one homogeneous fluid read 1000 kg/m³ and
so does the parcel they compose, which refutes additivity outright.
:::

:::definition "def_wholeProper" (parent := "extensivity") (lean := "PropertyKindCalculus.WholeProper")
A kind is _whole-proper_ when the value of the whole is produced by *no* aggregation over
the parts: neither by summing them nor by sharing a common reading with them. The
normal-mode frequency of a coupled pair is the standard case — a lone oscillator has no
normal mode, so there is nothing to sum and nothing to inherit. Bunge's four types do not
name this case; under the formalizations here it satisfies none of them, and in particular
it is not intensive, the value not being invariant with the extent of the system.
:::

:::proof "def_wholeProper"
A `Prop` structure whose two refutation fields are *exhibited*, as pairs of atomic parts,
rather than stated as negated universals: a negated universal is satisfied by a measurement
that is merely undefined somewhere, while a witness pins the failure to two parts a reader
can point at. What names the case is Marmodoro's distinction rather than Dybkær's vocabulary: her
structural powers constitute a whole out of parts, where the substantial power "*is* the
electron" {Manual.citep marmodoro_whole_but_not_one}[] — borne by the whole, and by nothing
the whole is made of.
:::

:::theorem "thm_normalMode_wholeProper" (parent := "extensivity") (lean := "PropertyKindCalculus.normalMode_wholeProper") (tags := "proved") (effort := "small")
*The whole-proper case is occupied.* Two oscillators at $`\omega_0 = 10` rad/s, coupled so the
upper normal mode sits at $`\omega_+ = 14` rad/s: the pair's reading is neither the parts'
sum (20) nor their common value (10). Uses {uses "def_wholeProper"}[whole-proper kinds].
:::

:::proof "thm_normalMode_wholeProper"
Both refutations are `decide` on the witness measurement, and the two derived theorems —
not extensive, not intensive — follow from the exhibited pair alone. The quantity-level
consequence is {uses "thm_assemble_ne_measured"}[assembling it anyway], in the object-type
chapter: with a license registered the sum still elaborates, and reports 20 rad/s for a mode
at 14.
:::
