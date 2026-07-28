import Verso
import VersoManual
import VersoBlueprint
-- The interaction-algebra nodes below now link real declarations, so this chapter
-- imports the `Interaction` module (carried by the PhysLib-backed `Dimension`
-- library). The coherence side-condition is stated over PhysLib's `Dimension`.
import PropertyKindCalculus.Interaction
-- The trust-model section links the core witness constructor and the operator table.
import PropertyKindCalculus.QuantityClassification
import PropertyKindCalculus.OperatorTable

open Verso.Genre
open Verso.Genre.Manual
open Informal

#doc (Manual) "The Interaction Algebra (Flater Appendix C)" =>

This is the contribution beyond the VIM4 2CD and OML, and the reason Flater's note is titled
_full tracking of kinds of quantities_. Dimensional analysis says torque and
energy share a dimension ($`\mathrm{M\,L^2\,T^{-2}}`), yet they are not the same
kind and not interchangeable. The interaction algebra records which kinds
legitimately combine, with the dimensional product as a coherence side-condition
rather than the definition. It is now _realized_, sorry-free, in the `Interaction`
module: the curated product, its division dual, the multiplication–division
round-trip, and the worked torque-versus-energy instance.

# The ternary product of kinds (Flater App. C)

:::group "interaction"
Combination of kinds is a ternary relation, not a binary function: a pair of
input kinds may produce a specific output kind (torque × angle → energy) or no
kind at all (a category error). Description logic role chains are binary,
regular, and arithmetic-free, so they cannot express this; here it is an ordinary
relation with proofs. An _interaction algebra_ bundles the sanctioned products an
application asserts with a proof that each is dimensionally coherent — so the
coherence law below holds for any algebra by construction.
:::

:::definition "def_kMul" (parent := "interaction") (lean := "PropertyKindCalculus.InteractionAlgebra.KMul")
$`\mathrm{KMul}\ k_1\ k_2\ k_3` holds when kind $`k_1` times kind $`k_2` yields
kind $`k_3`. It is partial and curated: an application asserts the legitimate
products of its {uses "def_kindOfProperty"}[kinds], each carrying the dimensional
coherence obligation discharged by {uses "thm_dim_homomorphism"}[the homomorphism theorem].
:::

:::proof "def_kMul"
Realized as the `KMul` field of `InteractionAlgebra`: a ternary relation over
{uses "def_dim"}[dimensioned kinds], paired in the same structure with the
well-formedness field `kMul_coherent` that requires every edge to satisfy
$`\dim k_3 = \dim k_1 \cdot \dim k_2`. The structure cannot be formed for an
algebra that violates coherence.
:::

:::definition "def_kDiv" (parent := "interaction") (lean := "PropertyKindCalculus.InteractionAlgebra.KDiv")
$`\mathrm{KDiv}\ k_3\ k_2\ k_1` is the division dual of {uses "def_kMul"}[the kind product]: $`k_3` divided by $`k_2` yields $`k_1`. Fuel-consumption $`\times`
rainfall is the classic Flater example whose careless handling yields a category
error rather than a number.
:::

:::proof "def_kDiv"
Realized as `InteractionAlgebra.KDiv`, defined as the product read backwards
($`\mathrm{KDiv}\ c\ b\ a := \mathrm{KMul}\ a\ b\ c`), so it inherits the same
partiality and coherence side-condition.
:::

:::theorem "thm_interaction_roundtrip" (parent := "interaction") (lean := "PropertyKindCalculus.InteractionAlgebra.kMul_iff_kDiv") (tags := "capstone, proved") (effort := "medium") (priority := "high")
*Multiplication and division are inverse on kinds.* A product and its quotient
hold together — the round-trip is an _equivalence_:
$$`\mathrm{KMul}\ k_1\ k_2\ k_3 \;\Longleftrightarrow\; \mathrm{KDiv}\ k_3\ k_2\ k_1.`
Together with {uses "thm_dim_homomorphism"}[dimensional coherence] this is the
calculus that OWL2 cannot host: an algebraic law with arithmetic side-conditions,
proved rather than consistency-checked. Builds on {uses "def_kMul"}[the kind product] and {uses "def_kDiv"}[the kind quotient].
:::

:::proof "thm_interaction_roundtrip"
Immediate from defining `KDiv` as the converse of `KMul`: the biconditional is
`Iff.rfl`. The round-trip is the symmetry of that definition.
:::

:::theorem "thm_torque_angle_work" (parent := "interaction") (lean := "PropertyKindCalculus.torque_angle_work") (tags := "proved") (effort := "small")
*Worked instance.* Torque times plane angle is energy, and energy is not torque,
even though $`\dim(\mathrm{torque}) = \dim(\mathrm{energy})`. Formally
$`\mathrm{KMul}\ \mathrm{torque}\ \mathrm{angle}\ \mathrm{energy}` holds while
$`\mathrm{energy} \neq \mathrm{torque}` — the small example that shows the algebra
carrying information dimension alone discards. Uses {uses "def_kMul"}[the kind product].
:::

:::proof "thm_torque_angle_work"
Proved in the `Interaction` module. `torque`, `angle` (dimension one), and
`energy` are declared as dimensioned kinds, with `torque` and `energy` both given
dimension `force · length`; the product edge `torque_angle_energy` is asserted in
the worked `siMech` algebra and its coherence checked by the `Dimension`-group
computation, while `energy.kind ≠ torque.kind` is `by decide`.
:::

# The trust model: what is checked, what is authored

:::group "trustmodel"
The interaction algebra is _curated_, and it pays to be precise about what the
type system guarantees for a curated edge: *explicitness and propagation, not
truth*. Every kind-changing operation demands a witness naming the full kind
equation at its call site, and no mechanism — no inference, no instance search,
no coercion — can introduce an edge silently. But whether a written edge is
metrologically _right_ is the author's claim, exactly as an axiom is a claim a
proof assistant checks everything _against_ but never _for_. This section fixes
the two poles the discipline sits between, and shows the residue between them is
finite, local, and mechanically enumerable.
:::

*The negative pole — kinds in the name only.* In an unkinded model every
quantity is a bare numeric: a vegetation-attenuation kernel reads
`attenuation (b ndvi : Float) : Float`, and the kind of each argument lives only
in its _name_. The type system then cannot see any of the kind algebra: the
swapped call `attenuation ndvi b` elaborates and silently computes the
role-swapped exponent; a damping `lam : Float` adds to a Gram-diagonal entry
`jtj : Float` whatever the entry's kind; a fitted gain from one forward model
substitutes for the differently-kinded gain of another. Dimension checking does
not recover the distinctions: attenuations, damping factors, and vegetation
indices are all dimension one, so a dimensional type system waves every one of
these confusions through (the torque-versus-energy instance above is the same
failure at dimension $`\mathrm{M\,L^2\,T^{-2}}`). Name-only kinds are
documentation; nothing enforces them.

*The positive pole — the kind algebra is explicit.* The same kernel written
over `Quantity` makes the kind a type index and gates every kind-changing
operation on a witness: `attenuationQ (b : Quantity paramB α) (ndvi : Quantity
vegetationIndex α)` rejects the swapped call at compile time, the cross-kind sum
`jtj + lam` fails to elaborate because addition is defined only at a _shared_
kind (there is deliberately no opt-in for heterogeneous addition), and each
product or exponential names its edge in full — `ProductKind.ofRatio paramB
vegetationIndex attenuationExponent` — where it is used. Downstream models
certify the rejections as build artifacts: a `#check_failure` probe succeeds
only if the forbidden term fails to elaborate, so the build proves the negative
examples _stay_ negative.

:::definition "def_ofRatio" (parent := "trustmodel") (lean := "PropertyKindCalculus.ProductKind.ofRatio")
*The liberal certificate authority.* `ProductKind.ofRatio k₁ k₂ k` signs
_any_ three ratio-scale kinds: the scale gate is checked, the kind equation is
not. This is deliberate — the same dimension-one ratio can legitimately land in
different kinds by role (a quotient of two backscatters is an attenuation in one
column of a Jacobian and a pure number in another), so the landing kind is
curation the calculus must let the author state. The cost is the trust model
above: an edge's truth is a reviewed claim. The guarantee that remains is that
the claim must be written, in full, where it is used — a wrong edge is not
impossible, it is impossible to write _silently_.
:::

:::proof "def_ofRatio"
Realized in `QuantityClassification` ("The trust model" in that module's
header): the witness Props (`ProductKind`, `QuotientKind`, `TranscendentalKind`)
carry only the ratio-scale gates, `ofRatio` discharges them by `rfl` for any
concrete kinds, and `Quantity.mul`/`div`/`exp` refuse to operate without the
witness.
:::

:::definition "def_operatorTable" (parent := "trustmodel") (lean := "PropertyKindCalculus.KindMul")
*Narrowing by instance table.* `KindMul k₁ k₂ k` (with `k` an `outParam`) and
its division dual `KindDiv` re-house authored edges as typeclass instances: a
model registers at most one signed edge per operand pair next to its kind
declarations, and adopting call sites use scoped `*`/`/` whose result kind is
resolved — not chosen — at each use. Where the table is adopted, an unlisted
edge is no longer merely unwritten; it is unresolvable.
:::

:::proof "def_operatorTable"
Realized in `OperatorTable`: the instance classes wrap
{uses "def_kMul"}[the curated ternary product] as resolution-driven registrations,
with `hmul_eq_mul` bridging the scoped operator back to the witness-passing
`Quantity.mul` by `rfl`.
:::

*The audit is mechanical.* A witness is to the kind algebra what an axiom is
to a proof, and the analogy extends to the tooling: soundness is judged by
_enumerating_ the trusted base, never by the absence of errors. Three queries
cover it. Instance-table registrations are listed by the stock `#instances
KindMul` command. Named witness theorems are found by scanning the environment
for declarations whose type mentions the witness Props. And every _call-site_
witness is lifted by Lean into an auxiliary theorem whose type _is_ the edge
(`attenuationQ._proof_2 : ProductKind paramB vegetationIndex
attenuationExponent`), so one environment scan over constant types — internal
names attributed to their parents — enumerates the complete authored edge set
of a kind, named and inline alike: the kind-algebra analog of `#print axioms`.

