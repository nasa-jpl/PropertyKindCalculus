import Verso
import VersoManual
import VersoBlueprint
-- The interaction-algebra nodes below now link real declarations, so this chapter
-- imports the `Interaction` module (carried by the PhysLib-backed `Dimension`
-- library). The coherence side-condition is stated over PhysLib's `Dimension`.
import PropertyKindCalculus.Interaction

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
