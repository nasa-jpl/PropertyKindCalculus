import Verso
import VersoManual
import VersoBlueprint

open Verso.Genre
open Verso.Genre.Manual
open Informal

#doc (Manual) "The Interaction Algebra (Flater Appendix C)" =>

This is the contribution beyond the VIM4 2CD and OML, and the reason Flater's note is titled
_full tracking of kinds of quantities_. Dimensional analysis says torque and
energy share a dimension ($`\mathrm{M\,L^2\,T^{-2}}`), yet they are not the same
kind and not interchangeable. The interaction algebra records which kinds
legitimately combine, with the dimensional product as a coherence side-condition
rather than the definition. This chapter is _planned_.

# The ternary product of kinds (Flater App. C)

:::group "interaction"
Combination of kinds is a ternary relation, not a binary function: a pair of
input kinds may produce a specific output kind (torque × angle → energy) or no
kind at all (a category error). Description logic role chains are binary,
regular, and arithmetic-free, so they cannot express this; here it is an ordinary
relation with proofs.
:::

:::definition "def_kMul" (parent := "interaction")
$`\mathrm{KMul}\ k_1\ k_2\ k_3` holds when kind $`k_1` times kind $`k_2` yields
kind $`k_3`. It is partial and curated: an application asserts the legitimate
products of its {uses "def_kindOfProperty"}[kinds], each carrying the dimensional
coherence obligation discharged by {uses "thm_dim_homomorphism"}[the homomorphism theorem].
:::

:::proof "def_kMul"
Planned. A relation (or a structure of asserted product-edges) over kinds, with
each edge required to satisfy $`\dim k_3 = \dim k_1 \cdot \dim k_2`.
:::

:::definition "def_kDiv" (parent := "interaction")
$`\mathrm{KDiv}\ k_3\ k_2\ k_1` is the division dual of {uses "def_kMul"}[the kind product]: $`k_3` divided by $`k_2` yields $`k_1`. Fuel-consumption $`\times`
rainfall is the classic Flater example whose careless handling yields a category
error rather than a number.
:::

:::proof "def_kDiv"
Planned. Defined from `KMul` by reassociating the triple, inheriting the same
coherence side-condition.
:::

:::theorem "thm_interaction_roundtrip" (parent := "interaction") (tags := "capstone, planned") (effort := "medium") (priority := "high")
*Multiplication and division are inverse on kinds.* Whenever a product is
defined, dividing the result by one factor recovers the other:
$$`\mathrm{KMul}\ k_1\ k_2\ k_3 \;\Longrightarrow\; \mathrm{KDiv}\ k_3\ k_2\ k_1.`
Together with {uses "thm_dim_homomorphism"}[dimensional coherence] this is the
calculus that OWL2 cannot host: an algebraic law with arithmetic side-conditions,
proved rather than consistency-checked. Builds on {uses "def_kMul"}[the kind product] and {uses "def_kDiv"}[the kind quotient].
:::

:::proof "thm_interaction_roundtrip"
Planned. Immediate from defining `KDiv` as the reassociation of `KMul`; the
round-trip is the symmetry of that definition.
:::

:::theorem "thm_torque_angle_work" (parent := "interaction") (tags := "planned") (effort := "small")
*Worked instance.* Torque times plane angle is energy, and energy is not torque,
even though $`\dim(\mathrm{torque}) = \dim(\mathrm{energy})`. Formally
$`\mathrm{KMul}\ \mathrm{torque}\ \mathrm{angle}\ \mathrm{energy}` holds while
$`\mathrm{energy} \neq \mathrm{torque}` — the small example that shows the algebra
carrying information dimension alone discards. Uses {uses "def_kMul"}[the kind product].
:::

:::proof "thm_torque_angle_work"
Planned. `torque`, `angle`, `energy` declared as kinds (angle dimension one); the
product edge is asserted and its coherence checked; `energy ≠ torque` is `by
decide`.
:::
