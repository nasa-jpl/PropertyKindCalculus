import Verso
import VersoManual
import VersoBlueprint

open Verso.Genre
open Verso.Genre.Manual
open Informal

#doc (Manual) "Dimension as a Forgetful Functor" =>

PropertyKindCalculus does not discard PhysLib's `Dimension`; it keeps it as a forgetful
functor. Dimension answers the coarse question — "are these even commensurable in
the SI base quantities?" — and the kind layer answers the fine one. This chapter
is _planned_: it records the coherence laws that make the two layers agree.

# The forgetful map (Dybkær Ch. 19)

:::group "dimension"
Every kind has a dimension, obtained by forgetting everything but its SI
base-quantity exponents. The functor must be a homomorphism: it has to respect
the interaction algebra, or the two layers would disagree about what
multiplication means.
:::

:::definition "def_dim" (parent := "dimension")
The _dimension map_ $`\dim : \mathrm{KindOfProperty} \to \mathrm{Dimension}`
sends a {uses "def_kindOfProperty"}[kind-of-property] to its PhysLib `Dimension`
(ℚ-exponents over length/mass/time/charge/temperature). It is deliberately
many-to-one: that is what makes {uses "thm_dimensionless_kinds_distinct"}[the dimension-1 disambiguation] true.
:::

:::proof "def_dim"
Planned. Pulls in PhysLib + Mathlib as a separate library (the spine stays
Mathlib-free). Each base SI kind is assigned its unit dimension; derived kinds
get the product/quotient of their factors' dimensions.
:::

:::theorem "thm_dim_homomorphism" (parent := "dimension") (tags := "capstone, planned") (effort := "medium") (priority := "high")
*Dimensional coherence — $`\dim` is a homomorphism.* Whenever the interaction
algebra says $`k_1` and $`k_2` combine to $`k_3`, their dimensions combine the
same way:
$$`\mathrm{KMul}\ k_1\ k_2\ k_3 \;\Longrightarrow\; \dim k_3 = \dim k_1 \cdot \dim k_2.`
This is the theorem that licenses forgetting to the dimension layer without
losing soundness: a kind-level product is always dimensionally consistent. Builds
on {uses "def_dim"}[the dimension map] and {uses "def_kMul"}[the kind product].
:::

:::proof "thm_dim_homomorphism"
Planned. By the construction of `KMul`: a well-formed kind product is defined by
composing the factors, and `dim` is defined to distribute over that composition,
so the equation holds by `rfl`/unfolding plus `Dimension`'s commutative-group
laws from PhysLib.
:::
