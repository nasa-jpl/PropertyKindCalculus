import Verso
import VersoManual
import VersoBlueprint
-- Importing the `Dimension` library lets the `(lean := …)` nodes below resolve to
-- the real, sorry-free declarations and report their *proved* status. This is the
-- one chapter that pulls in PhysLib + Mathlib (transitively, through that
-- library); the spine chapters stay Mathlib-free. The `Interaction` module (same
-- PhysLib-backed library) supplies the homomorphism capstone below.
import PropertyKindCalculus.Dimension
import PropertyKindCalculus.Interaction

open Verso.Genre
open Verso.Genre.Manual
open Informal

#doc (Manual) "Dimension as a Forgetful Functor" =>

PropertyKindCalculus does not discard PhysLib's `Dimension`; it keeps it as a forgetful
functor. Dimension answers the coarse question — "are these even commensurable in
the SI base quantities?" — and the kind layer answers the fine one. The forgetful
map, its multiplicativity, and the dimension-1 disambiguation it makes possible
are now _realized_, sorry-free, in the `Dimension` library; the full coherence law
— that $`\dim` is a homomorphism over the interaction algebra — is realized in the
`Interaction` module and stated as the homomorphism capstone below.

Two terms recur below; in plain engineering terms they mean this. A _forgetful
functor_ is a deliberately lossy, one-way map: $`\dim` keeps only a kind's SI
base-quantity exponents (length, mass, time, …) and discards everything else that
distinguishes it, so many kinds share one dimension and there is no inverse. A
_homomorphism_ is a map that respects an operation: here $`\dim` respects
multiplication — the dimension of a product is the product of the dimensions, the
exponents adding — which is exactly the bookkeeping of everyday dimensional
analysis, stated and proved here as a law rather than performed by hand.

# The forgetful map (Dybkær Ch. 19)

:::group "dimension"
A kind is given a dimension by forgetting everything but its SI base-quantity
exponents. To keep the core spine Mathlib-free, the dimension is paired with the
kind in this separate library rather than stored on `KindOfProperty`: an
application declares a _dimensioned kind_ with a `def`, exactly as it declares a
kind. The forgetful map then drops the kind identity and keeps the dimension.
:::

:::definition "def_dim" (parent := "dimension") (lean := "PropertyKindCalculus.DimensionedKind.toDimension")
The _dimension map_ $`\dim` sends a _dimensioned kind_ — a
{uses "def_kindOfProperty"}[kind-of-property] paired with a PhysLib `Dimension`
(ℚ-exponents over length/time/mass/charge/temperature) — to that dimension. It is
deliberately many-to-one: that is what makes
{uses "thm_dimensionless_kinds_distinct"}[the dimension-1 disambiguation] true.
:::

:::proof "def_dim"
Realized in the `Dimension` library (`dimension/`). `DimensionedKind` is the
structure pairing a kind with its `Dimension`; `toDimension` is the forgetful
projection. PhysLib + Mathlib enter only here, as a separate library; the spine
stays Mathlib-free.
:::

:::theorem "thm_dim_multiplicative" (parent := "dimension") (lean := "PropertyKindCalculus.DimensionedKind.toDimension_times") (tags := "proved")
*The forgetful functor preserves products.* The dimension of a product of
dimensioned kinds is the product of their dimensions,
$$`\dim (a \cdot b) = \dim a \cdot \dim b,`
the SI exponents adding — ordinary dimensional bookkeeping, proved as a law. This
is the dimension-component of functoriality, stated for the provisional product;
the full interaction-algebra version is {uses "thm_dim_homomorphism"}[the
homomorphism capstone] below. Builds on {uses "def_dim"}[the dimension map].
:::

:::proof "thm_dim_multiplicative"
The provisional product multiplies the dimension components (PhysLib's
`Dimension.mul`, i.e. exponent addition), so the equation holds by `rfl`. The unit
law $`\dim 1 = 1` holds likewise.
:::

:::theorem "thm_dim_homomorphism" (parent := "dimension") (lean := "PropertyKindCalculus.InteractionAlgebra.dim_homomorphism") (tags := "capstone, proved") (effort := "medium") (priority := "high")
*Dimensional coherence — $`\dim` is a homomorphism over the full interaction
algebra.* Whenever the interaction algebra says $`k_1` and $`k_2` combine to
$`k_3`, their dimensions combine the same way:
$$`\mathrm{KMul}\ k_1\ k_2\ k_3 \;\Longrightarrow\; \dim k_3 = \dim k_1 \cdot \dim k_2.`
This is the theorem that licenses forgetting to the dimension layer without
losing soundness: a kind-level product is always dimensionally consistent. It
upgrades {uses "thm_dim_multiplicative"}[the proved multiplicativity] from the
provisional product to Flater's gated {uses "def_kMul"}[kind product].
:::

:::proof "thm_dim_homomorphism"
Realized in the `Interaction` module as `InteractionAlgebra.dim_homomorphism`.
Coherence is a well-formedness field of every `InteractionAlgebra`, so the
homomorphism is its projection: any algebra that can be formed at all already
guarantees $`\dim k_3 = \dim k_1 \cdot \dim k_2` on every sanctioned edge. The
content sits in the worked algebra, where the obligation is discharged by the
`Dimension`-group computation, case by case.
:::
