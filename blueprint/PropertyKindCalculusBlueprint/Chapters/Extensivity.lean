import Verso
import VersoManual
import VersoBlueprint

open Verso.Genre
open Verso.Genre.Manual
open Informal

#doc (Manual) "Extensivity" =>

Dybkær §13.5 distinguishes _extensive_ kinds (whose value over a whole is the sum
over disjoint parts) from kinds where that fails. This is a quantified arithmetic
law over the mereology of systems — again something a description logic cannot
state. This chapter is _planned_.

# Extensive and conditionally-extensive kinds (Dybkær §13.5)

:::group "extensivity"
Mass is extensive: the mass of a whole is the sum of the masses of its parts.
Volume on mixing is not: ethanol and water mix sub-additively. Tracking which
kinds are extensive is a precondition for soundly aggregating measurements.
:::

:::definition "def_extensiveKind" (parent := "extensivity")
A kind is _extensive_ when, for any partition of a {uses "def_system"}[system]
into disjoint parts, the quantity of the whole equals the sum over the parts.
This requires the mereological structure deferred from the foundations chapter.
:::

:::proof "def_extensiveKind"
Planned. A predicate `Extensive k` asserting additivity of `measure` over a
`Decomposition` of the carrier system.
:::

:::theorem "thm_extensive_additive" (parent := "extensivity") (tags := "capstone, planned") (effort := "medium")
*Extensive aggregation.* For an extensive kind $`k` and a system decomposed into
parts $`s_1, \dots, s_n`,
$$`\mathrm{value}_k\Bigl(\bigsqcup_i s_i\Bigr) = \sum_i \mathrm{value}_k(s_i).`
The $`\forall`-quantified additivity law itself — not a single instance — is the
deliverable, and it is exactly what OWL2 has no vocabulary for. Builds on {uses "def_extensiveKind"}[extensive kinds].
:::

:::proof "thm_extensive_additive"
Planned. By induction on the decomposition, using the additivity field of
`Extensive k` at each split.
:::

:::theorem "thm_mixing_subadditive" (parent := "extensivity") (tags := "planned") (effort := "small")
*Counterexample — volume on mixing is not extensive.* Volume fails the additivity
law for a water/ethanol mixture: the volume of the mixture is strictly less than
the sum of the component volumes. Stating the negation keeps the extensive
predicate honest. Uses {uses "def_extensiveKind"}[extensive kinds].
:::

:::proof "thm_mixing_subadditive"
Planned. A concrete two-part decomposition with measured volumes whose mixture
volume is smaller, witnessing $`\neg\,\mathrm{Extensive}\ \mathrm{volume}` for
that system.
:::
