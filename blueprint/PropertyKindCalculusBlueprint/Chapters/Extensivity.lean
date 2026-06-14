import Verso
import VersoManual
import VersoBlueprint
-- The extensivity nodes below now link real declarations, so this chapter imports
-- the (Mathlib-free, core) `Extensivity` module.
import PropertyKindCalculus.Extensivity

open Verso.Genre
open Verso.Genre.Manual
open Informal

#doc (Manual) "Extensivity" =>

Dybkær §13.5 distinguishes _extensive_ kinds (whose value over a whole is the sum
over disjoint parts) from kinds where that fails. This is a quantified arithmetic
law over the mereology of systems — again something a description logic cannot
state. It is now _realized_, sorry-free, in the Mathlib-free `Extensivity` module:
the decomposition mereology, the `Extensive` predicate, the induction that lifts a
single split to the whole tree, and the volume-on-mixing counterexample.

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
