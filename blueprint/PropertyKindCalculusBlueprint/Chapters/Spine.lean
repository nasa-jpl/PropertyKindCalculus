import Verso
import VersoManual
import VersoBlueprint
-- Importing the library being documented lets the `(lean := "PropertyKindCalculus.…")`
-- nodes below resolve to real declarations and report their *proved* status.
import PropertyKindCalculus

open Verso.Genre
open Verso.Genre.Manual
open Informal

#doc (Manual) "The Proved Spine" =>

This chapter records what PropertyKindCalculus already establishes, sorry-free, in its
Mathlib-free core. Every node here links to a real declaration with
`(lean := "PropertyKindCalculus.…")`, so its _proved_ status in the dependency graph is
read directly from the checked library rather than asserted in prose.

The point to keep in view: each of these is a law or an operation, not a class
membership. A description-logic reasoner (OWL2/SROIQ) can record that `width`
specializes `length`; it cannot state, let alone prove, that specialization is
transitive or that operator availability is monotone in scale. Those are the
entries below.

:::author "author_nfr" (name := "Nicolas Rouquette")
:::

# Foundations — system and object (Dybkær Ch. 3)

:::group "spine_foundations"
The carrier layer: the systems (objects) whose features properties are.
:::

:::definition "def_system" (parent := "spine_foundations") (lean := "PropertyKindCalculus.System")
A _system_ (Dybkær §3.3) is a demarcated arrangement of elements and their
relationships; _object_ (§3.3 Note 6) is given as a synonym. Specified abstractly
by identity here; the mereological structure that extensivity needs is added in a
later module.
:::

:::proof "def_system"
A one-field `structure` with `DecidableEq`; nothing to prove. The synonym
`Object := System` keeps the instance layer reading as "characterizes an
object".
:::

# Scale — the operator-based division of ⟨property⟩ (Dybkær Ch. 12)

:::group "spine_scale"
Dybkær divides ⟨property⟩ by which algebraic operators are defined between
properties of a kind. This is the axis a description logic cannot represent: it
is about operations, and DL has none.
:::

:::definition "def_scaleType" (parent := "spine_scale") (lean := "PropertyKindCalculus.ScaleType")
The four _scale types_ of Dybkær Fig. 12.21, ordered by operator richness:
$`\mathrm{nominal} \sqsubset \mathrm{ordinal} \sqsubset \mathrm{interval}
\sqsubset \mathrm{ratio}`, admitting respectively $`\{=,\neq\}`, then
$`\{<,>\}`, then $`\{+,-\}`, then $`\{\times,\div\}`.
:::

:::proof "def_scaleType"
A four-constructor `inductive` with a `rank : ScaleType → Nat` and the induced
`≤`. The lemmas `le_def`, `le_refl`, `le_trans`, and `le_antisymm` establish that
`≤` is the expected linear order.
:::

:::theorem "thm_scale_linear_order" (parent := "spine_scale") (owner := "author_nfr") (lean := "PropertyKindCalculus.ScaleType.le_antisymm") (tags := "proved")
The scale order is a _linear order_: reflexive (`le_refl`), transitive
(`le_trans`), and antisymmetric (`le_antisymm`) on {uses "def_scaleType"}[the scale types].
:::

:::proof "thm_scale_linear_order"
Reflexivity and transitivity are inherited from `Nat.le` on `rank`.
Antisymmetry reduces to `Nat.le_antisymm` on the ranks followed by a four-by-four
case split (`cases a <;> cases b <;> simp_all`).
:::

:::theorem "thm_operator_monotonicity" (parent := "spine_scale") (owner := "author_nfr") (lean := "PropertyKindCalculus.ScaleType.allows_mono") (tags := "capstone, proved") (priority := "high")
*Operator-availability monotonicity.* A richer scale licenses every operation a
poorer one does: if $`a \le b` then `AllowsOrder`, `AllowsDifference`, and
`AllowsRatio` each transport from $`a` to $`b`. This is a meta-theorem OWL2's
reasoner cannot even phrase, since it quantifies over which operations are
defined for a kind. Builds on {uses "def_scaleType"}[the scale types].
:::

:::proof "thm_operator_monotonicity"
Decide all sixteen ordered pairs: `cases a <;> cases b <;> simp_all [AllowsOrder,
AllowsDifference, AllowsRatio, le_def, rank]`.
:::

# Kind-of-property and kind-of-quantity (Dybkær Ch. 6, 13)

:::group "spine_kind"
A kind is the "common defining aspect of mutually comparable properties"
(§6.19). It is an open value — applications declare new kinds as `def`s — and it
carries its scale and an optional examination principle (§7.5) used to
individuate otherwise-comparable kinds (width vs. height).
:::

:::definition "def_kindOfProperty" (parent := "spine_kind") (lean := "PropertyKindCalculus.KindOfProperty")
A _kind-of-property_ (§6.19) bundles a terminological `id`, a `scale` (from {uses "def_scaleType"}[the scale types]), and an optional examination principle. A kind
_is a kind-of-quantity_ (§13.3.1) iff its scale has magnitude (is at least
ordinal).
:::

:::proof "def_kindOfProperty"
A `structure` with `DecidableEq`. `IsQuantity`, and the scale divisions
`IsNominal`/`IsOrdinal`/`IsDifferential`/`IsRational` (§13.2), are definitional
predicates over the `scale` field.
:::

:::theorem "thm_nominal_not_quantity" (parent := "spine_kind") (owner := "author_nfr") (lean := "PropertyKindCalculus.KindOfProperty.nominal_not_quantity") (tags := "proved")
A nominal kind is, by construction, _not_ a kind-of-quantity: it has no
magnitude. Uses {uses "def_kindOfProperty"}[kind-of-property].
:::

:::proof "thm_nominal_not_quantity"
Unfold `IsQuantity`, `IsNominal`, and `HasMagnitude`; the scale is `nominal`, so
`scale ≠ nominal` is false.
:::

:::theorem "thm_rational_isQuantity" (parent := "spine_kind") (owner := "author_nfr") (lean := "PropertyKindCalculus.KindOfProperty.rational_isQuantity") (tags := "proved")
A rational kind _is_ a kind-of-quantity. Uses {uses "def_kindOfProperty"}[kind-of-property].
:::

:::proof "thm_rational_isQuantity"
The scale is `ratio`, so `scale ≠ nominal` holds; unfold and simplify.
:::

# Specialization and mutual comparability (OML / Dybkær §6)

:::group "spine_specialization"
`Specializes` relates kinds to kinds. Flater (NIST TN 1943 §6.2) stresses the
result is a lattice, not a tree. We generate it as the reflexive–transitive
closure of an application-supplied direct-parent edge relation, so each "system
of quantities" supplies its own hierarchy.
:::

:::definition "def_specializes" (parent := "spine_specialization") (lean := "PropertyKindCalculus.Specializes")
_Specialization_ `Specializes E` is the reflexive–transitive closure of a
direct-parent edge relation `E` over {uses "def_kindOfProperty"}[kind-of-property]. Different `E` give different per-application hierarchies — the extensibility a
fixed `inductive` would deny.
:::

:::proof "def_specializes"
An `inductive` with `refl` and `step` constructors; `of_edge` lifts a single
edge.
:::

:::theorem "thm_specialization_preorder" (parent := "spine_specialization") (owner := "author_nfr") (lean := "PropertyKindCalculus.Specializes.trans") (tags := "capstone, proved") (priority := "high")
*Specialization is a preorder.* It is reflexive (the `refl` constructor) and
transitive (`Specializes.trans`). Stating — let alone proving — an algebraic law
of the taxonomy is exactly what an OWL2 reasoner cannot do; it checks
consistency, not laws. Uses {uses "def_specializes"}[specialization].
:::

:::proof "thm_specialization_preorder"
Transitivity is by induction on the first derivation: `refl` returns the second
derivation, `step` re-applies the constructor under the inductive hypothesis.
:::

:::definition "def_mutuallyComparable" (parent := "spine_specialization") (lean := "PropertyKindCalculus.MutuallyComparable")
Two kinds are _mutually comparable_ iff they share a common super-kind
($`\exists p,\ a \sqsubseteq p \wedge b \sqsubseteq p`). This is how `width` and
`height` stay comparable as lengths while remaining distinct sub-kinds. Uses {uses "def_specializes"}[specialization].
:::

:::proof "def_mutuallyComparable"
An existential over a shared upper bound.
:::

:::theorem "thm_comparable_refl_symm" (parent := "spine_specialization") (owner := "author_nfr") (lean := "PropertyKindCalculus.MutuallyComparable.symm") (tags := "proved")
Mutual comparability is reflexive (`refl`) and symmetric (`symm`), and any
specialization induces it (`of_specializes`). Uses {uses "def_mutuallyComparable"}[mutual comparability].
:::

:::proof "thm_comparable_refl_symm"
Reflexivity takes the witness `a` itself; symmetry swaps the two halves of the
conjunction.
:::

# Examination — principle, method, procedure (Dybkær Ch. 7, 14)

:::group "spine_examination"
A kind-of-property is a "common defining aspect" (§6.19). One such defining
aspect is _how the property is examined_: its examination principle (§7.5, VIM
2.4) — the phenomenon serving as the basis — a method based on that principle
(VIM 2.5), and a procedure based on that method (VIM 2.6). These refine one
another and individuate kinds that scale and dimension alone cannot tell apart:
width and height are both rational lengths, separated only by the principle under
which each is examined. A description logic can record a link to a defining
aspect; it cannot state that refinement is a preorder, nor that refinement
preserves the principle.
:::

:::definition "def_examination" (parent := "spine_examination") (lean := "PropertyKindCalculus.ExaminationPrinciple")
The examination chain has three layers — an _examination principle_ (§7.5 / VIM
2.4), a _method_ based on a principle (VIM 2.5), and a _procedure_ based on a
method (VIM 2.6) — gathered into one carrier `ExaminationItem` so that refinement
is a homogeneous relation. The forgetful projection `basePrinciple` sends any
item down to the principle it rests on.
:::

:::proof "def_examination"
Three small `structure`s with `DecidableEq`, united by an `ExaminationItem`
inductive; `basePrinciple` is the projection to the principle layer.
:::

:::definition "def_refines" (parent := "spine_examination") (lean := "PropertyKindCalculus.Refines")
_Refinement_ `Refines` is the reflexive–transitive closure of the "based-on"
edges (a procedure is based on its method, a method on its principle): procedure
⊑ method ⊑ principle. It mirrors {uses "def_specializes"}[specialization] over
kinds — the same closure construction, one level down at the defining aspect.
:::

:::proof "def_refines"
An `inductive` with `refl` and `step` constructors over a `BasedOn` edge
relation; `of_basedOn` lifts a single edge.
:::

:::theorem "thm_refines_preorder" (parent := "spine_examination") (owner := "author_nfr") (lean := "PropertyKindCalculus.Refines.trans") (tags := "proved")
*Refinement is a preorder.* It is reflexive (the `refl` constructor) and
transitive (`Refines.trans`) on {uses "def_refines"}[the examination chain] — the
same algebraic law proved for specialization, which an OWL2 reasoner can neither
state nor prove.
:::

:::proof "thm_refines_preorder"
Transitivity is by induction on the first derivation, exactly as for
`Specializes`: `refl` returns the second derivation, `step` re-applies the
constructor under the inductive hypothesis.
:::

:::theorem "thm_examination_coherence" (parent := "spine_examination") (owner := "author_nfr") (lean := "PropertyKindCalculus.Refines.basePrinciple_eq") (tags := "capstone, proved") (priority := "high")
*Refinement preserves the principle.* Every examination in one refinement chain
rests on the same base principle:
$$`\mathrm{Refines}\ a\ b \;\Longrightarrow\; \mathrm{basePrinciple}\ a = \mathrm{basePrinciple}\ b.`
The forgetful projection to the principle layer is invariant along refinement —
the examination-layer analogue of $`\dim` being a homomorphism, and one provable
here in the Mathlib-free core without PhysLib. Builds on {uses "def_refines"}[refinement].
:::

:::proof "thm_examination_coherence"
By induction on the refinement derivation: each `BasedOn` edge preserves the base
principle (`cases … <;> rfl`), and the inductive step chains the resulting
equalities.
:::

:::theorem "thm_examPrinciple_defining" (parent := "spine_examination") (owner := "author_nfr") (lean := "PropertyKindCalculus.KindOfProperty.distinct_of_examPrinciple") (tags := "proved")
*The examination principle is a defining aspect.* Two {uses "def_kindOfProperty"}[kinds]
examined by different principles are distinct kinds — independently of scale and
dimension. This is what keeps width and height distinct while both remain
rational lengths, {uses "def_mutuallyComparable"}[mutually comparable] under their
shared super-kind Length.
:::

:::proof "thm_examPrinciple_defining"
The kinds differ in their `examPrinciple` field, so they are unequal by
congruence: substitute the assumed kind-equality and derive a contradiction from
the field inequality.
:::
