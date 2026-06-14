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
aspect is _how the property is examined_: its examination principle (§7.5, VIM4
2CD 2.4) — the phenomenon serving as the basis — a method based on that principle
(VIM4 2CD 2.5), and a procedure based on that method (VIM4 2CD 2.7). These refine one
another and individuate kinds that scale and dimension alone cannot tell apart:
width and height are both rational lengths, separated only by the principle under
which each is examined. A description logic can record a link to a defining
aspect; it cannot state that refinement is a preorder, nor that refinement
preserves the principle.
:::

:::definition "def_examination" (parent := "spine_examination") (lean := "PropertyKindCalculus.ExaminationPrinciple")
The examination chain has three layers — an _examination principle_ (§7.5 / VIM4
2CD 2.4), a _method_ based on a principle (VIM4 2CD 2.5), and a _procedure_ based
on a method (VIM4 2CD 2.7) — gathered into one carrier `ExaminationItem` so that refinement
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

# Property value and value scale (Dybkær Ch. 9, 16, 10, 17)

:::group "spine_value"
A _property value_ (§9.15) is an inherent feature of a property used in comparing
it with other properties of the _same_ kind-of-property; it is a member of a
_value scale_ (§10.14), the ordered set of possible, mutually comparable values
of a kind. A _quantity value_ (§16.10) is the special case carried as a numerical
value times a reference — Dybkær's "reference quantity multiplied by a number".
The laws below — that comparability of values is an equivalence, that a value
scale holds only mutually comparable values, that a value's scale type fixes which
operations are defined — quantify over relations, operations, and a scale's
members; a description logic can record an instance of the link but can neither
state nor prove the laws.
:::

:::definition "def_propertyValue" (parent := "spine_value") (lean := "PropertyKindCalculus.PropertyValue")
A _property value_ (§9.15) bundles its {uses "def_kindOfProperty"}[kind-of-property], a numeral (the numerical value, §16.10), and the reference the numeral is
taken against — a metrological unit for a quantity value, a designation for a
nominal one. A value _is a quantity value_ (§16.10) iff its kind has magnitude,
and two values are _comparable_ iff they are of the same kind.
:::

:::proof "def_propertyValue"
A `structure` with `DecidableEq`. `scale`, `IsQuantityValue`, and `Comparable` are
definitional projections over the `kind` field.
:::

:::theorem "thm_value_comparable_equiv" (parent := "spine_value") (owner := "author_nfr") (lean := "PropertyKindCalculus.PropertyValue.Comparable.trans") (tags := "proved")
*Comparability of values is an equivalence.* Two {uses "def_propertyValue"}[property values] are comparable iff they are of the same kind (§9.15); the relation is
reflexive, symmetric, and transitive. Comparable values are moreover governed by
the same scale type, so the _same_ operators are defined on both
(`scale_eq_of_comparable`). Transitivity is exactly the algebraic law a
description logic cannot state.
:::

:::proof "thm_value_comparable_equiv"
Comparability unfolds to equality of the `kind` field, so reflexivity, symmetry,
and transitivity are those of `Eq`; `scale_eq_of_comparable` is `congrArg` on the
`scale` projection.
:::

:::definition "def_valueScale" (parent := "spine_value") (lean := "PropertyKindCalculus.ValueScale")
A _property value scale_ (§10.14) is the ordered set of possible, mutually
comparable values of one {uses "def_kindOfProperty"}[kind]. It carries that kind
and a provenance — _true_ (consistent with the property's definition, §10.16.1) or
_examined_ (obtained by an examination procedure, §10.16.2). Its `scaleType` is
the kind's scale, the datum Table 17.4 uses to gate which manipulations a scale
admits, and `KindOfProperty.valueScale` gives the canonical true scale of a kind
(§9.15 ↔ §10.14).
:::

:::proof "def_valueScale"
A `structure` carrying `kind` and a `ScaleProvenance`; `Admits v` is
`v.kind = s.kind`, and `KindOfProperty.valueScale` builds the canonical true scale.
:::

:::theorem "thm_scale_members_comparable" (parent := "spine_value") (owner := "author_nfr") (lean := "PropertyKindCalculus.ValueScale.comparable_of_mem") (tags := "capstone, proved") (priority := "high")
*A value scale holds only mutually comparable values.* Any two values a
{uses "def_valueScale"}[value scale] admits are of the scale's kind, hence
{uses "def_propertyValue"}[comparable] (§10.14) — the defining property of a value
scale, quantified over its members. The scale type further licenses operations
monotonically (`allows_mono_of_le`): a richer value scale supports every
manipulation a poorer one does (Table 17.4), inherited from {uses "thm_operator_monotonicity"}[operator monotonicity].
:::

:::proof "thm_scale_members_comparable"
Membership unfolds to equality with the scale's kind, so two members' kinds are
equal by `trans`/`symm`; operator monotonicity is the scale-layer `allows_mono`
re-exported through `scaleType`.
:::
