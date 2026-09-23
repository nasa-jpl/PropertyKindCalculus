import Verso
import VersoManual
import VersoBlueprint
-- Importing the library being documented lets the `(lean := "PropertyKindCalculus.…")`
-- nodes below resolve to real declarations and report their *proved* status.
import PropertyKindCalculus

open Verso.Genre
open Verso.Genre.Manual
open Informal

#doc (Manual) "Dedicated kinds-of-property" =>
%%%
tag := "dedicated-kind"
%%%

A bare kind-of-property — _length_, _volume fraction_, _substance concentration_ —
is generic: it names _what is measured_ without saying _of what_. Dybkær's
Chapter 20 closes that gap with the _dedicated kind-of-property_, defined there as
"a kind-of-property with given sort of system and any pertinent component". It is
the syntax laboratory medicine already uses for a fully-specified measurand —
`System — Component ; kind-of-property`, as in _"Plasma — Glucose ; substance
concentration"_, or, in this project's home domain, _"Soil — Water ; volume
fraction"_ (volumetric water content). Note what the definition asks for: a
*sort* of system. _Plasma_ and _soil_ name sorts, and the catalogue entry is one
entry for every plasma sample and every soil sample there will ever be. The
_particular_ system a measured value characterizes enters one layer down, as the
object index of an individual quantity — dedication to the sort, individuation by
the object.

This is the construct the QUDV → OML/OWL2 lineage cannot express. A description
logic can record that a quantity _has_ a sort of system and _has_ a component, but
it cannot make _"Soil — Water ; volume fraction"_ and _"Soil — Water ; mass
fraction"_ provably distinct kinds _while keeping both dedicated to the same sort
and the same component_. Here that distinctness is a theorem, and it is the
_principled_ form of the dimension-1 disambiguation: volumetric and gravimetric
water content are the *same measurement target* — soil, water — examined as two
different kinds-of-property, so they differ *because the kinds-of-property differ*,
not because someone chose two different identity strings.

# The dedicated kind (Dybkær Ch. 20)

:::group "spine_dedicated"
A dedicated kind joins three things the spine already carries — a {uses "def_sortOfSystem"}[sort of system] (the definition's "given sort of system"), a component, and a {uses "def_kindOfProperty"}[kind-of-property] (Ch. 6) — into the IUPAC/IFCC `System — Component ; kind` designation, the `System` slot naming the sort. It is a Mathlib-free core module; the worked example _"Soil — Water ; volume fraction"_ versus _"… ; mass fraction"_ is checked in the `Examples` library.
:::

:::definition "def_component" (parent := "spine_dedicated") (lean := "PropertyKindCalculus.Component")
A _component_ (§20) is the pertinent component of the {uses "def_sortOfSystem"}[sort of system] a dedicated kind is about — _water_ in a _soil_ sample, _glucose_ in _plasma_. Specified abstractly by identity, exactly mirroring the sort carrier.
:::

:::proof "def_component"
A one-field `structure` with `DecidableEq`; nothing to prove.
:::

:::definition "def_dedicatedKind" (parent := "spine_dedicated") (lean := "PropertyKindCalculus.DedicatedKind")
A _dedicated kind-of-property_ (§20) bundles a {uses "def_sortOfSystem"}[sort of system], a {uses "def_component"}[component], and a {uses "def_kindOfProperty"}[kind-of-property]. Its `systematicTerm` renders the three as `System — Component ; kind`, and it _is a dedicated kind-of-quantity_ iff its underlying kind has magnitude (§13.3.1). `dedicatedTo` builds one from a bare kind.
:::

:::proof "def_dedicatedKind"
A three-field `structure` with `DecidableEq`. `systematicTerm` is string interpolation of the three ids; `IsQuantity` is the underlying kind's `IsQuantity`.
:::

:::definition "def_dedicatedFor" (parent := "spine_dedicated") (lean := "PropertyKindCalculus.KindOfProperty.dedicatedFor")
Dedicating a kind _through an object_: the object contributes exactly its sort, via the model's `Sorted` claim. This is the arrow from the {uses "def_individualQuantity"}[individual layer] to the catalogue — an individual quantity carries the particular in its type, and `dedicatedFor` says which catalogue entry that particular's readings instantiate. In the terms of the foundations chapter's ontological square, it is Lowe's dispositional route to exemplification: up the _instantiated by_ edge, then across the top.
:::

:::proof "def_dedicatedFor"
`dedicatedTo` applied to `Sorted.sortOf o`.
:::

:::theorem "thm_dedicatedFor_congr" (parent := "spine_dedicated") (lean := "PropertyKindCalculus.KindOfProperty.dedicatedFor_congr") (tags := "proved")
*Two objects of one sort dedicate to one kind.* The catalogue entry cannot tell two rovers apart, and is not supposed to: individuation is the object index's job, where combining quantities across the two is a compile-time type error. This is the load-bearing half of the corrected §20 reading — dedication to the sort, individuation by the object.
:::

:::proof "thm_dedicatedFor_congr"
Congruence: the two dedications differ only in the sort argument, and the hypothesis equates the sorts.
:::

:::theorem "thm_dedicated_distinct_kind" (parent := "spine_dedicated") (lean := "PropertyKindCalculus.DedicatedKind.distinct_of_kind") (tags := "capstone, proved") (priority := "high")
*Same sort and component, a different kind-of-property: a distinct dedicated kind.* This is the principled volumetric-versus-gravimetric distinctness. Both water contents are _"Soil — Water"_, but volume fraction and mass fraction are different {uses "def_kindOfProperty"}[kinds-of-property], so the {uses "def_dedicatedKind"}[dedicated kinds] differ — with the sort and component held identical, and without appeal to any hand-chosen identity string. This is exactly the discrimination an OWL2 reasoner cannot phrase.
:::

:::proof "thm_dedicated_distinct_kind"
Assume the two dedicated kinds are equal; then their `kind` projections are equal by congruence, contradicting the hypothesis (`intro he; apply h; rw [he]`). The companion laws `distinct_of_sort` and `distinct_of_component` are the same one-line argument on the other two projections.
:::

:::theorem "thm_dedicated_distinct_component" (parent := "spine_dedicated") (lean := "PropertyKindCalculus.DedicatedKind.distinct_of_component") (tags := "proved")
*Same sort and kind, a different component: a distinct dedicated kind.* The water content and the air content of soil share their {uses "def_sortOfSystem"}[sort of system] and their {uses "def_kindOfProperty"}[kind-of-property], differing only in the {uses "def_component"}[component] — and that alone makes them distinct {uses "def_dedicatedKind"}[dedicated kinds].
:::

:::proof "thm_dedicated_distinct_component"
Congruence on the `component` projection, exactly as for `distinct_of_kind`.
:::
