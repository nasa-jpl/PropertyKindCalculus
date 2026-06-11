# KindCalculus

A Lean 4 formalization of **Dybkær's *[An Ontology on Property for Physical,
Chemical, and Biological Systems](References/ontology-on-property.pdf)*** (2009),
extended with **Flater's full tracking of kinds of quantities**
([NIST Technical Note 1943](References/NIST.TN.1943.pdf), Appendix C).

## Why formalize the ontology in Lean rather than OWL/OML?

The author's prior metrology work modelled VIM concepts in OML (OWL2). OWL2
(SROIQ) faithfully captures the **taxonomy** — specialization, instantiation,
dimensional factoring — but is structurally unable to capture the **calculus**:

| Construct | OWL2 / OML | Lean |
|---|---|---|
| kind ⊑ kind, `Instantiates`, `HasUnit`, `Characterizes` | ✅ subClassOf, roles, punning | ✅ relations; some become *type indices* |
| dimension arithmetic (`M²/M`, `dim(a·b)=dim a + dim b`) | ❌ no datatype arithmetic | ✅ ordinary functions |
| interaction algebra (`torque × angle = work`) | ❌ role chains are binary, regular, no arithmetic side-conditions | ✅ `KMul` class + coherence proof field |
| scale-type operator gating (which of `= < + ×` are *defined*) | ❌ DL has no operations | ✅ scale-indexed typeclasses |
| extensivity (`value(whole) = Σ value(parts)`) | ❌ no quantified arithmetic | ✅ a `∀`-theorem |
| unit = number × reference; `convert` = ratio | ❌ no arithmetic | ✅ `def` + round-trip theorem |
| meta-theorems (⊑ is a partial order; `dim` is a homomorphism) | ❌ a reasoner checks consistency, not laws | ✅ theorems — the point |

The recurring gap is **arithmetic + operations + definedness-conditions + laws +
proofs** — exactly what makes a quantity *calculus* a calculus.

## Representational conventions

* **Meta-concepts** ("what it is to be a kind-of-quantity") → Lean
  `structure`/`class`.
* **Specific kinds** (length, mass, vwc) → **values** of those structures, so
  applications extend the ontology by writing `def`s (open-world), mirroring how
  OML *declares* concepts. A fixed `inductive` would not be extensible.
* **Individual quantities** ("the width of this pencil") → **terms** of the
  quantity type. An individual *instantiates* its kind; it is **not** a subtype.
* **OML relations** map directly: `GeneralUnitaryQuantity`→`KindOfProperty`,
  `Specializes`→`Specializes`, `IndividualUnitaryQuantity`→`IndividualProperty`,
  `HasUnit`/`Instantiates`→ the `u`/`kind` indices.
* **Traceability**: every definition cites Dybkær by section (`§x.y`) or Flater
  by section, so the formalization can be audited against the source.

## Libraries and how to consume them

The package ships two libraries so the core is exportable on its own:

| Library | Source tree | Contents | `lake build` |
|---|---|---|---|
| `KindCalculus` (default target) | `KindCalculus/` | the exportable ontological spine | `lake build` |
| `Examples` | `examples/` | worked examples (`KindCalculus.Examples.*`) | `lake build Examples` |

A downstream project depends on the package and imports selectively:

```lean
require KindCalculus from git "…/KindCalculus" @ "main"   -- in the consumer lakefile

import KindCalculus                       -- core spine only, no examples
-- import KindCalculus.Examples           -- opt in to the examples too
```

The **core spine is Mathlib-free** and builds with only the Lean toolchain. The
dimension/coherence layer (PhysLib `Dimension` as a forgetful functor) and the
soil-moisture *model* pull in PhysLib + Mathlib and land as further libraries
once the spine stabilizes.

## References

The primary sources are vendored under [`References/`](References/) so the
docstrings' `§x.y` citations resolve to a local copy:

* [`References/ontology-on-property.pdf`](References/ontology-on-property.pdf) —
  René Dybkær, *An Ontology on Property for Physical, Chemical, and Biological
  Systems* (2009).
* [`References/NIST.TN.1943.pdf`](References/NIST.TN.1943.pdf) — David Flater,
  *Architecture for Software-Assisted Quantity Calculus*, NIST Technical Note
  1943 (2016).

## Roadmap (faithful to Dybkær's chapter structure)

Status: ✅ built & proved · 🚧 next · ⬜ planned

| Module | Source | Status |
|---|---|---|
| `Foundations` — system, object | Dybkær Ch. 3 | ✅ |
| `Scale` — operator-based scale types + monotonicity meta-thm | Ch. 12 (Fig. 12.21) | ✅ |
| `Kind` — kind-of-property / -quantity + scale divisions | Ch. 6, §13.2–3 | ✅ |
| `Specialization` — `Specializes` closure (preorder) + comparability | OML / §6 | ✅ |
| `KindCalculus.Examples.MiniLengthWidth` (in the `Examples` lib) — length/width/height as checked facts | — | ✅ |
| `Examination` — principle / method / procedure (as defining aspects) | Ch. 7, 14 | 🚧 |
| `PropertyValue` + `ValueScale` — number × reference; scales | Ch. 9, 16, 10, 17 | ⬜ |
| `Unit` — metrological unit = *chosen reference quantity of a kind* | Ch. 18, §13.3.3 | ⬜ |
| `Dimension` — PhysLib `Dimension` as forgetful functor (+ coherence) | Ch. 19 | ⬜ (PhysLib) |
| `Interaction` — `KMul`/`KDiv`, dimensional coherence | Flater App. C | ⬜ |
| `Extensivity` — extensive / conditionally extensive kinds | §13.5 | ⬜ |
| `DedicatedKind` — kind × system × component | Ch. 20 | ⬜ |
| `Model.SI` — SI base kinds, verified well-formed | — | ⬜ |
| `Model.SoilMoisture` — vwc/gwc/permittivity/reflectivity/… | — | ⬜ |

## What builds today

`lake build` compiles the spine and the worked example with **no `sorry`**,
proving: `ScaleType` is a linear order; operator availability is monotone in
scale; `Specializes` is a preorder; mutual comparability is reflexive/symmetric;
and (in the example) that `width`/`height` are distinct sub-kinds of `length`,
mutually comparable, with "the width of a pencil" modelled as an instance.
