# PropertyKindCalculus

A Lean 4 formalization of **Dybkær's *[An Ontology on Property for Physical,
Chemical, and Biological Systems](References/ontology-on-property.pdf)*** (2009),
extended with **Flater's full tracking of kinds of quantities**
([NIST Technical Note 1943](References/NIST.TN.1943.pdf), Appendix C).

It continues a line of machine-checkable metrology modeling 
from the Object Management Group (OMG) Systems Modeling Language (SysML)
 Conceptual model of Quantities, Units, Dimensions and Values (QUDV),
then an OML/OWL2 metrology vocabulary grounded in Dybkær — and is the first in
which the *quantity calculus itself*, not just the taxonomy around it, is a
checked artifact. OWL2 captures the taxonomy (specialization, instantiation,
dimensional factoring) but is structurally unable to express the calculus: the
partial kind-interaction algebra, scale-type operator gating, extensivity, unit
conversion, or any algebraic *law* as a provable theorem. Lean has all of it
natively.

The full rationale — the QUDV → OML lineage and how each construct maps into
Lean's type system — is in the [design blueprint](blueprint/) ("Why a calculus,
not a taxonomy").

## On the name

The calculus is over **kinds of *property*** — Dybkær's root notion (§6.19),
which spans nominal, ordinal, and quantitative kinds alike. A **kind of
quantity** is the special case whose scale carries magnitude (§13.3.1, in Lean
`IsQuantity k := k.scale.HasMagnitude`); the `QuantityKind` of QUDT and SysML v2
is therefore *subsumed here* — as a scale-gated leaf of the property-kind spine,
not as its root. The name keeps "Property" in front to make that genus visible
(and to avoid reading the bare word "kind" in its type-theoretic sense). So the
project is broader than a quantity calculus by construction, with quantity kinds
as its motivating special case.

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
| `PropertyKindCalculus` (default target) | `PropertyKindCalculus/` | the exportable ontological spine | `lake build` |
| `Examples` | `examples/` | worked examples (`PropertyKindCalculus.Examples.*`) | `lake build Examples` |

A downstream project depends on the package and imports selectively:

```lean
require PropertyKindCalculus from git "…/PropertyKindCalculus" @ "main"   -- in the consumer lakefile

import PropertyKindCalculus                       -- core spine only, no examples
-- import PropertyKindCalculus.Examples           -- opt in to the examples too
```

The **core spine is Mathlib-free** and builds with only the Lean toolchain. The
dimension/coherence layer (PhysLib `Dimension` as a forgetful functor) and the
soil-moisture *model* pull in PhysLib + Mathlib and land as further libraries
once the spine stabilizes.

## Design blueprint

A [Verso](https://github.com/leanprover/verso) /
[verso-blueprint](https://github.com/leanprover/verso-blueprint) design document
lives in [`blueprint/`](blueprint/). It records the **proved spine** (each node
linked to a real, sorry-free declaration here, so its status is read from the
checked library) and the **capstone theorems we plan to provide** — the
dimension-1 disambiguation, dimensional coherence (`dim` is a homomorphism), the
Flater interaction algebra, unit-conversion round-trip, and extensivity — with a
generated dependency graph and status summary. It is a **separate Lake package**
(it pulls in Verso) so a plain `import PropertyKindCalculus` stays lightweight:

```bash
cd blueprint
lake update && lake build   # type-check the doc + its Lean links
./scripts/ci-pages.sh       # render both outputs + print absolute paths to open
```

Open either `_out/blueprint/html-single/index.html` (one self-contained page) or
`_out/blueprint/html-multi/index.html` (the full per-chapter site) directly as a
file — `ci-pages.sh` post-processes `html-multi` so chapter navigation works over
`file://`. Search and the dependency graph need an HTTP server (`python3 -m
http.server 8000 -d "$PWD/_out/blueprint/html-multi"`). See
[`blueprint/README.md`](blueprint/README.md) for details.

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
| `PropertyKindCalculus.Examples.MiniLengthWidth` (in the `Examples` lib) — length/width/height as checked facts | — | ✅ |
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
