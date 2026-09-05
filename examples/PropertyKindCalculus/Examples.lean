/-
# PropertyKindCalculus.Examples

Aggregator for the worked examples. These live in a **separate library**
(`Examples`, source tree `examples/`) so that downstream users can depend on the
core `PropertyKindCalculus` library without pulling in any example code, or import the
examples explicitly via `import PropertyKindCalculus.Examples`.

This module is also the library's Lake **root**, so its import closure is exactly what the
doc-gen4 API site renders (`scripts/build-api-docs.sh`). It therefore aggregates every
**Mathlib-free** example. The tape/LUT codegen demos (`TapeCodegen*`, `TapeCse*`,
`LmStepCodegenDemo`) are deliberately *not* imported here: they reach the `Torch` layer, whose
`TapeCarrier`/`LutCarrier` import Mathlib, and pulling that into the doc closure would make
doc-gen4 generate HTML for all of Mathlib. They are still built by `lake build Examples`, which
works off the library's globs rather than its root.
-/

import PropertyKindCalculus.Examples.MiniLengthWidth
import PropertyKindCalculus.Examples.MiniDedicatedKind
import PropertyKindCalculus.Examples.MiniExamination
import PropertyKindCalculus.Examples.MiniValueScale
import PropertyKindCalculus.Examples.MiniUnit
import PropertyKindCalculus.Examples.MiniExtensivity
import PropertyKindCalculus.Examples.MiniObjectTypes
import PropertyKindCalculus.Examples.MiniQuantity
import PropertyKindCalculus.Examples.MiniVectorQuantity
import PropertyKindCalculus.Examples.MiniRefinement
import PropertyKindCalculus.Examples.MiniClassification
import PropertyKindCalculus.Examples.MiniWriteOnce

-- The kinded AVS forward model and the `@[pkc_math]` rendering demo. Both are Mathlib-free, and
-- both carry `@[pkc_math]`-rendered docstrings, so they are what the API site exists to show.
import PropertyKindCalculus.Examples.AvsForward
import PropertyKindCalculus.Examples.DocGenMathDemo
