import VersoManual
import VersoBlueprint.PreviewManifest
import PropertyKindCalculusBlueprint.Blueprint

open Verso Doc
open Verso.Genre Manual

/--
Backport of verso PR #977 (upstream commit `a20c785b`, on `main` only): the margin-note
counter must be created inside `<main>`. Verso makes `<main>` a size query container
(`container: main / inline-size`, Html/Style.lean), and a query container applies CSS
*style containment*, which counters cannot cross — with the counter established on
`<body>` (Marginalia.css), each note's `counter-increment` finds no counter in scope,
starts its own, and every margin note and its in-text mark renders as "1". The reset
cannot sit on `<main>` itself either: a containment boundary blocks its own interior.
Upstream resets on `.content-wrapper`, and this rule is that fix verbatim.

Advancing the verso pin to `a20c785b` instead is blocked by the toolchain lockstep
(see lakefile.toml): that commit's own `lean-toolchain` is v4.34.0-rc2, two bumps past
this stack. Delete this override when the verso pin advances past #977.
-/
def versoMarginNoteCounterFix : String := r##"
.content-wrapper {
  counter-reset: margin-note-counter;
}
"##

/--
`extraCss` is set **directly on the `HtmlConfig`**, not through a nested
`toHtmlAssets := { … }`. The two are not interchangeable. `HtmlConfig extends HtmlAssets`
and overrides one inherited default — `features := .all` (Html/Config.lean), where
`HtmlAssets`'s own default is `.empty`. Supplying the parent record wholesale supplies
`features` along with it, so the child's override never applies and the document is built
with *no* `HtmlFeature`s: `.KaTeX` among them. Nothing fails. The pages still emit
`<code class="bp_math inline">…</code>` for every `$`…`` and the KaTeX render loop for them,
but `katex/katex.js` is never written and never linked, so the loop dies on
`Uncaught ReferenceError: katex is not defined` at its first node and all 553 math elements
stand as raw TeX. Naming `extraCss` here keeps the `HtmlConfig` defaults intact.
-/
def main (args : List String) : IO UInt32 :=
  Informal.PreviewManifest.blueprintMainWithPreviewData
    (%doc PropertyKindCalculusBlueprint.Blueprint)
    args
    (extensionImpls := by exact extension_impls%)
    (config := { toHtmlConfig := { extraCss := [versoMarginNoteCounterFix] } })
