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

def main (args : List String) : IO UInt32 :=
  Informal.PreviewManifest.blueprintMainWithPreviewData
    (%doc PropertyKindCalculusBlueprint.Blueprint)
    args
    (extensionImpls := by exact extension_impls%)
    (config := { toHtmlConfig := { toHtmlAssets := { extraCss := [versoMarginNoteCounterFix] } } })
