/-
# Package-version role for the blueprint — `{version}[]`

The declared PropertyKindCalculus version, exposed as the inline Verso role
`{version}[]`. `lakefile.lean`'s `version := v!"X.Y.Z"` is the single source of truth;
the literal below mirrors it. `scripts/bump-version.sh` writes both sites in one step
and refuses to bump when they disagree, and `scripts/check-doc-pins.py` gates the
agreement in CI ahead of the Lean build — so the published document's version cannot
drift from the package's.

Why a mirrored literal and not a read of the lakefile: Lake's trace for a module is its
own source, its imports' artifacts, the toolchain, the platform, and the library's
`leanOptions` (`Lake/Build/Module.lean`, `Module.recBuildLean`). A version obtained
*while this module elaborates* — by reading the file, by `include_str`, or by calling
into Lake — is in none of them, so the `.olean` keeps whatever value it was first built
with and no later bump gives Lake a reason to redo it. Of the two channels Lake does
watch, `leanOptions` is library-granular (a `-D` carrying the version re-elaborates
every module in the package on every bump), while source text is per-module: a literal
rebuilds this module, the document that quotes it, and nothing else.
-/
import Lean
import VersoManual

open Lean Elab
open Verso.Doc.Elab
open Verso.Genre Manual

namespace PropertyKindCalculusBlueprint.Version

/-- The declared package version, mirroring `lakefile.lean`'s `version := v!"X.Y.Z"`.
Both sites are written by `scripts/bump-version.sh` and their agreement is gated by
`scripts/check-doc-pins.py`; the line shape is what those two match on, so keep the
literal on one line, starting at column 0. -/
def versionStr : String := "0.112.0"

/-- Inline role: `{version}[]` expands to the declared package version. -/
@[role]
def version : RoleExpanderOf Unit
  | (), _ => ``(Verso.Doc.Inline.text PropertyKindCalculusBlueprint.Version.versionStr)

end PropertyKindCalculusBlueprint.Version
