/-
# Package-version role for the blueprint — `{version}[]`

Reads the PropertyKindCalculus package version from the parent package's
`lakefile.lean` (`version := v!"X.Y.Z"`) at *elaboration time*, and exposes it as
the inline Verso role `{version}[]`. The lakefile is the single source of truth,
kept in sync by `scripts/bump-version.sh`; because the blueprint reads that same
line every build, the published document's version can never drift from the source.

Mirrors the approach L4YAML uses in its Verso manual. Note the `lake clean` caveat:
Lake does not track the parent `lakefile.lean` as a dependency of this module, so a
version bump followed by an *incremental* blueprint build may show the stale cached
value — CI builds the document fresh, so the published version is always current;
locally, `lake clean` in `blueprint/` forces a refresh after a bump.
-/
import Lean
import VersoManual

open Lean Elab
open Verso.Doc.Elab
open Verso.Genre Manual

namespace PropertyKindCalculusBlueprint.Version

/-- Locate the parent PropertyKindCalculus package root — the directory holding the
`lakefile.lean` that declares the version. The blueprint may be built from its own
directory (`blueprint/`, so the root is `..`) or from the repo root, so both are
tried; `blueprint/` itself has a `lakefile.toml`, not `.lean`, so it never matches. -/
def resolveRepoRoot : IO System.FilePath := do
  let cwd ← IO.currentDir
  let candidates := #[cwd, cwd / ".."]
  for c in candidates do
    if ← (c / "lakefile.lean").pathExists then return c
  throw (IO.userError s!"resolveRepoRoot: cannot find PropertyKindCalculus lakefile.lean from {cwd}")

/-- The declared package version, read from `lakefile.lean`'s `version := v!"X.Y.Z"`
line — the single source of truth (`scripts/bump-version.sh` keeps it authoritative). -/
def readVersion : IO String := do
  let txt ← IO.FS.readFile ((← resolveRepoRoot) / "lakefile.lean")
  for line in txt.splitOn "\n" do
    match line.splitOn "version := v!\"" with
    | _ :: rest :: _ =>
      match rest.splitOn "\"" with
      | ver :: _ => return ver
      | _ => pure ()
    | _ => pure ()
  throw (IO.userError "readVersion: no `version := v!\"…\"` line in lakefile.lean")

elab "pkc_version_str" : term => do
  return Lean.mkStrLit (← readVersion)

/-- The declared package version, e.g. `"0.1.0"`. -/
def versionStr : String := pkc_version_str

/-- Inline role: `{version}[]` expands to the declared package version. -/
@[role]
def version : RoleExpanderOf Unit
  | (), _ => ``(Verso.Doc.Inline.text PropertyKindCalculusBlueprint.Version.versionStr)

end PropertyKindCalculusBlueprint.Version
