/-
Emit the per-declaration index blocks as JSON, for `scripts/inject-index-docs.py`.

Run from the repository root:

    lake env lean scripts/emit-index-json.lean

and it writes `.lake/build/pkc-index.json`. `scripts/build-api-docs.sh` does this between generating
the doc-gen4 HTML and injecting into it.

A *script* rather than a `lean_exe` on purpose. The blocks depend on the whole imported environment,
so an executable would have to `importModules` at runtime and drive `CoreM` by hand — machinery whose
only purpose would be to reproduce what `lake env lean` already does. It also always runs: an
executable's output would be a build artefact Lake does not track, so a cached rebuild could leave a
stale JSON beside fresh HTML, which is exactly the failure mode `build-api-docs.sh` already documents
for doc-gen4's own `*_built` markers.
-/
import PropertyKindCalculus.IndexPage

open Lean PropertyKindCalculus.Index

-- No `set_option maxHeartbeats` here on purpose: the harvest grants itself its allowance
-- (`Index.withHarvestBudget`), so every surface gets the same treatment and none has to know.
run_meta do
  let json ← indexJson #[`PropertyKindCalculus]
  let out := ".lake/build/pkc-index.json"
  IO.FS.writeFile out json.pretty
  let n := match json with
    | .obj kvs => kvs.size
    | _        => 0
  IO.println s!"wrote {out}: {n} declaration block(s)"
