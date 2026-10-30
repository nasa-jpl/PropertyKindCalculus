import PropertyKindCalculus.Interchange
import PropertyKindCalculus.Iso80000.Part3
import PropertyKindCalculus.Iso80000.Part4
import ForPhysLib.ClassicalMechanics
import HCP
open Lean PropertyKindCalculus.Interchange

/-! The kind catalogue the PhysLib contributor's ladder reads, as the SBVR.lean catalogue file
`HCP/sbvr/kinds.yaml` that `HCP/sbvr/physlib-contributor.yaml` adopts its quantity terms from
(SBVR.lean docs/QUANTITIES.md §2–3: `kinds:` with `id`, `scale`, `specializes`).

The kinds are harvested (`Harvest.harvestKindCatalogue`: the kind and specialization readers of
`Harvest.harvest`, the reader behind `scripts/emit-sysml.lean`, and no other) from the
scopes the lessons read their kinds from: ISO 80000 parts 3 and 4, ForPhysLib's classical
mechanics and the lessons' own `KindOfProperty`s (L5's viscous damping constant). Two
declarations of one kind id (ForPhysLib's `massK` is `Part4.mass.kind`) are one catalogue entry;
two declarations of one id with different scales are an error, and so is any kind declaration or
specialization witness in scope the harvester had to skip (the catalogue would silently lack a kind
or an edge); a contract, unit, module or requirement it cannot read is not this catalogue's concern. Entries are sorted by id so the
file is reproducible.

Run with `lake env lean scripts/emit-sbvr-kinds.lean` after
`lake build Interchange Iso80000 ForPhysLib HCP`; with `SBVR_KINDS_CHECK=1` set, the catalogue on
disk must equal the harvest or the script exits 1 (the CI gate). -/

def scaleName : Scale → String
  | .nominal => "nominal" | .ordinal => "ordinal" | .interval => "interval" | .ratio => "ratio"

def yamlQuote (s : String) : String :=
  "\"" ++ (s.replace "\\" "\\\\").replace "\"" "\\\"" ++ "\""

structure Entry where
  id : String
  scale : Scale
  specializes : List String
deriving Inhabited

def catalogueYaml (scopes : Array Name) : MetaM String := do
  let (m, warnings) ← Harvest.harvestKindCatalogue scopes "PhysLibKinds"
  -- a kind declaration or specialization the harvester skipped is one the catalogue would silently lack: refuse
  for w in warnings do IO.eprintln s!"PhysLibKinds: {w}"
  if !warnings.isEmpty then
    throwError s!"{warnings.size} kind declaration(s) or specialization(s) in scope were skipped; the catalogue would be incomplete"
  let idOf : Std.HashMap String String :=
    m.kinds.foldl (init := {}) fun acc k => acc.insert k.name k.id
  let mut entries : Std.HashMap String Entry := {}
  for k in m.kinds do
    let parents := k.specializes.filterMap fun n => idOf[n]?
    match entries[k.id]? with
    | some e =>
      if e.scale != k.scale then
        throwError s!"kind {yamlQuote k.id} is declared at two scales ({scaleName e.scale}, {scaleName k.scale})"
      entries := entries.insert k.id { e with specializes := e.specializes ++ parents.filter (!e.specializes.contains ·) }
    | none => entries := entries.insert k.id { id := k.id, scale := k.scale, specializes := parents }
  let sorted := (entries.toList.map (·.2)).toArray.qsort (fun a b => a.id < b.id)
  let mut out := "# The kind catalogue of the PhysLib contributor's ladder — written by\n# `lake env lean scripts/emit-sbvr-kinds.lean` from the harvested kinds; do not edit.\nkinds:\n"
  for e in sorted do
    out := out ++ s!"  - id: {yamlQuote e.id}\n    scale: {scaleName e.scale}\n"
    let ps := (e.specializes.filter (· != e.id)).toArray.qsort (· < ·)
    if !ps.isEmpty then
      out := out ++ "    specializes:\n"
      for p in ps do out := out ++ s!"      - {yamlQuote p}\n"
  return out

run_meta do
  let path := "HCP/sbvr/kinds.yaml"
  let yaml ← catalogueYaml #[`PropertyKindCalculus.Iso80000.Part3, `PropertyKindCalculus.Iso80000.Part4,
    `ForPhysLib.ClassicalMechanics, `HCP]
  let n := (yaml.splitOn "\n  - id: ").length - 1
  if (← IO.getEnv "SBVR_KINDS_CHECK").isSome then
    let onDisk ← (IO.FS.readFile path).toBaseIO
    match onDisk with
    | .ok s =>
      if s == yaml then IO.println s!"ok   {path} is the harvest ({n} kinds)"
      else throwError s!"{path} is stale: rerun `lake env lean scripts/emit-sbvr-kinds.lean`"
    | .error _ => throwError s!"{path} is missing: run `lake env lean scripts/emit-sbvr-kinds.lean`"
  else
    IO.FS.writeFile path yaml
    IO.println s!"wrote {path}: {n} kind(s)"
