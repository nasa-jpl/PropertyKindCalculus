import PropertyKindCalculus.Interchange
import PropertyKindCalculus.Iso80000.Part3
import Tutorial.HarmonicOscillatorRequirements
open Lean PropertyKindCalculus.Interchange

/-! The round trip through OpenSysML, checked by content: for each scope,
`ApiJson.read (api-json (EmitSysml.emit (Harvest.harvest scope))) = Harvest.harvest scope`.
`scripts/roundtrip-sysml.sh` runs the emission and the conversion first; this script reads
`.lake/build/sysml/<Package>.api.json` back and compares, failing on the first difference. -/

def check (scope : Array Name) (pkg : String) : MetaM Unit := do
  let (h, skipped) ← Harvest.harvest scope pkg
  for w in skipped do IO.eprintln s!"{pkg}: harvest: {w}"
  let text ← IO.FS.readFile s!".lake/build/sysml/{pkg}.api.json"
  match ApiJson.read text (some pkg) with
  | .error e => throwError "{pkg}: {e}"
  | .ok (r, warnings) =>
    for w in warnings do IO.eprintln s!"{pkg}: {w}"
    if r == h then
      IO.println s!"{pkg}: round trip agrees — {h.kinds.length} kind(s), {h.edges.length} edge(s), \
        {h.modules.length} module(s), {h.relations.length} relation(s), \
        {h.requirements.length} requirement(s), {h.tapes.length} tape(s)"
    else
      let diff := [("principles", h.principles == r.principles), ("kinds", h.kinds == r.kinds),
        ("edges", h.edges == r.edges), ("dedicated", h.dedicated == r.dedicated),
        ("units", h.units == r.units), ("modules", h.modules == r.modules),
        ("relations", h.relations == r.relations), ("requirements", h.requirements == r.requirements),
        ("tapes", h.tapes == r.tapes), ("matches", h.tapeMatches == r.tapeMatches)]
      throwError "{pkg}: round trip differs in {diff.filter (!·.2) |>.map (·.1)}"

run_meta do
  check #[`PropertyKindCalculus.Iso80000.Part3] "PKC_ISO80000_3"
  check #[`Tutorial.HarmonicOscillator] "HarmonicOscillatorRequirements"
