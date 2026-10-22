import PropertyKindCalculus.Interchange
import PropertyKindCalculus.Iso80000.Part3
import Tutorial.HarmonicOscillatorRequirements
open Lean PropertyKindCalculus.Interchange

/-! Harvest two scopes into the PKC DSL — the ISO 80000-3 catalogue (the kind layer) and the
harmonic-oscillator requirements tutorial (modules, relations, requirements) — writing each as
`.lake/build/sysml/<Package>.sysml` beside its `PkcModel` JSON. Run with
`lake env lean scripts/emit-sysml.lean` after `lake build Interchange Iso80000 Tutorial`. -/

def emitScope (scope : Array Name) (pkg : String) : MetaM Unit := do
  let (m, warnings) ← Harvest.harvest scope pkg
  for w in warnings do IO.eprintln s!"{pkg}: {w}"
  IO.FS.createDirAll ".lake/build/sysml"
  let sysml := s!".lake/build/sysml/{pkg}.sysml"
  let json := s!".lake/build/sysml/{pkg}.pkc.json"
  IO.FS.writeFile sysml (EmitSysml.emit m)
  IO.FS.writeFile json m.toJsonString
  IO.println s!"wrote {sysml}: {m.kinds.length} kind(s), {m.edges.length} edge(s), \
    {m.modules.length} module(s), {m.relations.length} relation(s), \
    {m.requirements.length} requirement(s), {m.tapes.length} tape(s); \
    {warnings.size} skipped declaration(s)"

run_meta do
  emitScope #[`PropertyKindCalculus.Iso80000.Part3] "PKC_ISO80000_3"
  emitScope #[`Tutorial.HarmonicOscillator] "HarmonicOscillatorRequirements"
