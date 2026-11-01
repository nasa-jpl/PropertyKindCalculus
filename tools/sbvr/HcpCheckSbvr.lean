module

public import Tools.HcpCheck
public import SBVR.Record
public import SBVR.Hcp

/-!
# `hcp-check-sbvr` — `hcp-check` with SBVR.lean in process (TOOLS.md §6 Q1)

The checker is `Tools.HcpCheck`, the root package's module; what `--sbvr` observes is answered here
by the library `sbvr-check` is built from — `SBVR.Record.load`, `ChainFile.run`, `SBVR.Hcp.synopsis`
— shaped as the binary prints it (`SbvrCheck.render`, `checkBody`), so the committed renderings are
the same bytes under either form. `renderObs_clean` and `checkObs_clean`: an observation exits 0
exactly when the library reports no gap, no finding.
-/

public section

namespace HcpCheckSbvr
open Tools.HcpCheck

/-- `sbvr-check render CHAIN v`, from the loaded chain: exit 0 with the synopsis when every term and
rule is sayable at the step, 1 with the rules' gaps on stderr, 2 when `v` names no vocabulary. -/
def renderObs (F : SBVR.Yaml.ChainFile) (v : String) : UInt32 × String × String :=
  match SBVR.Hcp.synopsis F.chain F.named v F.rules with
  | none => (2, "", s!"error: no project vocabulary {v}\n")
  | some (s, gaps) =>
    (if gaps.isEmpty then 0 else 1, s,
      String.join ((gaps.filter (·.startsWith "rule ")).map fun g => s!"gap: {g}\n"))

/-- `sbvr-check CHAIN`, from the loaded chain: each result line, exit 1 on a finding. -/
def checkObs (F : SBVR.Yaml.ChainFile) : UInt32 × String × String :=
  let (ls, ok) := F.run
  (if ok then 0 else 1, String.join (ls.map (· ++ "\n")), "")

theorem renderObs_clean (F : SBVR.Yaml.ChainFile) (v : String) :
    (renderObs F v).1 = 0 ↔ ∃ s, SBVR.Hcp.synopsis F.chain F.named v F.rules = some (s, []) := by
  unfold renderObs
  cases h : SBVR.Hcp.synopsis F.chain F.named v F.rules with
  | none => simp
  | some p =>
    obtain ⟨s, gaps⟩ := p
    cases gaps <;> simp

theorem checkObs_clean (F : SBVR.Yaml.ChainFile) : (checkObs F).1 = 0 ↔ F.run.2 = true := by
  unfold checkObs
  cases F.run with
  | mk ls ok => cases ok <;> simp

/-- The tool: the chain at `root` loaded by the library for each answer (`load` reports a malformed
chain on stderr itself and the exit code is the answer). -/
def tool (root : System.FilePath) : SbvrTool where
  check := do
    match ← SBVR.Record.load (root / sbvrChain).toString with
    | .error c => pure (c, "", "")
    | .ok F => pure (checkObs F)
  render v := do
    match ← SBVR.Record.load (root / sbvrChain).toString with
    | .error c => pure (c, "", "")
    | .ok F => pure (renderObs F v)

end HcpCheckSbvr

def main (args : List String) : IO UInt32 :=
  Tools.HcpCheck.mainWith "hcp-check-sbvr" (some HcpCheckSbvr.tool) args
