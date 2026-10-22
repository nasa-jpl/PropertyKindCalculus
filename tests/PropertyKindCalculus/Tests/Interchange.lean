/-
# Validation probes — the SysML v2 interchange

The interchange's two halves are checked on the models the repository already carries:
the harvested ISO 80000-3 catalogue and the harmonic-oscillator requirements tutorial are
read back from their own JSON unchanged (`PkcModel.ofJsonString ∘ toJsonString`), their
citations all name declarations of the environment, and the element-form reader recovers
the DSL's conventions — keywords, redefinition chains, defaults, nested records, connection
ends, negative literals — from a hand-built element list (`Tests.Interchange.ApiJson`).
Both harvests are complete — no declaration in scope is skipped — and a scope with a kind
that cannot be evaluated and a unit whose kind is out of scope (`Partial`) harvests without
them and reports both. The full round trip through OpenSysML,
`read (api-json (emit (harvest))) = harvest`, needs the `sysml` converter and runs as
`scripts/roundtrip-sysml.sh`.
-/

module

public import PropertyKindCalculus.Interchange
public import PropertyKindCalculus.Iso80000.Part3
public import Tutorial.HarmonicOscillatorRequirements
public import PropertyKindCalculus.Tests.Interchange.ApiJson
meta import PropertyKindCalculus.Interchange
meta import PropertyKindCalculus.Iso80000.Part3
meta import Tutorial.HarmonicOscillatorRequirements

@[expose] public section Blanket

namespace PropertyKindCalculus.Tests.Interchange

open Lean PropertyKindCalculus.Interchange

-- The harvested catalogue: read back from its JSON unchanged, every citation honoured, the
-- catalogue's kinds and principles all present.
run_meta do
  let (m, skipped) ← Harvest.harvest #[`PropertyKindCalculus.Iso80000.Part3] "PKC_ISO80000_3"
  unless skipped.isEmpty do throwError "the catalogue harvest skipped declarations: {skipped}"
  unless m.kinds.length == 42 do throwError "expected 42 kinds, harvested {m.kinds.length}"
  unless m.principles.length ≥ 8 do throwError "expected the length principles"
  let some width := m.kind? "width" | throwError "no `width`"
  unless width.specializes == ["length"] do throwError "width should specialize length"
  unless width.principle == some "transverse" do throwError "width should carry its principle"
  unless width.catalogueItem == some "3-1.2" do throwError "width should cite item 3-1.2"
  unless width.dimension == [{ base := "length", num := 1, den := 1 }] do
    throwError "width should carry the dimension L"
  match PkcModel.ofJsonString m.toJsonString with
  | .ok m' => unless m' == m do throwError "JSON round trip changed the catalogue model"
  | .error e => throwError "JSON round trip failed: {e}"
  let missing ← Harvest.unverifiedCitations m
  unless missing.isEmpty do throwError "unverified citations: {missing}"
  unless (EmitSysml.emit m).length > 0 do throwError "empty DSL emission"

-- The tutorial's modules, relations and requirements.
run_meta do
  let (m, skipped) ← Harvest.harvest #[`Tutorial.HarmonicOscillator] "HarmonicOscillatorRequirements"
  unless skipped.isEmpty do throwError "the tutorial harvest skipped declarations: {skipped}"
  unless m.modules.length == 5 do throwError "expected 5 boundaries, harvested {m.modules.length}"
  unless m.relations.length == 2 do throwError "expected 2 relations, harvested {m.relations.length}"
  unless m.requirements.length == 7 do throwError "expected 7 requirements"
  let some b := m.modules.find? (·.name == "complianceBoundary") | throwError "no complianceBoundary"
  unless b.ports.length == 4 do throwError "complianceBoundary should have 4 ports"
  unless b.ports.all (fun p => m.kind? p.kind |>.isSome) do
    throwError "every port kind should be a harvested kind"
  unless m.modules.any (·.role == .specification) do throwError "a specification boundary is expected"
  match PkcModel.ofJsonString m.toJsonString with
  | .ok m' => unless m' == m do throwError "JSON round trip changed the tutorial model"
  | .error e => throwError "JSON round trip failed: {e}"
  let missing ← Harvest.unverifiedCitations m
  unless missing.isEmpty do throwError "unverified citations: {missing}"
  -- the generated Lean names every boundary and relation
  let lean := EmitLean.emit m
  unless (lean.splitOn "Provenance.Contract String String").length == 6 do
    throwError "generated module should define 5 contracts"
  unless (lean.splitOn "Provenance.Relation where").length == 3 do
    throwError "generated module should define 2 relations"

-- A declaration the harvester cannot read is skipped and reported, never dropped silently:
-- a kind that cannot be evaluated and a unit whose kind is out of scope each leave a
-- warning naming them, and the model carries neither.
namespace Partial
noncomputable def unreadableKind : KindOfProperty :=
  { id := Classical.choice ⟨"unreadable"⟩, scale := .ratio }
def readableKind : KindOfProperty := { id := "readable", scale := .ratio }
def strayUnit : PropertyKindCalculus.MetrologicalUnit :=
  { kind := Tutorial.HarmonicOscillator.complianceK, symbol := "m/N" }
end Partial

run_meta do
  let (m, skipped) ← Harvest.harvest #[`PropertyKindCalculus.Tests.Interchange.Partial] "Partial"
  unless m.kinds.map (·.name) == ["readableKind"] do
    throwError "only the readable kind should be harvested, got {m.kinds.map (·.name)}"
  unless m.units.isEmpty do throwError "a unit of an out-of-scope kind should be skipped"
  unless skipped.size == 2 do throwError "expected 2 skipped declarations, got {skipped}"
  unless skipped.any (fun w => w.startsWith "PropertyKindCalculus.Tests.Interchange.Partial.unreadableKind: value not read:") do
    throwError "the unreadable kind should be reported: {skipped}"
  unless skipped.any (· == "PropertyKindCalculus.Tests.Interchange.Partial.strayUnit: unit skipped: \
      its kind 'compliance' is not a harvested kind") do
    throwError "the stray unit should be reported: {skipped}"

-- What counts as checked evidence: a constructor of a Prop does; an axiom, data, and a missing
-- name do not. A theorem's proof is not visible from a `module`, so here it is reported as
-- unverifiable rather than accepted; `scripts/roundtrip-sysml.lean` verifies the real citations
-- from outside the module system.
run_meta do
  let env ← getEnv
  if let some why ← Harvest.notEvidence env ``PropertyKindCalculus.Iso80000.Part3.Edge.width_length then
    throwError "a constructor of a Prop is evidence, but: {why}"
  unless (← Harvest.notEvidence env ``Tutorial.HarmonicOscillator.compliance_bounded).isSome do
    throwError "a theorem's proof is not visible from a module; it must not pass silently"
  unless (← Harvest.notEvidence env ``propext).isSome do
    throwError "an axiom is not evidence"
  unless (← Harvest.notEvidence env ``Nat.add).isSome do
    throwError "data is not evidence"
  unless (← Harvest.notEvidence env ``instInhabitedNat).isSome do
    throwError "a data-valued instance is not evidence"
  unless (← Harvest.notEvidence env `No.Such.Decl).isSome do
    throwError "a missing declaration is not evidence"

-- Model text cannot end, or nest, the generated comment it lands in.
#guard EmitLean.commentText "a -/ b /- c\nd" == "a - / b / - c d"

-- A SysML v2 reserved word is written quoted, including the two that name no declaration
-- kind (`about`, `new`); a KerML-only word is a name in a `.sysml` file and stays bare.
#guard EmitSysml.ident "about" == "'about'"
#guard EmitSysml.ident "new" == "'new'"
#guard EmitSysml.ident "part" == "'part'"
#guard EmitSysml.ident "type" == "type"
#guard EmitSysml.ident "length" == "length"

end PropertyKindCalculus.Tests.Interchange

end Blanket
