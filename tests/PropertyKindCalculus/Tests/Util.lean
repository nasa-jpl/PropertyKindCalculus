/-
# Validation probes — shared evaluation helpers

Helpers the emitter probes (`KindGraphD2`, `ModuleCard`, `IngestCard`, `KindLedger`) use
to pin generated text. Defined once here so a probe imports the helper instead of copying
it; a change to a helper's meaning happens in one place for every probe. Nothing here is a
probe — the file guards no requirement and the tier indices do not list it.
-/

module

@[expose] public section Blanket

namespace PropertyKindCalculus.Tests

/-- Does `sub` occur in `s`? Evaluation-only probe helper. -/
def hasSub (s sub : String) : Bool := (s.splitOn sub).length > 1

end PropertyKindCalculus.Tests

end Blanket
