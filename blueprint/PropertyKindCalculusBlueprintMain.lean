import VersoManual
import VersoBlueprint.PreviewManifest
import PropertyKindCalculusBlueprint.Blueprint

open Verso Doc
open Verso.Genre Manual

def main (args : List String) : IO UInt32 :=
  Informal.PreviewManifest.blueprintMainWithPreviewData
    (%doc PropertyKindCalculusBlueprint.Blueprint)
    args
    (extensionImpls := by exact extension_impls%)
