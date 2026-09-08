/-
# ISO 80000 validation probes — index

The catalogue tier's probes: the two Dimension-library censuses — `#kind_examination_coverage`
(the model template's M6) and `#kind_dimensional_coverage` (M10) — pinned over every part of
ISO 80000 as **records**, so that a change in what the catalogue individuates or how it
dimensions a kind is a visible diff rather than a silent drift. Gates (`_clean`) are pinned only
over the parts they pass on; a record of a violation is a finding awaiting a maintainer's
decision, not a blessing of it (`METHODOLOGY_TEMPLATES.md` §5). The probe is generated —
`scripts/gen-iso80000-coverage.py` runs the censuses and writes it from their output, and
`--check` shows how a catalogue change moved the records before anyone re-pins them.
-/
import PropertyKindCalculus.Tests.Iso80000.Coverage
