/-
# Worked examples — the ISO/IEC 80000 references catalogue

The catalogue renders citations by name and version (e.g. `IEC 80000-6, Edition 2.0,
2022-11`) — no normative content, only the citable identity of each licensed part.

Part-specific examples live in the sibling per-part modules
(`PropertyKindCalculus.DimensionExamples.Iso80000.Part3`, …), mirroring the `Iso80000`
library's own per-part layout under `Iso80000/`.
-/

module

public import PropertyKindCalculus.Iso80000
meta import PropertyKindCalculus.Iso80000

@[expose] public section Blanket

namespace PropertyKindCalculus.Examples.Iso80000.References

open PropertyKindCalculus
open PropertyKindCalculus.Iso80000

-- citations render in the conventional `body number-part, edition, date` form
#guard iec80000_6.cite == "IEC 80000-6, Edition 2.0, 2022-11"
#guard iso80000_3.cite == "ISO 80000-3, Second edition, 2019-10"
#guard iso80000_3.designation == "ISO 80000-3"
-- all thirteen licensed parts are catalogued …
#guard catalogue.length == 13
#guard iec80000_13.cite == "IEC 80000-13, Edition 2.0, 2025-02"
-- … and parts 6 (Electromagnetism) and 13 (Information science) are the IEC-published ones.
example : iec80000_6.body = StandardBody.IEC := rfl
example : iec80000_13.body = StandardBody.IEC := rfl

end PropertyKindCalculus.Examples.Iso80000.References

end Blanket
