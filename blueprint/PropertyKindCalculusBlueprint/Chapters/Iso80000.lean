import Verso
import VersoManual
import VersoBlueprint
-- The catalogue nodes link real declarations, so this chapter imports the
-- (Mathlib-free) references module of the `Iso80000` library.
import PropertyKindCalculus.Iso80000.References

open Verso.Genre
open Verso.Genre.Manual
open Informal

#doc (Manual) "ISO/IEC 80000 — The Standards Catalogue" =>

The quantity-kinds and units specified here are grounded against the international
standard series ISO/IEC 80000, _Quantities and units_. That series is *licensed
and copyrighted*: no normative content from it is reproduced in this work. What is
recorded is the _citable identity_ of each part — body, number, part, edition, and
publication date — so that every catalogued quantity-kind or unit can name its
exact source. This chapter specifies that references layer; the chapters that
follow specify one part's quantity-kinds and units at a time, each added as
coverage of that part becomes available.

# The references layer (citation metadata only)

:::group "iso80000"
The series is a joint ISO/IEC project, and this work catalogues thirteen of its
parts. Each part is issued under one body — in the catalogued copies parts 6
(_Electromagnetism_) and 13 (_Information science and technology_) are IEC and the
rest are ISO — and carries an edition designation and a publication date on its
cover. Recording these as typed data lets a downstream model render or
audit a citation rather than carry it as free text.
:::

:::definition "def_standardRef" (parent := "iso80000") (lean := "PropertyKindCalculus.Iso80000.StandardRef")
A _standard reference_ `StandardRef` is the bibliographic identity of one part: its
publishing body (ISO or IEC), the series number ($`80000`), the part number, the
edition designation as printed, the publication date, and the part's English title.
It carries *no* normative content — only what is needed to _cite_ the source. Its
`cite` renders the conventional form, e.g. `IEC 80000-6, Edition 2.0, 2022-11`.
:::

:::proof "def_standardRef"
Realized as `structure StandardRef` (Mathlib-free) with a `StandardBody`
(`ISO`/`IEC`) field and the printed edition, date, and title as strings, plus
`designation` (`ISO 80000-3`) and `cite` (the full reference). The values are read
off each licensed part's cover page; nothing normative is transcribed.
:::

:::definition "def_standardCatalogue" (parent := "iso80000") (lean := "PropertyKindCalculus.Iso80000.catalogue")
The _catalogue_ is the list of the thirteen catalogued parts in part order, each a
{uses "def_standardRef"}[standard reference]. It is the single place this work
names _which editions_ of ISO/IEC 80000 the catalogued quantity-kinds and units are
grounded against, so the grounding is auditable rather than implicit.
:::

:::proof "def_standardCatalogue"
Realized as `catalogue : List StandardRef`, the thirteen definitions `iso80000_1` …
`iec80000_13` (with `iec80000_6` and `iec80000_13` the IEC-published parts). The
edition is "Second edition" for every part except those two, both "Edition 2.0"; the
dates are the cover dates of the licensed copies.
:::
