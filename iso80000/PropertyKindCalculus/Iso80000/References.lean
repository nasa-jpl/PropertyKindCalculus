/-
# ISO/IEC 80000 — references catalog (citation metadata only)

The *Quantities and units* series ISO/IEC 80000 is the international standard this
library organizes its quantity-kinds (QK) and units (U) against. The series is
**licensed and copyrighted**: no normative content is reproduced here. This module
records only the **citable identity** of each part — body, number, part, edition,
and publication date — so that a quantity-kind or unit can name its exact source,
in the form `IEC 80000-6, Edition 2.0, 2022-11`.

The metadata is read off each part's cover page. Editions and dates correspond to
the copies this work was developed against; parts 2 and 12 additionally carry a
corrected version (2021-11), whose base edition/date are recorded here.
-/

namespace PropertyKindCalculus.Iso80000

/-- The standards body under which a part of the 80000 series is published. The
series is a joint ISO/IEC project; each part is issued under one body — in the
catalogued copies, part 6 (Electromagnetism) is IEC and the rest are ISO. -/
inductive StandardBody where
  | ISO
  | IEC
deriving DecidableEq, Repr

/-- A **bibliographic reference** to a published standard — body, number, part,
edition, and date only. No normative content is carried; this records the citable
identity so a {quantity-kind} or {unit} can name its exact source. -/
structure StandardRef where
  /-- The publishing body (ISO or IEC). -/
  body : StandardBody
  /-- The series number — `80000`. -/
  number : Nat
  /-- The part number (e.g. `3` for *Space and time*). -/
  part : Nat
  /-- The edition designation as printed on the cover (e.g. "Second edition",
  "Edition 2.0"). -/
  edition : String
  /-- Publication date, year-month (e.g. "2019-10"). -/
  date : String
  /-- The part's official English title (the subtitle after "Quantities and units —"). -/
  title : String
deriving DecidableEq, Repr

namespace StandardRef

/-- The publishing body as its printed acronym. -/
def bodyName : StandardBody → String
  | .ISO => "ISO"
  | .IEC => "IEC"

/-- The bare designation, e.g. `ISO 80000-3` or `IEC 80000-6`. -/
def designation (r : StandardRef) : String :=
  bodyName r.body ++ " " ++ toString r.number ++ "-" ++ toString r.part

/-- A full citation in the conventional form, e.g.
`IEC 80000-6, Edition 2.0, 2022-11`. -/
def cite (r : StandardRef) : String :=
  r.designation ++ ", " ++ r.edition ++ ", " ++ r.date

end StandardRef

/-! ## The catalogued parts

One `StandardRef` per licensed part, edition and date read off the cover. -/

/-- ISO 80000-1, *General*. -/
def iso80000_1 : StandardRef :=
  { body := .ISO, number := 80000, part := 1, edition := "Second edition",
    date := "2022-12", title := "General" }

/-- ISO 80000-2, *Mathematics* (corrected version 2021-11). The §18 framing of
scalars, vectors and tensors lives here. -/
def iso80000_2 : StandardRef :=
  { body := .ISO, number := 80000, part := 2, edition := "Second edition",
    date := "2019-08", title := "Mathematics" }

/-- ISO 80000-3, *Space and time*. -/
def iso80000_3 : StandardRef :=
  { body := .ISO, number := 80000, part := 3, edition := "Second edition",
    date := "2019-10", title := "Space and time" }

/-- ISO 80000-4, *Mechanics*. -/
def iso80000_4 : StandardRef :=
  { body := .ISO, number := 80000, part := 4, edition := "Second edition",
    date := "2019-08", title := "Mechanics" }

/-- ISO 80000-5, *Thermodynamics*. -/
def iso80000_5 : StandardRef :=
  { body := .ISO, number := 80000, part := 5, edition := "Second edition",
    date := "2019-08", title := "Thermodynamics" }

/-- IEC 80000-6, *Electromagnetism* — the one IEC-published part catalogued here. -/
def iec80000_6 : StandardRef :=
  { body := .IEC, number := 80000, part := 6, edition := "Edition 2.0",
    date := "2022-11", title := "Electromagnetism" }

/-- ISO 80000-7, *Light and radiation*. -/
def iso80000_7 : StandardRef :=
  { body := .ISO, number := 80000, part := 7, edition := "Second edition",
    date := "2019-08", title := "Light and radiation" }

/-- ISO 80000-8, *Acoustics*. -/
def iso80000_8 : StandardRef :=
  { body := .ISO, number := 80000, part := 8, edition := "Second edition",
    date := "2020-02", title := "Acoustics" }

/-- ISO 80000-9, *Physical chemistry and molecular physics*. -/
def iso80000_9 : StandardRef :=
  { body := .ISO, number := 80000, part := 9, edition := "Second edition",
    date := "2019-08", title := "Physical chemistry and molecular physics" }

/-- ISO 80000-10, *Atomic and nuclear physics*. -/
def iso80000_10 : StandardRef :=
  { body := .ISO, number := 80000, part := 10, edition := "Second edition",
    date := "2019-08", title := "Atomic and nuclear physics" }

/-- ISO 80000-11, *Characteristic numbers* (the dimensionless characteristic
numbers — directly relevant to the dimension-1 thesis). -/
def iso80000_11 : StandardRef :=
  { body := .ISO, number := 80000, part := 11, edition := "Second edition",
    date := "2019-10", title := "Characteristic numbers" }

/-- ISO 80000-12, *Condensed matter physics* (corrected version 2021-11). -/
def iso80000_12 : StandardRef :=
  { body := .ISO, number := 80000, part := 12, edition := "Second edition",
    date := "2019-08", title := "Condensed matter physics" }

/-- The full catalogue of licensed parts, in part order. -/
def catalogue : List StandardRef :=
  [iso80000_1, iso80000_2, iso80000_3, iso80000_4, iso80000_5, iec80000_6,
   iso80000_7, iso80000_8, iso80000_9, iso80000_10, iso80000_11, iso80000_12]

end PropertyKindCalculus.Iso80000
