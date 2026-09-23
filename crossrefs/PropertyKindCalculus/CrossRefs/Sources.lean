/-
# The external sources cross-referenced by this work

The cross-reference annotations (`@[dybkaer …]`, `@[vim4 …]`) point into two
external sources. This module records the *citable identity* of each — author or
body, title, edition/status, and date — mirroring `Iso80000.References`, so the
two index tables can render a proper citation header. No normative content from
either source is reproduced anywhere in this work; only locators travel with the
annotations.
-/

module

@[expose] public section Blanket

namespace PropertyKindCalculus.CrossRefs

/-- The bibliographic identity of one external source: a short tag for prose, the
author or responsible body, the full title, an edition/status designation (empty
if none), and the publication or draft date as printed. -/
structure OntologySource where
  /-- A short tag for prose, e.g. "Dybkær (2009)" or "VIM 4 2CD". -/
  shortName : String
  /-- The author or responsible body. -/
  author : String
  /-- The full title. -/
  title : String
  /-- An edition or draft-status designation, as printed; "" if none. -/
  edition : String
  /-- Publication or draft date, as printed. -/
  date : String
  deriving DecidableEq, Repr, Inhabited

/-- A full citation in the conventional form. -/
def OntologySource.cite (s : OntologySource) : String :=
  let parts := [s.author, s.title, s.edition, s.date].filter (· ≠ "")
  String.intercalate ", " parts

/-- **Dybkær (2009)** — the ontology on property this work formalizes. -/
def dybkaerSource : OntologySource :=
  { shortName := "Dybkær (2009)"
    author    := "René Dybkær"
    title     := "An Ontology on Property for Physical, Chemical, and Biological Systems"
    edition   := ""
    date      := "2009" }

/-- **VIM 4 2CD (2023-07-31)** — the *International Vocabulary of Metrology*, 4th
edition, Committee Draft 2, against which this work's concepts are aligned. The
2CD is a restricted committee draft; only clause locators are recorded. -/
def vim4Source : OntologySource :=
  { shortName := "VIM 4 2CD"
    author    := "JCGM"
    title     := "International Vocabulary of Metrology — Basic and general concepts and associated terms (VIM)"
    edition   := "4th edition, Committee Draft 2"
    date      := "2023-07-31" }

end PropertyKindCalculus.CrossRefs

end Blanket
