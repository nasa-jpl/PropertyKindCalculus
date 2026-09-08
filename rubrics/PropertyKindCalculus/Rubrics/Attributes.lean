/-
# Conformance evidence — the `@[rubric …]` attribute and the section map

A document conforms to a template by *declaring where* it addresses each rubric.
There are exactly two channels, and each carries its own integrity guarantee:

  * a **declaration site** is recorded by the `@[rubric "M12" "note"]` attribute,
    applied from a separate module the way `Requirements.Annotations` applies
    `@[requirement …]`. Because the attribute attaches to a real declaration, a site
    can never name one that does not exist — a rename is a compile error;
  * a **section site** is an entry in the document's `Conformance.sections` map,
    naming the `%%% tag := … %%%` of the section that states the rubric. The
    conformance matrix renders it as a section cross-reference, and Verso resolves
    that tag against the document's own traversal — a dangling tag is a render
    error, not a stale cell.

*Every* rubric requires a section site, because the template is a claim about a
document: a rubric discharged only by a declaration is one the document never
mentions, and reporting that as addressed is precisely the false green this layer
exists to prevent. What the evidence kind adds is whether a declaration is required
*as well* — for everything but `exposition`, it is. A hand-transcribed table sits in
a section exactly as a generated one does and reads the same on the page; a section
asserting a theorem reads exactly like one citing it. Requiring the declaration is
what separates each pair, because only the real one has a declaration to name.

Status is therefore *computed* from the sites and the rubric's own evidence kind.
There is no switch to forget to flip: adding the annotation is what moves a rubric
to `proved`, and removing the declaration it names is a build failure.

A site is one thing, and never a claim about the rest. For a rubric whose `closure`
names audits, the status therefore asks a third question the document does not
answer by declaring anything: whether each named audit left an `AuditReceipt`
(`PropertyKindCalculus.AuditReceipt`) over a scope covering the document's
`declScope`. A gated rubric annotated with two theorems and never audited reads
`partial`, exactly as one with a section and no declaration does — the receipt is
harvested from the audit probes in the import closure, so it cannot be supplied by
annotating something else.
-/

import Lean
import PropertyKindCalculus.AuditReceipt
import PropertyKindCalculus.Rubrics.Catalogue

open Lean

namespace PropertyKindCalculus.Rubrics

/-- Whether a rubric of this evidence kind requires a **declaration site** — a
kernel-visible declaration carrying the `@[rubric …]` attribute. -/
def Evidence.needsDecl : Evidence → Bool
  | .exposition => false
  | .generated  => true
  | .checked    => true
  | .measured   => true

/-- Whether a rubric of this evidence kind requires a **section site** — a tagged
section of the document that addresses it.

Every kind does. The template says what a *document* must address, so a rubric with a
declaration and no section is one the document is silent about, however green the
declaration is. This is deliberately not a per-kind choice: making it one is what
would let a matrix report `proved` for a theorem no chapter cites. -/
def Evidence.needsSection : Evidence → Bool
  | .exposition | .generated | .checked | .measured => true

/-- One declaration site: a Lean declaration offered as evidence that a document
addresses a rubric, with a short note in the document's own words. -/
structure RubricRef where
  /-- The annotated declaration (resolved, so it cannot dangle). -/
  decl : Name
  /-- The rubric identifier — `"M1"` … `"M26"`, `"D1"` … `"D17"`. -/
  rubric : String
  /-- What this declaration contributes, in the document's own words. -/
  note : String := ""
  deriving Repr, Inhabited, DecidableEq

/-- Environment extension collecting every `@[rubric …]`-annotated declaration. -/
initialize rubricExt :
    SimplePersistentEnvExtension RubricRef (Array RubricRef) ←
  registerSimplePersistentEnvExtension {
    addEntryFn    := fun a e => a.push e
    addImportedFn := fun ess => ess.foldl (init := #[]) (· ++ ·)
  }

/-- `@[rubric "<id>" ("<note>")?]` — record that a declaration is where a document
addresses a template rubric. -/
syntax (name := rubricAttr) "rubric " str (str)? : attr

initialize registerBuiltinAttribute {
  name  := `rubricAttr
  descr := "Conformance site: this declaration is where a document addresses a template rubric."
  add   := fun decl stx _kind => do
    match stx with
    | `(attr| rubric $id:str $[$note:str]?) =>
        let id := id.getString
        if (rubricById? id).isNone then
          throwError "unknown rubric '{id}'; it is not in \
            `PropertyKindCalculus.Rubrics.catalogue`"
        let note := (note.map (·.getString)).getD ""
        modifyEnv fun env =>
          rubricExt.addEntry env { decl := decl, rubric := id, note := note }
    | _ => throwError "invalid `rubric` attribute; expected `rubric \"<id>\" [\"<note>\"]`"
}

/-- Every declaration site harvested into `env`, in registration order. -/
def rubricRefs (env : Environment) : Array RubricRef :=
  rubricExt.getState env

/-- One section site: the tag of a section that states a rubric, with a short note.
Unlike a declaration site this is plain data, because a section is not a Lean
declaration — the guarantee comes from rendering it as a cross-reference, which the
document's own traversal must resolve. -/
structure SectionRef where
  /-- The rubric identifier. -/
  rubric : String
  /-- The `%%% tag := … %%%` of the section that states it. -/
  tag : String
  /-- How the section addresses the rubric, in the document's own words. -/
  note : String := ""
  deriving Repr, Inhabited, DecidableEq

/-- A document's declared conformance to one template: which template it answers to,
the section sites it offers, and the declaration namespace its `@[rubric …]`
annotations live under.

`declScope` exists because the attribute harvest is environment-wide: a document
that imports a library annotated for another document would otherwise count that
library's sites as its own. Leaving it `none` accepts every harvested site, which is
right only for a document whose environment contains no other. -/
structure Conformance where
  /-- The template this report is against. -/
  template : Template
  /-- The document's section sites. -/
  sections : List SectionRef := []
  /-- Restrict declaration sites to this namespace prefix. -/
  declScope : Option Name := none
  deriving Inhabited

/-- The declaration sites of `c` for rubric `id`, restricted to `c.declScope`. -/
def Conformance.declSites (c : Conformance) (env : Environment) (id : String) :
    Array RubricRef :=
  (rubricRefs env).filter fun r =>
    r.rubric == id && (match c.declScope with
      | none => true
      | some ns => ns.isPrefixOf r.decl)

/-- The section sites of `c` for rubric `id`. -/
def Conformance.sectionSites (c : Conformance) (id : String) : List SectionRef :=
  c.sections.filter (·.rubric == id)

/-- The audits a rubric's closure names that have left **no** receipt covering the
document's scope: what stands between a rubric's sites and its green. Empty for a
rubric whose closure names none. -/
def Conformance.missingAudits (c : Conformance) (env : Environment) (r : Rubric) :
    List String :=
  r.closure.audits.filter fun a => (auditReceiptsFor env a c.declScope).isEmpty

/-- The **evidence-derived status** of a rubric for a document — a computed fact
about the sites it declared and the audits that ran, never a hand-typed assertion:

  * the rubric's own `dischargedWord` (`stated` / `generated` / `proved` /
    `measured`) once every channel its evidence kind requires has a site **and**
    every audit its closure names has left a receipt covering `declScope`;
  * `"partial"` when it has sites but not in every required channel — the case a
    single "done" would hide, in either direction: a generated view cited by section
    with no generator named, or a theorem annotated with no section citing it — or
    when a named audit has not run (`missingAudits` says which);
  * `"unaddressed"` when the document offers no site at all.
-/
def Conformance.status (c : Conformance) (env : Environment) (r : Rubric) : String :=
  let decls := c.declSites env r.id
  let secs := c.sectionSites r.id
  if decls.isEmpty && secs.isEmpty then "unaddressed"
  else
    let declOk := !r.evidence.needsDecl || !decls.isEmpty
    let secOk := !r.evidence.needsSection || !secs.isEmpty
    let auditsOk := (c.missingAudits env r).isEmpty
    if declOk && secOk && auditsOk then r.evidence.dischargedWord else "partial"

/-- Whether a rubric is fully addressed by `c`. -/
def Conformance.addressed (c : Conformance) (env : Environment) (r : Rubric) : Bool :=
  let s := c.status env r
  s != "unaddressed" && s != "partial"

/-- How a document stands against its template: the raw material for the matrix's
headline claim. -/
structure Tally where
  /-- Rubrics in the template. -/
  total : Nat
  /-- Rubrics fully addressed. -/
  addressed : Nat
  /-- Rubrics with sites in some but not every required channel. -/
  incomplete : Nat
  /-- Rubrics with no site at all. -/
  unaddressed : Nat
  deriving Repr, Inhabited

/-- Tally a document's conformance against its template. -/
def Conformance.tally (c : Conformance) (env : Environment) : Tally :=
  c.template.rubrics.foldl (init := ⟨0, 0, 0, 0⟩) fun t r =>
    let t := { t with total := t.total + 1 }
    match c.status env r with
    | "unaddressed" => { t with unaddressed := t.unaddressed + 1 }
    | "partial"     => { t with incomplete := t.incomplete + 1 }
    | _             => { t with addressed := t.addressed + 1 }

end PropertyKindCalculus.Rubrics
