/-
# Cross-reference attributes — `@[dybkaer …]` and `@[vim4 …]`

This work's declarations correspond, concept by concept, to definitions in two
external sources:

  * **Dybkær (2009)**, *An Ontology on Property for Physical, Chemical, and
    Biological Systems* — addressed by chapter/section (e.g. "§20", "Ch. 6").
  * **VIM 4 2CD (2023-07-31)**, the *International Vocabulary of Metrology*, 4th
    edition, Committee Draft 2 — addressed by clause number (e.g. "2.4", "1.12").

These correspondences are already recorded, as free text, in the spine docstrings.
This module makes them **typed, decl-indexed metadata**: two parametric attributes,

```
@[dybkaer "§20" "dedicated kind-of-property"]
@[vim4 "2.4" "measurement principle"]
```

each backed by an environment extension that collects every tagged declaration.
Because an attribute attaches to a real declaration, a cross-reference can never
name a declaration that does not exist — a rename is a compile error, not silent
drift. The attributes are **applied from a separate module** (`Annotations`) via
the standalone `attribute [..] decl` command, so the Mathlib-free core spine never
imports this machinery and stays prelude-only.

Only *locators* are carried — the external clause designation and the external
term — never any normative text from either source (both are copyrighted; the VIM4
2CD is additionally a restricted committee draft). This mirrors the discipline of
`Iso80000.References`, which records only the citable identity of each ISO part.
-/

import Lean

open Lean

namespace PropertyKindCalculus.CrossRefs

/-- One cross-reference: the Lean declaration it annotates, the external *locus*
(a clause/section designation, as printed), the external *term*, and an optional
note in this work's own words. Carries locators only — never normative text. -/
structure OntologyRef where
  /-- The annotated Lean declaration (resolved, so it cannot dangle). -/
  decl : Name
  /-- The external locus as printed — e.g. "§20", "Ch. 6" (Dybkær) or "2.4",
  "1.12" (VIM4 2CD). -/
  locus : String
  /-- The external term, as printed in the source. -/
  term : String
  /-- A short note on the correspondence, in this work's own words. -/
  note : String := ""
  deriving Repr, Inhabited, DecidableEq

/-! ## Dybkær cross-references -/

/-- Environment extension collecting every `@[dybkaer …]`-annotated declaration. -/
initialize dybkaerExt :
    SimplePersistentEnvExtension OntologyRef (Array OntologyRef) ←
  registerSimplePersistentEnvExtension {
    addEntryFn    := fun a e => a.push e
    addImportedFn := fun ess => ess.foldl (init := #[]) (· ++ ·)
  }

/-- `@[dybkaer "<locus>" "<term>" ("<note>")?]` — annotate a declaration with the
locus of the corresponding concept in Dybkær's *Ontology on Property* (2009). -/
syntax (name := dybkaerAttr) "dybkaer " str str (str)? : attr

initialize registerBuiltinAttribute {
  name  := `dybkaerAttr
  descr := "Cross-reference to a locus in Dybkær's Ontology on Property (2009)."
  add   := fun decl stx _kind => do
    match stx with
    | `(attr| dybkaer $locus:str $term:str $[$note:str]?) =>
        let note := (note.map (·.getString)).getD ""
        modifyEnv fun env =>
          dybkaerExt.addEntry env
            { decl := decl, locus := locus.getString, term := term.getString, note := note }
    | _ => throwError "invalid `dybkaer` attribute; expected `dybkaer \"<locus>\" \"<term>\" [\"<note>\"]`"
}

/-- Every Dybkær cross-reference harvested into `env`, in registration order. -/
def dybkaerRefs (env : Environment) : Array OntologyRef := dybkaerExt.getState env

/-! ## VIM 4 2CD cross-references -/

/-- Environment extension collecting every `@[vim4 …]`-annotated declaration. -/
initialize vim4Ext :
    SimplePersistentEnvExtension OntologyRef (Array OntologyRef) ←
  registerSimplePersistentEnvExtension {
    addEntryFn    := fun a e => a.push e
    addImportedFn := fun ess => ess.foldl (init := #[]) (· ++ ·)
  }

/-- `@[vim4 "<clause>" "<term>" ("<note>")?]` — annotate a declaration with the
clause of the corresponding concept in the VIM 4 2CD (2023-07-31). -/
syntax (name := vim4Attr) "vim4 " str str (str)? : attr

initialize registerBuiltinAttribute {
  name  := `vim4Attr
  descr := "Cross-reference to a clause in the VIM 4 2CD (2023-07-31)."
  add   := fun decl stx _kind => do
    match stx with
    | `(attr| vim4 $clause:str $term:str $[$note:str]?) =>
        let note := (note.map (·.getString)).getD ""
        modifyEnv fun env =>
          vim4Ext.addEntry env
            { decl := decl, locus := clause.getString, term := term.getString, note := note }
    | _ => throwError "invalid `vim4` attribute; expected `vim4 \"<clause>\" \"<term>\" [\"<note>\"]`"
}

/-- Every VIM 4 2CD cross-reference harvested into `env`, in registration order. -/
def vim4Refs (env : Environment) : Array OntologyRef := vim4Ext.getState env

end PropertyKindCalculus.CrossRefs
