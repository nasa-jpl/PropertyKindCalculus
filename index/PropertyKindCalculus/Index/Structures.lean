/-
Copyright (c) 2026 California Institute of Technology. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nicolas Rouquette
-/

module

public import PropertyKindCalculus.Index.Basic
public import PropertyKindCalculus.DocGenMath.Registry

/-!
# Indexing what is *built* on the kinds — kinded records and kinded operations

A model does not stop at declaring kinds. It bundles them into records

    structure MironovNK (α : Type) where
      nd : Quantity nIndexKind α
      kd : Quantity kLossKind α
      …

and it consumes and produces them in operations

    def mironovDielectric (s ill : System) … :
        DedicatedQuantity (soilPermittivity s) (Complex α) := …

Both are ordinary Lean declarations, so the question this module answers is what *makes* one of them
an index entry. The answer is the registry the boundary audit already trusts:

* a **kinded record** is a structure at least one of whose fields is a registered kind carrier
  applied to a kind — `Quantity`, `CertifiedQuantity`, or whatever a downstream layer registered
  with `@[kindCarrier]` (soil-moisture-model registers its `DedicatedQuantity`);
* a **kinded operation** is a definition whose *result type* is such a carrier.

No annotation decides membership, and deliberately so. `@[kindCarrier]` is the single opt-in, and it
is already required for the boundary audit to see the carrier at all — so a layer that teaches the
audit about its carrier gets these two indexes for free, and cannot register for one and forget the
other. `MironovNK` qualifies on seven fields; `JacColsQ` on four; a configuration structure holding
raw `Float`s qualifies on none and appears only in the configuration-types index. A configuration
structure whose fields *are* quantities appears in both, which is not a duplicate: it genuinely is a
kinded record (these are its kinds) and genuinely is a configuration type (these are the constants
that render qualified).

The useful column differs between the two. For a record it is the **notation**: the fields carry the
`@[pkc_math_symbol]` declarations that make a rendered equation read `n_d`, `k_b`, `m_{vt}` as the
literature writes them, and those live nowhere else. For an operation it is the **kind signature** —
which kinds go in, which comes out — together with the authored crossings the body routes through,
because that is the operation's actual contract with the calculus.
-/

public section -- pkc-blanket
@[expose] section -- pkc-blanket-expose

namespace PropertyKindCalculus.Index

open Lean Meta

/-! ## Recognizing carrier-typed positions -/

/-- A carrier-typed position: which carrier, and the kind it is applied to (pretty-printed).
Every registered carrier takes its kind first, which is what `BoundaryAudit.collectBoundary` relies
on when it reads a mint's kind out of a constructor application. -/
structure CarrierUse where
  /-- The carrier structure (`Quantity`, `DedicatedQuantity`, …). -/
  carrier : Name
  /-- The kind argument, pretty-printed — the fallback rendering, and the only one available for a
  kind that is computed rather than named (`soilWaterVWC s`). -/
  kind : String
  /-- The kind's own declaration, when the argument *is* a named kind. -/
  kindDecl? : Option Name
deriving Repr, Inhabited, BEq

/-- Read a type as a carrier application, or `none` if its head is not a registered carrier. -/
def carrierUse? (carriers : Array Name) (t : Expr) : MetaM (Option CarrierUse) := do
  let .const c _ := t.getAppFn | return none
  unless carriers.contains c do return none
  let args := t.getAppArgs
  let some k := args[0]? | return none
  let kindDecl? := match k.getAppFn with
    | .const kc _ => if kc.isInternal then none else some kc
    | _ => none
  return some { carrier := c, kind := toString (← ppExpr k), kindDecl? }

/-- A kind position as a table cell: a link to the kind's declaration where it is a named kind (so
the cell reads `backscatter`, not `PropertyKindCalculus.Examples.AvsForward.backscatter`, and points
at the kind's own row), and the rendered expression where it is computed. -/
def CarrierUse.cell (u : CarrierUse) : IndexCell :=
  match u.kindDecl? with
  | some k => .decl k (lastComponent k)
  | none   => .code u.kind

/-! ## Kinded records -/

/-- One carrier-typed field of a kinded record. -/
structure KindedField where
  /-- The field's projection name. -/
  proj : Name
  /-- The field's own (unqualified) name. -/
  field : String
  /-- The carrier and kind the field is typed at. -/
  use : CarrierUse
  /-- The LaTeX the field renders as, if it declares one with `@[pkc_math_symbol]`. -/
  notation? : Option String
deriving Repr, Inhabited

/-- The carrier-typed fields of `structName`, in declaration order. Empty for a structure that is not
a kinded record — which is exactly the membership test. -/
def kindedFields (carriers : Array Name) (symbols : Std.HashMap Name String) (structName : Name) :
    MetaM (Array KindedField) := do
  let env ← getEnv
  let some (.inductInfo iv) := env.find? structName | return #[]
  let [ctor] := iv.ctors | return #[]
  let some (.ctorInfo cv) := env.find? ctor | return #[]
  let fields := getStructureFields env structName
  forallTelescope cv.type fun xs _ => do
    let mut out : Array KindedField := #[]
    for i in [cv.numParams : xs.size] do
      let some x := xs[i]? | continue
      let some fname := fields[i - cv.numParams]? | continue
      let some use ← carrierUse? carriers (← inferType x) | continue
      let proj := structName ++ fname
      out := out.push {
        proj, field := toString fname, use, notation? := symbols[proj]? }
    return out

/-- Every structure in scope that is a kinded record, with its carrier-typed fields.

Registered carriers are themselves excluded: `Quantity` is the mechanism, not a model's record. -/
def kindedRecords (carriers : Array Name) (symbols : Std.HashMap Name String) (scope : Scope) :
    MetaM (Array (Name × Array KindedField)) := do
  let env ← getEnv
  let mut out : Array (Name × Array KindedField) := #[]
  for (n, info) in env.constants.toList do
    unless scope.covers n do continue
    unless isAuthored env n do continue
    unless info matches .inductInfo _ do continue
    unless isStructure env n do continue
    if carriers.contains n then continue
    let fs ← kindedFields carriers symbols n
    unless fs.isEmpty do out := out.push (n, fs)
  return out.qsort (fun a b => nameLt a.1 b.1)

/-! ## Kinded operations -/

/-- One definition whose result is a kinded value. -/
structure KindedOp where
  /-- The definition. -/
  decl : Name
  /-- The carrier-typed arguments, in order. -/
  inputs : Array CarrierUse
  /-- The carrier and kind of the result. -/
  result : CarrierUse
  /-- The authored boundary sites the body routes through. -/
  crossings : Array Name
deriving Repr, Inhabited

/-- Every definition in scope whose result type is a registered carrier, with its kind signature and
the tagged boundary sites its body calls.

The crossings column is what makes the row a contract rather than a signature: an operation that
changes kind must reach an authored crossing to do it, so listing them says which sanctioned
re-typings this operation depends on. `BoundaryAudit.boundaryTags` supplies the sanctioned set;
`Expr.getUsedConstants` says which of them the body actually mentions.

**Field projections are excluded.** `MironovNK.nd` is a definition whose result type is
`Quantity nIndexKind α`, so it satisfies the criterion literally — but it is the record's accessor,
not an operation on kinds, and it is already a row of the kinded-records table. Including it would
list every field of every record twice. -/
def kindedOps (carriers : Array Name) (scope : Scope) : MetaM (Array KindedOp) := do
  let env ← getEnv
  let tagged : Std.HashSet Name :=
    (BoundaryAudit.boundaryTags env).foldl (fun s t => s.insert t.decl) {}
  let mut out : Array KindedOp := #[]
  for (n, info) in env.constants.toList do
    unless scope.covers n do continue
    unless isAuthored env n do continue
    unless info matches .defnInfo _ do continue
    if env.isProjectionFn n then continue
    if carriers.any (fun c => c.isPrefixOf n) then continue
    let sig ← forallTelescopeReducing info.type fun xs body => do
      let some result ← carrierUse? carriers body | return none
      let mut inputs : Array CarrierUse := #[]
      for x in xs do
        if let some u ← carrierUse? carriers (← inferType x) then inputs := inputs.push u
      return some (inputs, result)
    let some (inputs, result) := sig | continue
    let crossings := match info.value? with
      | some v => (v.getUsedConstants.filter tagged.contains).qsort nameLt
      | none   => #[]
    out := out.push { decl := n, inputs, result, crossings }
  return out.qsort (fun a b => nameLt a.decl b.decl)

/-! ## The tables -/

/-- The registered carriers plus the `@[pkc_math_symbol]` map — the two lookups both tables need. -/
def carrierContext : MetaM (Array Name × Std.HashMap Name String) := do
  let env ← getEnv
  let carriers := BoundaryAudit.kindCarrierNames env
  let symbols := (paramAttrEntries DocGenMath.pkcMathSymbolAttr env).foldl
    (init := ({} : Std.HashMap Name String)) fun m (n, notation_) => m.insert n notation_.latex
  return (carriers, symbols)

/-- Kinded records in scope: the structures that bundle quantities, with each field's kind and the
notation it renders as. -/
def recordsTable (scope : Scope) : MetaM IndexTable := do
  let (carriers, symbols) ← carrierContext
  let headers := #["Record", "Field", "Carrier", "Kind", "Notation"]
  let records ← kindedRecords carriers symbols scope
  if records.isEmpty then
    return IndexTable.empty "records" "Kinded records" headers
  let mut rows : Array (Array IndexCell) := #[]
  for (n, fields) in records do
    -- One row per field, the record named only on its first — a grouped table, not a repeated one.
    let mut first := true
    for f in fields do
      rows := rows.push #[
        (if first then .decl n (lastComponent n) else .text ""),
        .decl f.proj f.field,
        .code (lastComponent f.use.carrier),
        f.use.cell,
        .code (f.notation?.getD "")]
      first := false
  return { id := "records", title := "Kinded records", headers, rows }

/-- Kinded operations in scope: the definitions that produce a kinded value, with their kind
signature and the authored crossings they route through. -/
def operationsTable (scope : Scope) : MetaM IndexTable := do
  let (carriers, _) ← carrierContext
  let headers := #["Operation", "Argument kinds", "Result kind", "Crossings"]
  let ops ← kindedOps carriers scope
  if ops.isEmpty then
    return IndexTable.empty "operations" "Kinded operations" headers
  let mut rows : Array (Array IndexCell) := #[]
  for o in ops do
    -- Named argument kinds become links; computed ones (`soilWaterVWC s`) keep their expression.
    let argCell : IndexCell :=
      if o.inputs.all (·.kindDecl?.isSome) then
        .links (o.inputs.filterMap fun u => u.kindDecl?.map fun k => (k, lastComponent k))
      else
        .code (String.intercalate ", " (o.inputs.toList.map (·.kind)))
    rows := rows.push #[
      .decl o.decl (lastComponent o.decl),
      argCell,
      o.result.cell,
      .links (o.crossings.map fun c => (c, lastComponent c))]
  return { id := "operations", title := "Kinded operations", headers, rows }

end PropertyKindCalculus.Index

end -- pkc-blanket-expose
end -- pkc-blanket
