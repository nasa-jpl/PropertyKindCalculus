/-
Copyright (c) 2026 California Institute of Technology. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nicolas Rouquette
-/
import PropertyKindCalculus.Index.Basic
import PropertyKindCalculus.Uncertainty.BoundaryBudget

/-!
# The port-budget index — declared `PortBudget`s as a table

A contract states a boundary and a relation states what one boundary claims of another;
a `PortBudget` states which uncertainties a produced port's value carries, term by
influencing source. This table is where a document enumerates the attachments.
Membership is by type, like the ontology tables: every constant of type
`Uncertainty.PortBudget` in scope is a row, so a budget cannot be declared and left out
of the rendering.

The table renders; it does not judge. The checks — the port produced and at the stated
kind, the assembly acyclic, every term an influencing source — are `#kind_budget`'s,
and its pinned reports are their gate.
-/

namespace PropertyKindCalculus.Index

open Lean Meta
open PropertyKindCalculus.Uncertainty (portBudgetValueOf)

/-- The `port-budgets` table: every `Uncertainty.PortBudget` declared in scope, one row
per attachment — the budget declaration, the port and kind it attaches at, the term
count, and the combined standard uncertainty (the quadrature of the terms, computed). -/
def portBudgetsTable (scope : Scope) : MetaM IndexTable := do
  let env ← getEnv
  let headers := #["Budget", "Port", "Kind", "Terms", "Combined"]
  let names := constantsOfType env ``PropertyKindCalculus.Uncertainty.PortBudget scope
  if names.isEmpty then
    return IndexTable.empty "port-budgets" "Uncertainty budgets at the boundary" headers
  let mut rows : Array (Array IndexCell) := #[]
  for n in names do
    let b ← portBudgetValueOf n
    rows := rows.push #[
      .decl n (lastComponent n),
      .code b.port.render,
      .code b.kind.render,
      .code (toString b.terms.length),
      .code (toString b.combined)]
  return { id := "port-budgets", title := "Uncertainty budgets at the boundary",
           headers, rows }

end PropertyKindCalculus.Index
