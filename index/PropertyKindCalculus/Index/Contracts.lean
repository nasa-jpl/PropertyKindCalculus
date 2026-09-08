/-
Copyright (c) 2026 California Institute of Technology. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nicolas Rouquette
-/
import PropertyKindCalculus.Index.Basic
import PropertyKindCalculus.KindIncidence
import PropertyKindCalculus.ContractCoverage
import PropertyKindCalculus.Uncertainty.BoundaryBudget

/-!
# The boundary index — declared `Provenance.Contract`s as a table, absences beside them

A `Provenance.Relation` states what one boundary claims of another; the boundary itself is a
`Provenance.Contract`, and this is where a document enumerates them. Membership is by type,
like the ontology tables: every constant whose type is headed by `Provenance.Contract` in
scope is a row, so a boundary cannot be declared and left out of the rendering.

The `contracts` table renders; it does not judge. The checks — the clauses each answered for
by name, the declared boundary the one the members compute — are `#kind_contract`'s, and the
pinned `#kind_contracts` sweep is their gate at scale. What this table adds to the sweep is
the **join**: which theorem edges land on each boundary, read off every declared `Relation`
in the environment.

The `provenance-coverage` table is the join's complement — the absences. A checker can verify
the internal consistency of what was declared; it cannot notice what was never declared at
all, and an absence is only visible to a query that renders absences. Two are rendered: a
boundary no theorem edge lands on, and a produced port no uncertainty budget attaches to.
The table's row count is in its title line, so a pinned empty table *is* the coverage claim,
and a scope where nothing matches pins `0` rather than passing invisibly.

`@[kindCounterexample]`-tagged declarations are handled the way the sweeps handle them: a
tagged contract renders in the `contracts` table with a `counterexample` clause and is not a
coverage subject, and a tagged relation is not a witness — a deliberate misdeclaration must
not satisfy a real boundary's edge obligation.
-/

namespace PropertyKindCalculus.Index

open Lean Meta
open PropertyKindCalculus.KindIncidence (relationValueOf contractValueOf)
open PropertyKindCalculus.Uncertainty (portBudgetValueOf)

/-- The witness join: every non-counterexample `Provenance.Relation` in the environment, as a
map from the contract declaration name it cites (left or right) to the edges citing it. This
is `ContractCoverage.edgesByContract` — the same join the M12 census gates on, so the record
and the gate cannot drift — kept under this name for the tables; the argument is unused. -/
def edgesByContract (_env : Environment) : MetaM (Std.HashMap String (Array Name)) :=
  PropertyKindCalculus.ContractCoverage.edgesByContract

/-- The `contracts` table: every `Provenance.Contract` declared in scope, one row per
boundary — the contract declaration, the boundary name it declares, the interface at a
glance, the member count, the declared clauses (deciders, aggregations, suppliers, and the
`counterexample` mark where one is tagged), and the theorem edges landing on it. An empty
edges cell is an absence a reader can see — and the `provenance-coverage` table's subject. -/
def contractsTable (scope : Scope) : MetaM IndexTable := do
  let env ← getEnv
  let headers := #["Contract", "Boundary", "Interface", "Members", "Clauses", "Theorem edges"]
  let names := constantsOfType env ``PropertyKindCalculus.Provenance.Contract scope
  if names.isEmpty then
    return IndexTable.empty "contracts" "Declared boundaries" headers
  let edges ← edgesByContract env
  let exempt : NameSet :=
    (BoundaryAudit.kindCounterexamples env).foldl (init := {}) (·.insert ·)
  let mut rows : Array (Array IndexCell) := #[]
  for n in names do
    let c ← contractValueOf n
    let clauses := String.intercalate "; " <|
      (if exempt.contains n then ["counterexample"] else [])
        ++ (if c.deciders.isEmpty then [] else [s!"decides {c.deciders.length}"])
        ++ (if c.aggregations.isEmpty then [] else [s!"aggregates {c.aggregations.length}"])
        ++ (if c.suppliers.isEmpty then [] else [s!"supplies {c.suppliers.length}"])
    let es := edges.getD n.toString #[]
    rows := rows.push #[
      .decl n (lastComponent n),
      .code s!"'{c.name}'",
      .code s!"{c.ports.length} ports ({c.params.length} params), {c.exits.length} exits",
      .code (toString c.members.length),
      if clauses.isEmpty then IndexCell.blank else .code clauses,
      if es.isEmpty then IndexCell.blank
      else .links (es.map fun e => (e, lastComponent e))]
  return { id := "contracts", title := "Declared boundaries", headers, rows }

/-- The `provenance-coverage` table: the declared absences over the contracts in scope. One
row per absence — a boundary no (non-counterexample) theorem edge lands on, and a produced
port no `PortBudget` attaches to. The edges and budgets are joined unscoped, like the
`contracts` table's edge column, because an attachment may live anywhere; the contracts are
scoped, and `@[kindCounterexample]`-tagged ones are not subjects — a deliberate
misdeclaration owes nobody an edge or a budget.

The table renders absences; it does not demand them filled. Which absences are debts and
which are deliberate is the author's adjudication, and pinning the table is how the current
adjudication is recorded: a new unwitnessed boundary or unbudgeted output changes the pinned
row count, so it arrives as a build failure instead of a silence. -/
def provenanceCoverageTable (scope : Scope) : MetaM IndexTable := do
  let env ← getEnv
  let headers := #["Absence", "Contract", "At"]
  let exempt : NameSet :=
    (BoundaryAudit.kindCounterexamples env).foldl (init := {}) (·.insert ·)
  let names := (constantsOfType env ``PropertyKindCalculus.Provenance.Contract scope).filter
    (fun n => !exempt.contains n)
  if names.isEmpty then
    return IndexTable.empty "provenance-coverage" "Provenance coverage absences" headers
  let edges ← edgesByContract env
  let budgetNames := constantsOfType env ``PropertyKindCalculus.Uncertainty.PortBudget #[]
  let mut budgeted : Std.HashSet String := {}
  for bn in budgetNames do
    budgeted := budgeted.insert (← portBudgetValueOf bn).port
  let mut rows : Array (Array IndexCell) := #[]
  for n in names do
    let c ← contractValueOf n
    if (edges.getD n.toString #[]).isEmpty then
      rows := rows.push #[
        .text "no theorem edge", .decl n (lastComponent n), .code s!"'{c.name}'"]
    for p in c.ports do
      if p.dir.produced && !budgeted.contains p.node then
        rows := rows.push #[
          .text "no uncertainty budget", .decl n (lastComponent n),
          .code s!"{p.node} : {p.kind}"]
  return { id := "provenance-coverage", title := "Provenance coverage absences",
           headers, rows }

end PropertyKindCalculus.Index
