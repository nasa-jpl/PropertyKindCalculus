/-
Copyright (c) 2026 California Institute of Technology. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nicolas Rouquette
-/
import PropertyKindCalculus.Index.Basic
import PropertyKindCalculus.KindIncidence

/-!
# The theorem-edge index — declared `Provenance.Relation`s as a table

A contract states a boundary and a discharge states that tiers stack; what one boundary
*claims of another* — inverts it, refines it under a hypothesis, equals it, departs from
it by no more than a declared tolerance — is a `Provenance.Relation`, and this table is
where a document enumerates them. Membership is by type, like the ontology tables: every
constant of type `Provenance.Relation` in scope is a row, so an edge cannot be declared
and left out of the rendering.

The table renders; it does not judge. The checks — the witness a sorry-free theorem, the
conclusion in the claimed shape, the tolerance a `Quantity` at a produced port's kind,
every hypothesis mentioned, every license rung answered for — are `#kind_relation`'s,
and the pinned `#kind_relations` survey is their gate at scale. A row here reads what
the declaration says, exactly as the crossings table reads what the registry says.
-/

namespace PropertyKindCalculus.Index

open Lean Meta
open PropertyKindCalculus.KindIncidence (relationValueOf contractValueOf)

/-- The `relations` table: every `Provenance.Relation` declared in scope, one row per
edge — the edge declaration, the claim (the two boundary names and the relation kind),
the witness theorem, the optional clauses (tolerance, hypotheses, license rungs,
well-posedness with its domain, surfaced ambiguity), and the claim in the author's own
words. -/
def relationsTable (scope : Scope) : MetaM IndexTable := do
  let env ← getEnv
  let headers := #["Edge", "Claim", "Witness", "Clauses", "In the author's words"]
  let names := constantsOfType env ``PropertyKindCalculus.Provenance.Relation scope
  if names.isEmpty then
    return IndexTable.empty "relations" "Theorem edges between boundaries" headers
  let exempt : NameSet :=
    (BoundaryAudit.kindCounterexamples env).foldl (init := {}) (·.insert ·)
  let mut rows : Array (Array IndexCell) := #[]
  for n in names do
    let rel ← relationValueOf n
    let left ← contractValueOf rel.left
    let right ← contractValueOf rel.right
    let clauses := String.intercalate "; " <|
      (if exempt.contains n then ["counterexample"] else [])
        ++ (if rel.tolerance.isAnonymous then []
            else [s!"tolerance {shortenNames (toString rel.tolerance)}"])
        ++ (if rel.hypotheses.isEmpty then []
            else [s!"hypotheses {String.intercalate ", "
              ((rel.hypotheses.map toString).map shortenNames)}"])
        ++ (if rel.licenses.isEmpty then []
            else [s!"rungs {String.intercalate ", " (rel.licenses.map (·.rung))}"])
        ++ (if rel.wellPosed.isAnonymous then []
            else [s!"well-posed {shortenNames (toString rel.wellPosed)} on \
              {shortenNames (toString rel.domain)}"])
        ++ (if rel.ambiguity.isAnonymous then []
            else [s!"ambiguity {shortenNames (toString rel.ambiguity)}"])
    rows := rows.push #[
      .decl n (lastComponent n),
      .code s!"'{left.name}' {rel.kind.label} '{right.name}'",
      .decl rel.witness (lastComponent rel.witness),
      if clauses.isEmpty then IndexCell.blank else .code clauses,
      .prose rel.claim]
  return { id := "relations", title := "Theorem edges between boundaries", headers, rows }

end PropertyKindCalculus.Index
