/-
# `#kind_occurrences` — the incidence harvest

Where `#kind_edges` enumerates a kind's authored *licenses*, this command reads the
**occurrences**: the consuming applications inside one definition — each site where a
witness argument is discharged against actual operand quantities — printed with their
operands (`alphaK · betaK → gammaK ⟨x, y⟩`), in body order, with multiplicity: two uses
of one witness are two occurrences. This is the provenance hypergraph's occurrence
relation read off elaborated values, incidence included — *which* values met at the
edge, the datum the edge enumeration alone does not carry.

    #kind_occurrences myStep

The collector itself (`KindEdges.collectOccurrences`) reads the edge off the consumer's
instantiated *binder type*, so a pinned occurrence is stable across the elaborator's
witness spellings — inline constructor, lifted or shared `._proof_N` reference,
`let`-bound witness. Operands render as a binder name or an application's head constant.
A hypothesis witness contributes no occurrence: the occurrence sits at the caller that
discharges the license.

This module, not `KindEdges`, holds the user surface because operand positions are
identified by the boundary audit's **carrier registry** (`kindCarrierNames`), and
importing the audit puts its meta-heavy bodies into `producerModules`' walk set — a cost
every `#kind_edges` consumer would pay. Per-declaration occurrence reading walks one
value, so it is cheap here; files that pin both readings keep them in separate modules.
-/
import PropertyKindCalculus.KindEdges
import PropertyKindCalculus.IndividualQuantity
import PropertyKindCalculus.BoundaryAudit

namespace PropertyKindCalculus.KindIncidence

open Lean
open PropertyKindCalculus.KindEdges (KindOccurrence collectOccurrences)

/-- The carrier heads an operand position is recognized by: the audit's registry
(`Quantity`, `CertifiedQuantity`, `NominalValue`, plus every downstream `@[kindCarrier]`
registration), and `IndividualQuantity` — not a boundary-audit carrier (registering it
would put its constructor and projection on the mint/erase report), but its
kind-licensed operations consume the same witnesses. A carrier-*generic* telescope
(operands at a variable type) contributes its occurrences at the monomorphic call
sites, the same places its witnesses are discharged. -/
def operandCarriers (env : Environment) : Array Name :=
  BoundaryAudit.kindCarrierNames env ++ #[``PropertyKindCalculus.IndividualQuantity]

/-- Every inline occurrence in `decl`'s value, in body order, multiplicity kept — two
uses of one witness are two occurrences. Signature binders are opened first, so operand
names print as the signature spells them. A declaration without a value has none. -/
def occurrencesIn (decl : Name) : MetaM (Array KindOccurrence) := do
  let env ← getEnv
  let some info := env.find? decl
    | throwError "unknown declaration '{decl}'"
  let some v := info.value? | return #[]
  Meta.lambdaTelescope v fun _ body =>
    collectOccurrences env (operandCarriers env) body

open Elab Command in
/-- `#kind_occurrences d` prints every inline occurrence in `d`'s value — each consuming
application's edge with the operand quantities that met there, in body order, with
multiplicity — as a single `info` message suitable for `#guard_msgs` pinning. -/
elab "#kind_occurrences " id:ident : command => liftTermElabM do
  let decl ← realizeGlobalConstNoOverload id
  let occs ← occurrencesIn decl
  if occs.isEmpty then
    logInfo m!"no inline kind occurrences in '{decl}'"
  else
    let lines := occs.toList.map (·.render)
    logInfo m!"inline kind occurrences in '{decl}':\n{String.intercalate "\n" lines}"

end PropertyKindCalculus.KindIncidence
