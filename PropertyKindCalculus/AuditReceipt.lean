/-
# AuditReceipt — what an audit leaves behind when it runs

An audit here is a *command* (`#kind_boundary_clean ns …`), not a declaration, so nothing in
the environment records that it ran. That is the one gap in the application templates'
conformance layer: a document scoring itself against a *gated* rubric can annotate any
declaration as the rubric's site and never run the gate, and the matrix reads exactly as it
would if it had (`METHODOLOGY_TEMPLATES.md` §1 — soil-moisture-model's M6 is the instance).

A **receipt** is the one fact a command can leave: its identity, the namespaces it walked,
and the module it ran in. It is recorded at the command's *success point* — after a gate
has decided not to throw, after a reading has logged — so

  * for a `_clean` gate, which throws on any violation, a receipt **is a pass** over that
    scope in this build;
  * for a reading, a receipt says only that the reading happened. The pinned reading is
    the record; the receipt says the record was made in this build, which is the fact a
    conformance matrix needs and cannot otherwise get.

What a receipt does *not* say: that the scope was the right one beyond a prefix test
(`AuditReceipt.covers`), or that a pin is current — a stale pin is a build failure, which
is its own signal. The extension is persistent and imported, so a document sees the
receipts of every module in its import closure: the audit probes downstream repositories
keep beside their pinned reports are exactly where the receipts are minted.
-/

module

public import Lean

public section -- pkc-blanket
@[expose] section -- pkc-blanket-expose

namespace PropertyKindCalculus

open Lean

/-- One run of an audit command. -/
structure AuditReceipt where
  /-- The audit's identity — the command's name without its `#`, e.g. `kind_boundary_clean`.
  This is the string a rubric's `Closure` names in `audits`. -/
  audit : String
  /-- The namespaces the run walked, as the author spelled them. -/
  scope : Array Name
  /-- The module the command ran in. -/
  module : Name
  deriving Repr, Inhabited, BEq

/-- Environment extension collecting every receipt, local and imported. -/
initialize auditReceiptExt :
    SimplePersistentEnvExtension AuditReceipt (Array AuditReceipt) ←
  registerSimplePersistentEnvExtension {
    addEntryFn    := fun a e => a.push e
    addImportedFn := fun ess => ess.foldl (init := #[]) (· ++ ·)
  }

/-- Record that `audit` ran over `scope` in the current module. Call it at a command's
success point and nowhere else — after a gate's `unless … throwError` block, so that the
receipt exists exactly when the gate did not fire. -/
def recordAuditReceipt {m : Type → Type} [Monad m] [MonadEnv m] (audit : String)
    (scope : Array Name) : m Unit :=
  modifyEnv fun env =>
    auditReceiptExt.addEntry env { audit, scope, module := env.mainModule }

/-- Every receipt in the environment, in registration order. -/
def auditReceipts (env : Environment) : Array AuditReceipt :=
  auditReceiptExt.getState env

/-- Does a run cover a document's declaration scope? A run over `ns` covers every scope
under it: the audit walked `SoilMoisture`, so it walked `SoilMoisture.Algorithm`. The
reverse is not coverage — a run over a sub-namespace says nothing about the rest — which is
the direction a conformance check must refuse. A document with no scope accepts any run of
the audit, which is right only when its environment contains no other document's. -/
def AuditReceipt.covers (r : AuditReceipt) (ns : Option Name) : Bool :=
  match ns with
  | none   => true
  | some n => r.scope.any fun s => s.isPrefixOf n

/-- The receipts for `audit` whose scope covers `ns`. -/
def auditReceiptsFor (env : Environment) (audit : String) (ns : Option Name) :
    Array AuditReceipt :=
  (auditReceipts env).filter fun r => r.audit == audit && r.covers ns

end PropertyKindCalculus

end -- pkc-blanket-expose
end -- pkc-blanket
