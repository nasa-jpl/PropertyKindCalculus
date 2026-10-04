/-
# Requirement — what a model's quantities must satisfy, and how that is discharged

A declared boundary says what a model computes; a theorem edge says how two boundaries
relate. Neither says what the model's quantities *must* satisfy — the input/output ratio
that may not exceed a bound, the output that must lie in a band, the idealization whose
error must stay below a tolerance — nor by what evidence each demand is met. The
**requirement** is that statement, as data beside the boundary it governs, in the shape
the theorem edge set: declaration names the environment resolves, the author's words
where the calculus cannot read them, and nothing the commands do not check.

Two categories, told apart by the statement and not by the effort:

  * A **provable requirement** closes over the model's own declarations and kinded
    quantities: every constant its statement mentions is the model's or the library's, so a
    theorem about the model discharges it. The discharge is a theorem edge (`Relation`)
    between the governed boundary and a *specification boundary* — a contract whose one
    member computes the bound — or, where no bound is computed, a bare theorem; and, where
    the model also runs, named **spot checks**: `Bool` declarations the requirement command
    evaluates, the way an inhabitation check spot-checks a proof. A *negative* provable
    requirement — "this is never summed over the pair" — is discharged by the absence of a
    license: a class application the command asks the environment for and must not find.
  * An **empirical requirement** names a **referent** the model does not define — a
    datasheet value, a prior, a reference measurement, a population. No theorem about the
    model alone can discharge it, however much proof is spent, because the referent is a
    free variable only observation closes. It is discharged by a **gate** — a decider whose
    threshold is the referent — or deferred by an attestation. The referent is a kinded
    quantity carrying `@[kindReferent "where it comes from"]`, and the mark is what makes
    the demarcation mechanical: a provable requirement's statement may name no referent,
    and an empirical requirement's gate must name one.

Either category may be **attested** — deferred with a reason in the author's words. That is
not a third category but a ratchet: counted by the coverage census, and meant to fall.

A requirement has a **scope**: the objects it quantifies over — every object the boundary
is evaluated for, every object of a named sort (reached through `Sorted`), named objects,
or the objects a named decider selects. "Every spring" is a sort, "the coupling spring" is
an object, and neither is statable over a boundary whose objects are nominal.

Prelude-only data; the marks, the checks and the censuses live in `KindRequirement`.
-/

module

public import PropertyKindCalculus.Provenance

@[expose] public section Blanket

namespace PropertyKindCalculus.Provenance

/-- The category of a requirement: how its statement is closed, and so how it is
discharged. -/
inductive RequirementKind where
  /-- The statement closes over the model's own declarations: a theorem discharges it, and
  spot checks evaluate it where the model runs. -/
  | provable
  /-- The statement names a referent the model does not define: a gate on an observation
  discharges it. -/
  | empirical
deriving DecidableEq, Repr, Inhabited, BEq

/-- How a requirement kind prints in a rendered report. -/
def RequirementKind.label : RequirementKind → String
  | .provable => "provable"
  | .empirical => "empirical"

/-- The objects a requirement quantifies over. -/
inductive RequirementScope where
  /-- Every object the governed boundary is evaluated for. -/
  | all
  /-- Every object of the named sort — a `SortOfSystem` declaration, which the objects
  reach through their `Sorted` instance. -/
  | sort (sort : Lean.Name)
  /-- The named objects: declarations whose type carries a `Sorted` instance, so each is an
  object of some sort and not a bare value. -/
  | objects (objects : List Lean.Name)
  /-- The objects a named decider selects — a batch's subset, where the objects are carved
  by a predicate rather than named. -/
  | decided (decider : Lean.Name)
deriving DecidableEq, Repr, Inhabited, BEq

/-- How a requirement scope prints in a rendered report. -/
def RequirementScope.label : RequirementScope → String
  | .all => "all"
  | .sort s => s!"sort {s}"
  | .objects os => s!"objects {String.intercalate ", " (os.map toString)}"
  | .decided d => s!"decided by {d}"

/-- **A requirement on a declared boundary**: what the boundary's quantities must satisfy,
in the author's words, and the evidence by which it is met — the theorem edge or theorem
of a provable requirement with its spot checks, the referents and gate of an empirical
one, or the attestation that defers either. The prose is not checked and is not meant to
be; what is checked is that the governed boundary is a model's, that each named
declaration exists and has the shape its field claims, that a provable statement names no
referent and an empirical gate names one, that each spot check evaluates to `true`, and
that a claimed absence is absent. -/
structure Requirement where
  /-- The requirement's identifier, as a document cites it. -/
  name : String
  /-- The requirement in the author's words: what must hold, of what. -/
  statement : String
  /-- Provable or empirical. -/
  kind : RequirementKind
  /-- The declaration name of the model boundary the requirement governs. -/
  governs : Lean.Name
  /-- The governed port of that boundary, or `none` for everything the boundary
  produces. -/
  port : Option NodeId := none
  /-- The objects the requirement quantifies over. -/
  scope : RequirementScope := .all
  /-- Provable: the discharge — a `Relation` whose left side is the governed boundary and
  whose right side is a specification boundary, or a sorry-free theorem. Anonymous where
  the requirement is attested. -/
  witness : Lean.Name := .anonymous
  /-- Named `Bool` declarations the requirement command evaluates and requires `true`: the
  runtime spot checks of a proof, at the carrier the model runs on, on operational
  inputs. -/
  spotChecks : List Lean.Name := []
  /-- Provable, negative: the declaration of a `Prop` that is a class application — a
  license — of which the environment must hold no instance. -/
  absent : Lean.Name := .anonymous
  /-- Empirical: the `@[kindReferent]`-marked declarations the statement names — what the
  model does not define. -/
  referents : List Lean.Name := []
  /-- Empirical: the declaration that decides the requirement against its referent — a
  `KindAdmissible` instance, a `Bool`-valued predicate — which must mention one of the
  referents. Anonymous where the requirement is attested. -/
  gate : Lean.Name := .anonymous
  /-- The deferral, in the author's words, where the requirement is not yet discharged.
  Empty where it is. -/
  attested : String := ""
deriving Repr, Inhabited

end PropertyKindCalculus.Provenance

end Blanket
