/-
# `@[kindPrincipleFree "reason"]` — the declared exception to M6

The model template's M6 asks that every kind of dimension one be individuated by its
examination principle: inside the dimension-one fiber the principle is the *only* thing
that separates two kinds, so a dimension-one kind declared without one has been named,
not individuated. `#kind_examination_coverage` (`ExaminationCoverage.lean`) is the census
of that obligation, and a census with honest negatives needs a way to record them or it
is a census someone switches off.

The honest negatives are real. A geometry vocabulary — an illumination cosine, a
normalized wavenumber — is the wave calculus's own and is the product of no measurement
phenomenon; a nominal designation has no principle to carry; a bookkeeping fraction
(a pixel's valid-count ratio) is examined by nothing. Each is dimension one and each is
*correctly* principle-free. Today such a decision lives in a docstring
(`soil-moisture-model`'s `kinds/fresnel.lean`, "NO EXAMINATION PRINCIPLE"), where no
audit can read it. This attribute is that sentence as data: the sweep lists a marked kind
as `⊘ exempted` with its reason, and the gate does not fire on it.

The mark attaches to the **`DimensionedKind`** declaration, not to the `KindOfProperty`,
because the population it exempts a kind from is "dimension one" — a fact about the
`DimensionedKind` — and because the ISO 80000 catalogue and most domain models declare
their kinds inline inside one. A mark on a kind that *does* carry a principle is inert:
the sweep reports the principle and ignores the mark, so a stale exemption cannot hide
an individuation that was later supplied.

Same shape as `@[kindCounterexample]` (`BoundaryAudit.lean`): opting *out* is what takes
an explicit mark, so forgetting to exempt fails loudly at the sweep, and forgetting to
enroll is impossible.
-/
import Lean
import PropertyKindCalculus.Dimension

namespace PropertyKindCalculus

open Lean

/-- One declared exemption: the `DimensionedKind` declaration and the reason it carries no
examination principle, in the author's words. -/
structure PrincipleFreeMark where
  /-- The marked `DimensionedKind` declaration (resolved, so it cannot dangle). -/
  decl : Name
  /-- Why this dimension-one kind is legitimately principle-free. Required and non-empty:
  an exemption without a reason is the docstring problem in a new place. -/
  reason : String
  deriving Repr, Inhabited, BEq

/-- Environment extension collecting every `@[kindPrincipleFree …]`-marked declaration. -/
initialize kindPrincipleFreeExt :
    SimplePersistentEnvExtension PrincipleFreeMark (Array PrincipleFreeMark) ←
  registerSimplePersistentEnvExtension {
    addEntryFn    := fun a e => a.push e
    addImportedFn := fun ess => ess.foldl (init := #[]) (· ++ ·)
  }

/-- `@[kindPrincipleFree "<reason>"]` — declare that a dimension-one `DimensionedKind` is
legitimately without an examination principle. -/
syntax (name := kindPrincipleFreeAttr) "kindPrincipleFree " str : attr

initialize registerBuiltinAttribute {
  name  := `kindPrincipleFreeAttr
  descr := "A dimension-one kind declared principle-free on purpose: `#kind_examination_coverage` lists it as exempted instead of gating on it."
  add   := fun decl stx _kind => do
    match stx with
    | `(attr| kindPrincipleFree $reason:str) =>
        let env ← getEnv
        let some info := env.find? decl
          | throwError "`@[kindPrincipleFree]` could not find '{decl}' in the environment"
        unless info.type.getAppFn.isConstOf ``PropertyKindCalculus.DimensionedKind do
          throwError "`@[kindPrincipleFree]` expects a 'DimensionedKind' — '{decl}' is not \
            one. The mark exempts a dimension-one kind from the examination-coverage sweep, \
            and dimension is a fact about the DimensionedKind, so that is where the mark goes."
        let r := reason.getString
        if r.all Char.isWhitespace then
          throwError "`@[kindPrincipleFree]` on '{decl}' needs a reason: an exemption \
            without one is the docstring problem in a new place"
        modifyEnv fun env => kindPrincipleFreeExt.addEntry env { decl, reason := r }
    | _ => throwError "invalid `kindPrincipleFree` attribute; expected \
        `kindPrincipleFree \"<reason>\"`"
}

/-- Every declared exemption in the environment. -/
def kindPrincipleFreeMarks (env : Environment) : Array PrincipleFreeMark :=
  kindPrincipleFreeExt.getState env

end PropertyKindCalculus
