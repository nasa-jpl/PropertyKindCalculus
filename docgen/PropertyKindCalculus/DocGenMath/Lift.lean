/-
Copyright (c) 2026 California Institute of Technology. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nicolas Rouquette
-/
import Lean
import PropertyKindCalculus
import PropertyKindCalculus.DocGenMath.Term
import PropertyKindCalculus.DocGenMath.Registry

/-!
# Stage 1 — Lift `Lean.Expr → MathTerm`

Walk the *authored surface* of a definition's value (never `whnf`/unfold — that would collapse
`Quantity.mul h a b` into `Quantity.mk (a.magnitude * b.magnitude)` and destroy the notation we want
to show). We match the PKC combinator alphabet by its head symbol and keep only the value operands,
dropping the kind-law `Prop` witnesses, the instance arguments, the carrier/kind implicits, and any
`mdata`. Associativity is flattened here, so `a + b + c` and `a·b·c` become single n-ary nodes.

## What the lift recognizes beyond the arithmetic alphabet

* **`let` bindings.** By default they are `zeta`-reduced — the bound value is substituted into the
  body — so the body renders in terms of the model's operators rather than falling to the
  opaque-leaf branch. That is a presentation-only inlining: it duplicates a bound subterm used more
  than once, which is fine for one threaded intermediate and ruinous for a shared one. A
  `KeepPolicy` says which bindings to *keep* instead, emitting each as an auxiliary equation
  (`MathSystem.aux`) and leaving its name in the body — the `where` of a textbook equation.
* **Structure literals.** `{ nd := …, kd := … }` lifts to a `record`, which the printer renders as
  the *system* of field equations. A model whose result is a record of quantities has no single
  defining equation, and collapsing it into one was how such definitions used to render.
* **`match`.** A single-alternative match is a destructuring binder (`let (n, k) := nkOfEps …`):
  the components are named, the pair is emitted as one auxiliary equation, and the body renders in
  terms of the names. A multi-alternative match is genuine case analysis and lifts to `cases`, whose
  patterns come from the matcher's own equation lemmas — so a branch is labelled with the pattern
  the author wrote, not with a guess from constructor order.
* **`@[pkc_math_config]` fields.** `cfg.two` lifts as a bare `sym`, not as an application: it is one
  of the model's named constants, and the configuration value it is read from carries nothing for
  the reader. `Registry.resolveToken` then qualifies it by its type (`\mathrm{AvsConfig.two}`).
* **`@[pkc_math_transparent]` wrappers.** An application of a tagged notational wrapper renders as
  its argument, so a carrier's numeral injection `ofN 2` reads `2` instead of `\mathrm{ofN}(2)`.
* **Object-indexed quantities.** `IndividualQuantity o k R` gates its operations on a shared
  object as well as on the kinds, and a leaf of that type renders with the object as a
  **subscript** (`objectLabel?`): `V_A = m_A\,\omega_A^2\,x_A^2`. Without it two systems'
  equations are distinct types that reach the page as the same string. A definition generic in
  its object renders unsubscripted. The layer's named combinators (`IndividualQuantity.mul`,
  `div`, `add`) join their `Quantity` twins in the operator alphabet; a model written through
  `OperatorTable`'s instances arrives as `HMul.hMul` and needs no separate case, since the
  binary branch reads the last two arguments and is indifferent to what precedes them.

`substitute` is the opt-in **delta** counterpart to the `let`-zeta: given a set of declaration names
it inlines their bodies, so `@[pkc_math substituting attenuationQ]` can show a model's equation with
a named helper expanded (`RENDERING.md` §5, *Derivations by substitution*). It runs as a pre-pass on
the `Expr`, before the lift, so the inlined body's own `let`s are handled on the way in exactly as if
they had been written at the use site. Delta is meaning-preserving, so the result stays in the
**F** (faithful) tier.

The lift is **total and defensive**: any head it does not special-case becomes a generic `fn`
(keeping only the explicit arguments), and any leaf it cannot read becomes an escaped `raw` `\text{…}`
box. It never fails, and it never emits malformed LaTeX, so rendering degrades gracefully on an
unfamiliar model rather than crashing the attribute or publishing broken math.
-/

namespace PropertyKindCalculus.DocGenMath

open Lean Meta

/-- Which `let` bindings to keep as auxiliary equations instead of inlining.

The default inlines everything, which is what every rendering did before `keeping` existed, so an
un-annotated definition renders byte-identically. -/
inductive KeepPolicy where
  /-- Zeta-reduce every `let` (the default). -/
  | inlineAll
  /-- Keep every `let` as an auxiliary equation, in binding order. -/
  | keepAll
  /-- Keep only the bindings with these binder names. -/
  | keepOnly (names : Array Name)
  deriving Inhabited, BEq

/-- Whether a `let` binder of this name is kept as an auxiliary equation. -/
def KeepPolicy.keeps : KeepPolicy → Name → Bool
  | .inlineAll,    _ => false
  | .keepAll,      _ => true
  | .keepOnly ns,  n => ns.contains n

/-- Every `let` binder name occurring in `e`, including inside `match` alternatives. -/
private partial def collectLetNames : Expr → Array Name → Array Name
  | .letE n _ v b _,   acc => collectLetNames b (collectLetNames v (acc.push n))
  | .app f a,          acc => collectLetNames a (collectLetNames f acc)
  | .lam _ t b _,      acc => collectLetNames b (collectLetNames t acc)
  | .forallE _ t b _,  acc => collectLetNames b (collectLetNames t acc)
  | .mdata _ e,        acc => collectLetNames e acc
  | .proj _ _ e,       acc => collectLetNames e acc
  | _,                 acc => acc

/-- The `let` binder names of `declName`'s value — what `@[pkc_math keeping x, y]` may name. Reading
them lets the attribute reject a name that binds nothing, instead of silently rendering as if the
clause had not been written. -/
def letBinderNames (declName : Name) : CoreM (Array Name) := do
  match (← getEnv).find? declName with
  | some (.defnInfo di) => return collectLetNames di.value #[]
  | _                   => return #[]

/-- The lift's state: the auxiliary equations accumulated so far, in binding order. -/
abbrev LiftM := StateRefT (Array (MathTerm × MathTerm)) MetaM

/-- Splice a term into an n-ary sum's argument array (flatten nested `add`). -/
private def addArgs : MathTerm → Array MathTerm
  | .add ts => ts
  | t       => #[t]

/-- Splice a term into an n-ary product's argument array (flatten nested `mul`). -/
private def mulArgs : MathTerm → Array MathTerm
  | .mul ts => ts
  | t       => #[t]

/-- Splice a term into a tuple's component array. Only the *second* component of a `Prod.mk` is
spliced, because `Prod` nests to the right: `(a, b, c)` is `⟨a, ⟨b, c⟩⟩` and renders as one
three-component tuple, exactly as Lean's anonymous-constructor notation displays it, while a
genuinely nested left component `⟨⟨a, b⟩, c⟩` keeps its inner parentheses. -/
private def tupleArgs : MathTerm → Array MathTerm
  | .tuple ts => ts
  | t         => #[t]

/-- The last argument of an application (the innermost operand of a unary combinator). -/
private def lastArg (args : Array Expr) : Expr := args[args.size - 1]!

/-- The last two arguments (the operands of a binary combinator, regardless of how many
implicit/instance arguments precede them). -/
private def lastTwo (args : Array Expr) : Expr × Expr :=
  (args[args.size - 2]!, args[args.size - 1]!)

/-- **The object subscript of a leaf.** For a leaf whose type is `IndividualQuantity o k R` with
a *concrete* object `o`, the label to subscript its symbol with; `none` for every other type.

An object-indexed model is the one that keeps the quantities of two systems apart, and without
this the distinction is invisible on the page: the potential energies of two oscillators are
rigorously distinct types that would otherwise render to the same string — the very confusion
the object index exists to prevent, reappearing in the presentation. Subscripting is also what a
physicist writes (`V_A = m_A\,\omega_A^2\,x_A^2`), so the index becomes the notation rather than
bookkeeping the reader has to be told about.

The label is the `@[pkc_math_symbol]` override registered on the object's own declaration when
there is one — which is how an author gets a short `A` out of a system named
`"oscillator A"` — and otherwise the system's `id` in a `\text{…}` box, which is always valid
and never silently wrong.

A definition *generic* in its object (`(o : Object)` still a binder) has no concrete object to
name, so it renders unsubscripted: `whnf` cannot reach a `System.mk` and this returns `none`.
So does a quantity indexed by a **structural** object type — a host library's particle or mesh
cell, which the layer gates but cannot name (`Foundations.lean`, `Designated`): there is no
`System.mk` to reach, and an unsubscripted symbol is the honest rendering of an object that has
no designation. An author who wants a label there registers `@[pkc_math_symbol]` on the object's
own declaration, which is the first branch below and works for any object type.

Arity 4, not 3: the object type is the layer's leading implicit parameter, so the object itself
is argument 1. -/
def objectLabel? (ty : Expr) : MetaM (Option String) := do
  let ty ← whnf ty
  unless ty.isAppOfArity ``PropertyKindCalculus.IndividualQuantity 4 do return none
  let o := ty.getAppArgs[1]!
  -- an override registered on the object's own declaration wins
  if let .const c _ := o.getAppFn then
    if let some nota := getMathSymbol? (← getEnv) c then return some nota.latex
  -- otherwise unfold the object to its `System.mk "…"` literal and take the id
  let o ← whnf o
  unless o.isAppOfArity ``PropertyKindCalculus.System.mk 1 do return none
  match ← whnf o.getAppArgs[0]! with
  | .lit (.strVal s) =>
    -- A short token-like id is usable as a symbol directly (`"A"`, `"rotor2"`), through the same
    -- heuristics an atom name gets — so a system named for its subscript needs no override at
    -- all. Anything with spaces or punctuation is not LaTeX and goes in a `\text{…}` box, which
    -- is verbose but never silently malformed; `@[pkc_math_symbol]` is how such a system gets a
    -- short label.
    if !s.isEmpty && s.all Char.isAlphanum then return some (builtinSymbol s)
    else return some (latexText s)
  | _                => return none

/-- The names of the transcendental/trig unary functions, rendered as `fn <base> #[arg]`. -/
private def unaryFns : List Name :=
  [``PropertyKindCalculus.Quantity.exp, ``PropertyKindCalculus.Quantity.log,
   ``PropertyKindCalculus.Quantity.sin, ``PropertyKindCalculus.Quantity.cos,
   ``PropertyKindCalculus.Quantity.tan, ``PropertyKindCalculus.Quantity.sinh,
   ``PropertyKindCalculus.Quantity.cosh, ``PropertyKindCalculus.Quantity.tanh,
   ``PropertyKindCalculus.Quantity.asin, ``PropertyKindCalculus.Quantity.acos,
   ``PropertyKindCalculus.Quantity.atan]

/-- Keep only the explicitly-bound arguments of `fn` applied to `args` (drop implicits, instances,
and strict-implicits), for the generic `fn` fallback on an unrecognized head. -/
private def explicitArgs (fn : Expr) (args : Array Expr) : MetaM (Array Expr) := do
  let finfo ← getFunInfo fn
  let mut out := #[]
  for h : i in [0:args.size] do
    let a := args[i]
    if hi : i < finfo.paramInfo.size then
      if finfo.paramInfo[i].binderInfo == .default then out := out.push a
    else
      out := out.push a
  return out

/-- The structure fields of `name`'s constructor, when `name` *is* a structure constructor whose
field list matches its arity — the shape a structure literal elaborates to. `none` for every other
constant, so ordinary applications keep the ordinary path. -/
private def structureLiteralFields? (env : Environment) (name : Name) (numArgs : Nat) :
    Option (Nat × Array Name) :=
  match env.find? name with
  -- `isStructure` must be checked *before* `getStructureFields`, which panics on anything else
  | some (.ctorInfo ci) =>
    if isStructure env ci.induct && ci.numFields > 0
        && numArgs == ci.numParams + ci.numFields then
      let fields := getStructureFields env ci.induct
      if fields.size == ci.numFields then some (ci.numParams, fields.map (ci.induct ++ ·)) else none
    else none
  | _ => none

mutual

/-- Stage 1. Lift an already-elaborated value `Expr` to the presentation IR, accumulating the
auxiliary equations of whatever `policy` keeps. -/
partial def liftTerm (policy : KeepPolicy) (e : Expr) : LiftM MathTerm := do
  match e with
  | .mdata _ e'        => liftTerm policy e'
  | .letE n t v b _    =>
    if policy.keeps n then
      -- name it: the binding becomes one auxiliary equation and the body refers to it by name.
      -- A name already taken is *disambiguated*, not dropped: a definition may open two blocks with
      -- the same local name for different values (`denomB` and `denomU` each bind their own
      -- `let ωτ := ω·τ`), and two equations with one left-hand side and two right-hand sides is not
      -- a system anyone can read. The suffix rides the trailing-digit rule, so the second reads
      -- `\mathrm{ωτ}_{2}`.
      let vT ← liftTerm policy v
      let taken := (← get).flatMap fun (l, _) => match l with
        | .sym s   => #[s]
        | .tuple ts => ts.filterMap fun t => match t with | .sym s => some s | _ => none
        | _        => #[]
      let mut nm := toString n
      let mut k := 2
      while taken.contains nm do
        nm := toString n ++ toString k
        k := k + 1
      modify (·.push (.sym nm, vT))
      withLetDecl (Name.mkSimple nm) t v fun x => liftTerm policy (b.instantiate1 x)
    else
      liftTerm policy (b.instantiate1 v)          -- zeta: inline the `let`-bound value
  | .lit (.natVal n)   => return .num (Int.ofNat n)
  | .fvar fid          => do
    let nm := toString (← fid.getUserName)
    match ← objectLabel? (← fid.getType) with
    -- an object-indexed leaf carries its object as a subscript. The base token is resolved
    -- *here* rather than left to the printer because the result is composed LaTeX, not a token
    -- the registry could look up — hence `raw`, which shares `sym`'s atom precedence.
    | some lbl => return .raw ((resolveToken (← getEnv) nm).latex ++ "_{" ++ lbl ++ "}")
    | none     => return .sym nm
  | .bvar _            => return .raw (latexText "?")   -- should not occur after a telescope
  | _ =>
    -- a `match` is not an ordinary application: its motive and alternatives are lambdas, and
    -- rendering it as `match_1(fun x ↦ …, …)` is how a case analysis used to reach the page
    if let some app ← matchMatcherApp? e then
      if let some t ← liftMatcher policy app then return t
    let fn := e.getAppFn
    let args := e.getAppArgs
    match fn with
    | .const name _ => liftApp policy name args e
    | .fvar fid =>
      let nm := toString (← fid.getUserName)
      if args.isEmpty then return .sym nm
      else return .fn nm (← (← explicitArgs fn args).mapM (liftTerm policy))
    | _ => return .raw (latexText (toString (← ppExpr e)))

/-- Lift an application whose head is the constant `name`. -/
partial def liftApp (policy : KeepPolicy) (name : Name) (args : Array Expr) (e : Expr) :
    LiftM MathTerm := do
  let fn := e.getAppFn
  -- numerals: `@OfNat.ofNat α n inst` — the numeral is the raw `Nat` literal argument
  if name == ``OfNat.ofNat then
    if let some n := args.findSome? (fun a => match a with
        | .lit (.natVal k) => some k | _ => none) then
      return .num (Int.ofNat n)
  -- coercions: drop and descend into the underlying value
  if name == ``Nat.cast || name == ``Int.cast || name == ``NatCast.natCast
      || name == ``IntCast.intCast then
    if args.size ≥ 1 then return ← liftTerm policy (lastArg args)
  -- the `Quantity` / `IndividualQuantity` wrapper: `⟨r⟩` — render its magnitude
  if name == ``PropertyKindCalculus.Quantity.mk
      || name == ``PropertyKindCalculus.IndividualQuantity.mk then
    if args.size ≥ 1 then return ← liftTerm policy (lastArg args)
  -- an authored notational wrapper (`ofN 2`): render the argument it wraps
  if isTransparentWrapper (← getEnv) name then
    let expl ← explicitArgs fn args
    if expl.size == 1 then return ← liftTerm policy expl[0]!
  -- tuples: a multi-output model (residual + Jacobian columns, …) returns a `Prod.mk` chain
  if name == ``Prod.mk && args.size ≥ 2 then
    let (x, y) := lastTwo args
    return .tuple (#[← liftTerm policy x] ++ tupleArgs (← liftTerm policy y))
  -- binary ring operators (ergonomic `+ - * /` and the named kind-gated forms)
  if args.size ≥ 2 then
    let (x, y) := lastTwo args
    if name == ``HAdd.hAdd || name == ``PropertyKindCalculus.Quantity.add
        || name == ``PropertyKindCalculus.IndividualQuantity.add then
      return .add (addArgs (← liftTerm policy x) ++ addArgs (← liftTerm policy y))
    if name == ``HSub.hSub || name == ``PropertyKindCalculus.Quantity.sub then
      return .add (addArgs (← liftTerm policy x) ++ #[.neg (← liftTerm policy y)])
    if name == ``HMul.hMul || name == ``PropertyKindCalculus.Quantity.mul
        || name == ``PropertyKindCalculus.IndividualQuantity.mul then
      return .mul (mulArgs (← liftTerm policy x) ++ mulArgs (← liftTerm policy y))
    if name == ``HDiv.hDiv || name == ``PropertyKindCalculus.Quantity.div
        || name == ``PropertyKindCalculus.IndividualQuantity.div then
      return .frac (← liftTerm policy x) (← liftTerm policy y)
    if name == ``HPow.hPow then
      return .pow (← liftTerm policy x) (← liftTerm policy y)
    if name == ``PropertyKindCalculus.Quantity.atan2 then
      return .fn "atan2" #[← liftTerm policy x, ← liftTerm policy y]
  -- unary negation
  if name == ``Neg.neg && args.size ≥ 1 then
    return .neg (← liftTerm policy (lastArg args))
  -- unary transcendental/trig functions: keep the last (value) operand, drop the witness
  if unaryFns.contains name && args.size ≥ 1 then
    return .fn name.getString! #[← liftTerm policy (lastArg args)]
  -- a field of a `@[pkc_math_config]` structure is one of the model's named constants, not a
  -- function of the configuration: drop the configuration value and render the qualified symbol
  if (configFieldName? (← getEnv) name).isSome then
    return .sym (toString name)
  -- a structure literal is a *system* of field equations, not one equation
  if let some (numParams, fields) := structureLiteralFields? (← getEnv) name args.size then
    let vals := args.extract numParams args.size
    return .record (← (fields.zip vals).mapM fun (f, v) =>
      return (toString f, ← liftTerm policy v))
  -- generic fallback: a named application, keeping only explicit operands
  let expl ← explicitArgs fn args
  if expl.isEmpty then return .sym (toString name)
  else return .fn (toString name) (← expl.mapM (liftTerm policy))

/-- Lift a `match`. Returns `none` when the shape is one this stage cannot read faithfully, so the
caller falls back to the generic application path (which is at least valid LaTeX).

A **single alternative** is a destructuring binder — `let (n, k) := nkOfEps …`, which elaborates to a
one-branch match on a structure. There is no case analysis to show: the components are named, the
binder itself becomes one auxiliary equation `(n, k) = nkOfEps …`, and the body renders in terms of
the names. That is both what the source says and the only rendering that does not duplicate the
scrutinee once per component.

**Several alternatives** are genuine case analysis, rendered as `cases`. -/
partial def liftMatcher (policy : KeepPolicy) (app : MatcherApp) : LiftM (Option MathTerm) := do
  if app.alts.isEmpty || app.discrs.isEmpty then return none
  let ds ← app.discrs.mapM (liftTerm policy)
  let scrutinee : MathTerm := if h : ds.size = 1 then ds[0]'(by omega) else .tuple ds
  if app.alts.size == 1 then
    let numFields := app.altInfos[0]!.numFields
    let numBinders := app.altNumParams[0]!
    return ← lambdaBoundedTelescope app.alts[0]! numBinders fun xs body => do
      unless xs.size == numBinders do return none
      if numFields == 0 then
        -- `match e with | _ => body`: nothing is bound, so there is nothing to name
        return some (← liftTerm policy body)
      let names ← xs.extract 0 numFields |>.mapM fun x => do
        return MathTerm.sym (toString (← x.fvarId!.getUserName))
      modify (·.push (if h : names.size = 1 then names[0]'(by omega) else .tuple names, scrutinee))
      return some (← liftTerm policy body)
  let patterns ← matcherPatterns app
  let mut alts : Array (MathTerm × MathTerm) := #[]
  for h : i in [0:app.alts.size] do
    let numBinders := app.altNumParams[i]!
    let value ← lambdaBoundedTelescope app.alts[i] numBinders fun _ body => liftTerm policy body
    alts := alts.push (patterns[i]!, value)
  return some (.cases scrutinee alts)

/-- The pattern of each alternative of a `match`, read from the matcher's own equation lemmas — the
only place Lean keeps them (`MatcherInfo` records arities, not patterns). Each equation's left-hand
side is the matcher applied to *that branch's pattern*, so lifting that argument gives exactly what
the author wrote the branch on.

Falls back to an unlabelled `\text{case i}` when the equations are unavailable or do not correspond
one-to-one with the alternatives (overlapping patterns generate a different number of them). Guessing
from constructor order instead would silently mislabel a branch whenever a `match` lists its cases in
another order — a wrong equation on a published page, which is worse than an unlabelled one. -/
partial def matcherPatterns (app : MatcherApp) : LiftM (Array MathTerm) := do
  let fallback : Array MathTerm :=
    (Array.range app.alts.size).map fun i => .raw (latexText s!"case {i + 1}")
  let eqns? : Option Match.MatchEqns ←
    try
      pure (some (← Match.getEquationsFor app.matcherName))
    catch _ => pure none
  let some eqns := eqns? | return fallback
  unless eqns.eqnNames.size == app.alts.size do return fallback
  let discrIdx := app.numParams + 1                 -- params, then the motive, then the discrs
  let mut out : Array MathTerm := #[]
  for h : i in [0:eqns.eqnNames.size] do
    let some ci := (← getEnv).find? eqns.eqnNames[i] | return fallback
    let pat? ← forallTelescope ci.type fun _ concl => do
      let some (_, lhs, _) := concl.eq? | return none
      let lhsArgs := lhs.getAppArgs
      if h : discrIdx < lhsArgs.size then
        return some (← liftTerm .inlineAll lhsArgs[discrIdx])
      else
        return none
    match pat? with
    | some p => out := out.push p
    | none   => return fallback
  return out

end

/-- Lift `e` to a `MathSystem`: the term, plus the auxiliary equations `policy` kept, with
record-field aliases collapsed. -/
def liftSystem (policy : KeepPolicy) (e : Expr) : MetaM MathSystem := do
  let (body, aux) ← (liftTerm policy e).run #[]
  return ({ body, aux } : MathSystem).collapseAliases

/-- Lift `e` to a bare `MathTerm`, inlining every `let` — the entry point for a rendering with no
`where` block, and the one the pure-stage tests use. -/
def liftExpr (e : Expr) : MetaM MathTerm :=
  return (← liftSystem .inlineAll e).body

/-- The opt-in **delta** pre-pass: inline the body of every application whose head is one of
`names`, so the caller's equation can be shown with those helpers substituted. Runs before
`liftTerm`, so the inlined `let`s are handled by the lift as usual.

`Meta.transform`'s `.visit` revisits each result, so nested occurrences (a substituted body that
itself calls a substituted helper) are expanded too. That would not terminate on a helper whose own
value mentions it, which is why `DocGenMath.Attr` rejects such a name at attribute-application time
rather than looping here. Anything that is not a `defnInfo` — a `partial def`, an opaque constant,
a theorem — is left alone. -/
def substitute (names : Array Name) (e : Expr) : MetaM Expr := do
  if names.isEmpty then return e
  Meta.transform e (pre := fun s => do
    let .const n us := s.getAppFn | return .continue
    unless names.contains n do return .continue
    let some (.defnInfo di) := (← getEnv).find? n | return .continue
    let value := di.value.instantiateLevelParams di.levelParams us
    return .visit (mkAppN value s.getAppArgs).headBeta)

/-- Whether `declName` can be substituted without looping: it must be a definition whose own value
does not mention it (a recursive definition would make `substitute`'s `.visit` diverge). -/
def isSubstitutable (env : Environment) (declName : Name) : Bool :=
  match env.find? declName with
  | some (.defnInfo di) => (di.value.find? (·.isConstOf declName)).isNone
  | _                   => false

end PropertyKindCalculus.DocGenMath
