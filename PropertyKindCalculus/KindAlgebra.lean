/-
# `kind_algebra` — a model's derived-kind algebra in one declaration

The residue MR11 leaves after the operator table is the *stand-up* cost: before
`V = m·ω²·x²` can be authored with operators, its model must declare each derived kind
(`angular frequency squared`, `mass × angular frequency²`, …) and register each
operator-table entry — in the harmonic-oscillator benchmark, three kind declarations and
four instances, seven declarations of scaffolding whose entire information content is four
kind equations.

`kind_algebra` collapses that to the kind equations themselves. One block —

```
kind_algebra
  kω2  : "angular frequency squared"  := angularFrequency * angularFrequency
  kmω2 : "mass × angular frequency²"  := massK * kω2
```

— expands, per line, to exactly the declarations written by hand today: the derived
`KindOfProperty` (ratio scale, with the given id) and the `KindMul`/`KindDiv` table entry
that produces it, witnessed by `ProductKind.ofRatio`/`QuotientKind.ofRatio`. Later lines
may use kinds minted by earlier lines. Nothing in the discipline weakens: the expansion
*is* the hand-written registration, the block is the authored declaration `grep` finds,
and the curation rule (at most one entry per operand pair) is unchanged — a duplicate
pair is registered exactly as wrongly as it would be by hand.

Scope, deliberately narrow: minted kinds are ratio-scale with no examination principle —
the case of every *derived* kind in a product algebra. Base kinds (which carry the
examination principle, the semantics) are still declared by hand; a non-ratio algebra
still writes its witnesses explicitly.

Like `KindEdges`, this module imports `Lean` and is built by the package glob but kept out
of the prelude-only `import PropertyKindCalculus` spine.
-/

module

public import Lean
public import PropertyKindCalculus.OperatorTable

public section -- pkc-blanket

namespace PropertyKindCalculus.KindAlgebra

open Lean Elab Command

/-- One line of a model's kind algebra: mint the derived kind `name` (ratio scale, with
the quoted id) and register the operator-table entry `a * b ↦ name` (or `a / b ↦ name`)
that produces it. -/
syntax kindAlgebraEntry := ident " : " str " := " term:71 (" * " <|> " / ") term:71

/-- A model's derived-kind algebra, one kind equation per line. Each line expands to the
derived `KindOfProperty` and its curated `KindMul`/`KindDiv` table entry — exactly the
declarations otherwise written by hand. -/
syntax "kind_algebra" withPosition((colGe kindAlgebraEntry)+) : command

elab_rules : command
  | `(command| kind_algebra $entries:kindAlgebraEntry*) => do
    for e in entries do
      match e with
      | `(kindAlgebraEntry| $name:ident : $id:str := $a * $b) => do
        elabCommand (← `(command|
          def $name : KindOfProperty := { id := $id, scale := .ratio }))
        elabCommand (← `(command|
          instance : KindMul $a $b $name := ⟨ProductKind.ofRatio _ _ _⟩))
      | `(kindAlgebraEntry| $name:ident : $id:str := $a / $b) => do
        elabCommand (← `(command|
          def $name : KindOfProperty := { id := $id, scale := .ratio }))
        elabCommand (← `(command|
          instance : KindDiv $a $b $name := ⟨QuotientKind.ofRatio _ _ _⟩))
      | _ => throwErrorAt e "unrecognized kind_algebra entry"

end PropertyKindCalculus.KindAlgebra

end -- pkc-blanket
