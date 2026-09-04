/-
# Assembly over a finite index — `assembleOver` / `assembleAll`

`Composite.lean` (Mathlib-free core) states assembly over PKC's own mereology: a
`Decomposition` tree of parts, folded with `Carrier.add`. That is the right shape for the
§13.5 law, which is a statement about disjoint composition to arbitrary depth, and it is the
one `assemble_eq_measured` cashes.

A host library does not usually hand over a tree. It hands over a **finite index**: a
`Fintype` of particles, the cells of a grid, a `Multiset` coerced to a type. Its own totals
are then written `∑ p : P, …`, and the whole value of a kinded layer over such a library is
that its arithmetic is *definitionally* the library's — a gate added, nothing computed
differently. Folding a tree instead would give a different term and lose that.

So this is the same license (`Assembles`) over the other index structure, and it lives with
the `Dimension` library for the reason `BoundsReal` does: `Finset.sum` needs Mathlib, the one
dependency kept out of the core. It is not ℝ-specific — any `AddCommMonoid` carrier serves,
and a frame vector or a `Float32` is as good as a real.
-/

import PropertyKindCalculus.Composite
import Mathlib.Algebra.BigOperators.Finprod

namespace PropertyKindCalculus

universe u v

variable {O : Type u} {P : Type v} {k : KindOfProperty} {R : Type}

/-- **Assembly over a finite set of parts.** The quantity of `whole`, summed from the
quantities of the parts in `s` — each of which must characterize *its own* part, which is
the gate, and licensed by `Assembles k`, which is the curation.

The magnitude is a plain `Finset.sum`, so a host library's own total is recovered by `rfl`
rather than by a rewriting lemma. -/
def assembleOver [AddCommMonoid R] [Assembles k] (whole : O) (part : P → O) (s : Finset P)
    (f : (p : P) → IndividualQuantity (part p) k R) : IndividualQuantity whole k R :=
  ⟨∑ p ∈ s, (f p).magnitude⟩

@[simp] theorem assembleOver_magnitude [AddCommMonoid R] [Assembles k] (whole : O)
    (part : P → O) (s : Finset P) (f : (p : P) → IndividualQuantity (part p) k R) :
    (assembleOver whole part s f).magnitude = ∑ p ∈ s, (f p).magnitude := rfl

/-- **Assembly over every part** — `assembleOver` at `Finset.univ`, which is the form a host
library's aggregate is written in (`∑ p : P, …` is notation for exactly this sum). -/
def assembleAll [Fintype P] [AddCommMonoid R] [Assembles k] (whole : O) (part : P → O)
    (f : (p : P) → IndividualQuantity (part p) k R) : IndividualQuantity whole k R :=
  assembleOver whole part Finset.univ f

@[simp] theorem assembleAll_magnitude [Fintype P] [AddCommMonoid R] [Assembles k] (whole : O)
    (part : P → O) (f : (p : P) → IndividualQuantity (part p) k R) :
    (assembleAll whole part f).magnitude = ∑ p : P, (f p).magnitude := rfl

end PropertyKindCalculus
