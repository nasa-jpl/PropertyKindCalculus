/-
# The object layer over a finite index — resultants and assembly

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

## Two sums, and they are not the same sum

A `Finset.sum` of quantities appears in applied models in two shapes that look alike on the
page and are different operations:

  * a **resultant** — several quantities *of one object and one kind* combined into one of the
    same object and kind: the forces acting on a particle, the currents into a node, the
    contributions to one budget. Nothing about the object changes, so nothing but the scale
    gate `add` already demands is needed;
  * an **assembly** — the quantities of the *parts* combined into a quantity of the *whole*.
    The object changes, and whether that is even meaningful is a fact about the kind (§13.5),
    which is what `Assembles` records.

Summing velocities over particles is refused because it is an assembly of an unlicensed kind.
Summing forces on one particle is not an assembly at all, and refusing it would be wrong. Both
are below, and the difference between them is the object index.
-/

import PropertyKindCalculus.Composite
import Mathlib.Algebra.BigOperators.Finprod

namespace PropertyKindCalculus

universe u v

variable {O : Type u} {P : Type v} {k : KindOfProperty} {R V : Type}

/-! ## Resultant — one object, one kind -/

/-- **The resultant of several quantities of one object and kind.** The net force on a
particle, the total current into a node: same object, same kind, so the only gate is the
scale witness `add` itself demands — an ordinal kind has no resultant, a ratio kind does.

The magnitude is a plain `Finset.sum`, so a host library's own `∑ … with …` resultant is
recovered by `rfl`. The index `P` is whatever the library sums over — a `Finset` of forces, a
subtype of a multiset — and is *not* the object: every summand characterizes the same `o`. -/
def resultantOver [AddCommMonoid V] {o : O} {k : KindOfProperty} (_h : DifferenceKind k)
    (s : Finset P) (f : P → IndividualQuantity o k V) : IndividualQuantity o k V :=
  ⟨∑ p ∈ s, (f p).magnitude⟩

@[simp] theorem resultantOver_magnitude [AddCommMonoid V] {o : O} {k : KindOfProperty}
    (h : DifferenceKind k) (s : Finset P) (f : P → IndividualQuantity o k V) :
    (resultantOver h s f).magnitude = ∑ p ∈ s, (f p).magnitude := rfl

/-- **The resultant over every summand** — `resultantOver` at `Finset.univ`, the form
`∑ x : P, …` is notation for. -/
def resultantAll [Fintype P] [AddCommMonoid V] {o : O} {k : KindOfProperty}
    (h : DifferenceKind k) (f : P → IndividualQuantity o k V) : IndividualQuantity o k V :=
  resultantOver h Finset.univ f

@[simp] theorem resultantAll_magnitude [Fintype P] [AddCommMonoid V] {o : O}
    {k : KindOfProperty} (h : DifferenceKind k) (f : P → IndividualQuantity o k V) :
    (resultantAll h f).magnitude = ∑ p : P, (f p).magnitude := rfl

/-- **The object-free twin.** The same `Finset.sum` one layer down, for a model that kinds its
quantities without indexing them by object. It is here rather than with `Quantity` for the
reason the rest of this module is: the sum is Mathlib's. Having both means a comparison
between an object-indexed model and a kind-only one differs in the object index and in nothing
else. -/
def Quantity.resultantOver [AddCommMonoid V] {k : KindOfProperty} (_h : DifferenceKind k)
    (s : Finset P) (f : P → Quantity k V) : Quantity k V :=
  ⟨∑ p ∈ s, (f p).magnitude⟩

@[simp] theorem Quantity.resultantOver_magnitude [AddCommMonoid V] {k : KindOfProperty}
    (h : DifferenceKind k) (s : Finset P) (f : P → Quantity k V) :
    (Quantity.resultantOver h s f).magnitude = ∑ p ∈ s, (f p).magnitude := rfl

/-! ## Assembly — the parts to the whole -/

/-- **Assembly over a finite set of parts.** The quantity of `whole`, summed from the
quantities of the parts in `s` — each of which must characterize *its own* part, which is
the gate, and licensed by `Assembles k`, which is the curation.

The magnitude is a plain `Finset.sum`, so a host library's own total is recovered by `rfl`
rather than by a rewriting lemma. -/
def assembleOver [AddCommMonoid R] (σ : SortOfSystem) [Assembles σ k] (whole : O)
    (part : P → O) (s : Finset P)
    (f : (p : P) → IndividualQuantity (part p) k R) : IndividualQuantity whole k R :=
  ⟨∑ p ∈ s, (f p).magnitude⟩

@[simp] theorem assembleOver_magnitude [AddCommMonoid R] (σ : SortOfSystem) [Assembles σ k]
    (whole : O)
    (part : P → O) (s : Finset P) (f : (p : P) → IndividualQuantity (part p) k R) :
    (assembleOver σ whole part s f).magnitude = ∑ p ∈ s, (f p).magnitude := rfl

/-- **Assembly over every part** — `assembleOver` at `Finset.univ`, which is the form a host
library's aggregate is written in (`∑ p : P, …` is notation for exactly this sum). -/
def assembleAll [Fintype P] [AddCommMonoid R] (σ : SortOfSystem) [Assembles σ k] (whole : O)
    (part : P → O)
    (f : (p : P) → IndividualQuantity (part p) k R) : IndividualQuantity whole k R :=
  assembleOver σ whole part Finset.univ f

@[simp] theorem assembleAll_magnitude [Fintype P] [AddCommMonoid R] (σ : SortOfSystem)
    [Assembles σ k] (whole : O)
    (part : P → O) (f : (p : P) → IndividualQuantity (part p) k R) :
    (assembleAll σ whole part f).magnitude = ∑ p : P, (f p).magnitude := rfl

end PropertyKindCalculus
