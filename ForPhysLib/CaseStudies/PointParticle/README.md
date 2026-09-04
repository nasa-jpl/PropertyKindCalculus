# Case study — point particles, and how a quantity says whose it is

Four attempts at typing the same physics, scored. The point is not that one attempt wins; it
is that **each fails in a way characteristic of its own idea**, and that those failures are
build artifacts rather than opinions.

The occasion is [physlib#1612](https://github.com/leanprover-community/physlib/pull/1612)
(head `3ae4ae20`, unmerged), which ties a force to the object it acts on with a structure
field. That is the first time upstream has needed the question
[Tier 3](../../REQUIREMENTS.md#tier-3--two-objects) asks, and it answers it a different
way — so it is a good subject: good enough to show both what a field structurally cannot do
*and* what it costs to fix.

Requirements are not restated here. Each is a link.

---

## The question

A measured quantity is always the property of some object. There are exactly two places to
put that object:

- **in the value** — a field the force carries, available to a runtime test, invisible to the
  checker. This is #1612.
- **in the type** — an index, checked, and (naively) at the cost of the shape the library is
  written in.

The four attempts are the four points on that line, and the last one shows the choice is
false.

## The physics

A system is a reference frame and a **multiset** of particles, coerced to a type — so a
particle is a *position in a multiset*: anonymous, with no id, no name, and no `DecidableEq`
written for it. Every attempt has to say something about an object that cannot be named.

Five statements, chosen because each fails differently under a different typing:

| | statement | why it is here |
|---|---|---|
| 1 | Newton II, per particle: `netForce p = m_p · a_p` | a *scalar* quantity acting on a *vector* one |
| 2 | Newton III: `internalForces.map reverse = internalForces` | a statement about an ordered **pair** of objects |
| 3 | the aggregates: `System.mass`, `System.momentum` | quantities of the **whole**, from quantities of the parts |
| 4 | the aggregate that is not one: `∑ p, p.velocity` | same shape as (3), and wrong |
| 5 | the resultant that is not an aggregate: `netForce` | same `∑`, and right — the object does not change |

(4) and (5) are the pair to watch. They are written identically in the first two attempts, and
telling them apart is the whole content of the object layer.

## The attempts

One file each, in `ForPhysLib`. The shared subject — the replica of #1612's shape, the kind
vocabulary, the registrations — is [`Common.lean`](Common.lean), so what differs between the
attempts is *only* the typing of a force and of a per-particle quantity.

| file | idea |
|---|---|
| [`Attempt1Fields.lean`](Attempt1Fields.lean) | **#1612 as written.** `target` a field, values bare `frame.Vector`. Includes what the PR gets right, which is not nothing. |
| [`Attempt2Kinds.lean`](Attempt2Kinds.lean) | **Kind the values, keep the field.** The proposal's Stage 2 applied to this PR: every value at its ISO 80000 kind, `target` untouched. |
| [`Attempt3Indexed.lean`](Attempt3Indexed.lean) | **Move the target into the type.** The direct fix, given its best shot, then priced. |
| [`Attempt4Dependent.lean`](Attempt4Dependent.lean) | **Keep the field; let the value's type depend on it.** One line differs from #1612. |

[`Scorecard.lean`](Scorecard.lean) is the only place the attempts meet, and carries the part
of the table below a build can check.

---

## The scorecard

✅ checked · ❌ accepted and wrong · ⚠️ accepted at a cost

| | | 1 · field | 2 · kinds | 3 · indexed | 4 · dependent |
|---|---|---|---|---|---|
| **Metrology** | position + force of one particle ([MR1](../../REQUIREMENTS.md#mr1-dimensional-homogeneity)) | ❌ | ✅ | ✅ | ✅ |
| | mass of `p` × acceleration of `q` ([MR7](../../REQUIREMENTS.md#mr7-object-identity)) | ❌ | ❌ | ✅ | ✅ |
| | two particles' masses add ([MR7](../../REQUIREMENTS.md#mr7-object-identity)) | ❌ | ❌ | ✅ | ✅ |
| | retarget a force by record update ([MR10](../../REQUIREMENTS.md#mr10-provenance-survives-a-function-boundary)) | ❌ | ❌ | ✅ | ✅ |
| | whole-system mass + a part's ([MR9](../../REQUIREMENTS.md#mr9-whole-system-quantities), [MR22](../../REQUIREMENTS.md#mr22-whole-system-quantities-are-not-part-quantities)) | ❌ | ❌ | ✅ | ✅ |
| | `∑ p, p.velocity` as a system quantity ([MR8](../../REQUIREMENTS.md#mr8-aggregation-is-licensed-per-kind-in-both-directions), [MR21](../../REQUIREMENTS.md#mr21-assembly-is-licensed-per-kind-and-two-sided)) | ❌ | ❌ | ✅ | ✅ |
| | a `reverse` that forgets to swap | ❌ | ❌ | ❌ | ✅ |
| | `‖v‖` — vector quantity to scalar | — | — | — | — *(no licensed form; §6 of Attempt 4)* |
| **Ergonomics** | forces are one multiset, as upstream | ✅ | ✅ | ⚠️ `Σ`-pairs | ✅ |
| | construction sites unchanged | ✅ | ✅ | ⚠️ `⟨p, …⟩` everywhere | ✅ |
| | `netForce` is a filter on the field | ✅ | ✅ | ⚠️ + transport | ⚠️ + transport |
| | `CoeFun` uniform | ✅ | ✅ | ⚠️ per index | ✅ *(result type names `f.target`)* |
| | totals erase to upstream's by `rfl` | — | ✅ | ✅ | ✅ |
| **Mints** | new ISO 80000 items needed | — | 0 | 0 | 0 |

Three rows carry the argument.

**The `reverse` row is the surprise.** Attempt 3 pays the whole ergonomic price and still does
not buy Newton's third law, because indexing by the *target* records one object and the law is
about a *pair*. That is what says the question is not "field versus index" but *which object*.

**The velocity row is the one about code not yet written.** Momentum conservation and the
work–energy theorem are both aggregation laws. Attempts 1 and 2 write the licensed and the
unlicensed sum with the same `∑` at the same type; nothing there can be taught the difference,
because the difference is that one sum changes the object.

**The ergonomics rows are why Attempt 4 exists.** Attempt 3 is what a reader would expect the
proposal to demand, and a maintainer would be right to reject it. Attempt 4 is one line:

```lean
structure Force (s : System d) where
  target : s.Particle                                                       -- #1612's field
  value  : Time → IndividualQuantity (Composite.part target) forceK s.Vector -- was s.Vector
```

The target stays a field, so the store stays `Multiset (Force s)`, construction sites stay
record syntax, and Newton's laws stay `∀ particle` statements that can be fields of the
system. The value's type *reads the field*, so the object is checked. The one residual cost is
the transport in `netForce` — a `h ▸` where the runtime filter meets the type — written once.

## What this case study asks of #1612

Nothing. Every verdict above holds with the PR exactly as written; the layer is additive, per
[MR31](../../REQUIREMENTS.md#mr31-adoption-is-scoped-and-monotone). What the study establishes
is that **the ergonomic objection to the object layer is answerable** — not by making the
layer cheaper, but by putting the index where the PR already put the information.

## What it does not settle

- **The norm crossing.** `½ m ‖v‖²` needs a licensed operation carrying a vector quantity to a
  scalar one; there is none, and an inner product `⟪p, v⟫` has the same shape. Attempt 4 §6
  pins the gap as a refusal.
- **Momentum conservation is stated, not proved.** The proof is the multiset involution
  Newton's third law supplies. What the layer contributes is that the statement is about the
  system rather than about two vectors of the same dimension.
- **A particle still cannot be named.** `Designated s.Particle` does not synthesize, and the
  instance an author would write instead is refused by the injectivity obligation. That is a
  PhysLib-side ask for a label field, and a separate one — see
  [Exhibit F](../../Exhibits/PointParticle/Findings.lean).
