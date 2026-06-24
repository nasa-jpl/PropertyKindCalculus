import Verso
import VersoManual
import VersoBlueprint
-- This is a *methodology* chapter: it cross-references the proved spine nodes with `{uses …}`
-- (the labels resolve at blueprint-generation time, not Lean elaboration), and illustrates each
-- step with the soil-moisture-model decls by name only. It re-declares nothing, so — unlike the
-- node-bearing chapters — it does not import `PropertyKindCalculus` or the model.

open Verso.Genre
open Verso.Genre.Manual
open Informal

#doc (Manual) "Write Once, Correctly" =>

The chapters so far catalogue what PropertyKindCalculus _provides_. This one is about _method_:
the order in which an application author reaches for those pieces when specifying a real model,
and why the order is forced rather than a matter of taste. The running example is the
[`soil-moisture-model`](https://github.jpl.nasa.gov/nfr/soil-moisture-model) library — the typed
SMAP–NISAR soil-moisture retrieval — read here only to _infer the recipe_. That library declares
its own kinds and proofs and is cited live by its own
[verifiable ATBD](https://github.jpl.nasa.gov/nfr/SMAP-AVS-ATBD); PropertyKindCalculus re-declares
none of it and only supplies the four primitives named below.

The discipline has a slogan the model states in its own source: _write once correctly, go fast
automatically_. A quantity is authored once, carrying its kind, over an abstract numeric carrier;
the kind layer is checked by the elaborator and then _erases_ — projected away by `.magnitude` —
to a bare floating-point kernel, bit for bit. Correctness lives in the types and is paid for at
compile time, while the number that runs is the same one a hand-written kernel would compute.
Getting the _authoring order_ right is what makes that erasure sound: each layer must be in place
before the one above it can type-check.

# The four steps

:::group "write-once"
These four steps are the order in which a PropertyKindCalculus model is authored. Each rests on
the layer beneath it; each is shown with where the soil-moisture model realizes it.
:::

## Step 1 — Start from the measurement principle: declare the kinds

:::definition "wo-kinds" (parent := "write-once")
Before any number, name _what each quantity is_ by the examination that produces it. A
{uses "def_kindOfProperty"}[kind-of-property] is the common defining aspect of mutually comparable
properties (Dybkær §6.19); two otherwise-comparable kinds are individuated by their
{uses "def_examination"}[examination principle] — the defining aspect of the procedure that
measures them, so that {uses "thm_examPrinciple_defining"}[a different principle forces a different
kind]. This is the layer a description logic partly has: it can record a class, but not the
operator algebra or the laws the later steps add.

In the model this is the catalogue of bare kinds — the radar `backscatter` $`\sigma^0`, the
optical `ndvi`, the surface `reflectivity`, and the dielectric kinds — each declared as a `def` of
`KindOfProperty`, named by the instrument or principle that examines it. A kind is _general_ (a
type); _this pixel's_ backscatter is _individual_ (a term, `Quantity backscatter α`). Fix the kinds
first: everything above is indexed by them.
:::

## Step 2 — Pair each kind with its dimension

:::definition "wo-dimension" (parent := "write-once")
Give each kind its dimension, and let dimension do only what it can. The {uses "def_dim"}[dimension
map] is a forgetful functor — it keeps a kind's SI base-quantity exponents and discards the rest —
so it answers only the coarse question, _are these even commensurable?_ It
{uses "thm_dim_homomorphism"}[respects products], which is ordinary dimensional bookkeeping proved
as a law, but it _does not decide_ identity. This step matters precisely because the quantities
that carry the retrieval are almost all dimension one — a volume fraction, a reflectivity, an
index. Dimension equates them all; the kind layer keeps them apart. Pairing a kind with its
dimension here is what lets a later product be checked for dimensional consistency _and_ kind
consistency at once.

In the model, volumetric and gravimetric water content are both dimension one yet distinct kinds —
a units library alone would silently accept one for the other, which is exactly the failure this
layer removes.
:::

## Step 3 — Build kind-differentiated quantities; gate the arithmetic

:::definition "wo-quantities" (parent := "write-once")
Now write the model's data and forward maps as records of typed quantities, and let the
{uses "def_kMul"}[interaction algebra] gate the arithmetic: a product is formed only where the
kinds sanction it (`KMul` for products, {uses "def_kDiv"}[`KDiv` for quotients]), so a wrong
pairing is a compile error, not a wrong number. Same-kind addition is the gate on `+`; products and
quotients change kind by the algebra. Authored over an abstract carrier `α`, the whole record
re-represents at the proof carrier (`ℝ`), the rounding spec (binary32), and the executable (`Float`)
by one map, preserving every kind.

The model's `MironovCoeffs α` is the pattern: each Mironov-2009 fit constant is a field of its own
kind — a dry refractive index `ndA0 : Quantity nIndexKind α`, a relaxation time
`taub0 : Quantity relaxTimeKind α`, a conductivity `sigbF0 : Quantity conductivityKind α` — so the
elaborator refuses to pass a relaxation time where a conductivity is expected, even though all three
erase to the same `Float`. Its `MironovCoeffs.map` re-represents the whole table at any carrier,
each constant keeping its kind.
:::

## Step 4 — Differentiate shared kinds: dedicate, or index by field

:::definition "wo-dedication" (parent := "write-once")
Finally, decide what to do about quantities that share a kind. There are two cases, and they go on
_different axes_.

When two quantities _should_ be different kinds because their measurement target differs — same
quantity, different system or component — make them distinct with a {uses "def_dedicatedKind"}[
dedicated kind]: holding the {uses "def_component"}[component] (or system) apart
{uses "thm_dedicated_distinct_component"}[is enough to force distinct kinds], without inventing
identity strings. In the model the bound-water and free-water static permittivities are one
relative-permittivity kind dedicated to two components, hence provably distinct.

When the algebra _forces_ a genuinely shared kind, the leftover distinction is _positional_, not
metrological, and belongs on a second axis carried by _named record fields_ — not arrays. The
Cholesky factor `CholQ α` is row-homogeneous: row 2 is three fields `l20 l21 l22`, all
`Quantity reflectivity α`, because $`A = L L^{\mathsf T}` makes every $`L_{ik} L_{jk}` land at the
same kind regardless of the column — a kind that separated them would make the factorization's own
row sums ill-typed. The forward-substitution intermediate `YQ α` is likewise uniformly
`backscatter`. The remaining "which slot" distinction is held by the distinct field names and
checked off the kind axis by the erasure `rfl`: `cholesky4Q` equals the bare kernel only when the
slots line up, so a same-kind swap still type-checks but breaks parity. A `Fin 4`-indexed array
would push that positional bookkeeping onto the type and discard the named slots; the record keeps
both axes separable — kind by the elaborator, position by parity-to-reference.
:::

# The payoff

Authored in this order, the model is _one source_. The kinds make every operation in the forward
physics and the normal-equations solve a checked equation; the dimension layer certifies
commensurability without conflating dimension-one quantities; the interaction algebra gates the
arithmetic; and dedication plus named fields carry the distinctions the kind axis cannot. Then
`.magnitude` erases the whole overlay and the compiled kernel is the bare `Float` program — proved,
by a definitional `rfl` for every input, to be the same numbers. _Write once correctly, go fast
automatically._

The worked model is the
[`soil-moisture-model`](https://github.jpl.nasa.gov/nfr/soil-moisture-model) library (build-gated
by its own CI); its claims are cited live, with proved or `sorry` status, by the
[SMAP-AVS verifiable ATBD](https://github.jpl.nasa.gov/nfr/SMAP-AVS-ATBD). PropertyKindCalculus
supplies the four primitives this chapter names; the model composes them in this order.
