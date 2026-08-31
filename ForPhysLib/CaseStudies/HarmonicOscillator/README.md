# Case study — the harmonic oscillator

Four honest attempts at typing the same physics, scored against
[the requirements](../../REQUIREMENTS.md). The point is not that one attempt wins; it is that
**each fails in a way characteristic of its own idea**, and that those failures are build
artifacts rather than opinions.

The occasion is [physlib#1579](https://github.com/leanprover-community/physlib/pull/1579),
where jstoobysmith observed that PhysLib's `Dimension`/`Unit` layer is under-used and
suggested the harmonic oscillator as a place to start — and where the thread also raises
**ergonomics**. It is a good choice of example: good enough that it exposes both what
dimensional analysis structurally cannot do *and* what it costs to fix, which is why the
requirements run to six tiers here and not one.

Requirements are not restated in this file. Each is a link.

---

## The physics

**One oscillator.** PhysLib's `QuantumMechanics.HarmonicOscillator d` carries a mass `m : ℝ`
and natural frequencies `ω : Fin d → ℝ`, and derives the characteristic length
`ξ i = √ℏ / (√m · √(ω i))` and the Hamiltonian `p²/2m + ½m Σ ωᵢ²xᵢ²`.

**Two oscillators.** Two masses on springs to fixed walls, coupled by a third spring:

```
    ▓╱╲╱╲╱╲[ m_A ]╱╲╱╲╱╲[ m_B ]╱╲╱╲╱╲▓
        k_A          k_c         k_B
```

with bare angular frequencies `ω_A = √(k_A/m_A)`, `ω_B = √(k_B/m_B)` and normal modes `ω_∓`,
which are *not* the bare frequencies. Concrete magnitudes throughout, chosen so every
arithmetic fact is decidable:

| quantity | A | B | pair |
|---|---|---|---|
| mass | 3 | 5 | **8** — extensive, `3 + 5` |
| angular frequency | 2 | 4 | **5** — `ω₊`, *not* `2 + 4` |

The two rows differ in exactly one respect — whether the whole's value is the sum of the
parts' — and **nothing in a dimension, a unit, or a magnitude distinguishes them.** Both rows
are `M` and `T⁻¹` respectively, on every part and on the whole. That single observation is
what the benchmark is built to make undeniable, and it is
[MR8](../../REQUIREMENTS.md#mr8-aggregation-is-licensed-per-kind-in-both-directions).

**Driven and damped.** Tier 5 additionally uses the driven oscillator's mechanical impedance
`Z(ω) = c + i(mω − k/ω)`, with `c = 3`, `m = 5`, `ω = 2`, `k = 12`, so `Z = 3 + 4i`,
`|Z| = 5`.

**In a plane.** Tier 6 puts the oscillators in two dimensions, so a position and a velocity
are Cartesian vectors. A's velocity is `(3, 4)`; the anisotropic oscillator has `ω = (2, 7)`,
hence stiffness matrix `diag(4, 49)`. The change of frame throughout is the Pythagorean
rotation `cos θ = 3/5`, `sin θ = 4/5` — every entry rational, every fact decidable, and
deliberately *not* a quarter turn, which merely permutes the axes and would hide what
[MR19](../../REQUIREMENTS.md#mr19-an-indexed-family-is-not-a-set-of-vector-components) turns
on.

---

## The attempts

Sources live in the `ForPhysLib` library, one attempt per file, each running the whole
list MR1–MR19 in order (with the appended MR32 at the end) so it reads end to end as a single account of a single idea.

| file | idea |
|---|---|
| [`Attempt1Reals.lean`](Attempt1Reals.lean) | **Plain reals in a bundle.** PhysLib's status quo: `m : ℝ`, `ω : Fin d → ℝ` as fields of a `structure`. Includes the strongest form of the "the structure *is* the object" defence. |
| [`Attempt2Dimension.lean`](Attempt2Dimension.lean) | **PhysLib `Dimension` / `WithDim`.** The #1579 proposal, done properly: `m : WithDim Dim.mass ℝ`, `ω : WithDim Dim.time⁻¹ ℝ`, with `dimScale` covariance. |
| [`Attempt3Tagged.lean`](Attempt3Tagged.lean) | **Buckingham-π object tagging.** Extend the dimension basis with one generator per oscillator, so `m_A` and `m_B` carry different dimensions. The classic trick, given its best shot, then pushed until it breaks. |
| [`Attempt4Pkc.lean`](Attempt4Pkc.lean) | **PKC.** `KindOfProperty` above `Dimension`; `IndividualQuantity o k R` for object identity; `Extensive` for licensed aggregation; `DedicatedKind` for `System — Component ; kind`; `Quantity k R`'s carrier axis; `InFrame f var k R`'s frame and variance indices. |
| [`Scorecard.lean`](Scorecard.lean) | The head-to-head verdicts, re-derived so the table below cannot drift from the files — plus the four authorings of `V = m·ω²·x²`, the one comparison that is inherently cross-attempt. |

---

## Scorecard

✅ satisfied · ❌ failed · ⚠️ partial, or satisfied only by author discipline — scored as
failed, per [rule 2](../../PLAN.md#rules-of-engagement)

| | requirement | 1 · reals | 2 · `WithDim` | 3 · tagged | 4 · PKC |
|---|---|---|---|---|---|
| **Tier 1** | [MR1](../../REQUIREMENTS.md#mr1-dimensional-homogeneity) dimensional homogeneity | ❌ | ✅ | ✅ | ✅ |
| | [MR2](../../REQUIREMENTS.md#mr2-derived-dimensions-are-computed-not-annotated) derived dimensions computed | ❌ | ✅ | ⚠️ | ✅ |
| | [MR3](../../REQUIREMENTS.md#mr3-unit-change-covariance) unit-change covariance | ❌ | ✅ | ❌ | ✅ |
| **Tier 2** | [MR4](../../REQUIREMENTS.md#mr4-same-dimension-kinds-stay-apart) same-dimension kinds | ❌ | ❌ | ❌ | ✅ |
| | [MR5](../../REQUIREMENTS.md#mr5-scale-type-gates-the-operators) scale type gates operators | ❌ | ❌ | ❌ | ✅ |
| | [MR6](../../REQUIREMENTS.md#mr6-degrees-of-freedom-are-distinguishable) degrees of freedom | ⚠️ | ❌ | ⚠️ | ✅ |
| **Tier 3** | [MR7](../../REQUIREMENTS.md#mr7-object-identity) object identity | ⚠️ | ❌ | ✅ | ✅ |
| | [MR8](../../REQUIREMENTS.md#mr8-aggregation-is-licensed-per-kind-in-both-directions) licensed aggregation, two-sided | ❌ | ❌ | ❌ | ✅ |
| | [MR9](../../REQUIREMENTS.md#mr9-whole-system-quantities) whole-system quantities | ❌ | ❌ | ❌ | ✅ |
| | [MR10](../../REQUIREMENTS.md#mr10-provenance-survives-a-function-boundary) provenance across a call | ❌ | ✅ | ✅ | ✅ |
| **Tier 4** | [MR11](../../REQUIREMENTS.md#mr11-authoring-ergonomics) authoring ergonomics | ✅ | ⚠️ | ❌ | ⚠️ |
| | [MR12](../../REQUIREMENTS.md#mr12-rendering-ergonomics) rendering ergonomics | ⚠️ | ❌ | ❌ | ✅ |
| **Tier 5** | [MR13](../../REQUIREMENTS.md#mr13-carrier-parametricity) carrier parametricity | ❌ | ❌ | ❌ | ✅ |
| | [MR14](../../REQUIREMENTS.md#mr14-complex-valued-quantities) complex-valued quantities | ⚠️ | ❌ | ❌ | ✅ |
| | [MR15](../../REQUIREMENTS.md#mr15-exec-and-spec-agree) exec/spec agreement | ❌ | ❌ | ❌ | ✅ |
| **Tier 6** | [MR16](../../REQUIREMENTS.md#mr16-a-carrier-morphism-cannot-change-the-kind) carrier morphism keeps the kind | ❌ | ❌ | ❌ | ✅ |
| | [MR17](../../REQUIREMENTS.md#mr17-a-vector-quantity-is-one-quantity) vector quantity is one quantity | ❌ | ⚠️ | ⚠️ | ✅ |
| | [MR18](../../REQUIREMENTS.md#mr18-frame-covariance-and-what-survives-it) frame covariance | ❌ | ❌ | ❌ | ✅ |
| | [MR19](../../REQUIREMENTS.md#mr19-an-indexed-family-is-not-a-set-of-vector-components) indexed family ≠ vector | ❌ | ❌ | ❌ | ✅ |
| **App.** | [MR32](../../REQUIREMENTS.md#mr32-specialization-keeps-kinds-comparable) specialization keeps kinds comparable | ❌ | ❌ | ❌ | ⚠️ |

**MR32 is the appended row** — Tier 2 by content, numbered at the end, the same append
discipline as PKC's own catalogue. It is also the first row with no ✅ anywhere: Attempts
1–2 collapse the energy family into one type, Attempt 3 distinguishes it and loses
`H = T + V` (`kinetic_ne_potential` — proved before the requirement was stated), and PKC
proves the lattice (`mr32_comparable`) but ships no quantity-level operation that consumes
it, so the licensed sum at the join is missing machinery (`Attempt4Pkc.lean`, section MR32,
scored ⚠️ by rule 5).
---

## What the table says

### Tiers 1–3: one fact, seen twice

Attempt 2's MR1–MR3 ✅ sits next to MR4–MR9 ❌, and attempt 3's MR7 ✅ sits next to its MR8 ❌.
Both are consequences of `Dimension B` being a free commutative group: every distinction it
can draw is multiplicative and cancelling, and every question it can answer is a linear
condition on exponents.

Attempt 3 buys [MR7](../../REQUIREMENTS.md#mr7-object-identity) by making "being oscillator A"
a group element, and pays immediately — a group element that distinguishes `m_A` from `m_B`
also forbids their sum, leaves a residual tag in the dimensionless ratio `ω_A/ω_B`, and makes
the phase `ω_A·t` non-dimensionless, so `cos(ωt)` is inexpressible. The sharpest form of that
bill: kinetic energy `m·v²` carries tag exponent 3 and potential energy `m·ω²·x²` carries 5,
so **`H = T + V` does not type-check for a single oscillator** (`Attempt3.kinetic_ne_potential`).
Object identity is not multiplicative.

**None of this is a defect in PhysLib's `Dimension`.** It is what a dimension *is*, and it is
exactly what makes Tier 1 and [MR10](../../REQUIREMENTS.md#mr10-provenance-survives-a-function-boundary)
come out so cleanly.

### Tier 4. The ranking reverses

Written longhand, PKC is the *worst* attempt at
[MR11](../../REQUIREMENTS.md#mr11-authoring-ergonomics) by a wide margin: four multiplications
cost four `ProductKind` witnesses and three intermediate kind declarations, and the infix
operators disappear from the source entirely. **That is the ergonomics concern in its
strongest form, and it is correct as stated.**

Two things answer it, and neither is a promise.

**The witness is what `@[pkc_math]` deletes.** `DocGenMath/Lift.lean` drops "the kind-law
`Prop` witnesses, the instance arguments, the carrier/kind implicits", so the term renders as
`V = m\,\omega^{2}\,x^{2}`, and `@[pkc_math substituting …]` produces a derivation chain by
`delta`-substitution, which preserves meaning at every step. The bookkeeping the author writes
is bookkeeping the reader never sees.

**And the author need not write it either.** `PropertyKindCalculus.OperatorTable` is the
curated operator layer over the same kind-laws: `KindMul`/`KindDiv` instances registered once
per model — at most one entry per operand pair, opt-in per file, no `Mul` instance on
`Quantity` itself — whose `outParam` result kind lets instance search compute the interior
kinds of a chained product, plus scoped `HMul`/`HDiv` on both `Quantity` and
`IndividualQuantity` so `x * y` elaborates through the table and an unregistered pair **fails
to elaborate**. `hmul_eq_mul` proves operator form = witness form by `rfl`, so the witness is
still in the elaborated term and MR12 is untouched. Attempt 4's formula is then
`m * (ω * ω) * (x * x)` — character-identical to attempt 1's — with every Tier-2 and Tier-3
guarantee enforced, and `Scorecard.ho11_operators_same_term` proves the operator form is the
same term as the longhand one.

**MR11 is therefore ⚠️ and not ✅.** Writing formulas costs nothing; standing a model up costs
three kind declarations and four table entries. That is a genuine burden attempt 1 does not
have — though it is paid **per model** where attempt 2's cast is paid **per formula**, so the
two scale in opposite directions. That observation is the whole basis for
[MR28](../../REQUIREMENTS.md#mr28-kind-generic): in a *library*, per-model is the favourable
denominator.

MR12 is ✅ on three counts, each pinned with `#guard_msgs`: the equation renders as typeset
mathematics; a derivation renders; and the **object index reaches the page as a subscript**,
so `energyOscA` and `energyOscB` — distinct types that Tier 3 keeps apart — render as
`V = m_{A}\,\omega_{A}^{2}\,x_{A}^{2}` and `V = m_{B}\,\omega_{B}^{2}\,x_{B}^{2}` rather than
as the same string. That is how a physicist writes a coupled system, so the index that wins
Tiers 2 and 3 is notation rather than bookkeeping.

### Tier 5: the axis attempts 1–3 do not have

`WithDim d M` is parametric in `M` for the *additive* structure only — `HMul` and `HDiv` are
declared at `M = ℝ` and nowhere else — so a physical model written in that algebra is `ℝ`-only.
PhysLib says as much in `Units/Basic.lean`: other Lean unit libraries "allow for or work in
Floats, allowing computability and the use of `#eval`. This is currently not possible with the
more theoretical implementation here in Physlib which is based exclusively on Reals."

That closes [MR13](../../REQUIREMENTS.md#mr13-carrier-parametricity) and with it MR14 and
MR15: a complex impedance can be *held* in `WithDim d ℂ` and not *combined*, and with a single
carrier there is no exec/spec gap to name. Attempt 1 fails MR13 differently and more
instructively — it *can* run, by declaring the model a second time at `Float`, and nothing in
either type records that the two are the same model.

### Tier 6: variance is a third axis, and not a finer basis

Variance is independent of dimension **in both directions at once**: a velocity and a
frequency family have *different* dimensions and are handed the *same* transformation by
anything dispatching on the dimension, while a velocity and the same velocity read in another
frame have the *same* dimension and must not be interchanged. So no refinement of the
dimension group reaches it.

Attempt 3's answer to Tier 3 — adding a generator — fails here for a reason worth stating: a
dimension is an exponent vector and multiplying dimensions adds exponents, so everything the
basis can express is a *scaling*. **There is no element of a free commutative group whose
action on a pair of numbers is a rotation.**

The requirement that decides the tier is
[MR19](../../REQUIREMENTS.md#mr19-an-indexed-family-is-not-a-set-of-vector-components),
because it is the one where the two `Fin d → ℝ`s in PhysLib's own `HarmonicOscillator`
structure — `ω` and a configuration — turn out to obey different laws while being written
identically.

---

## What Tier 6 changed

Per [rule 5](../../PLAN.md#rules-of-engagement), the record of what this tier did to PKC,
since it did not merely score it.

Tier 6 was added after the first five, and **PKC failed two of its four requirements when they
were written.** The blueprint had already said so: R11 specified the ISO 80000-2 §18 numerical
array and recorded that "value representation in the structural sense — coordinate frames,
tensor variance, bound-versus-free vectors, and frame transformations — is *not yet specified*
here". The benchmark is what turned that owed item into a compile error.

Two changes to the core library followed, and both are visible in `Attempt4Pkc.lean` as the
things that make its ✅ cells true:

- **`ScalarCarrier`** (`PropertyKindCalculus/Quantity.lean`). `Quantity.mul` required only
  `[Mul R]`, and Lean supplies a pointwise `Mul (Fin n → R)`, so the componentwise product of
  two position vectors elaborated as an area — correctly kinded, correctly dimensioned, and
  not a thing. `QuantityClassification`'s own header had stated the doctrine the code did not
  implement — "a kind's scale says an operation is meaningful; a carrier's tier says the
  representation can compute it; a sound quantity operation needs both" — and the class
  supplies the missing half, so a vector carrier now fails to synthesize. It is a marker class,
  because the same `ι → R` is a scalar carrier when its indices are independent *samples* and
  not when they are *components*, and no property of the type decides which.
- **`Frame` / `FrameReal`** (core, and the `Dimension` library for the laws). `InFrame f var k R`
  indexes a reading by the frame it was taken in and the variance it transforms with;
  `FrameChange n R f g` is a change of frame; and `FrameReal` proves the three things that make
  it an action rather than a notation — functoriality, invariance of the scalar product under
  an orthonormal change, and, with a witness, the *non*-invariance of a component.

What did not change is the score. MR11 is still ⚠️, and MR17's failure was real until it was
fixed — which is the only reason those two facts are recorded in the same paragraph.

---

## Evidence in PhysLib today

The benchmark scores four *reconstructions*. This section points at PhysLib's own harmonic
oscillator and its neighbours, where the same requirements are failed by shipped code. These
are the raw material for [Exhibit C](../../PLAN.md#exhibit-c-harmonicoscillator).

| PhysLib code | requirement | what is wrong |
|---|---|---|
| `HarmonicOscillator/Basic.lean` — `lagrangian (t) (x) (v)` and `hamiltonian (t) (p) (x)`, both `Time → E → E → ℝ` | [MR1](../../REQUIREMENTS.md#mr1-dimensional-homogeneity), [MR7](../../REQUIREMENTS.md#mr7-object-identity) | position, velocity, momentum and force are all `EuclideanSpace ℝ (Fin 1)`; `S.hamiltonian t x p` is well-typed and wrong |
| `HarmonicOscillator/Basic.lean` — `hamiltonian_eq` states `fun _ p x` and proves it with `funext t x p` | [MR7](../../REQUIREMENTS.md#mr7-object-identity), [MR10](../../REQUIREMENTS.md#mr10-provenance-survives-a-function-boundary) | binder names transposed: inside the proof, `x` *is* the momentum. Statement correct, proof valid, nothing notices |
| `HarmonicOscillator` `{ m k : ℝ }`, `SimplePendulum` `{ m ℓ g : ℝ }` | [MR1](../../REQUIREMENTS.md#mr1-dimensional-homogeneity), [MR4](../../REQUIREMENTS.md#mr4-same-dimension-kinds-stay-apart) | `√(k/m)` and `√(m/k)`, `√(g/ℓ)` and `√(ℓ/g)` are equally well-typed |
| `SpaceAndTime/Time/Basic.lean` module doc | [MR4](../../REQUIREMENTS.md#mr4-same-dimension-kinds-stay-apart) | *"Lean will not catch inconsistencies in the choice of units or origin"* — and it names `t` and `ω` as the pair at risk |
| `Time` documented origin-dependent, instanced `Module ℝ` + `Norm` + `InnerProductSpace` | [MR5](../../REQUIREMENTS.md#mr5-scale-type-gates-the-operators) | `t.val • v` and `(t₂ - t₁).val • v` are equally well-typed; only the second is meaningful |
| `RigidBody/AngularVelocity.lean` — `angularVelocity` and `bodyAngularVelocity`, both `Fin 3 → ℝ` | [MR18](../../REQUIREMENTS.md#mr18-frame-covariance-and-what-survives-it) | the frame is the substring `body`; see [M5](../../MOTIVATION.md#m5-a-correctness-constraint-enforced-by-not-using-an-abbreviation) |
| `QuantumMechanics.HarmonicOscillator d` — `ω : Fin d → ℝ` beside a configuration `Fin d → ℝ` | [MR19](../../REQUIREMENTS.md#mr19-an-indexed-family-is-not-a-set-of-vector-components) | an indexed family of independent frequencies and a vector's components, written identically, obeying different laws |
| `Units/Basic.lean` — "based exclusively on Reals" | [MR13](../../REQUIREMENTS.md#mr13-carrier-parametricity), [MR27](../../REQUIREMENTS.md#mr27-carrier-generic) | the model cannot be executed, so a shipped implementation is related to it only by prose |

Each row is currently prose. Per [rule 2](../../PLAN.md#rules-of-engagement) each must become
a probe before it is cited upstream.

---

## The conclusion

Narrow, and — we think — friendly to the thread it came from: **PhysLib's `Dimension` is the
right bottom layer, and the harmonic oscillator is a good demonstration that something has to
sit above it.** PKC already consumes `Dimension` as its forgetful functor
`DimensionedKind.toDimension`; the layers compose rather than compete.

What the benchmark adds to that claim is a price list. Tiers 2, 3, 5 and 6 are what the kind,
carrier and frame axes buy. Tier 4 is what they cost, and the MR11 column is not one anybody
should pretend away: no amount of machinery beats `m * (ω * ω) * (x * x)` over bare reals for
the person typing it, and a model built on kinds has to be stood up before it can be written
in.

The defensible claim is not that the safety is free. It is that **the per-formula cost can be
driven to zero, the residual cost is per model, and what is paid at the keyboard comes back on
the page.**
