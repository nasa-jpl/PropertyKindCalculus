/-
# Worked example: write once, correctly — the four-step authoring recipe

A *self-contained, public* miniature of a soil-moisture retrieval, written purely
against the core `PropertyKindCalculus` library, to illustrate the four steps a
model author follows (the *Write Once, Correctly* methodology chapter):

  1. **Declare the kinds** by the examination principle that measures each.
  2. **Pair each kind with its dimension** — here all dimension one, kept apart by kind.
  3. **Build kind-differentiated typed records**, re-representable at any carrier.
  4. **Differentiate shared kinds**: *dedicate* (same kind, different component), and
     carry the leftover *positional* distinction on **named record fields**, checked
     off the kind axis by an erasure `rfl`.

This is a deliberately *simplified subset* — it retains only the salient structure
each step needs and omits the full retrieval (the real Mironov dielectric fit, the
Gram/Cholesky/`sqrt` arithmetic, the forward radar physics). Everything here is a
*checked fact*: the module builds in the `Examples` library under CI, which is what
makes the methodology chapter's claims true rather than merely asserted.

Mathlib-free; part of the separate `Examples` library — it imports the core
`PropertyKindCalculus` library exactly as a downstream consumer would.
-/

module

public import PropertyKindCalculus
meta import PropertyKindCalculus

public section -- pkc-blanket
@[expose] section -- pkc-blanket-expose

namespace PropertyKindCalculus.Examples.MiniWriteOnce

open PropertyKindCalculus

/-! ## Step 1 — Start from the measurement principle: declare the kinds

Name *what each quantity is* by the examination that produces it. Each is a bare
`KindOfProperty`, named for the instrument or principle that examines it — the
radar backscatter `σ⁰`, the optical vegetation index, the surface reflectivity,
and the three Mironov-2009 dielectric fit constants used in Step 3. -/

/-- Radar backscatter coefficient `σ⁰`. -/
def backscatter : KindOfProperty := { id := "backscatter coefficient", scale := .ratio }
/-- Optical normalized vegetation index. -/
def ndvi : KindOfProperty := { id := "vegetation index", scale := .ratio }
/-- Surface reflectivity. -/
def reflectivity : KindOfProperty := { id := "reflectivity", scale := .ratio }

/-- Mironov dry refractive index `n`. -/
def refractiveIndexKind : KindOfProperty :=
  { id := "refractive index (n)", scale := .ratio, examPrinciple := some "refractive-mixing" }
/-- Mironov dielectric relaxation time `τ`. -/
def relaxTimeKind : KindOfProperty :=
  { id := "dielectric relaxation time", scale := .ratio, examPrinciple := some "debye-relaxation" }
/-- Mironov ionic conductivity `σ`. -/
def conductivityKind : KindOfProperty :=
  { id := "ionic conductivity", scale := .ratio, examPrinciple := some "ionic-conduction" }

-- Distinct names ⇒ distinct kinds.
example : backscatter ≠ reflectivity := by decide

/-- *A different examination principle forces a different kind*, even when the name,
scale, and dimension all agree: monostatic and bistatic reflectivity share `id`
`"reflectivity"` and ratio scale, yet are distinct kinds because the principle
that examines them differs (§7.5). -/
def reflMonostatic : KindOfProperty :=
  { id := "reflectivity", scale := .ratio, examPrinciple := some "monostatic" }
/-- Bistatic reflectivity — same name and scale, different examination principle. -/
def reflBistatic : KindOfProperty :=
  { id := "reflectivity", scale := .ratio, examPrinciple := some "bistatic" }

example : reflMonostatic ≠ reflBistatic := by decide

/-! ## Step 2 — Pair each kind with its dimension

The quantities that carry the retrieval are almost all **dimension one** — a volume
fraction, a mass fraction, a reflectivity, an index. Dimension equates them all; the
*kind* layer keeps them apart. Volumetric and gravimetric water content are the
textbook case: both `volume/volume` resp. `mass/mass`, hence dimension one, yet a
units library alone would silently accept one for the other. Here they are *distinct
kinds*, so that confusion is a type error.

(The literal `dim`-functor collapse — `dim vwc = dim gwc = 1` — is the Mathlib-backed
dimension layer, demonstrated in the *Units* / *Dimension* chapters; this Mathlib-free
example makes the point one level up, at the kind.) -/

/-- Volumetric water content (water volume / soil volume) — dimension one. -/
def vwc : KindOfProperty :=
  { id := "volumetric water content", scale := .ratio, examPrinciple := some "ratio of volumes" }
/-- Gravimetric water content (water mass / dry-soil mass) — also dimension one. -/
def gwc : KindOfProperty :=
  { id := "gravimetric water content", scale := .ratio, examPrinciple := some "ratio of masses" }

-- Both dimension one, yet distinct kinds — the dimension-1 disambiguation.
example : vwc ≠ gwc := by decide

/-! ## Step 3 — Build kind-differentiated quantities

Write the model's constants as a record of *typed* quantities, each field its own
kind. Authored over an abstract carrier `α`, the whole record re-represents at any
carrier by one `map`, every kind preserved. This miniature keeps three of the
Mironov-2009 fit constants — the pattern is the same for the full table. -/

/-- A miniature Mironov fit table: three constants, each of its own kind, over a
carrier `α`. The elaborator refuses to pass a relaxation time where a conductivity
is wanted, even though all three erase to the same `α`. -/
structure MiniMironovCoeffs (α : Type) where
  /-- Dry refractive index. -/
  ndA0 : Quantity refractiveIndexKind α
  /-- Dielectric relaxation time. -/
  taub0 : Quantity relaxTimeKind α
  /-- Ionic conductivity. -/
  sigbF0 : Quantity conductivityKind α

/-- Re-represent the whole table at a new carrier, each constant keeping its kind. -/
def MiniMironovCoeffs.map {α β : Type} (f : α → β) (c : MiniMironovCoeffs α) :
    MiniMironovCoeffs β :=
  { ndA0 := ⟨f c.ndA0.magnitude⟩, taub0 := ⟨f c.taub0.magnitude⟩, sigbF0 := ⟨f c.sigbF0.magnitude⟩ }

/-- A concrete table at the `Int` carrier. -/
def coeffsInt : MiniMironovCoeffs Int := { ndA0 := ⟨1⟩, taub0 := ⟨7⟩, sigbF0 := ⟨3⟩ }

-- The fields are different kinds, so they are *not* interchangeable. The next line is
-- a type error — a `Quantity relaxTimeKind` cannot stand in for a `Quantity conductivityKind`,
-- even though both magnitudes are `Int`:
--
--     example : Quantity conductivityKind Int := coeffsInt.taub0   -- kind mismatch
--
-- The kind index keeps the constants apart; `map` re-represents them all at once.
#guard (coeffsInt.map (· + 1)).taub0.magnitude == 8

-- The *same* table re-represented at the executable `Float` carrier — one `map`,
-- every kind preserved (prints `7.000000`):
#eval (coeffsInt.map Float.ofInt).taub0.magnitude

/-! ## Step 4 — Differentiate shared kinds: dedicate, or index by named field

Two cases, on two different axes.

### (a) Same kind, different component — *dedicate*

When two quantities *should* differ because their measurement target differs — same
relative-permittivity kind, different water phase — make them distinct with a
*dedicated kind*: holding the component apart is enough to force distinct kinds,
without inventing identity strings. -/

/-- The sort of system under examination. -/
def soilWater : SortOfSystem := { id := "soil water" }
/-- One pertinent component. -/
def boundWater : Component := { id := "bound water" }
/-- A second pertinent component. -/
def freeWater : Component := { id := "free water" }
/-- One generic kind-of-property, shared by both phases. -/
def relPermKind : KindOfProperty := { id := "relative permittivity", scale := .ratio }

/-- Bound-water static permittivity = the permittivity kind dedicated to soil-water / bound water. -/
def boundStaticPerm : DedicatedKind := relPermKind.dedicatedTo soilWater boundWater
/-- Free-water static permittivity = the *same* kind dedicated to soil-water / free water. -/
def freeStaticPerm : DedicatedKind := relPermKind.dedicatedTo soilWater freeWater

-- Same sort of system and same kind-of-property …
example : boundStaticPerm.sort = freeStaticPerm.sort := rfl
example : boundStaticPerm.kind = freeStaticPerm.kind := rfl
-- … yet distinct dedicated kinds, because the *component* differs.
example : boundStaticPerm ≠ freeStaticPerm := DedicatedKind.distinct_of_component (by decide)

/-! ### (b) Genuinely shared kind — carry position on *named fields*

When the algebra *forces* one kind, the leftover distinction is *positional*, not
metrological. A row of a lower-triangular Cholesky factor `L` (from `A = L·Lᵀ`) is
**row-homogeneous**: every entry of a row lands at the *same* kind, here
`reflectivity`, regardless of column — a kind that separated the columns would make
the factorization's own row sums ill-typed. The remaining "which slot" distinction is
held by the **named fields**, not by the kind and not by a `Fin n`-indexed array, and
is checked off the kind axis by an *erasure* `rfl` against a bare-`Float` kernel.

(The genuine Cholesky entries also carry `sqrt`/division arithmetic; that — and the
Gram-matrix kind bookkeeping — is the omitted detail. Kept here: the within-kind
update shape, which is what exhibits the row-homogeneity and the erasure.) -/

/-- One row of the lower-triangular factor: three same-kind named fields. -/
structure CholRowQ (α : Type) where
  /-- column 0 -/
  l20 : Quantity reflectivity α
  /-- column 1 -/
  l21 : Quantity reflectivity α
  /-- column 2 (the diagonal) -/
  l22 : Quantity reflectivity α

/-- Project the kinded row to its bare magnitudes — the erasure `.magnitude` per slot. -/
def CholRowQ.magnitudes {α : Type} (r : CholRowQ α) : α × α × α :=
  (r.l20.magnitude, r.l21.magnitude, r.l22.magnitude)

/-- The bare-`Float` kernel a hand-written factorization would run: the within-kind
row update on raw numbers. -/
def bareCholRow (a b c : Float) : Float × Float × Float := (a, b - a, c - a)

/-- The kinded row, built with the *computational* `-` (the executable-kernel
spelling), every entry staying at `reflectivity`. -/
def cholRowQ (a b c : Quantity reflectivity Float) : CholRowQ Float :=
  { l20 := a, l21 := b - a, l22 := c - a }

/-- **Erasure parity.** The kinded factor's magnitudes are *definitionally* the bare
kernel's outputs — `.magnitude` erases the whole kind overlay and the number that runs
is the one a hand-written kernel would compute, bit for bit. -/
theorem cholRowQ_magnitudes (a b c : Quantity reflectivity Float) :
    (cholRowQ a b c).magnitudes = bareCholRow a.magnitude b.magnitude c.magnitude := rfl

-- The positional distinction lives in the *named fields*: swapping two same-kind
-- slots (`l20` ↔ `l21`) still type-checks — both are `Quantity reflectivity` — but
-- breaks the parity `rfl`, so the swap is caught by parity-to-reference, not by the
-- kind. A `Fin 3`-indexed array would push that bookkeeping onto the type and discard
-- the named slots; the record keeps both axes separable.

end PropertyKindCalculus.Examples.MiniWriteOnce

end -- pkc-blanket-expose
end -- pkc-blanket
