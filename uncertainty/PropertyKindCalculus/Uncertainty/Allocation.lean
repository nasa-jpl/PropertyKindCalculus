/-
`PropertyKindCalculus.Uncertainty.Allocation` — **sensitivity-driven sample allocation** for SSPRC
(Degenhardt et al. 2025, §4 adaptive extension; `UNCERTAINTY.md` §3.2 item 3, Stage 4 "Scale").

SSPRC's freedom that Monte Carlo lacks is that its cost is *additive*: `N_s = Σ Nᵢ`, one budget
`Nᵢ` per input, spent independently (`Ssprc.deviationDists`). This module decides how to *split* a
fixed total budget across the inputs so the samples land where they change the answer.

The ranking key is each input's **contribution to the combined standard uncertainty**,
`wᵢ = |cᵢ|·uᵢ` — exactly the per-input term whose square is the GUM variance summand
(`u_c² = Σ cᵢ²·uᵢ² = Σ wᵢ²`, `Combine.gumStdUnc`). The `cᵢ` are the same sensitivity coefficients
Stage 1 already computes from the write-once kernel by one autograd reverse pass
(`Sensitivity.coefficients`); the `uᵢ = √varianceᵢ` come from the inputs' `MomentData`. So this
slice consumes only quantities the pipeline already produces — no new model machinery.

`allocate` then (1) **drops** any input whose contribution is a negligible fraction of the largest
(`wᵢ ≤ dropRatio · maxⱼ wⱼ` ⇒ `Nᵢ = 0`; that input's deviation distribution is a point mass, so it
contributes nothing to `E(Y)`/`Var(Y)` and costs no evaluations), and (2) splits the whole remaining
budget across the survivors **in proportion to `wᵢ`**, apportioned by the largest-remainder
(Hamilton) method so `Σ Nᵢ = total` *exactly* and a larger contribution never receives fewer
samples. The result is a pure `List Nat` that drops straight into `Ssprc.run` / `SsprcBatched.run`'s
`ns` argument. Deterministic, Mathlib- and TorchLean-free — so unlike the batched propagator it is
checked at build time by `#guard` (see `examples/…/DegenhardtAllocation.lean`).
-/

module

public import PropertyKindCalculus.Uncertainty.InputDist

@[expose] public section Blanket

namespace PropertyKindCalculus.Uncertainty.Allocation

open PropertyKindCalculus.Uncertainty

/-! ## The ranking key — per-input contribution to the combined uncertainty -/

/-- The **uncertainty contribution** `wᵢ = |cᵢ|·uᵢ` of one input: its sensitivity coefficient times
its standard uncertainty `uᵢ = √varianceᵢ`. Its square is the input's GUM variance summand, so
ranking by `wᵢ` ranks inputs by how much they move the combined `u_c`. -/
def contribution (c : Float) (m : MomentData Float) : Float :=
  c.abs * Float.sqrt m.variance

/-- The contributions of every `(cᵢ, momentsᵢ)` term — the vector `allocate` ranks. -/
def contributions (terms : List (Float × MomentData Float)) : List Float :=
  terms.map (fun t => contribution t.1 t.2)

/-! ## The allocator -/

/-- Split `total` equally across `n` bins by largest remainder (`Σ = total`): the first `total % n`
bins get `⌈total/n⌉`, the rest `⌊total/n⌋`. The fallback when no input has a positive contribution
(a constant model — every input is equally, and trivially, irrelevant). -/
def equalSplit (total n : Nat) : List Nat :=
  if n == 0 then []
  else
    let q := total / n
    let r := total % n
    (List.range n).map (fun i => if i < r then q + 1 else q)

/-- **Sensitivity-driven sample allocation.** Given per-input contributions `ws = [w₀, …, w_{n-1}]`
(`wᵢ = |cᵢ|·uᵢ`) and a total systematic-sample budget `total`, return the per-input counts `Nᵢ`:

  * **Drop** input `i` (`Nᵢ = 0`) when `wᵢ ≤ dropRatio · maxⱼ wⱼ` — its deviation distribution is a
    point mass, contributing nothing to `E(Y)`/`Var(Y)`, so spending evaluations on it is waste.
    `dropRatio = 0` (the default) keeps every input with a strictly positive contribution.
  * **Proportion** the whole budget across the survivors by `wᵢ`, apportioned by largest remainder
    so `Σ Nᵢ = total` exactly and a larger contribution never gets fewer samples than a smaller one.

Pure `List Nat`; feeds `Ssprc.run` / `SsprcBatched.run`'s `ns` unchanged. When no input survives the
drop (all contributions zero), the budget is split equally (`equalSplit`). -/
def allocate (total : Nat) (ws : List Float) (dropRatio : Float := 0.0) : List Nat := Id.run do
  let n := ws.length
  let wsA := ws.toArray
  -- largest contribution, and the drop threshold below which an input is negligible
  let wmax := ws.foldl (fun a w => if w > a then w else a) 0.0
  let thresh := dropRatio * wmax
  -- survivors and their total weight
  let mut kept : Array Bool := Array.replicate n false
  let mut sumKept : Float := 0.0
  for i in [0:n] do
    let w := wsA[i]!
    if w > 0.0 && w > thresh then
      kept := kept.set! i true
      sumKept := sumKept + w
  -- no survivor (constant model): equal split so the budget is not silently discarded
  if sumKept ≤ 0.0 then
    return equalSplit total n
  -- proportional real target rᵢ = total·wᵢ/ΣwKept; keep the floor now, its fraction for the remainder
  let mut base : Array Nat := Array.replicate n 0
  let mut fracs : Array Float := Array.replicate n 0.0   -- fractional part (−1 once its +1 is awarded)
  let mut used : Nat := 0
  for i in [0:n] do
    if kept[i]! then
      let r := total.toFloat * wsA[i]! / sumKept
      let fl := Float.floor r
      let b := fl.toUInt64.toNat
      base := base.set! i b
      fracs := fracs.set! i (r - fl)
      used := used + b
  -- largest-remainder top-up: award the `total − Σ⌊rᵢ⌋` leftover units to the largest fractions.
  -- `0 ≤ rem < #survivors` (Σrᵢ = total, each fraction < 1), so each award hits a distinct survivor.
  let mut rem := total - used
  while rem > 0 do
    let mut bestI : Option Nat := none
    let mut bestF : Float := -1.0
    for i in [0:n] do
      if kept[i]! && fracs[i]! > bestF then
        bestF := fracs[i]!
        bestI := some i
    match bestI with
    | some i =>
        base := base.set! i (base[i]! + 1)
        fracs := fracs.set! i (-1.0)   -- spent — do not award this survivor twice
        rem := rem - 1
    | none => rem := 0                 -- defensive: no positive fraction left (float rounding)
  return base.toList

/-- `allocate` straight from `(cᵢ, momentsᵢ)` terms — the shape `Sensitivity.coefficients` returns
and `Combine.gumStdUnc` consumes: contribution-rank and split in one call. -/
def allocateFromTerms (total : Nat) (terms : List (Float × MomentData Float))
    (dropRatio : Float := 0.0) : List Nat :=
  allocate total (contributions terms) dropRatio

end PropertyKindCalculus.Uncertainty.Allocation

end Blanket
