/-
`PropertyKindCalculus.Uncertainty.Adequacy` — the **executable numerical-adequacy carrier** over
`Float` (Stage 3, `UNCERTAINTY.md` §4.3). The *runtime certificate* — the pragmatic first target of
the adequacy layer.

Numerical adequacy asks whether a floating-point evaluation loses information *at the scale of the
input uncertainties* (`UNCERTAINTY.md` P4). Because a science model is written once over
`[NumCarrier α]` (the WO1 discipline), we get the check **for free** by instantiating the *same*
model at an analysis carrier that, alongside each value, tracks the uncertainty it carries and
flags every operation that would silently drop it:

  * **swamping** (absorption) at an addition: the smaller-magnitude operand's uncertainty falls below
    half a ulp of the sum, so it is numerically invisible — the exact hazard the `ℝ`-level
    `Adequacy.Soundness.verdict_sound` (A3) proves the flag sound for;
  * **catastrophic cancellation** at a subtraction: the result is exact (Sterbenz,
    `Adequacy.Sterbenz32.flx_sterbenz`) yet its *relative* uncertainty reaches or exceeds 100%
    (`Adequacy.Sterbenz32.relUnc_amplifies`).

This is the *decidable* runtime check of `UNCERTAINTY.md` §4.3 — sound at each site by the `ℝ`
theorems, computed here over Lean's `Float`. (TorchLean's `FP32`/Flocq layer is `noncomputable`, so
the executable carrier necessarily runs over `Float`; the binary32 ulp is modelled directly. Bridging
the two is Stage 3.3 — see `Adequacy.Fp32Grounding`.) Mathlib- and TorchLean-free.
-/
import PropertyKindCalculus.Uncertainty.Carriers

namespace PropertyKindCalculus.Uncertainty

open PropertyKindCalculus.Paradigm

/-- The accumulated **adequacy report**: counts of the swamping and cancellation sites encountered so
far in an evaluation. A model is *adequate* on its inputs iff both are zero. -/
structure AdequacyReport where
  /-- Number of absorption (swamping) sites: an operand uncertainty dropped below half a ulp. -/
  absorptions : Nat := 0
  /-- Number of catastrophic-cancellation sites: a subtraction with ≥ 100% relative uncertainty. -/
  cancellations : Nat := 0
  deriving Repr, DecidableEq

/-- Combine the reports of two operands (their site counts add). -/
def AdequacyReport.merge (r s : AdequacyReport) : AdequacyReport :=
  { absorptions := r.absorptions + s.absorptions,
    cancellations := r.cancellations + s.cancellations }

/-- **The numerical-adequacy analysis carrier.** A value carries its `Float` magnitude, the absolute
uncertainty propagated to it, and the accumulated `report` of adequacy violations. Instantiating a
WO1 `[NumCarrier α]` model at `Adequacy` runs it once and emits the report — no model rewrite. -/
structure Adequacy where
  /-- The computed magnitude (over `Float`). -/
  value : Float
  /-- The absolute uncertainty contribution carried to this value. -/
  unc : Float
  /-- The accumulated adequacy report. -/
  report : AdequacyReport := {}
  deriving Repr

namespace Adequacy

/-- The **unit in the last place** of binary32 (IEEE-754 single) at magnitude `x`:
`ulp₃₂(x) = 2^(⌊log₂|x|⌋ − 23)`, the spacing of representable binary32 reals near `x` (24-bit
significand). Computed over `Float`; `0` maps to the smallest subnormal `2⁻¹⁴⁹`. This is the concrete
image of the abstract grid spacing `u` of `Adequacy.Grid`. -/
def ulp32 (x : Float) : Float :=
  if x == 0.0 then Float.exp2 (-149.0)
  else Float.exp2 (Float.floor (Float.log2 x.abs) - 23.0)

/-- An **uncertain input**: a value with an absolute uncertainty, and an empty report. -/
def input (v u : Float) : Adequacy := { value := v, unc := u }

/-- An **exact constant**: a value with zero uncertainty. -/
def exact (v : Float) : Adequacy := { value := v, unc := 0.0 }

/-- The verdict: the evaluation is **adequate** iff no swamping or cancellation site was recorded. -/
def isAdequate (a : Adequacy) : Bool :=
  a.report.absorptions == 0 && a.report.cancellations == 0

/-- Apply a `Float` function to the value, carrying the uncertainty and report unchanged
(0th-order — the carrier targets `+`/`−` adequacy; transcendental sensitivity is Stage 3.x). -/
private def mapVal (f : Float → Float) (a : Adequacy) : Adequacy := { a with value := f a.value }

/-! ## The `NumCarrier` instance — swamping and cancellation checks on `+` and `−` -/

/-- **Addition with a swamping check.** The value and uncertainty propagate; the site is flagged as
*absorbing* when the smaller-magnitude operand carries a positive uncertainty below half the sum's
ulp — it is numerically invisible in the result (A3, `Adequacy.Soundness.verdict_sound`). -/
protected def add (a b : Adequacy) : Adequacy :=
  let v := a.value + b.value
  -- the uncertainty of the smaller-magnitude operand is the one at risk of being swamped
  let riskUnc := if a.value.abs ≤ b.value.abs then a.unc else b.unc
  let flagged := decide (0.0 < riskUnc) && decide (riskUnc < ulp32 v / 2.0)
  let m := a.report.merge b.report
  { value := v, unc := a.unc + b.unc,
    report := if flagged then { m with absorptions := m.absorptions + 1 } else m }

/-- **Subtraction with a cancellation check.** The value and uncertainty propagate; the site is
flagged as *catastrophic cancellation* when the result shrinks below an operand's magnitude yet its
combined uncertainty reaches the result — relative uncertainty ≥ 100%
(`Adequacy.Sterbenz32.relUnc_amplifies`). -/
protected def sub (a b : Adequacy) : Adequacy :=
  let v := a.value - b.value
  let u := a.unc + b.unc
  let flagged := decide (0.0 < u) && decide (v.abs ≤ u) && decide (v.abs < a.value.abs)
  let m := a.report.merge b.report
  { value := v, unc := u,
    report := if flagged then { m with cancellations := m.cancellations + 1 } else m }

/-- **Multiplication** with first-order uncertainty propagation `u(ab) = |a|·u_b + |b|·u_a`. -/
protected def mul (a b : Adequacy) : Adequacy :=
  { value := a.value * b.value,
    unc := a.value.abs * b.unc + b.value.abs * a.unc,
    report := a.report.merge b.report }

/-- **Division** with first-order uncertainty propagation `u(a/b) = (|a|·u_b + |b|·u_a)/b²`. -/
protected def div (a b : Adequacy) : Adequacy :=
  { value := a.value / b.value,
    unc := (a.value.abs * b.unc + b.value.abs * a.unc) / (b.value * b.value),
    report := a.report.merge b.report }

instance : Zero Adequacy := ⟨exact 0.0⟩
instance : One Adequacy := ⟨exact 1.0⟩
instance : Add Adequacy := ⟨Adequacy.add⟩
instance : Sub Adequacy := ⟨Adequacy.sub⟩
instance : Mul Adequacy := ⟨Adequacy.mul⟩
instance : Div Adequacy := ⟨Adequacy.div⟩
instance : Min Adequacy :=
  ⟨fun a b => { value := min a.value b.value, unc := max a.unc b.unc,
                report := a.report.merge b.report }⟩
instance : Max Adequacy :=
  ⟨fun a b => { value := max a.value b.value, unc := max a.unc b.unc,
                report := a.report.merge b.report }⟩
instance : Coe Nat Adequacy := ⟨fun n => exact n.toFloat⟩

instance : MathCarrier Adequacy where
  exp a := mapVal Float.exp a
  log a := mapVal Float.log a
  sin a := mapVal Float.sin a
  cos a := mapVal Float.cos a
  sinh a := mapVal Float.sinh a
  cosh a := mapVal Float.cosh a
  tanh a := mapVal Float.tanh a
  sqrt a := mapVal Float.sqrt a
  abs a := mapVal Float.abs a
  pi := exact 3.141592653589793

/-- **`Adequacy` is a branchless numeric carrier.** With the arithmetic/lattice instances and
`MathCarrier` above, the `NumCarrier` bundle closes — so any WO1 `[NumCarrier α]` model instantiates
at `Adequacy` and is analyzed for numerical adequacy with no rewrite (`UNCERTAINTY.md` P1/§4.3). -/
instance : NumCarrier Adequacy := {}

end Adequacy

end PropertyKindCalculus.Uncertainty
