/-
# Adequacy-limit verification — where a report may not be read, and where the carrier may not be used

`AdequacySwamping` shows what the `Adequacy` carrier *does*: it flags the two ways a
floating-point evaluation discards an input uncertainty. This module is the other half of the
same obligation — the two places where a report, taken at face value, says something the carrier
did not establish. Both are limits on **reading**, not soundness bugs: `Adequacy.isAdequate` is
sound in both.

  * **Limit 1 — the report's counts are path multiplicities, not site counts.** A number that
    looks like a measurement, and is not one.
  * **Limit 2 — a 0th-order `sqrt` turns a contraction into an expansion.** The carrier's
    *arithmetic* is not implicated; what is missing is one derivative, and inside a fixed point
    that is enough to make the cancellation flag fire on everything.

Every claim below is a `#guard`, so this module either builds or names the claim that stopped
being true; the `#eval`s print the tables `UNCERTAINTY.md` §7 quotes. Mathlib- and
TorchLean-free, like the carrier it exercises — it imports nothing but
`PropertyKindCalculus.Uncertainty.Adequacy`, so it is a sub-second check that anyone can rerun
before touching the carrier.

**Both limits were found by scoring a real model**, not by reading the source: soil-moisture-
model's closed-form Stage-3 retrieval, instantiated at this carrier over a 2000-node domain.
That model is downstream and cannot be imported here, so each limit is reduced below to the
handful of lines that exhibit it. The numbers taken from that run are labelled where they
appear; everything else is computed here.

**What this module does not claim.** It shows *that* the two effects occur and *what* produces
them. Whether the frequency and magnitude seen on one retrieval are representative is a separate
question that more models would settle — and the limits are worth pinning either way, because
each is a statement about the carrier's own arithmetic rather than about any model.
-/

module

public import PropertyKindCalculus.Uncertainty.Adequacy
meta import PropertyKindCalculus.Uncertainty.Adequacy

public section -- pkc-blanket
@[expose] section -- pkc-blanket-expose

open PropertyKindCalculus
open PropertyKindCalculus.Uncertainty
open PropertyKindCalculus.Uncertainty.Adequacy

namespace PropertyKindCalculus.UncertaintyExamples.AdequacyLimits

/-! ## Limit 1 — `AdequacyReport`'s counts are path multiplicities, not site counts

`AdequacyReport.merge` adds its operands' counts, and the carrier is a plain value carrier: a
`let`-bound sub-expression used twice contributes its report twice. So a *site* is counted once
per evaluation path that reaches it, and the number in the report is not a number of sites. -/

/-- Exactly one absorption site: `1.0 ± 1e-10` added to an exact `1e6`. `ulp32(1e6)/2 = 0.03125`,
the smaller-magnitude operand's uncertainty is `1e-10`, and `1e-10 < 0.03125`, so the addition
flags — once. -/
def oneSite : Adequacy := Adequacy.input 1.0 1e-10 + Adequacy.exact 1e6

#guard oneSite.report.absorptions == 1

/-- The same single site, reached by `2 ^ k` paths. Nothing new is flagged: `Adequacy.mul` finds
no site of its own, it only merges. -/
def reused : Nat → Adequacy
  | 0 => oneSite
  | n + 1 => reused n * reused n

/-! **The count doubles per reuse while the number of sites stays one.** -/
#guard (List.range 5).map (fun k => (reused k).report.absorptions) == [1, 2, 4, 8, 16]

/-- **Zero is nevertheless preserved exactly**, in both directions — a count is non-zero iff some
path reaches a flagged site iff some site is flagged. So `isAdequate` is sound and is the only
part of a report that may be read. -/
def cleanSite : Adequacy := Adequacy.input 1.0 1e-1 + Adequacy.exact 1e6

#guard cleanSite.report.absorptions == 0
#guard Adequacy.isAdequate ((cleanSite * cleanSite) * (cleanSite * cleanSite)) == true
#guard Adequacy.isAdequate (reused 4) == false

/-! ## Limit 2 — a 0th-order `sqrt` turns a contraction into an expansion

`Adequacy`'s `MathCarrier` maps the value through `exp`, `log` and `sqrt` and carries the
uncertainty *unchanged*. Its header records that as 0th order and defers first-order
sensitivities to Stage 3.x. What the deferral costs is larger than "the sensitivity is
approximate": inside a fixed-point iteration it replaces the loop's damping factor with `1`,
and any multiplication in the loop then compounds unopposed.

The arithmetic operators are not implicated, which is what makes the diagnosis specific — the
first two loops below converge correctly. -/

/-- Iterate `f` on `v`, `n` times. -/
def iterate (n : Nat) (f : Adequacy → Adequacy) (v : Adequacy) : Adequacy :=
  match n with | 0 => v | n + 1 => iterate n f (f v)

/-- The input uncertainty every loop below starts from. -/
def u0 : Float := 1e-3

/-! ### The arithmetic contraction is handled correctly

`v ↦ ½·v + c` has fixed point `v* = 2c` and standard first-order uncertainty `u(v*) = 2·u(c)`.
The carrier converges to exactly that: `u₀·(1 + ½ + ¼ + …) → 2·u₀`. -/
def linearLoop (c v : Adequacy) : Adequacy := Adequacy.exact 0.5 * v + c

#eval (List.range 9).map fun n =>
  (n, (iterate n (linearLoop (Adequacy.input 1.0 u0)) (Adequacy.exact 0.0)).unc)

/-! Within a thousandth of the true `2·u₀` after eight steps. -/
#guard ((iterate 8 (linearLoop (Adequacy.input 1.0 u0)) (Adequacy.exact 0.0)).unc
          - 2.0 * u0).abs < 1e-5

/-! ### A division in the loop is handled correctly too

`v ↦ c/(2 + v) + 0.4·v`, with the uncertain value in the *divisor* — `Adequacy.div`'s
first-order propagation, in a loop. It converges. -/
def divLoop (c v : Adequacy) : Adequacy :=
  c / (Adequacy.exact 2.0 + v) + Adequacy.exact 0.4 * v

#guard (iterate 8 (divLoop (Adequacy.input 1.0 u0)) (Adequacy.exact 0.0)).unc < 1e-3

/-! ### The `sqrt` loop diverges, at a rate the caller chooses

`f(v) = C·√v` has fixed point `v* = C²` and derivative `f'(v) = C / (2√v)`, so `f'(v*) = ½`
for **every** `C`: the value contracts at one half, always. The carrier models `u(√x) = u(x)`,
so its modelled per-step factor is `C` rather than `½`, and for `C > 1` the uncertainty grows
geometrically while the value converges.

`C = 93` is not special — it is the factor that was measured on the real model, reproduced
here to show it is the carrier's arithmetic and not that model's shape. -/
def sqrtLoop (C : Float) (v : Adequacy) : Adequacy :=
  Adequacy.exact C * MathCarrier.sqrt v

def sqrtRun (C : Float) : List (Nat × Float × Float) :=
  (List.range 9).map fun n =>
    let a := iterate n (sqrtLoop C) (Adequacy.input 1.0 u0)
    (n, a.value, a.unc)

#eval sqrtRun 93.0
#eval sqrtRun 0.5

/-! **The value converges** to `v* = 93² = 8649`: eight steps take it within 4% of the fixed
point, still descending. -/
#guard (((iterate 8 (sqrtLoop 93.0) (Adequacy.input 1.0 u0)).value - 8649.0) / 8649.0).abs < 0.04

/-! **The modelled uncertainty grows by exactly `C` per step** — `u₀ · C⁸`, to within rounding.
A contraction reported as an expansion, geometrically, with no flag saying so. -/
#guard ((iterate 8 (sqrtLoop 93.0) (Adequacy.input 1.0 u0)).unc
          / (u0 * Float.pow 93.0 8.0) - 1.0).abs < 1e-9

/-! And with the amplification removed (`C = ½`), the same loop's uncertainty contracts — so it
is the `sqrt`'s missing `1/(2√x)` that is doing the damage, not the presence of a loop. -/
#guard (iterate 8 (sqrtLoop 0.5) (Adequacy.input 1.0 u0)).unc < u0

/-! ### The consequence

A cancellation flag fires when a subtraction's result falls below the uncertainty reaching it.
Under a propagation that can be many decades too large, it fires everywhere and discriminates
nothing — which is what was observed on the real model: every node of a 2000-node domain
flagged at every input uncertainty from `10⁻²` to `10⁻⁹`, against a finite-difference
first-order figure of `1.3 × 10⁻²`. The swamping flag is unaffected, because it compares an
operand's *own* uncertainty against half a ulp before the accumulation reaches it. -/

end PropertyKindCalculus.UncertaintyExamples.AdequacyLimits

end -- pkc-blanket-expose
end -- pkc-blanket
