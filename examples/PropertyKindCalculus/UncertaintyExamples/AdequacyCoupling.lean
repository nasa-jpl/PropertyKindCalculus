/-
# Worked example — Stage 3.4: the kind-typed Axis-U significance budget

Stage 3.4 couples the two areas from *one* `InputDist` descriptor, and (this revision) carries the
metrological intent in the *types*. The GUM budget has three roles a naked `Float` conflates —
an input standard uncertainty `u(xᵢ) : Quantity kᵢ`, a sensitivity `cᵢ = ∂y/∂xᵢ : Quantity (kₒ/kᵢ)`,
and an output contribution `uᵢ(y) = |cᵢ|·u(xᵢ) : Quantity kₒ` — and `Uncertainty.Budget` gives each
its kind. `Adequacy.analyzeQ` folds them into a `CouplingResultQ kₒ` whose contributions and combined
uncertainty are `Quantity kₒ`; the model itself stays carrier-raw (kind-erased on the tape and the
adequacy carrier).

Three things are checked here:

  * **The kinded budget reproduces GUM.** On the Degenhardt fictive model (`Y = (X₁+X₂²)·X₃`), the
    contributions are `cᵢ·uᵢ = [1.0, 1.30, 0.28]` at kind `measurandY`, and their quadrature
    `combined` reproduces the GUM combined uncertainty `u_c ≈ 1.662` — now a `Quantity measurandY`.
    The verdict is adequate (the model loses nothing at that scale).
  * **The conflations are type errors.** `#check_failure` probes show you cannot feed an input
    uncertainty where a sensitivity is expected, cannot combine contributions of different kinds, and
    cannot swap the `CouplingResultQ` fields — the exact misuses two naked `List Float` fields allowed.
  * **A swamped contribution.** A large accumulator `baseline + δ` swamps `δ`'s contribution
    (`cₓ·uₓ = 1 < ½ ulp32(10⁸) = 4`); the verdict flags it, and the closing A3 theorem is applied at
    that contribution scale.

Everything here is a **checked fact** (the module builds under CI). Depends on TorchLean (the tape
carrier) and Mathlib (the `ℝ` A3 verdict).
-/

module

public import PropertyKindCalculus.Uncertainty.Adequacy.Significance
meta import PropertyKindCalculus.Uncertainty.Adequacy.Significance
public import PropertyKindCalculus.Uncertainty.Adequacy.Soundness
meta import PropertyKindCalculus.Uncertainty.Adequacy.Soundness
public import PropertyKindCalculus.UncertaintyExamples.DegenhardtFictive
meta import PropertyKindCalculus.UncertaintyExamples.DegenhardtFictive

public section -- pkc-blanket
@[expose] section -- pkc-blanket-expose

namespace PropertyKindCalculus.UncertaintyExamples.AdequacyCoupling

open PropertyKindCalculus PropertyKindCalculus.Paradigm PropertyKindCalculus.Uncertainty
open PropertyKindCalculus (Quantity ProductKind KindOfProperty)
open PropertyKindCalculus.UncertaintyExamples.DegenhardtFictive

/-! ## The output/input/sensitivity kinds of the fictive budget

`measurandY` and `influenceX` come from `DegenhardtFictive` (distinct ratio-scale kinds). The
sensitivity kind is `measurandY / influenceX`; the `ProductKind` witness `sensitivityYX·influenceX =
measurandY` is the GUM units cancellation `analyzeQ` demands. -/

/-- The sensitivity kind `∂(measurand Y)/∂(influence X)`. -/
def sensitivityYX : KindOfProperty := { id := "sensitivity ∂(fictive Y)/∂(influence X)", scale := .ratio }

/-- The GUM units cancellation `(measurandY/influenceX)·influenceX = measurandY`. -/
theorem hSensY : ProductKind sensitivityYX influenceX measurandY :=
  ProductKind.ofRatio sensitivityYX influenceX measurandY

/-! ## Run 1 — the kinded budget on the Degenhardt model reproduces GUM -/

/-- `Y = (X₁ + X₂²)·X₃` as a carrier-polymorphic list-model (body = `fictiveModel`). -/
def degenModel : Adequacy.ListModel := fun xs =>
  match xs with
  | [a, b, c] => fictiveModel a b c
  | _ => 0

/-- One `analyzeQ` on the *same* `[x1, x2, x3]` descriptors Stage 1 differentiated — kind-typed at
`measurandY`. -/
def couplingY : Except String (Adequacy.CouplingResultQ measurandY) :=
  Adequacy.analyzeQ hSensY degenModel [x1, x2, x3]

def contribMagsY : List Float :=
  couplingY.toOption.map (fun r => r.contributions.map (·.magnitude)) |>.getD []
def combinedMagY : Float := couplingY.toOption.map (fun r => r.combined.magnitude) |>.getD 0.0
def adequateY : Bool := couplingY.toOption.map (fun r => Adequacy.isAdequate r.verdict) |>.getD false

#eval s!"Degenhardt: contributions cᵢ·uᵢ = {contribMagsY}   combined u_c = {combinedMagY}   " ++
  s!"(GUM u_c = {gum})   adequate? {adequateY}"

-- The contributions cᵢ·uᵢ (at kind measurandY), from the same descriptors' moments.
#guard contribMagsY.length == 3
#guard Float.abs (contribMagsY[0]! - 1.0) < 1e-6          -- 5 · 0.2
#guard Float.abs (contribMagsY[1]! - 1.299038) < 1e-4     -- 5 · √(0.45²/3)
#guard Float.abs (contribMagsY[2]! - 0.275568) < 1e-4     -- 2.25 · √(0.3²/6)
-- Quadrature of the contributions *is* the GUM combined standard uncertainty u_c ≈ 1.662.
#guard Float.abs (combinedMagY - gum) < 1e-6
#guard Float.abs (combinedMagY - 1.662) < 0.01
-- Adequate at that scale (small accumulator, nothing swamped).
#guard adequateY == true

/-! ## The metrological conflations are now type errors

Each `#check_failure` is a misuse two naked `List Float` fields silently allowed. -/

-- A well-typed contribution: sensitivity (measurandY/influenceX) × input uncertainty (influenceX)
-- lands in measurandY.
#check (contributionQ hSensY (sensitivityQ (kS := sensitivityYX) 5.0)
  (stdUncQ (k := influenceX) x1.moments) : Quantity measurandY Float)

-- FORBIDDEN: feed an *input uncertainty* (Quantity influenceX) where a *sensitivity*
-- (Quantity sensitivityYX) is expected.
#check_failure contributionQ hSensY (stdUncQ (k := influenceX) x1.moments)
  (stdUncQ (k := influenceX) x2.moments)

-- FORBIDDEN: combine a contribution (measurandY) with an input uncertainty (influenceX) in one
-- quadrature — the list is not homogeneous in its kind.
#check_failure combinedQ
  [contributionQ hSensY (sensitivityQ (kS := sensitivityYX) 5.0) (stdUncQ (k := influenceX) x1.moments),
   stdUncQ (k := influenceX) x2.moments]

-- FORBIDDEN: put input uncertainties (Quantity influenceX) in the `contributions` field, which is
-- typed `List (Quantity measurandY Float)`.
#check_failure (show Adequacy.CouplingResultQ measurandY from
  { contributions := [stdUncQ (k := influenceX) x1.moments],
    combined := stdUncQ (k := influenceX) x1.moments,
    verdict := Adequacy.exact 0.0 })

/-! ## Run 2 — a large accumulator swamps a contribution

`baseline + δ` with `baseline = 10⁸` (exact) and `δ = 0 ± 1`, all at kind `deflection`. The
sensitivity is dimensionless (`∂(a+b)/∂b = 1`), so `δ`'s contribution is `1·1 = 1`, which the carrier
flags swamped below `½ ulp32(10⁸) = 4`. -/

/-- A measurement kind and the (dimensionless) sensitivity of an accumulator w.r.t. one sample. -/
def deflection : KindOfProperty := { id := "beam deflection", scale := .ratio }
def deflSens : KindOfProperty := { id := "sensitivity ∂(accumulated deflection)/∂(sample)", scale := .ratio }
theorem hSensD : ProductKind deflSens deflection deflection :=
  ProductKind.ofRatio deflSens deflection deflection

def accModel : Adequacy.ListModel := fun xs =>
  match xs with
  | [baseline, δ] => baseline + δ
  | _ => 0

def swampInputs : List (InputDist Float) := [InputDist.normal 1e8 0.0, InputDist.normal 0.0 1.0]
def swampCoupling : Except String (Adequacy.CouplingResultQ deflection) :=
  Adequacy.analyzeQ hSensD accModel swampInputs

def swampContribs : List Float :=
  swampCoupling.toOption.map (fun r => r.contributions.map (·.magnitude)) |>.getD []
def swampAbsorptions : Nat :=
  swampCoupling.toOption.map (fun r => r.verdict.report.absorptions) |>.getD 0
def swampAdequate : Bool :=
  swampCoupling.toOption.map (fun r => Adequacy.isAdequate r.verdict) |>.getD true

#eval s!"accumulator: contributions = {swampContribs}   absorptions = {swampAbsorptions}   " ++
  s!"adequate? {swampAdequate}"

#guard swampContribs.length == 2
#guard Float.abs (swampContribs[0]! - 0.0) < 1e-9        -- baseline exact
#guard Float.abs (swampContribs[1]! - 1.0) < 1e-9        -- 1 · 1
#guard swampAbsorptions == 1
#guard swampAdequate == false

/-! ## The budget is carrier-generic — run it at the `Adequacy` carrier

`Budget` is a write-once model over `[NumCarrier R]`, so the *same* `combinedQ` that produced the
`Float` number `1.662359` also runs at the `Adequacy` carrier — where it adequacy-checks its *own*
quadrature `√(Σ uᵢ²)`. Contributions of comparable magnitude combine cleanly; a contribution far
smaller than another is swamped in the sum of squares and flagged — *"is the combined-uncertainty
computation itself numerically adequate?"*, answered for free by instantiating at a different carrier. -/

/-- A `measurandY` contribution carried at the `Adequacy` analysis carrier (value = magnitude,
uncertainty = itself: the contribution *is* an uncertainty magnitude). -/
def adqContrib (v : Float) : Quantity measurandY Adequacy := ⟨Adequacy.input v v⟩

/-- Comparable contributions — the quadrature loses nothing. -/
def adqClean : Quantity measurandY Adequacy := combinedQ [adqContrib 1.0, adqContrib 1.3]
/-- A `10⁻³` contribution beside a `10⁸` one — swamped in `Σ uᵢ²`. -/
def adqSwamped : Quantity measurandY Adequacy := combinedQ [adqContrib 1e8, adqContrib 1e-3]

#eval s!"budget@Adequacy: clean absorptions = {adqClean.magnitude.report.absorptions}   " ++
  s!"swamped absorptions = {adqSwamped.magnitude.report.absorptions}"

-- The identical `combinedQ`, at `R := Adequacy`, certifies the clean quadrature and flags the swamped
-- one — the two-axis payoff (one budget × any carrier), with no rewrite.
#guard adqClean.magnitude.report.absorptions == 0
#guard adqSwamped.magnitude.report.absorptions == 1

/-! ## Soundness — inherited from A3, applied at the contribution scale -/

open PropertyKindCalculus.Uncertainty.Adequacy in
/-- The A3 verdict at the swamped contribution scale `s = cₓ·uₓ = 1` on the `10⁸` binary32 grid
(`ulp = 8`): a contribution of `1` is flagged absorbed iff the rounded sum is unchanged. Stage 3.4
supplies the `1` from `Budget.contributionQ`; the equivalence is A3 (`verdict_sound`). -/
theorem contribution_absorbed_at_scale :
    AbsorptionFlag 8 1 ↔ gridRound 8 ((100000000 : ℝ) + 1) = 100000000 :=
  verdict_sound (by norm_num) ⟨12500000, by push_cast; norm_num⟩ (by norm_num) (by norm_num)

/-- info: 'PropertyKindCalculus.UncertaintyExamples.AdequacyCoupling.contribution_absorbed_at_scale' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms contribution_absorbed_at_scale

end PropertyKindCalculus.UncertaintyExamples.AdequacyCoupling

end -- pkc-blanket-expose
end -- pkc-blanket
