/-
# The angle-augmented base — PKC adopts the metrological angle reform

A decade of *Metrologia* argument (Quincey 2016, 2019; Mills 2016; Kalinin 2019;
Leonard 2021; Mohr 2022) holds that *plane angle* should be a base dimension of its
own, with *solid angle* carrying its square (`sr = rad²`), so that the dimensional
algebra itself distinguishes the radian, the steradian, and a pure number, and
forbids spurious factors of `2π`. Because PhysLib's `Dimension` is now **parametric
in its basis** (the base-set-parametric API the author contributed upstream), PKC
can *adopt* that reform: its canonical dimensional basis is `Base`, PhysLib's five
generators augmented with `angle`.

Over `Base` the reform's claims are theorems of the dimension group:

* `radian ≠ steradian ≠ 1` — the three are dimensionally distinct (contrast the
  five-generator sub-basis, where all three collapse to dimension one);
* `torque ≠ energy` — torque is energy *per angle* (`M·L²·T⁻²·A⁻¹`), the separation
  the classical `M·L²·T⁻²` sub-basis cannot see;
* `torque · angle = energy` — the sanctioned product is coherent by genuine
  cancellation of the angle exponent, not by multiplying by a hidden `1`.

The angle-free ISO 80000 catalogue keeps its natural five-generator sub-basis and
**lifts** into `Base` along the injective embedding `emb : LTMCTDimensionBase ↪ Base`, with
the *kind* invariant under the lift (`DimensionedKind.extend_kind`): the base choice
is invisible at the kind layer. And the dimension-one conflation the kind layer
exists to repair *survives* the reform — volumetric and gravimetric water content are
angle-free, hence still one dimension yet distinct kinds — so the kind layer is
needed even with angle promoted.

Library module (theorems only); worked `#eval`/`example` demonstrations live in
`DimensionExamples`. Built by `lake build Dimension`.
-/

module

public import PropertyKindCalculus.Dimension

public section -- pkc-blanket
@[expose] section -- pkc-blanket-expose

open Dimension

namespace PropertyKindCalculus

/-- **PKC's canonical base-dimension basis**: PhysLib's five generators (length,
time, mass, charge, temperature) augmented with **`angle`**, adopting the reform in
which plane angle is a base dimension and solid angle its square. -/
inductive Base
  | length | time | mass | charge | temperature | angle
  deriving DecidableEq

-- The `Fintype` derive handler produces an ill-typed `Finset` under Lean v4.33
-- (its generated `Membership` rewrite no longer typechecks at reducible
-- transparency), so the instance is written out.
instance : Fintype Base where
  elems := {.length, .time, .mass, .charge, .temperature, .angle}
  complete := fun x => by cases x <;> decide

-- `Dimension B` takes `[DimensionBasis B]`: a basis must say what native tuple of exponents
-- represents it. `DimensionBasis.pi` is PhysLib's function-backed representation, for a basis
-- with no specialized tuple — which is this one. The specialized alternative buys a packed
-- `Exponents` type (as `LTMCTDimensionBase` has), and nothing here reads the representation.
instance : DimensionBasis Base := DimensionBasis.pi Base

namespace AngleReform

/-! ## Generators of the angle-augmented base -/

/-- Length generator over `Base`. -/
def L : Dimension Base := single .length
/-- Time generator over `Base`. -/
def T : Dimension Base := single .time
/-- Mass generator over `Base`. -/
def M : Dimension Base := single .mass
/-- **The plane-angle generator** — the reform's added base dimension. -/
def A : Dimension Base := single .angle

/-! ## Reform quantities, native over `Base` -/

/-- Energy/work over the angle-augmented base, `M·L²·T⁻²` (angle-free). -/
def energy : Dimension Base := M * L * L / T / T
/-- **Plane angle** (the radian), dimension `A`. -/
def planeAngle : Dimension Base := A
/-- **Solid angle** (the steradian), the *square* of plane angle: `sr = rad²`. -/
def solidAngle : Dimension Base := planeAngle ^ (2 : ℕ)
/-- **Torque**, `M·L²·T⁻²·A⁻¹` — energy *per angle*. The reform separates it from
energy; the classical `M·L²·T⁻²` sub-basis cannot. -/
def torque : Dimension Base := energy / planeAngle

/-! ## The reform's dimensional claims, as theorems -/

/-- Solid angle is the square of plane angle: `sr = rad²`. -/
theorem solidAngle_eq_sq : solidAngle = planeAngle * planeAngle := by
  rw [solidAngle, pow_two]

/-- **Plane angle is dimensionally distinct from a pure number** — the radian is not
dimensionless in the reform. -/
theorem planeAngle_ne_one : planeAngle ≠ 1 := by
  intro h
  have := congrArg (fun d => Dimension.exponent d .angle) h
  simp [planeAngle, A, single_exponent] at this

/-- **Solid angle is dimensionally distinct from plane angle** — the steradian is not
the radian. -/
theorem solidAngle_ne_planeAngle : solidAngle ≠ planeAngle := by
  intro h
  have := congrArg (fun d => Dimension.exponent d .angle) h
  simp [solidAngle, planeAngle, A, npow_exponent, single_exponent] at this

/-- **Solid angle is dimensionally distinct from a pure number.** -/
theorem solidAngle_ne_one : solidAngle ≠ 1 := by
  intro h
  have := congrArg (fun d => Dimension.exponent d .angle) h
  simp [solidAngle, planeAngle, A, npow_exponent, single_exponent] at this

/-- **Torque and energy carry different dimensions** — the reform's headline. Torque
is energy per angle (`A`-exponent `-1`); energy is angle-free (`A`-exponent `0`). -/
theorem torque_ne_energy : torque ≠ energy := by
  intro h
  have := congrArg (fun d => Dimension.exponent d .angle) h
  simp [torque, energy, planeAngle, A, L, T, M, div_exponent, mul_exponent,
    single_exponent] at this

/-- **The sanctioned product `torque · angle = energy` is coherent by cancellation.**
The angle exponent of torque (`-1`) and of angle (`+1`) sum to `0`, recovering energy
— a genuine group cancellation, not multiplication by a hidden dimensionless `1`. -/
theorem torque_mul_angle_eq_energy : torque * planeAngle = energy := by
  rw [torque, div_mul_cancel]

/-! ## The five-generator catalogue embeds faithfully, kinds invariant

`emb` injects PhysLib's basis into `Base`; the existing catalogue re-expresses
losslessly along it, and every *kind* is fixed by the re-coordinatization. -/

/-- The injective embedding of PhysLib's basis into the angle-augmented `Base`. -/
def emb : LTMCTDimensionBase → Base
  | .length => .length
  | .time => .time
  | .mass => .mass
  | .charge => .charge
  | .temperature => .temperature

/-- `emb` is injective, so the lift along it preserves every exponent. -/
theorem emb_injective : Function.Injective emb := by
  intro a b h; cases a <;> cases b <;> simp_all [emb]

/-- **The catalogue lifts faithfully into the reform base.** Re-coordinatizing a
five-generator kind along the embedding preserves every original exponent (here,
length's `1` in `lengthKind`), so the catalogue re-expresses over `Base` without loss —
the added `angle` generator only contributes fresh zero exponents. -/
theorem lengthKind_lift_faithful :
    (lengthKind.extend emb).toDimension.exponent (emb .length)
      = lengthKind.toDimension.exponent .length :=
  DimensionedKind.extend_toDimension_exponent emb_injective lengthKind .length

/-- **Energy stays angle-free in the reform base**: lifting it adds only a zero
exponent for the new `angle` generator. -/
theorem energy_angle_free : energy.exponent .angle = 0 := by
  simp [energy, M, L, T, div_exponent, mul_exponent, single_exponent]

/-! ## Kinds over the angle-augmented base

The reform separates the radian, steradian, and number **at the dimension layer**.
The kind layer still separates the quantities the dimension layer cannot — angle-free
distinct kinds such as volumetric and gravimetric water content. -/

/-- The plane-angle kind (the radian), over `Base`. -/
def radianKind : DimensionedKind Base :=
  { kind := { id := "plane angle", scale := .ratio }, dim := planeAngle }
/-- The solid-angle kind (the steradian), over `Base`. -/
def steradianKind : DimensionedKind Base :=
  { kind := { id := "solid angle", scale := .ratio }, dim := solidAngle }
/-- The pure-number kind (dimension one), over `Base`. -/
def numberKind : DimensionedKind Base :=
  { kind := { id := "number", scale := .ratio }, dim := 1 }

/-- **Radian, steradian, and number are pairwise dimensionally distinct** under the
reform — the separation a five-generator basis cannot draw, now drawn by the dimension
group itself. -/
theorem radian_steradian_number_distinct :
    radianKind.toDimension ≠ steradianKind.toDimension ∧
    radianKind.toDimension ≠ numberKind.toDimension ∧
    steradianKind.toDimension ≠ numberKind.toDimension :=
  ⟨fun h => solidAngle_ne_planeAngle h.symm, planeAngle_ne_one, solidAngle_ne_one⟩

/-- **The lift fixes the kind.** A catalogue kind re-expressed over the angle-augmented
base is the *same kind* — the base choice is invisible one layer up. -/
theorem lengthKind_lift_kind : (lengthKind.extend emb).kind = lengthKind.kind := rfl

/-- **The dimension-one conflation survives the reform.** Volumetric and gravimetric
water content are angle-free, so they remain a single dimension (`1`) over the
angle-augmented base too, yet are distinct kinds — the kind layer is still needed even
with angle promoted to a base dimension. -/
theorem waterContent_still_conflated :
    (vwc.extend emb).toDimension = (gwc.extend emb).toDimension ∧
    (vwc.extend emb).kind ≠ (gwc.extend emb).kind :=
  ⟨rfl, vwc_ne_gwc⟩

end AngleReform
end PropertyKindCalculus

end -- pkc-blanket-expose
end -- pkc-blanket
