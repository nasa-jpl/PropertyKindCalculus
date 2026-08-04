/-
`examples.avs_forward` — **the AVS Stage-2 soil-moisture forward, kinded, written once**.

The shared kinded authority for the AVS/LAVS backscatter forward model
`σ⁰ = a·ndvi + exp(−2·b·ndvi)·c·r + d` and its residual + four analytic Jacobian columns, used by the
codegen demos `examples.tape_codegen_demo` and `examples.lm_step_codegen_demo`. Written in the
calculus' rigorous quantity discipline (the soil-moisture-model's `AvsKinds`/`ConfigKinds` pattern):
every parameter/covariate is a `Quantity` of its forced kind, the one numeric constant (the two-way
optical-path factor `2`) is a kinded quantity in a config structure, and a naked `Float` appears only
at the **emission boundary** (`attenuation`/`lavsResidual`/`lavsJacResidual`/`resJac`), where
`.magnitude` — definitionally the scalar op-tree — feeds the tape recorder. Because the boundary
functions are `.magnitude` projections of the kinded kernels, the recorded tape is byte-identical to
the naked kernel it replaces, so the codegen demos' bit-exactness `#guard`s and `Evaluates`
faithfulness proofs are unaffected.

Self-contained: PKC cannot import `soil-moisture-model` (that package already requires PKC — a
dependency cycle), so the AVS kinds and kernel are reproduced fresh here. The op-structure matches
`kernel.avs_batch.lavsResidual`/`lavsJacResidual` op-for-op.
-/
import PropertyKindCalculus.Quantity
import PropertyKindCalculus.QuantityClassification
import PropertyKindCalculus.QuantityFunction
import PropertyKindCalculus.Paradigm.NumCarrier

namespace PropertyKindCalculus.Examples.AvsForward

open PropertyKindCalculus
open PropertyKindCalculus.Paradigm (NumCarrier)

/-! ## The AVS kinds-of-property (the opt-in registry)

Read off `σ⁰ = a·ndvi + exp(−2·b·ndvi)·c·r + d`: `b·ndvi` sits in `exp` ⇒ `b : ndvi⁻¹`; `a·ndvi` is a
backscatter ⇒ `a : σ⁰·ndvi⁻¹`; `c·r` is a backscatter ⇒ `c : σ⁰·reflectivity⁻¹`; `d : σ⁰`. All
ratio-scale (so the kind arithmetic is defined) and all dimension one (a dimension checker cannot
separate the three roles below — only the kind check can). -/

/-- σ⁰, the backscatter coefficient — the model output and the measured input `s0`. -/
def backscatter : KindOfProperty := { id := "AVS backscatter coefficient σ⁰", scale := .ratio }
/-- The vegetation index `ndvi` — the model's covariate. -/
def vegetationIndex : KindOfProperty := { id := "AVS vegetation index", scale := .ratio }
/-- The surface reflectivity `r` — the soil-moisture-sensitive covariate. -/
def reflectivity : KindOfProperty := { id := "AVS surface reflectivity", scale := .ratio }
/-- The pure number — the identity of the kind algebra; here the two-way coefficient `−2` and the
`−1` of `∂/∂d`. -/
def pureNumber : KindOfProperty := { id := "AVS pure number", scale := .ratio }
/-- The attenuation exponent `−2·b·ndvi` — dimension one (because `b : ndvi⁻¹`), consumed only by `exp`. -/
def attenExponent : KindOfProperty := { id := "AVS attenuation exponent", scale := .ratio }
/-- The vegetation attenuation `E = exp(−2·b·ndvi)` — the two-way canopy transmittance. -/
def attenuationK : KindOfProperty := { id := "AVS vegetation attenuation", scale := .ratio }
/-- `a : σ⁰·ndvi⁻¹` — the (linearised) vegetation gain. -/
def paramA : KindOfProperty := { id := "AVS gain a (σ⁰ per NDVI)", scale := .ratio }
/-- `b : ndvi⁻¹` — the canopy attenuation rate. -/
def paramB : KindOfProperty := { id := "AVS rate b (inverse NDVI)", scale := .ratio }
/-- `c : σ⁰·reflectivity⁻¹` — the soil gain. -/
def paramC : KindOfProperty := { id := "AVS gain c (σ⁰ per reflectivity)", scale := .ratio }
/-- `∂residual/∂b : σ⁰·ndvi` (= σ⁰/b). -/
def jacB : KindOfProperty := { id := "AVS backscatter times NDVI", scale := .ratio }
/-- The left-associated partial `ndvi·c` that `2·ndvi·c·r` passes through (`(2·ndvi)·c`). -/
def jacBPartial : KindOfProperty := { id := "AVS NDVI times gain c", scale := .ratio }

/-- The three dimension-one roles are pairwise distinct kinds — what a dimension checker cannot see. -/
theorem attenuation_roles_distinct :
    pureNumber ≠ attenExponent ∧ pureNumber ≠ attenuationK ∧ attenExponent ≠ attenuationK := by
  refine ⟨?_, ?_, ?_⟩ <;> decide

/-! ## The configuration — the one numeric constant, as a kinded quantity -/

/-- `Nat → α` embedding (the sanctioned structural-literal lift; `NumCarrier` gives `Coe Nat α`). -/
def ofN {α : Type} [NumCarrier α] (n : Nat) : α := (n : α)

/-- The AVS forward's configuration: the two-way optical-path factor `2`, as a kinded quantity — the
sole numeral of the model. -/
structure AvsConfig (α : Type) where
  /-- The two-way optical-path factor `2` (kind `pureNumber`). -/
  two : Quantity pureNumber α

/-- The deployed configuration `two = 2` — carrier-generic, one config read at every carrier. -/
def deployed {α : Type} [NumCarrier α] : AvsConfig α := { two := ⟨ofN 2⟩ }

/-! ## The kinded kernels — literal-free

Each mirrors `kernel.avs_batch` op-for-op, so its `.magnitude` is the same `Float` the bare kernel
computes; the only inline symbols are the carrier's `0`/`1` identities. -/

/-- The vegetation attenuation `τ = exp(−2·b·ndvi)`, kind `attenuationK`. -/
def attenuationQ {α : Type} [NumCarrier α] (cfg : AvsConfig α)
    (b : Quantity paramB α) (ndvi : Quantity vegetationIndex α) : Quantity attenuationK α :=
  let negTwo : Quantity pureNumber α := (⟨(0 : α)⟩ : Quantity pureNumber α) - cfg.two
  let arg : Quantity attenExponent α :=
    Quantity.mul (ProductKind.ofRatio paramB vegetationIndex attenExponent)
      (Quantity.mul (ProductKind.ofRatio pureNumber paramB paramB) negTwo b) ndvi
  Quantity.exp (⟨rfl, rfl⟩ : TranscendentalKind attenExponent attenuationK) arg

/-- The LAVS forward `σ⁰ = a·ndvi + (τ·c)·r + d`, kind `backscatter`. -/
def lavsForwardQ {α : Type} [NumCarrier α] (cfg : AvsConfig α)
    (a : Quantity paramA α) (b : Quantity paramB α) (c : Quantity paramC α) (d : Quantity backscatter α)
    (ndvi : Quantity vegetationIndex α) (r : Quantity reflectivity α) : Quantity backscatter α :=
  let att := attenuationQ cfg b ndvi
  Quantity.mul (ProductKind.ofRatio paramA vegetationIndex backscatter) a ndvi
    + Quantity.mul (ProductKind.ofRatio paramC reflectivity backscatter)
        (Quantity.mul (ProductKind.ofRatio attenuationK paramC paramC) att c) r
    + d

/-- The LAVS residual `s0 − σ⁰`, kind `backscatter` (subtraction forces the shared kind). -/
def lavsResidualQ {α : Type} [NumCarrier α] (cfg : AvsConfig α)
    (a : Quantity paramA α) (b : Quantity paramB α) (c : Quantity paramC α) (d : Quantity backscatter α)
    (ndvi : Quantity vegetationIndex α) (r : Quantity reflectivity α) (s0 : Quantity backscatter α) :
    Quantity backscatter α :=
  s0 - lavsForwardQ cfg a b c d ndvi r

/-- The four analytic Jacobian columns `∂residual/∂(a,b,c,d)`, each at its forced kind. Grouping
matches `kernel.avs_batch.lavsJacResidual` (the `∂/∂b` left-fold passes through `jacBPartial`). -/
def lavsJacResidualQ {α : Type} [NumCarrier α] (cfg : AvsConfig α)
    (b : Quantity paramB α) (c : Quantity paramC α)
    (ndvi : Quantity vegetationIndex α) (r : Quantity reflectivity α) :
    Quantity vegetationIndex α × Quantity jacB α × Quantity reflectivity α × Quantity pureNumber α :=
  let att := attenuationQ cfg b ndvi
  let ja : Quantity vegetationIndex α := (⟨(0 : α)⟩ : Quantity vegetationIndex α) - ndvi
  let jb : Quantity jacB α :=
    Quantity.mul (ProductKind.ofRatio jacB attenuationK jacB)
      (Quantity.mul (ProductKind.ofRatio jacBPartial reflectivity jacB)
        (Quantity.mul (ProductKind.ofRatio vegetationIndex paramC jacBPartial)
          (Quantity.mul (ProductKind.ofRatio pureNumber vegetationIndex vegetationIndex) cfg.two ndvi)
          c)
        r)
      att
  let jc : Quantity reflectivity α :=
    (⟨(0 : α)⟩ : Quantity reflectivity α)
      - Quantity.mul (ProductKind.ofRatio attenuationK reflectivity reflectivity) att r
  let jd : Quantity pureNumber α :=
    (⟨(0 : α)⟩ : Quantity pureNumber α) - (⟨(1 : α)⟩ : Quantity pureNumber α)
  (ja, jb, jc, jd)

/-! ## The emission boundary — `.magnitude` projections for the scalar tape recorder

Naked `Float`/`α` appears only here, where the model meets the (scalar) tape recorder. Each is
definitionally the scalar op-tree of `kernel.avs_batch`, so recording these builds a tape byte-identical
to the naked kernel. -/

/-- Boundary: `exp(−2·b·ndvi)` at the carrier (the `.magnitude` of `attenuationQ deployed`). -/
def attenuation {α : Type} [NumCarrier α] (b ndvi : α) : α :=
  (attenuationQ deployed ⟨b⟩ ⟨ndvi⟩).magnitude

/-- Boundary: the residual `s0 − σ⁰` at the carrier. -/
def lavsResidual {α : Type} [NumCarrier α] (a b c d ndvi r s0 : α) : α :=
  (lavsResidualQ deployed ⟨a⟩ ⟨b⟩ ⟨c⟩ ⟨d⟩ ⟨ndvi⟩ ⟨r⟩ ⟨s0⟩).magnitude

/-- Boundary: the four Jacobian columns `∂residual/∂(a,b,c,d)` at the carrier. -/
def lavsJacResidual {α : Type} [NumCarrier α] (b c ndvi r : α) : α × α × α × α :=
  let J := lavsJacResidualQ deployed ⟨b⟩ ⟨c⟩ ⟨ndvi⟩ ⟨r⟩
  (J.1.magnitude, J.2.1.magnitude, J.2.2.1.magnitude, J.2.2.2.magnitude)

/-- Boundary: residual + the four Jacobian columns — the `.magnitude`s of the kinded residual and
Jacobian kernels (no naked op-tree twin). The recorder shares the recomputed `att` at CSE time.
Op-structure identical to `avs_batch.lavsResidual + lavsJacResidual`. -/
def resJac {α : Type} [NumCarrier α] (a b c d ndvi r s0 : α) : α × α × α × α × α :=
  let res := (lavsResidualQ deployed ⟨a⟩ ⟨b⟩ ⟨c⟩ ⟨d⟩ ⟨ndvi⟩ ⟨r⟩ ⟨s0⟩).magnitude
  let J := lavsJacResidualQ deployed ⟨b⟩ ⟨c⟩ ⟨ndvi⟩ ⟨r⟩
  (res, J.1.magnitude, J.2.1.magnitude, J.2.2.1.magnitude, J.2.2.2.magnitude)

end PropertyKindCalculus.Examples.AvsForward
