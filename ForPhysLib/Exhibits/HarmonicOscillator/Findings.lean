/-
# Exhibit C — HarmonicOscillator: the findings

**Source.** `Physlib/ClassicalMechanics/HarmonicOscillator/Basic.lean` and
`Physlib/ClassicalMechanics/Pendulum/SimplePendulum/Basic.lean`, probed directly.

**The findings (M6 — names are load-bearing and unchecked):**

1. **The argument-order collision.** `lagrangian (t) (x) (v)` takes position second;
   `hamiltonian (t) (p) (x)` takes *momentum* second — both at
   `EuclideanSpace ℝ (Fin 1)`, so calling the Hamiltonian with position and momentum
   swapped elaborates. This is what makes the `funext t x p` in `hamiltonian_eq`'s proof
   possible: the binder named `x` there *is the momentum* and the binder named `p` is the
   position, and nothing in the file can notice.
2. **`S.force` accepts a momentum.** The force wants a position; the canonical momentum
   has the same type; the composition type-checks.
3. **`toCanonicalMomentum : E ≃ₗ[ℝ] E`** carries a velocity to a momentum between
   *identical* types — so the momentum of a momentum also type-checks.
4. **Bare-real system parameters.** `HarmonicOscillator { m k : ℝ }` and
   `SimplePendulum { m ℓ g : ℝ }`: `√(m/k)` and `√(ℓ/g)` are exactly as well-typed as
   the correct `√(k/m)` and `√(g/ℓ)`.

**The MR11 question, answered on real library code.** The kinded re-authoring below puts
the oscillator's formulas next to PhysLib's own: `(1/2 : ℝ) • (m * (v * v))` against
`1 / (2 : ℝ) * S.m * ⟪v, v⟫_ℝ`, and `√((S.k / S.m).magnitude)` against `√(S.k / S.m)` —
one `kind_algebra` block and two joined table entries stand the whole algebra up, every
finding above becomes a `#check_failure`, and `√(m/k)` now dies *before* the square root:
`m / k` is not a registered edge. The kinetic energy is then instantiated, from the same
definition, at `ℝ` and at `Float32`, with the magnitude law one carrier-quantified `rfl`
(MR27; the exec/spec scope honesty stays as the case study states it).
-/

module

public import Physlib.ClassicalMechanics.HarmonicOscillator.Basic
meta import Physlib.ClassicalMechanics.HarmonicOscillator.Basic
public import Physlib.ClassicalMechanics.Pendulum.SimplePendulum.Basic
meta import Physlib.ClassicalMechanics.Pendulum.SimplePendulum.Basic
public import PropertyKindCalculus.KindAlgebra
meta import PropertyKindCalculus.KindAlgebra
public import PropertyKindCalculus.Iso80000.Part3
meta import PropertyKindCalculus.Iso80000.Part3
public import PropertyKindCalculus.Iso80000.Part4
meta import PropertyKindCalculus.Iso80000.Part4
public import PropertyKindCalculus.QuantityReal
meta import PropertyKindCalculus.QuantityReal

@[expose] public section

namespace ForPhysLib.Exhibits.HarmonicOscillator

open PropertyKindCalculus Real

/-! ## Finding 1 — the argument-order collision -/

/-- The Hamiltonian called with position and momentum **swapped**: elaborates, and is
`H` evaluated at nonsense. `lagrangian` reads `(t, x, v)`; `hamiltonian` reads
`(t, p, x)`; the types cannot object. -/
noncomputable example (S : ClassicalMechanics.HarmonicOscillator) (t : Time)
    (p x : EuclideanSpace ℝ (Fin 1)) : ℝ :=
  S.hamiltonian t x p

/-! ## Finding 2 — the force accepts a momentum -/

/-- `force` wants a position; the canonical momentum is the same type. -/
noncomputable example (S : ClassicalMechanics.HarmonicOscillator) (t : Time)
    (x v : EuclideanSpace ℝ (Fin 1)) : EuclideanSpace ℝ (Fin 1) :=
  S.force (S.toCanonicalMomentum t x v)

/-! ## Finding 3 — the momentum of a momentum -/

/-- `toCanonicalMomentum` is an equivalence of a type with itself, so it happily maps a
momentum to a "momentum of a momentum". -/
noncomputable example (S : ClassicalMechanics.HarmonicOscillator) (t : Time)
    (x v : EuclideanSpace ℝ (Fin 1)) : EuclideanSpace ℝ (Fin 1) :=
  S.toCanonicalMomentum t x (S.toCanonicalMomentum t x v)

/-! ## Finding 4 — the reciprocal frequency -/

/-- `√(m/k)` — the *period* recipe where the frequency was wanted — is exactly as
well-typed as the file's `ω = √(k/m)`. -/
noncomputable example (S : ClassicalMechanics.HarmonicOscillator) : ℝ := √(S.m / S.k)

/-- And the pendulum's `√(ℓ/g)` likewise, against its `ω = √(g/ℓ)`. -/
noncomputable example (P : ClassicalMechanics.SimplePendulum) : ℝ := √(P.ℓ / P.g)

/-! ## The kinded re-authoring — MR11 measured on real library code

Four base kinds by hand (base kinds carry the semantics), one `kind_algebra` block for
the derived algebra, and two hand-registered entries where two products *join* at the
same kind — energy is one kind with two licensed factorizations, which a generated block
deliberately cannot say. -/

/-- Mass — the oscillator's `m`; the catalogue's own 4-1. -/
def massK : KindOfProperty := (Iso80000.Part4.mass).kind

/-- Stiffness — the oscillator's `k`, examined as restoring force per displacement. -/
def stiffnessK : KindOfProperty :=
  { id := "stiffness", scale := .ratio, examPrinciple := some "restoring-per-displacement" }

/-- Displacement from equilibrium — the oscillator's `x`; the catalogue's own 3-1.11. -/
def dispK : KindOfProperty := (Iso80000.Part3.displacement).kind

/-- Velocity — the oscillator's `v`; the catalogue's own 3-10.1. -/
def velK : KindOfProperty := (Iso80000.Part3.velocity).kind

/-- Angular frequency — the `ω` the square root lands at; the catalogue's own 3-18. -/
def angularFrequencyK : KindOfProperty := (Iso80000.Part3.angularFrequency).kind

kind_algebra
  momentumK : "mass × velocity"          := massK * velK
  kv2       : "velocity squared"         := velK * velK
  kx2       : "displacement squared"     := dispK * dispK
  kp2       : "momentum squared"         := momentumK * momentumK
  kω2       : "angular frequency squared" := stiffnessK / massK
  forceK    : "stiffness × displacement" := stiffnessK * dispK

/-- Energy — the catalogue's own mechanical energy (4-28.3): one kind, reached by two
licensed factorizations below. -/
def energyK : KindOfProperty := (Iso80000.Part4.mechanicalEnergy).kind

/-- `m · v²` is an energy — the kinetic factorization. -/
instance : KindMul massK kv2 energyK := ⟨ProductKind.ofRatio _ _ _⟩

/-- `k · x²` is an energy — the potential factorization, joining at the same kind. -/
instance : KindMul stiffnessK kx2 energyK := ⟨ProductKind.ofRatio _ _ _⟩

/-- `p² / m` is an energy — the Hamiltonian's kinetic term. -/
instance : KindDiv kp2 massK energyK := ⟨QuotientKind.ofRatio _ _ _⟩

open scoped PropertyKindCalculus.OperatorTable

/-- A dimensionless numeral scales a quantity without changing its kind — the `½` the
benchmark dropped, restored as a scoped action. Scoped like the operator table's
instances, and with the same honesty: the action is the Mathlib-interface tier (MR30) —
a dimensioned magnitude smuggled in as a bare numeral is what the audit measures, not
what the type prevents. -/
scoped instance {k : KindOfProperty} {R : Type} [Mul R] : SMul R (Quantity k R) :=
  ⟨fun c q => ⟨c * q.magnitude⟩⟩

/-- The kinded oscillator: PhysLib's `{ m k : ℝ, m_pos, k_pos }`, with the two
parameters carrying their kinds. Reading weight: two ascriptions. -/
structure KOscillator where
  /-- The mass. -/
  m : Quantity massK ℝ
  /-- The spring constant. -/
  k : Quantity stiffnessK ℝ
  /-- The mass is positive. -/
  m_pos : 0 < m.magnitude
  /-- The spring constant is positive. -/
  k_pos : 0 < k.magnitude

namespace KOscillator

variable (S : KOscillator)

/-- `ω = √(k/m)` — PhysLib writes `√(S.k / S.m)`; the kinded form differs by one
`.magnitude` and one attestation naming the crossing the kind layer does not yet spell
(a square root of the `ω²` kind). The wrong quotient no longer reaches the root: see
the `#check_failure` below. -/
noncomputable def ω : Quantity angularFrequencyK ℝ :=
  .attest "the square root of the registered ω² = k/m edge" (√((S.k / S.m).magnitude))

/- **Finding 4, closed before the square root.** `m / k` is not a registered edge of the
algebra, so the reciprocal-frequency mistake fails to *elaborate* — there is no number to
take the root of. -/
#check_failure fun (S : KOscillator) => S.m / S.k

/-- `ω² = k/m`, PhysLib's `ω_sq`, with PhysLib's own proof term. -/
theorem ω_sq : S.ω.magnitude ^ 2 = (S.k / S.m).magnitude :=
  sq_sqrt (div_pos S.k_pos S.m_pos).le

end KOscillator

/-! ## The energies, at reading weight

PhysLib: `1 / (2 : ℝ) * S.m * ⟪v, v⟫_ℝ - S.potentialEnergy x`. Below, the same shapes
with the kinds riding along — the `½` restored by the scoped action, the products
through the table. -/

/-- Kinetic energy `½ m v²` — carrier-generic: the *same definition* serves `ℝ` and
`Float32` below (MR27). -/
def kineticE {R : Type} [Mul R] [ScalarCarrier R] (half : R)
    (m : Quantity massK R) (v : Quantity velK R) : Quantity energyK R :=
  half • (m * (v * v))

/-- Potential energy `½ k x²`. -/
def potentialE {R : Type} [Mul R] [ScalarCarrier R] (half : R)
    (k : Quantity stiffnessK R) (x : Quantity dispK R) : Quantity energyK R :=
  half • (k * (x * x))

/-- The total energy — the sum elaborates because both factorizations join at
`energyK`; this is the two-entry curation above earning its keep. -/
def totalE {R : Type} [Mul R] [Add R] [ScalarCarrier R] (half : R)
    (m : Quantity massK R) (v : Quantity velK R)
    (k : Quantity stiffnessK R) (x : Quantity dispK R) : Quantity energyK R :=
  kineticE half m v + potentialE half k x

/-- The canonical momentum `p = m v` — between *distinct* types now. -/
def toMomentumQ {R : Type} [Mul R] [ScalarCarrier R]
    (m : Quantity massK R) (v : Quantity velK R) : Quantity momentumK R :=
  m * v

/-- The Hamiltonian `H = ½ p²/m + ½ k x²` — reading `(p, x)`, and only `(p, x)`. -/
noncomputable def hamiltonianQ (S : KOscillator)
    (p : Quantity momentumK ℝ) (x : Quantity dispK ℝ) : Quantity energyK ℝ :=
  (1 / 2 : ℝ) • ((p * p) / S.m) + (1 / 2 : ℝ) • (S.k * (x * x))

/-- The force `F = -k x`, landing at its own kind. -/
def forceQ (S : KOscillator) (x : Quantity dispK ℝ) : Quantity forceK ℝ :=
  (-1 : ℝ) • (S.k * x)

/- **Finding 1, closed.** The Hamiltonian with `p` and `x` swapped does not elaborate. -/
#check_failure fun (S : KOscillator) (p : Quantity momentumK ℝ)
    (x : Quantity dispK ℝ) => hamiltonianQ S x p

/- **Finding 2, closed.** The force refuses a momentum. -/
#check_failure fun (S : KOscillator) (p : Quantity momentumK ℝ) => forceQ S p

/- **Finding 3, closed.** The momentum of a momentum does not elaborate: `toMomentumQ`
maps velocity to momentum, and a momentum is not a velocity. -/
#check_failure fun (m : Quantity massK ℝ) (v : Quantity velK ℝ) =>
  toMomentumQ m (toMomentumQ m v)

/-! ## MR27 — one definition, two carriers, agreement as a theorem -/

/-- `Float32` is a scalar carrier — vocabulary, as `Float` already is in the core. -/
instance : ScalarCarrier Float32 := ⟨⟩

/-- The kinetic energy at the specification carrier. -/
noncomputable def kineticReal : Quantity massK ℝ → Quantity velK ℝ → Quantity energyK ℝ :=
  kineticE (1 / 2 : ℝ)

/-- The *same definition* at genuine IEEE binary32. -/
def kineticF32 : Quantity massK Float32 → Quantity velK Float32 → Quantity energyK Float32 :=
  kineticE (0.5 : Float32)

/-- **The agreement.** One magnitude law, quantified over the carrier, `rfl` — it *is*
the statement that `kineticReal` and `kineticF32` compute the same polynomial. What it
deliberately does not claim is a rounding bound; that scope honesty is the case study's
MR15 verdict, unchanged. -/
theorem kineticE_magnitude {R : Type} [Mul R] [ScalarCarrier R] (half : R)
    (m : Quantity massK R) (v : Quantity velK R) :
    (kineticE half m v).magnitude = half * (m.magnitude * (v.magnitude * v.magnitude)) :=
  rfl

/- And the executable carrier executes: `½ · 2 · 3² = 9`. -/
#guard (kineticF32 ⟨2⟩ ⟨3⟩).magnitude == 9.0

end ForPhysLib.Exhibits.HarmonicOscillator

