/-
# Requirement annotations reaching into the Dimension layer

The requirements whose discharging declarations live in the PhysLib-backed
`Dimension` / `Interaction` / `ScaleSpanning` / `UnitConversion` / `AggregationLaws` /
`UnitReal` libraries: R1's dimension-1 disambiguation (`dim` is not injective), R5's
interaction algebra, R7's dimension homomorphism, R9's two aggregation laws whose
arithmetic the Mathlib-free core cannot do (the weighted mean, the parallel-axis
transport), R13's scale-spanning unit classification, and R17's unit conversion over
`ℝ` — both the power-of-radix factor and the arbitrary chosen reference. Applied from
afar, so the layers being annotated need no import of this machinery.

These pull in PhysLib (and, transitively, Mathlib), so — like
`CrossRefs.DimensionAnnotations` — this module is not Mathlib-free even though the
core-spine annotations in `Annotations` are.
-/

module

public import PropertyKindCalculus.Dimension
meta import PropertyKindCalculus.Dimension
public import PropertyKindCalculus.Interaction
meta import PropertyKindCalculus.Interaction
public import PropertyKindCalculus.ScaleSpanning
meta import PropertyKindCalculus.ScaleSpanning
public import PropertyKindCalculus.UnitConversion
meta import PropertyKindCalculus.UnitConversion
public import PropertyKindCalculus.UnitReal
meta import PropertyKindCalculus.UnitReal
public import PropertyKindCalculus.AggregationLaws
meta import PropertyKindCalculus.AggregationLaws
public import PropertyKindCalculus.FrameReal
meta import PropertyKindCalculus.FrameReal
public import PropertyKindCalculus.DimensionExamples.UnitConversion
meta import PropertyKindCalculus.DimensionExamples.UnitConversion
public import PropertyKindCalculus.DimensionExamples.Frames
meta import PropertyKindCalculus.DimensionExamples.Frames
public import PropertyKindCalculus.Requirements.Attributes
meta import PropertyKindCalculus.Requirements.Attributes

public section -- pkc-blanket
@[expose] section -- pkc-blanket-expose

namespace PropertyKindCalculus

/-! ## R1 — the dimension-1 disambiguation (many kinds, one dimension) -/

attribute [requirement "R1" proves "distinct kinds collapse to one dimension — dim is not injective"]
  dim_not_injective

/-! ## R5 — the interaction algebra (partial, typed, ternary product) -/

attribute [requirement "R5" specifies "the curated partial ternary product KMul (Flater App. C)"]
  InteractionAlgebra
attribute [requirement "R5" specifies "the division dual of the kind product"] InteractionAlgebra.KDiv
attribute [requirement "R5" proves "multiplication and division are inverse (a × b = c ⇔ c / b = a)"]
  InteractionAlgebra.kMul_iff_kDiv
attribute [requirement "R5" exemplifies "torque × angle = energy is sanctioned, though torque and energy share a dimension"]
  torque_angle_work

/-! ## R7 — dimension certifies coherence; it does not decide legality -/

attribute [requirement "R7" specifies "the forgetful functor dim : Kind → Dimension"]
  DimensionedKind.toDimension
attribute [requirement "R7" proves "dim is a homomorphism over the interaction algebra"]
  InteractionAlgebra.dim_homomorphism
attribute [requirement "R7" exemplifies "torque and energy share the dimension M·L²·T⁻² yet are different kinds"]
  Dim.torque_eq_energy

/-! ## R13 — scale-spanning units (a third unit category beyond base and derived) -/

attribute [requirement "R13" specifies "the three-way unit classification (base / derived / scale-spanning)"]
  UnitCategory
attribute [requirement "R13" specifies "a scale-spanning unit: dimensionally dependent, retained via a coefficient"]
  ScaleSpanningUnit
attribute [requirement "R13" specifies "the mechanical-reducibility criterion the dimension layer can detect"]
  Dimension.MechanicallyReducible
attribute [requirement "R13" proves "scale-spanning is not a function of dimension alone"]
  ScaleSpanning.scaleSpanning_not_determined_by_dimension
attribute [requirement "R13" exemplifies "the kelvin's scale-spanning character is invisible to the dimension layer (Θ kept independent)"]
  ScaleSpanning.kelvin_reduction_invisible_to_dimension
attribute [requirement "R13" exemplifies "the ampere is a genuine physical base — not scale-spanning — the contrast unit"]
  ScaleSpanning.ampere_is_physicalBase

/-! ## R17 — unit conversion round-trip, the numeric (ℝ) statement -/

-- The exact `Int`-exponent round-trip is proved core-side (`Annotations`); this is
-- the companion over the real carrier: the magnitude is multiplied by the
-- power-of-ten factor `10 ^ shift`, and the round-trip closes because the factor is
-- structurally nonzero — no chosen-reference nonzeroness needed.
attribute [requirement "R17" specifies "the §1.22 conversion factor as a real number, 10 ^ (power-of-ten shift)"]
  PrefixedUnit.realFactor
attribute [requirement "R17" proves "over ℝ, converting a magnitude between units and back is the identity (10 ^ shift · 10 ^ (−shift) = 1)"]
  PrefixedUnit.convertReal_roundtrip
attribute [requirement "R17" exemplifies "over ℝ, a cm magnitude converted to km and back returns exactly (×10⁵ then ×10⁻⁵)"]
  PropertyKindCalculus.Examples.UnitConversion.cm_km_real_roundtrip
attribute [requirement "R17" exemplifies "over ℝ at radix 2, a KiB magnitude converted to MiB and back returns exactly — the same theorem"]
  PropertyKindCalculus.Examples.UnitConversion.kib_mib_real_roundtrip

/-! ## R20 — frames and variance: the structural half of value representation

R11 specifies the ISO 80000-2 §18 *numerical* reading — one kind, one scalar unit, an
indexed array. R20 is the sentence §18 puts next to it: the quantity is independent of the
choice of coordinate system while its components are not. Independence of a choice is not a
property an array has, so the frame and the transformation law are carried as indices, and
what survives a change of frame is a theorem rather than a convention.

The definitions are Mathlib-free (`Frame`), so a change of frame runs at `Float`; the laws
need ring reasoning and so live over `ℝ` (`FrameReal`) — the same core/`QuantityReal` split
`Quantity` uses. -/

attribute [requirement "R20" specifies "a coordinate frame: the choice components are read relative to"]
  Frame
attribute [requirement "R20" specifies "the transformation law a quantity's components obey (scalar / vector / rank-2)"]
  Variance
attribute [requirement "R20" specifies "components read in a named frame at a stated variance"]
  InFrame
attribute [requirement "R20" specifies "a change of frame, and orthonormality as a hypothesis on it rather than a field of it"]
  FrameChange.IsOrthonormal
attribute [requirement "R20" proves "a change of frame is an action: the identity change acts as the identity"]
  toFrameVector_id
attribute [requirement "R20" proves "a change of frame is an action: composing two changes is the composite change"]
  toFrameVector_comp
attribute [requirement "R20" proves "the scalar product is invariant under an orthonormal change of frame — the sense in which a change of representation does not change the physics"]
  dot_toFrameVector
attribute [requirement "R20" proves "and a component is not invariant — stated with a witness, so the previous result cannot be over-read"]
  component_not_invariant
attribute [requirement "R20" specifies "the scalar gate: which carriers' × is the multiplication of magnitudes, so a numerical-array carrier cannot sign a pointwise product as a product of kinds"]
  ScalarCarrier

/-! ## R9 — the two aggregation laws whose arithmetic needs Mathlib

The weighted-mean *mode* is carrier-parametric and annotated in the core (`Annotations`); what
is annotated here is its law, which cancels a denominator and so needs a field. -/

attribute [requirement "R9" proves "the mean of a constant is that constant — the law that distinguishes a mean from a sum, at the carrier whose cancellation can prove it"]
  WeightedCarving.mean_const
attribute [requirement "R9" proves "the parallel-axis theorem: a moment of inertia transports between axes by a correction built from the carving's own first moment and total mass"]
  parallelAxis

/-! ## R20 — the worked frame change

The requirement's own scenario: a planar rover's velocity read in the lab frame and in a frame
turned a quarter turn from it. The contraction that a kinetic energy is does not move; a
component does, exhibited with the vector that shows it, so the first fact cannot be read as
"nothing changes". -/

attribute [requirement "R20" exemplifies "the kinetic-energy contraction `v·v` read in a quarter-turned frame equals the one read in the lab frame — the sense in which choosing coordinates does not change the physics"]
  PropertyKindCalculus.DimensionExamples.Frames.contraction_invariant
attribute [requirement "R20" exemplifies "and a component of the same quantity does move between the two frames — one quantity, two frames, not two quantities"]
  PropertyKindCalculus.DimensionExamples.Frames.component_moves

/-! ## R17 — the real-valued unit: an arbitrary chosen reference -/

attribute [requirement "R17" specifies "a unit as a chosen reference quantity of a kind, carrying the nonzero-magnitude license"]
  RealUnit
attribute [requirement "R17" proves "measuring and re-applying a real-valued unit is a bijection — the §13.3.3 number-and-reference round-trip over ℝ"]
  RealUnit.ofNumber_measure
attribute [requirement "R17" proves "the two conversion factors between two units of a kind are reciprocal, for an arbitrary chosen reference"]
  RealUnit.ratio_mul_ratio_symm

end PropertyKindCalculus

end -- pkc-blanket-expose
end -- pkc-blanket
