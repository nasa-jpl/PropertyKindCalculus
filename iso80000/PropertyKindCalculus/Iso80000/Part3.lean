/-
# ISO 80000-3 — Space and time (the full catalogue)

The complete set of quantity-kinds (QK) and their coherent SI units (U) for
ISO 80000-3 *Space and time* — all of items 3-1.1 … 3-26.3 — each carrying its
exact source as data: the part (`iso80000_3`), the printed item designation, the
principal quantity symbol, and the coherent SI unit symbol. Only **citation
locators** are recorded (item number, symbol, coherent SI unit); no normative
content (definitions, remarks) from the licensed standard is reproduced. The
defining *mathematics* of selected remarks is formalized in the sibling modules
`Part3.AreaElement`, `Part3.VolumeElement`, and `Part3.DefiningRelations`.

Three things this catalogue makes structural rather than prose:

* **The length family is a specialization lattice (requirement R2), realized on the
  real standard.** ISO 80000-3 lists width, height, thickness, diameter, radius,
  path length, distance, … as separate items, all of dimension `L` and all
  ratio-scale — distinguished in the standard only by their *prose definitions*.
  Here each is a {kind} that {specializes} the general length kind (item 3-1.1) and
  is individuated **not by fiat** but by an explicit {examination principle}
  (Dybkær §7.5): `width ≠ distance` is proved from their differing measurement
  principles, while both remain *mutually comparable* as lengths. The
  specialization edges mirror the standard's own "defined in terms of" links
  (a diameter is a width of a circle; a radius is half a diameter; a distance is a
  shortest path length; …).

* **Dimension does not classify; the kind does.** Part 3 alone is dense with
  *dimension collisions*: plane angle, solid angle, rotation, and the logarithmic
  decrement are all dimension one; frequency, rotational frequency, angular
  frequency, angular velocity, and the damping coefficient are all `T⁻¹`; velocity
  and speed are both `L·T⁻¹`. The {dimension functor} `dim` cannot separate them —
  the kind layer does. This is the dimension-1 disambiguation capstone, here on
  standard quantities.

* **The dimensional facts are checked computations**, not annotations: area is `L²`,
  volume is `L³`, curvature is `L⁻¹`, frequency is `T⁻¹`, all discharged in
  PhysLib's dimension group.
-/

module

public import PropertyKindCalculus.Dimension
public import PropertyKindCalculus.Iso80000.References
public import PropertyKindCalculus.Iso80000.Catalogue
-- Private scope only: the checks below reduce through bodies sealed in the core
-- library; `import all` gives this file the reduction without exposing them.
import all PropertyKindCalculus.UnitPrefix

public section -- pkc-blanket
@[expose] section -- pkc-blanket-expose

namespace PropertyKindCalculus.Iso80000.Part3

open PropertyKindCalculus

/-- The part of the series this module catalogues. -/
def source : StandardRef := iso80000_3

/-- Build a catalogued kind from this part, given its locators and dimensioned kind. -/
def cat (item symbol coherentUnit : String) (qk : DimensionedKind) :
    CataloguedKind :=
  CataloguedKind.of source item symbol coherentUnit qk

/-! ## (A) The length family — a specialization lattice individuated by measurement
principle (items 3-1.1 … 3-1.12, and 3-19)

Item 3-1.1, *length*, is the broad genus: a ratio-scale kind of dimension `L` with
no distinguishing examination principle. Items 3-1.2 … 3-1.12 (and the wavelength,
3-19, "the length of the repetition interval") are *species* of length — same
dimension, same scale — individuated by an explicit examination principle. This is
the standards-grounded realization of requirement **R2**. -/

/-! ### Examination principles for the length species

The examination principles (Dybkær §7.5) that individuate the length species. Each
`id` is this work's own terse descriptor of the *measurement principle* that
distinguishes the species — not the standard's normative definition. -/

namespace LengthPrinciple
/-- Width — transverse extent. -/
def transverse : ExaminationPrinciple := { id := "transverse-extent" }
/-- Height — vertical extent. -/
def vertical : ExaminationPrinciple := { id := "vertical-extent" }
/-- Thickness — through-extent (a width in the depth direction). -/
def through : ExaminationPrinciple := { id := "through-extent" }
/-- Diameter — the width across a circle, cylinder, or sphere. -/
def acrossCircle : ExaminationPrinciple := { id := "across-circle" }
/-- Radius — centre to rim. -/
def centreToRim : ExaminationPrinciple := { id := "centre-to-rim" }
/-- Path length — measured along a rectifiable curve. -/
def alongCurve : ExaminationPrinciple := { id := "along-curve" }
/-- Distance — the shortest path length between two points. -/
def shortestPath : ExaminationPrinciple := { id := "shortest-path" }
/-- Radial distance — from a designated reference point. -/
def fromReferencePoint : ExaminationPrinciple := { id := "from-reference-point" }
/-- Position vector — from the chosen origin. -/
def fromOrigin : ExaminationPrinciple := { id := "from-origin" }
/-- Displacement — between two points (a free vector). -/
def betweenPoints : ExaminationPrinciple := { id := "between-points" }
/-- Radius of curvature — the radius of the osculating circle. -/
def osculating : ExaminationPrinciple := { id := "osculating-circle" }
/-- Wavelength — the length of the repetition interval. -/
def repetitionInterval : ExaminationPrinciple := { id := "repetition-interval" }
end LengthPrinciple

/-- A length species: dimension `L`, ratio-scale, individuated by its measurement
(examination) principle. -/
def lengthSpecies (id : String) (p : ExaminationPrinciple) : DimensionedKind :=
  { kind := { id := id, scale := .ratio, examPrinciple := some p.id }, dim := Dim.length }

/-- Length — item 3-1.1, dimension `L`. The broad genus of the length family. -/
def length : DimensionedKind :=
  { kind := { id := "length", scale := .ratio }, dim := Dim.length }

/-- Width (breadth) — item 3-1.2, a length species (transverse extent). -/
def width : DimensionedKind := lengthSpecies "width" LengthPrinciple.transverse
/-- Height (depth, altitude) — item 3-1.3, a length species (vertical extent). -/
def height : DimensionedKind := lengthSpecies "height" LengthPrinciple.vertical
/-- Thickness — item 3-1.4, a length species (through-extent). -/
def thickness : DimensionedKind := lengthSpecies "thickness" LengthPrinciple.through
/-- Diameter — item 3-1.5, a length species (width across a circle). -/
def diameter : DimensionedKind := lengthSpecies "diameter" LengthPrinciple.acrossCircle
/-- Radius — item 3-1.6, a length species (centre to rim). -/
def radius : DimensionedKind := lengthSpecies "radius" LengthPrinciple.centreToRim
/-- Path length (arc length) — item 3-1.7, a length species (along a curve). -/
def pathLength : DimensionedKind := lengthSpecies "path length" LengthPrinciple.alongCurve
/-- Distance — item 3-1.8, a length species (shortest path length). -/
def distance : DimensionedKind := lengthSpecies "distance" LengthPrinciple.shortestPath
/-- Radial distance — item 3-1.9, a length species (from a reference point). -/
def radialDistance : DimensionedKind :=
  lengthSpecies "radial distance" LengthPrinciple.fromReferencePoint
/-- Position vector — item 3-1.10, a **vector** length quantity (from the origin). -/
def positionVector : DimensionedKind :=
  lengthSpecies "position vector" LengthPrinciple.fromOrigin
/-- Displacement — item 3-1.11, a **vector** length quantity (between two points).
Its vector-ness lives in the numeric carrier of a `Quantity displacement.kind
(Fin 3 → R)` under one scalar unit (ISO 80000-2 §18). -/
def displacement : DimensionedKind :=
  lengthSpecies "displacement" LengthPrinciple.betweenPoints
/-- Radius of curvature — item 3-1.12, a length species (osculating-circle radius). -/
def radiusOfCurvature : DimensionedKind :=
  lengthSpecies "radius of curvature" LengthPrinciple.osculating
/-- Wavelength — item 3-19, a length species (the repetition interval). -/
def wavelength : DimensionedKind :=
  lengthSpecies "wavelength" LengthPrinciple.repetitionInterval

/-! ## (B) Curvature and the spatial-frequency family (dimension `L⁻¹`) -/

/-- Curvature — item 3-2, dimension `L⁻¹` (the inverse of the radius of curvature). -/
def curvature : DimensionedKind := dimKind "curvature" Dim.length⁻¹
/-- Repetency (wavenumber) — item 3-20, dimension `L⁻¹` (inverse of the wavelength). -/
def repetency : DimensionedKind := dimKind "repetency" Dim.length⁻¹
/-- Wave vector — item 3-21, dimension `L⁻¹` (a vector quantity). -/
def waveVector : DimensionedKind := dimKind "wave vector" Dim.length⁻¹
/-- Angular repetency (angular wavenumber) — item 3-22, dimension `L⁻¹`. -/
def angularRepetency : DimensionedKind := dimKind "angular repetency" Dim.length⁻¹
/-- Attenuation (extinction) — item 3-26.1, dimension `L⁻¹`. -/
def attenuation : DimensionedKind := dimKind "attenuation" Dim.length⁻¹
/-- Phase coefficient — item 3-26.2, dimension `L⁻¹`. -/
def phaseCoefficient : DimensionedKind := dimKind "phase coefficient" Dim.length⁻¹
/-- Propagation coefficient — item 3-26.3, dimension `L⁻¹`. -/
def propagationCoefficient : DimensionedKind :=
  dimKind "propagation coefficient" Dim.length⁻¹

/-! ## (C) Area and volume (dimensions `L²`, `L³`) -/

/-- Area — item 3-3, dimension `L²`. The surface-element remark is formalized in
`Part3.AreaElement`. -/
def area : DimensionedKind := dimKind "area" Dim.area
/-- Volume — item 3-4, dimension `L³`. The volume-element remark is formalized in
`Part3.VolumeElement`. -/
def volume : DimensionedKind := dimKind "volume" (Dim.area * Dim.length)

/-! ## (D) The dimensionless angular quantities (dimension one)

Plane angle, rotational displacement, phase angle, solid angle, rotation, and the
logarithmic decrement are *all* dimension one — yet distinct kinds, measured in
distinct units (rad, sr, 1). This is the dimension-1 disambiguation, on standard
quantities. -/

/-- Plane angle (angular measure) — item 3-5, dimension one, unit rad. The
arc/radius remark is formalized in `Part3.DefiningRelations`. -/
def planeAngle : DimensionedKind := dimKind "plane angle" Dim.one
/-- Rotational (angular) displacement — item 3-6, dimension one, unit rad. -/
def rotationalDisplacement : DimensionedKind :=
  dimKind "rotational displacement" Dim.one
/-- Phase angle — item 3-7, dimension one, unit rad. -/
def phaseAngle : DimensionedKind := dimKind "phase angle" Dim.one
/-- Solid angle (solid angular measure) — item 3-8, dimension one, unit sr. -/
def solidAngle : DimensionedKind := dimKind "solid angle" Dim.one
/-- Rotation — item 3-16, dimension one (a number of revolutions). -/
def rotation : DimensionedKind := dimKind "rotation" Dim.one
/-- Logarithmic decrement — item 3-25, dimension one. -/
def logarithmicDecrement : DimensionedKind := dimKind "logarithmic decrement" Dim.one

/-! ## (E) The time family (dimension `T`) -/

/-- Duration (time) — item 3-9, dimension `T`. -/
def duration : DimensionedKind := dimKind "duration" Dim.time
/-- Period duration (period) — item 3-14, dimension `T`. -/
def periodDuration : DimensionedKind := dimKind "period duration" Dim.time
/-- Time constant — item 3-15, dimension `T`. -/
def timeConstant : DimensionedKind := dimKind "time constant" Dim.time

/-! ## (F) The temporal-frequency family (dimension `T⁻¹`)

Frequency, rotational frequency, angular frequency, angular velocity, and the
damping coefficient are *all* dimension `T⁻¹` — distinct kinds in distinct units
(Hz, s⁻¹, rad/s). ISO 80000-3 is explicit that hertz is reserved for frequency and
rad/s for angular frequency though they are dimensionally identical; the kind layer
makes that distinction structural. -/

/-- Frequency — item 3-17.1, dimension `T⁻¹`, unit Hz. The `f = 1/T` remark is
formalized in `Part3.DefiningRelations`. -/
def frequency : DimensionedKind := dimKind "frequency" Dim.time⁻¹
/-- Rotational frequency — item 3-17.2, dimension `T⁻¹`, unit s⁻¹. -/
def rotationalFrequency : DimensionedKind := dimKind "rotational frequency" Dim.time⁻¹
/-- Angular frequency — item 3-18, dimension `T⁻¹`, unit rad/s. -/
def angularFrequency : DimensionedKind := dimKind "angular frequency" Dim.time⁻¹
/-- Angular velocity — item 3-12, dimension `T⁻¹`, unit rad/s (a vector quantity). -/
def angularVelocity : DimensionedKind := dimKind "angular velocity" Dim.time⁻¹
/-- Damping coefficient — item 3-24, dimension `T⁻¹`, unit s⁻¹. -/
def dampingCoefficient : DimensionedKind := dimKind "damping coefficient" Dim.time⁻¹

/-! ## (G) The velocity/speed family (dimension `L·T⁻¹`)

Velocity and speed share the dimension `L·T⁻¹`; velocity is the vector, speed its
magnitude — distinct kinds, same dimension, same unit (m/s). -/

/-- Velocity — item 3-10.1, dimension `L·T⁻¹` (a vector quantity). -/
def velocity : DimensionedKind := dimKind "velocity" Dim.speed
/-- Speed — item 3-10.2, dimension `L·T⁻¹`. The `v = ds/dt` remark is formalized
(as `speed = path length / duration`) in `Part3.DefiningRelations`. -/
def speed : DimensionedKind := dimKind "speed" Dim.speed
/-- Phase velocity (phase speed) — item 3-23.1, dimension `L·T⁻¹`. -/
def phaseVelocity : DimensionedKind := dimKind "phase velocity" Dim.speed
/-- Group velocity (group speed) — item 3-23.2, dimension `L·T⁻¹`. -/
def groupVelocity : DimensionedKind := dimKind "group velocity" Dim.speed

/-! ## (H) The acceleration family (dimensions `L·T⁻²`, `T⁻²`) -/

/-- Acceleration — item 3-11, dimension `L·T⁻²` (a vector quantity). -/
def acceleration : DimensionedKind :=
  dimKind "acceleration" (Dim.length / (Dim.time * Dim.time))
/-- Angular acceleration — item 3-13, dimension `T⁻²`, unit rad/s². -/
def angularAcceleration : DimensionedKind :=
  dimKind "angular acceleration" (Dim.time * Dim.time)⁻¹

/-! ## The catalogue (every kind, with its source as data) -/

/-- The length-family catalogued kinds (items 3-1.1 … 3-1.12). -/
def lengthCK : CataloguedKind := cat "3-1.1" "l" "m" length
def widthCK : CataloguedKind := cat "3-1.2" "b" "m" width
def heightCK : CataloguedKind := cat "3-1.3" "h" "m" height
def thicknessCK : CataloguedKind := cat "3-1.4" "d" "m" thickness
def diameterCK : CataloguedKind := cat "3-1.5" "d" "m" diameter
def radiusCK : CataloguedKind := cat "3-1.6" "r" "m" radius
def pathLengthCK : CataloguedKind := cat "3-1.7" "s" "m" pathLength
def distanceCK : CataloguedKind := cat "3-1.8" "d" "m" distance
def radialDistanceCK : CataloguedKind := cat "3-1.9" "r_Q" "m" radialDistance
def positionVectorCK : CataloguedKind := cat "3-1.10" "r" "m" positionVector
def displacementCK : CataloguedKind := cat "3-1.11" "Δr" "m" displacement
def radiusOfCurvatureCK : CataloguedKind := cat "3-1.12" "ρ" "m" radiusOfCurvature

/-- The `L⁻¹` family. -/
def curvatureCK : CataloguedKind := cat "3-2" "κ" "m⁻¹" curvature
def repetencyCK : CataloguedKind := cat "3-20" "σ" "m⁻¹" repetency
def waveVectorCK : CataloguedKind := cat "3-21" "k" "m⁻¹" waveVector
def angularRepetencyCK : CataloguedKind := cat "3-22" "k" "m⁻¹" angularRepetency
def attenuationCK : CataloguedKind := cat "3-26.1" "α" "m⁻¹" attenuation
def phaseCoefficientCK : CataloguedKind := cat "3-26.2" "β" "rad/m" phaseCoefficient
def propagationCoefficientCK : CataloguedKind :=
  cat "3-26.3" "γ" "m⁻¹" propagationCoefficient

/-- Area, volume. -/
def areaCK : CataloguedKind := cat "3-3" "A" "m²" area
def volumeCK : CataloguedKind := cat "3-4" "V" "m³" volume

/-- The dimensionless angular quantities. -/
def planeAngleCK : CataloguedKind := cat "3-5" "α" "rad" planeAngle
def rotationalDisplacementCK : CataloguedKind := cat "3-6" "φ" "rad" rotationalDisplacement
def phaseAngleCK : CataloguedKind := cat "3-7" "φ" "rad" phaseAngle
def solidAngleCK : CataloguedKind := cat "3-8" "Ω" "sr" solidAngle
def rotationCK : CataloguedKind := cat "3-16" "N" "1" rotation
def logarithmicDecrementCK : CataloguedKind := cat "3-25" "Λ" "1" logarithmicDecrement

/-- The time family. -/
def durationCK : CataloguedKind := cat "3-9" "t" "s" duration
def periodDurationCK : CataloguedKind := cat "3-14" "T" "s" periodDuration
def timeConstantCK : CataloguedKind := cat "3-15" "τ" "s" timeConstant

/-- The `T⁻¹` family. -/
def frequencyCK : CataloguedKind := cat "3-17.1" "f" "Hz" frequency
def rotationalFrequencyCK : CataloguedKind := cat "3-17.2" "n" "s⁻¹" rotationalFrequency
def angularFrequencyCK : CataloguedKind := cat "3-18" "ω" "rad/s" angularFrequency
def angularVelocityCK : CataloguedKind := cat "3-12" "ω" "rad/s" angularVelocity
def dampingCoefficientCK : CataloguedKind := cat "3-24" "δ" "s⁻¹" dampingCoefficient

/-- The velocity/speed family. -/
def velocityCK : CataloguedKind := cat "3-10.1" "v" "m/s" velocity
def speedCK : CataloguedKind := cat "3-10.2" "v" "m/s" speed
def phaseVelocityCK : CataloguedKind := cat "3-23.1" "c" "m/s" phaseVelocity
def groupVelocityCK : CataloguedKind := cat "3-23.2" "c_g" "m/s" groupVelocity

/-- The acceleration family, and the wavelength. -/
def accelerationCK : CataloguedKind := cat "3-11" "a" "m/s²" acceleration
def angularAccelerationCK : CataloguedKind := cat "3-13" "α" "rad/s²" angularAcceleration
def wavelengthCK : CataloguedKind := cat "3-19" "λ" "m" wavelength

/-- The full ISO 80000-3 catalogue, in item order. -/
def catalogue : List CataloguedKind :=
  [lengthCK, widthCK, heightCK, thicknessCK, diameterCK, radiusCK, pathLengthCK,
   distanceCK, radialDistanceCK, positionVectorCK, displacementCK, radiusOfCurvatureCK,
   curvatureCK, areaCK, volumeCK, planeAngleCK, rotationalDisplacementCK, phaseAngleCK,
   solidAngleCK, durationCK, velocityCK, speedCK, accelerationCK, angularVelocityCK,
   angularAccelerationCK, periodDurationCK, timeConstantCK, rotationCK, frequencyCK,
   rotationalFrequencyCK, angularFrequencyCK, wavelengthCK, repetencyCK, waveVectorCK,
   angularRepetencyCK, phaseVelocityCK, groupVelocityCK, dampingCoefficientCK,
   logarithmicDecrementCK, attenuationCK, phaseCoefficientCK, propagationCoefficientCK]

/-! ## (I) Units — a few coherent SI units of these kinds

Each unit references its kind, so a metre and a second are not commensurable; a
radian and a steradian are not commensurable *though both are dimension one*; and a
hertz and a radian-per-second are not commensurable *though both are `T⁻¹`* — all
type-level facts, not runtime checks. -/

/-- The metre, the SI unit of length (item 3-1.1). -/
def metre : MetrologicalUnit := length.kind.unit "m"
/-- The centimetre as a **prefixed unit** (VIM4 §1.21): the `centi` submultiple of
the metre. Its symbol `"cm"` and conversion factor (`10⁻²`) follow from the prefix
and the base. -/
def centimetrePrefixed : PrefixedUnit := metre.withPrefix SIPrefix.centi
/-- The centimetre, the projection of `centimetrePrefixed` to a plain unit. -/
def centimetre : MetrologicalUnit := centimetrePrefixed.toUnit
/-- The second, the SI unit of duration (item 3-9). -/
def second : MetrologicalUnit := duration.kind.unit "s"
/-- The square metre, the SI unit of area (item 3-3). -/
def squareMetre : MetrologicalUnit := area.kind.unit "m²"
/-- The cubic metre, the SI unit of volume (item 3-4). -/
def cubicMetre : MetrologicalUnit := volume.kind.unit "m³"
/-- The radian, the SI unit of plane angle (item 3-5) — dimension one. -/
def radian : MetrologicalUnit := planeAngle.kind.unit "rad"
/-- The steradian, the SI unit of solid angle (item 3-8) — dimension one. -/
def steradian : MetrologicalUnit := solidAngle.kind.unit "sr"
/-- The hertz, the SI unit of frequency (item 3-17.1) — dimension `T⁻¹`. -/
def hertz : MetrologicalUnit := frequency.kind.unit "Hz"
/-- The radian per second, the SI unit of angular frequency (item 3-18) — also `T⁻¹`. -/
def radianPerSecond : MetrologicalUnit := angularFrequency.kind.unit "rad/s"
/-- The metre per second, the SI unit of speed (item 3-10.2). -/
def metrePerSecond : MetrologicalUnit := speed.kind.unit "m/s"

/-! ## (J) Checked dimensional facts (the dimensional algebra) -/

/-- Length carries the length dimension `L`. -/
theorem length_dim : length.dim = Dim.length := rfl

/-- Area is `L²`: its length-exponent is `2` (ISO 80000-3 item 3-3). -/
theorem area_dim_length : area.dim.length = 2 := Dim.area_length

/-- Volume is `L³`: its length-exponent is `3` (ISO 80000-3 item 3-4). -/
theorem volume_dim_length : volume.dim.length = 3 := by
  norm_num [volume, dimKind, Dim.area, Dim.length, Dimension.length_mul, Dimension.L𝓭_length]

/-- Curvature is `L⁻¹`: its length-exponent is `-1` (ISO 80000-3 item 3-2). -/
theorem curvature_dim_length : curvature.dim.length = -1 := by
  simp [curvature, dimKind, Dim.length, Dimension.inv_length, Dimension.L𝓭_length]

/-- Speed is length over time (`L·T⁻¹`), ISO 80000-3 item 3-10.2. -/
theorem speed_dim : speed.dim = Dim.length / Dim.time := Dim.speed_eq

/-- Frequency is `T⁻¹`: its time-exponent is `-1` (ISO 80000-3 item 3-17.1). -/
theorem frequency_dim_time : frequency.dim.time = -1 := by
  simp [frequency, dimKind, Dim.time, Dimension.inv_time, Dimension.T𝓭_time]

/-- Acceleration is `L·T⁻²`: its time-exponent is `-2` (ISO 80000-3 item 3-11). -/
theorem acceleration_dim_time : acceleration.dim.time = -2 := by
  norm_num [acceleration, dimKind, Dim.length, Dim.time, Dimension.div_time,
    Dimension.time_mul, Dimension.L𝓭_time, Dimension.T𝓭_time]

/-! ## (K) Unit well-formedness and (in)commensurability -/

/-- The metre is a well-formed unit (length is ratio-scale, so it bears a unit). -/
theorem metre_wellFormed : metre.WellFormed := KindOfProperty.rational_bears_unit rfl

/-- The metre and the centimetre are commensurable — both reference `length`. -/
theorem metre_centimetre_commensurable : metre.Commensurable centimetre :=
  centimetrePrefixed.commensurable_base

/-- The centimetre's symbol is `"cm"` — composed from the prefix symbol and the base. -/
theorem centimetre_symbol : centimetre.symbol = "cm" := rfl

/-- The centimetre is a submultiple of the metre with conversion factor `10⁻²`. -/
theorem centimetre_conversionExponent : centimetrePrefixed.conversionExponent = -2 := rfl

/-- The centimetre is a decimal *submultiple* of the metre (VIM4 §1.21). -/
theorem centimetre_isSubmultiple : centimetrePrefixed.IsSubmultiple := by
  unfold PrefixedUnit.IsSubmultiple; decide

/-- The centimetre is itself a well-formed metrological unit. -/
theorem centimetre_wellFormed : centimetre.WellFormed :=
  centimetrePrefixed.toUnit_wellFormed metre_wellFormed

/-- The square metre is a well-formed unit of area. -/
theorem squareMetre_wellFormed : squareMetre.WellFormed :=
  KindOfProperty.rational_bears_unit rfl

/-- The metre and the second are **not** commensurable — length and duration are
distinct kinds (a type-level fact). -/
theorem metre_second_not_commensurable : ¬ metre.Commensurable second := by
  unfold MetrologicalUnit.Commensurable metre second length duration KindOfProperty.unit
  decide

/-- The radian and the steradian are **not** commensurable — plane angle and solid
angle are distinct kinds, *though both are dimension one*. The kind separates units
the dimension cannot. -/
theorem radian_steradian_not_commensurable : ¬ radian.Commensurable steradian := by
  unfold MetrologicalUnit.Commensurable radian steradian planeAngle solidAngle dimKind
    KindOfProperty.unit
  decide

/-- The hertz and the radian-per-second are **not** commensurable — frequency and
angular frequency are distinct kinds, *though both are `T⁻¹`*. -/
theorem hertz_radianPerSecond_not_commensurable :
    ¬ hertz.Commensurable radianPerSecond := by
  unfold MetrologicalUnit.Commensurable hertz radianPerSecond frequency angularFrequency
    dimKind KindOfProperty.unit
  decide

/-! ## (L) The length family as a specialization lattice (requirement R2)

The direct-parent edges of the length family, mirroring the standard's own
"defined in terms of" links: a thickness and a diameter are kinds of width, a radius
is a kind of diameter, a distance is a kind of path length, and so on — all rooted at
the general length kind (3-1.1). Specialization is the reflexive-transitive closure
of these edges; it is a preorder, so a radius specializes length transitively. -/

/-- This application's system of length quantities — the direct-parent edges among
the kinds of the length family (3-1). -/
inductive Edge : KindOfProperty → KindOfProperty → Prop
  /-- Width is a kind of length. -/
  | width_length : Edge width.kind length.kind
  /-- Height is a kind of length. -/
  | height_length : Edge height.kind length.kind
  /-- Thickness is a kind of width (item 3-1.4 is defined via width). -/
  | thickness_width : Edge thickness.kind width.kind
  /-- A diameter is a width across a circle (item 3-1.5 via width). -/
  | diameter_width : Edge diameter.kind width.kind
  /-- A radius is half a diameter (item 3-1.6 via diameter). -/
  | radius_diameter : Edge radius.kind diameter.kind
  /-- Path length is a kind of length. -/
  | pathLength_length : Edge pathLength.kind length.kind
  /-- A distance is a shortest path length (item 3-1.8 via path length). -/
  | distance_pathLength : Edge distance.kind pathLength.kind
  /-- A radial distance is a distance (item 3-1.9 via distance). -/
  | radialDistance_distance : Edge radialDistance.kind distance.kind
  /-- A radius of curvature is a radius (item 3-1.12 via radius). -/
  | radiusOfCurvature_radius : Edge radiusOfCurvature.kind radius.kind
  /-- A position vector is a length quantity from the origin (item 3-1.10). -/
  | positionVector_length : Edge positionVector.kind length.kind
  /-- A displacement is a length quantity between points (item 3-1.11). -/
  | displacement_length : Edge displacement.kind length.kind
  /-- A wavelength is the length of the repetition interval (item 3-19). -/
  | wavelength_length : Edge wavelength.kind length.kind

/-- Width specializes length. -/
theorem width_specializes_length : Specializes Edge width.kind length.kind :=
  Specializes.of_edge Edge.width_length

/-- A **radius specializes length transitively** (radius ⊑ diameter ⊑ width ⊑ length)
— specialization is a preorder, not just the direct edges. -/
theorem radius_specializes_length : Specializes Edge radius.kind length.kind :=
  Specializes.trans (Specializes.of_edge Edge.radius_diameter)
    (Specializes.trans (Specializes.of_edge Edge.diameter_width)
      (Specializes.of_edge Edge.width_length))

/-- Each length species is **examined by** its declared measurement principle: the
examination layer links back to the kind (Dybkær §7.5). -/
theorem width_examinedBy : width.kind.examinedBy LengthPrinciple.transverse := rfl

/-- **Distinction not by fiat but by measurement principle.** Width and distance are
distinct kinds *because they are examined by different principles* (transverse extent
vs shortest path), not merely because their `id` strings differ — this is the
user-facing point of `distinct_of_examPrinciple` applied to the standard. -/
theorem width_ne_distance : width.kind ≠ distance.kind :=
  KindOfProperty.distinct_of_examPrinciple (by decide)

/-- Width and height are distinct kinds, again by their differing examination
principles. -/
theorem width_ne_height : width.kind ≠ height.kind :=
  KindOfProperty.distinct_of_examPrinciple (by decide)

/-- A length species is distinct from the general length kind: a species carries an
examination principle, the genus carries none. -/
theorem width_ne_length : width.kind ≠ length.kind :=
  KindOfProperty.distinct_of_examPrinciple (by decide)

/-- **Mutual comparability is preserved.** Width and distance, though distinct kinds,
remain *mutually comparable* — they share the super-kind length, so combining them is
possible but only via an explicit up-cast, never silently. -/
theorem width_distance_comparable : MutuallyComparable Edge width.kind distance.kind :=
  ⟨length.kind, Specializes.of_edge Edge.width_length,
    Specializes.trans (Specializes.of_edge Edge.distance_pathLength)
      (Specializes.of_edge Edge.pathLength_length)⟩

/-! ## (M) Dimension collisions — the kind classifies where the dimension cannot

Same-dimension/distinct-kind pairs drawn from the catalogue above. The {dimension
functor} `dim` identifies the members of each pair; the kind layer keeps them
apart. -/

/-- Width and distance share the length dimension `L`. -/
theorem width_dim_eq_distance_dim : width.dim = distance.dim := rfl

/-- Plane angle and solid angle share dimension one. -/
theorem planeAngle_dim_eq_solidAngle_dim : planeAngle.dim = solidAngle.dim := rfl

/-- Plane angle and solid angle are distinct kinds. -/
theorem planeAngle_ne_solidAngle : planeAngle.kind ≠ solidAngle.kind := by
  unfold planeAngle solidAngle dimKind; decide

/-- Frequency and angular frequency share dimension `T⁻¹`. -/
theorem frequency_dim_eq_angularFrequency_dim :
    frequency.dim = angularFrequency.dim := rfl

/-- Frequency and angular frequency are distinct kinds. -/
theorem frequency_ne_angularFrequency : frequency.kind ≠ angularFrequency.kind := by
  unfold frequency angularFrequency dimKind; decide

/-- Velocity and speed share dimension `L·T⁻¹`. -/
theorem velocity_dim_eq_speed_dim : velocity.dim = speed.dim := rfl

/-- Velocity and speed are distinct kinds (the vector and its magnitude). -/
theorem velocity_ne_speed : velocity.kind ≠ speed.kind := by
  unfold velocity speed dimKind; decide

/-- **The dimension-1 disambiguation, on standard quantities.** There exist distinct
ISO 80000-3 kinds with the same dimension one — plane angle and solid angle witness
it. PhysLib's `Dimension`, and any dimension-only type system, cannot separate them;
the kind layer does. (Generalizes `Dimension.dim_not_injective` to the standard.) -/
theorem iso80000_3_dim_one_collision :
    ∃ a b : DimensionedKind, a.kind ≠ b.kind ∧ a.dim = b.dim ∧ a.dim = 1 :=
  ⟨planeAngle, solidAngle, planeAngle_ne_solidAngle,
    planeAngle_dim_eq_solidAngle_dim, rfl⟩

/-- **A dimensionful collision.** Distinct ISO 80000-3 kinds also share *dimensionful*
dimensions — frequency and angular frequency are both `T⁻¹`. Dimension is not a
classifier even away from dimension one. -/
theorem iso80000_3_dim_collision :
    ∃ a b : DimensionedKind, a.kind ≠ b.kind ∧ a.dim = b.dim :=
  ⟨frequency, angularFrequency, frequency_ne_angularFrequency,
    frequency_dim_eq_angularFrequency_dim⟩

end PropertyKindCalculus.Iso80000.Part3

end -- pkc-blanket-expose
end -- pkc-blanket
