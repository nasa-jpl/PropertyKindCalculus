/-
# IEC 80000-13 — Information science and technology (the full catalogue)

The complete set of quantity-kinds (QK) and their units (U) for IEC 80000-13 *Information
science and technology* — all of items 13-1 … 13-42, forty-two in all (the part uses flat
item numbers, with no sub-suffixes) — each carrying its exact source as data: the part
(`iec80000_13`), the printed item designation, the principal quantity symbol, and the
unit symbol. Only **citation locators** are recorded; no normative content from the licensed
standard is reproduced. The defining *mathematics* of selected remarks is formalized in the
sibling module `Part13.DefiningRelations`.

Information science is the second IEC-published part (after electromagnetism), and the place
where the Finkelstein–Whitehead *scale-spanning* reduction (Eur. J. Phys. 46 (2025) 035701;
see `ScaleSpanning`, requirement **R13**) meets *human-selected counts of information*. Its
characteristic quantities are all **dimension one** — yet they carry special, mutually
*incommensurable* units, and belong to distinct kinds:

* **Dimension one, three kind families, incommensurable special units.** Information content
  and entropy (13-24 …) are measured in the *shannon* `Sh`, the *hartley* `Hart`, or the
  *natural unit* `nat` — alternative units of one kind, related by the logarithm base (2, 10,
  e). Traffic intensity (13-1 …) is measured in the *erlang* `E`. Storage capacity (13-9,
  13-10) in the *bit* (or octet/byte). All are dimension one; the {dimension functor}
  collapses them to a single point, and the kind layer keeps the shannon of information from
  the erlang of traffic from the bit of storage.

* **The shannon, erlang, and bit are scale-spanning units (R13).** Like the candela
  (ISO 80000-7) and the mole (ISO 80000-9), they are *human-selected* references for a
  dimensionless count, not base dimensions. A bit of storage and a shannon of information
  are both "dimension one", yet not interchangeable.

* **The information rates re-dimension to `T⁻¹`.** Per-character entropies are dimension one,
  but the per-second rates — the average information rate, the average transinformation
  rate, the channel (time) capacity, the bit and transfer rates — carry `T⁻¹`.

* **The dimensional facts are checked computations**, discharged in PhysLib's dimension
  group over mass, length, and time.
-/

module

public import PropertyKindCalculus.Dimension
public import PropertyKindCalculus.ScaleSpanning
public import PropertyKindCalculus.Iso80000.References
public import PropertyKindCalculus.Iso80000.Catalogue

@[expose] public section Blanket

namespace PropertyKindCalculus.Iso80000.Part13

open PropertyKindCalculus

/-- The part of the series this module catalogues. -/
def source : StandardRef := iec80000_13

/-- Build a catalogued kind from this part, given its locators and dimensioned kind. -/
def cat (item symbol coherentUnit : String) (qk : DimensionedKind) :
    CataloguedKind :=
  CataloguedKind.of source item symbol coherentUnit qk

/-! ## Information-science dimensions

Almost every quantity is dimension one; the rates carry `T⁻¹`, the periods `T`, the powers
`M·L²·T⁻³`, and the signal energy `M·L²·T⁻²`. -/

namespace IDim

/-- Per time, `T⁻¹` (`s⁻¹`, `bit/s`, `Bd`, `Sh/s`) — the call, bit, transfer, modulation,
and information rates. -/
def perTime : Dimension LTMCTDimensionBase := Dim.time⁻¹

end IDim

/-! ## (A) Teletraffic engineering (items 13-1 … 13-8)

Traffic intensity and its variants (13-1 … 13-3) are dimension one, measured in the
*erlang*; the queue length and probabilities (13-4 … 13-6) are dimension one; the call
intensities (13-7, 13-8) are `T⁻¹`. -/

def trafficIntensity : DimensionedKind := dimKind "traffic intensity" Dim.one
def trafficOfferedIntensity : DimensionedKind :=
  dimKind "traffic offered intensity" Dim.one
def trafficCarriedIntensity : DimensionedKind :=
  dimKind "traffic carried intensity" Dim.one
def meanQueueLength : DimensionedKind := dimKind "mean queue length" Dim.one
def lossProbability : DimensionedKind := dimKind "loss probability" Dim.one
def waitingProbability : DimensionedKind := dimKind "waiting probability" Dim.one
def callIntensity : DimensionedKind := dimKind "call intensity" IDim.perTime
def completedCallIntensity : DimensionedKind :=
  dimKind "completed call intensity" IDim.perTime

/-! ## (B) Storage and transfer (items 13-9 … 13-19)

Storage capacity (13-9, 13-10) is dimension one, measured in the *bit*; the rates (13-11,
13-13, 13-15, 13-16) are `T⁻¹`; the periods (13-12, 13-14) are `T`; the powers (13-17,
13-18) are `M·L²·T⁻³`; the signal energy per bit (13-19) is `M·L²·T⁻²`. -/

def storageCapacity : DimensionedKind := dimKind "storage capacity" Dim.one
def equivalentBinaryStorageCapacity : DimensionedKind :=
  dimKind "equivalent binary storage capacity" Dim.one
def transferRate : DimensionedKind := dimKind "transfer rate" IDim.perTime
def periodOfDataElements : DimensionedKind :=
  dimKind "period of data elements" Dim.time
def binaryDigitRate : DimensionedKind := dimKind "binary digit rate" IDim.perTime
def periodOfBinaryDigits : DimensionedKind :=
  dimKind "period of binary digits" Dim.time
def equivalentBinaryDigitRate : DimensionedKind :=
  dimKind "equivalent binary digit rate" IDim.perTime
def modulationRate : DimensionedKind := dimKind "modulation rate" IDim.perTime
def quantizingDistortion : DimensionedKind := dimKind "quantizing distortion" Dim.power
def carrierPower : DimensionedKind := dimKind "carrier power" Dim.power
def signalEnergyPerBinaryDigit : DimensionedKind :=
  dimKind "signal energy per binary digit" Dim.energy

/-! ## (C) Coding and information theory (items 13-20 … 13-37)

The error probability, Hamming distance, decision content (13-20 … 13-23) are dimension
one; the information-theoretic quantities (13-24 … 13-37, 13-39, 13-41) are dimension one,
measured in the *shannon*, *hartley*, or *natural unit*. -/

def errorProbability : DimensionedKind := dimKind "error probability" Dim.one
def hammingDistance : DimensionedKind := dimKind "Hamming distance" Dim.one
def clockFrequency : DimensionedKind := dimKind "clock frequency" IDim.perTime
def decisionContent : DimensionedKind := dimKind "decision content" Dim.one
def informationContent : DimensionedKind := dimKind "information content" Dim.one
def entropy : DimensionedKind := dimKind "entropy" Dim.one
def maximumEntropy : DimensionedKind := dimKind "maximum entropy" Dim.one
def relativeEntropy : DimensionedKind := dimKind "relative entropy" Dim.one
def redundancy : DimensionedKind := dimKind "redundancy" Dim.one
def relativeRedundancy : DimensionedKind := dimKind "relative redundancy" Dim.one
def jointInformationContent : DimensionedKind :=
  dimKind "joint information content" Dim.one
def conditionalInformationContent : DimensionedKind :=
  dimKind "conditional information content" Dim.one
def conditionalEntropy : DimensionedKind := dimKind "conditional entropy" Dim.one
def equivocation : DimensionedKind := dimKind "equivocation" Dim.one
def irrelevance : DimensionedKind := dimKind "irrelevance" Dim.one
def transinformationContent : DimensionedKind :=
  dimKind "transinformation content" Dim.one
def meanTransinformationContent : DimensionedKind :=
  dimKind "mean transinformation content" Dim.one
def characterMeanEntropy : DimensionedKind := dimKind "character mean entropy" Dim.one

/-! ## (D) Rates and channel capacity (items 13-38 … 13-42)

The per-character quantities (13-39, 13-41) are dimension one; the per-second rates (13-38,
13-40, 13-42) re-dimension to `T⁻¹`, measured in the *shannon per second*. -/

def averageInformationRate : DimensionedKind :=
  dimKind "average information rate" IDim.perTime
def characterMeanTransinformationContent : DimensionedKind :=
  dimKind "character mean transinformation content" Dim.one
def averageTransinformationRate : DimensionedKind :=
  dimKind "average transinformation rate" IDim.perTime
def channelCapacityPerCharacter : DimensionedKind :=
  dimKind "channel capacity per character" Dim.one
def channelTimeCapacity : DimensionedKind := dimKind "channel time capacity" IDim.perTime

/-! ## The catalogue (every kind, with its source as data) -/

def trafficIntensityCK : CataloguedKind := cat "13-1" "A" "E" trafficIntensity
def trafficOfferedIntensityCK : CataloguedKind :=
  cat "13-2" "A_o" "E" trafficOfferedIntensity
def trafficCarriedIntensityCK : CataloguedKind :=
  cat "13-3" "Y" "E" trafficCarriedIntensity
def meanQueueLengthCK : CataloguedKind := cat "13-4" "L" "1" meanQueueLength
def lossProbabilityCK : CataloguedKind := cat "13-5" "B" "1" lossProbability
def waitingProbabilityCK : CataloguedKind := cat "13-6" "W" "1" waitingProbability
def callIntensityCK : CataloguedKind := cat "13-7" "λ" "s⁻¹" callIntensity
def completedCallIntensityCK : CataloguedKind :=
  cat "13-8" "μ" "s⁻¹" completedCallIntensity
def storageCapacityCK : CataloguedKind := cat "13-9" "M" "bit" storageCapacity
def equivalentBinaryStorageCapacityCK : CataloguedKind :=
  cat "13-10" "M_e" "bit" equivalentBinaryStorageCapacity
def transferRateCK : CataloguedKind := cat "13-11" "r" "s⁻¹" transferRate
def periodOfDataElementsCK : CataloguedKind := cat "13-12" "T" "s" periodOfDataElements
def binaryDigitRateCK : CataloguedKind := cat "13-13" "r_bit" "bit/s" binaryDigitRate
def periodOfBinaryDigitsCK : CataloguedKind :=
  cat "13-14" "T_bit" "s" periodOfBinaryDigits
def equivalentBinaryDigitRateCK : CataloguedKind :=
  cat "13-15" "r_e" "bit/s" equivalentBinaryDigitRate
def modulationRateCK : CataloguedKind := cat "13-16" "r_m" "Bd" modulationRate
def quantizingDistortionCK : CataloguedKind := cat "13-17" "T_Q" "W" quantizingDistortion
def carrierPowerCK : CataloguedKind := cat "13-18" "P_c" "W" carrierPower
def signalEnergyPerBinaryDigitCK : CataloguedKind :=
  cat "13-19" "E_bit" "J" signalEnergyPerBinaryDigit
def errorProbabilityCK : CataloguedKind := cat "13-20" "P" "1" errorProbability
def hammingDistanceCK : CataloguedKind := cat "13-21" "d_n" "1" hammingDistance
def clockFrequencyCK : CataloguedKind := cat "13-22" "f_cl" "Hz" clockFrequency
def decisionContentCK : CataloguedKind := cat "13-23" "D_a" "1" decisionContent
def informationContentCK : CataloguedKind := cat "13-24" "I(x)" "Sh" informationContent
def entropyCK : CataloguedKind := cat "13-25" "H" "Sh" entropy
def maximumEntropyCK : CataloguedKind := cat "13-26" "H_0" "Sh" maximumEntropy
def relativeEntropyCK : CataloguedKind := cat "13-27" "H_r" "1" relativeEntropy
def redundancyCK : CataloguedKind := cat "13-28" "R" "Sh" redundancy
def relativeRedundancyCK : CataloguedKind := cat "13-29" "r" "1" relativeRedundancy
def jointInformationContentCK : CataloguedKind :=
  cat "13-30" "I(x,y)" "Sh" jointInformationContent
def conditionalInformationContentCK : CataloguedKind :=
  cat "13-31" "I(x|y)" "Sh" conditionalInformationContent
def conditionalEntropyCK : CataloguedKind := cat "13-32" "H(X|Y)" "Sh" conditionalEntropy
def equivocationCK : CataloguedKind := cat "13-33" "H_x(X|Y)" "Sh" equivocation
def irrelevanceCK : CataloguedKind := cat "13-34" "H_y(Y|X)" "Sh" irrelevance
def transinformationContentCK : CataloguedKind :=
  cat "13-35" "T(x,y)" "Sh" transinformationContent
def meanTransinformationContentCK : CataloguedKind :=
  cat "13-36" "T" "Sh" meanTransinformationContent
def characterMeanEntropyCK : CataloguedKind := cat "13-37" "H′" "Sh" characterMeanEntropy
def averageInformationRateCK : CataloguedKind :=
  cat "13-38" "H*" "Sh/s" averageInformationRate
def characterMeanTransinformationContentCK : CataloguedKind :=
  cat "13-39" "T′" "Sh" characterMeanTransinformationContent
def averageTransinformationRateCK : CataloguedKind :=
  cat "13-40" "T*" "Sh/s" averageTransinformationRate
def channelCapacityPerCharacterCK : CataloguedKind :=
  cat "13-41" "C′" "Sh" channelCapacityPerCharacter
def channelTimeCapacityCK : CataloguedKind := cat "13-42" "C*" "Sh/s" channelTimeCapacity

/-- The full IEC 80000-13 catalogue, in item order. -/
def catalogue : List CataloguedKind :=
  [trafficIntensityCK, trafficOfferedIntensityCK, trafficCarriedIntensityCK,
   meanQueueLengthCK, lossProbabilityCK, waitingProbabilityCK, callIntensityCK,
   completedCallIntensityCK, storageCapacityCK, equivalentBinaryStorageCapacityCK,
   transferRateCK, periodOfDataElementsCK, binaryDigitRateCK, periodOfBinaryDigitsCK,
   equivalentBinaryDigitRateCK, modulationRateCK, quantizingDistortionCK, carrierPowerCK,
   signalEnergyPerBinaryDigitCK, errorProbabilityCK, hammingDistanceCK, clockFrequencyCK,
   decisionContentCK, informationContentCK, entropyCK, maximumEntropyCK, relativeEntropyCK,
   redundancyCK, relativeRedundancyCK, jointInformationContentCK,
   conditionalInformationContentCK, conditionalEntropyCK, equivocationCK, irrelevanceCK,
   transinformationContentCK, meanTransinformationContentCK, characterMeanEntropyCK,
   averageInformationRateCK, characterMeanTransinformationContentCK,
   averageTransinformationRateCK, channelCapacityPerCharacterCK, channelTimeCapacityCK]

/-! ## (E) Units — the shannon, the erlang, the bit

All three are units of *dimension-one* quantities, yet of different kinds, and so are not
commensurable: the shannon of information content, the erlang of traffic intensity, and the
bit of storage capacity. This is the scale-spanning collision (R13) on information: three
human-selected dimensionless references, kept apart by kind. -/

/-- The shannon of information content (item 13-24). -/
def shannon : MetrologicalUnit := informationContent.kind.unit "Sh"
/-- The erlang of traffic intensity (item 13-1) — *also* dimension one. -/
def erlang : MetrologicalUnit := trafficIntensity.kind.unit "E"
/-- The bit of storage capacity (item 13-9) — *also* dimension one. -/
def bit : MetrologicalUnit := storageCapacity.kind.unit "bit"

/-! ## (F) Checked dimensional facts (the dimensional algebra) -/

/-- Information content is dimension one (item 13-24). -/
theorem informationContent_dim_eq_one : informationContent.dim = 1 := rfl

/-- The binary digit rate is `T⁻¹` — its time-exponent is `-1` (item 13-13). -/
theorem binaryDigitRate_dim_time : binaryDigitRate.dim.time = -1 := by
  norm_num [binaryDigitRate, dimKind, IDim.perTime, Dim.time, Dimension.inv_time,
    Dimension.T𝓭_time]

/-- The carrier power is `M·L²·T⁻³` — its time-exponent is `-3` (item 13-18). -/
theorem carrierPower_dim_time : carrierPower.dim.time = -3 := Dim.power_time

/-- The signal energy per binary digit is `M·L²·T⁻²` — its time-exponent is `-2` (item
13-19). -/
theorem signalEnergyPerBinaryDigit_dim_time : signalEnergyPerBinaryDigit.dim.time = -2 :=
  Dim.energy_time

/-! ## (G) Unit well-formedness and (in)commensurability -/

/-- The shannon of information content is a well-formed unit. -/
theorem shannon_wellFormed : shannon.WellFormed := KindOfProperty.rational_bears_unit rfl

/-- The erlang of traffic intensity is a well-formed unit. -/
theorem erlang_wellFormed : erlang.WellFormed := KindOfProperty.rational_bears_unit rfl

/-- **The shannon of information content and the erlang of traffic intensity are not
commensurable, though both are dimension one.** Two human-selected dimensionless references
for two different kinds — a bit of information is not an erlang of traffic. The
scale-spanning collision (R13) on information. -/
theorem shannon_erlang_not_commensurable : ¬ shannon.Commensurable erlang := by
  unfold MetrologicalUnit.Commensurable shannon erlang informationContent trafficIntensity
    dimKind KindOfProperty.unit
  decide

/-- **The shannon of information and the bit of storage are not commensurable, though both
are dimension one.** Information content and storage capacity are distinct kinds. -/
theorem shannon_bit_not_commensurable : ¬ shannon.Commensurable bit := by
  unfold MetrologicalUnit.Commensurable shannon bit informationContent storageCapacity
    dimKind KindOfProperty.unit
  decide

/-! ## (H) Dimension collisions — the kind classifies where the dimension cannot

The whole part lives at dimension one (the information quantities) and `T⁻¹` (the rates).
The information content, traffic intensity, and storage capacity all collide on dimension
one with distinct special units; the bit rate and the call intensity collide on `T⁻¹`. -/

/-- Information content and traffic intensity share dimension one. -/
theorem informationContent_dim_eq_trafficIntensity_dim :
    informationContent.dim = trafficIntensity.dim := rfl

/-- The binary digit rate and the call intensity share dimension `T⁻¹`. -/
theorem binaryDigitRate_dim_eq_callIntensity_dim :
    binaryDigitRate.dim = callIntensity.dim := rfl

/-- Information content is not traffic intensity, though both are dimension one. -/
theorem informationContent_ne_trafficIntensity :
    informationContent.kind ≠ trafficIntensity.kind := by
  unfold informationContent trafficIntensity dimKind; decide

/-- The binary digit rate is not the call intensity, though both are `T⁻¹`. -/
theorem binaryDigitRate_ne_callIntensity :
    binaryDigitRate.kind ≠ callIntensity.kind := by
  unfold binaryDigitRate callIntensity dimKind; decide

/-- **The dimension-one collision capstone, on the standard.** There exist distinct
IEC 80000-13 kinds with the same dimension one — information content and traffic intensity
witness it, alongside storage capacity, the entropies, and the probabilities. With distinct
special units (shannon, erlang, bit), the {dimension functor} cannot separate them; the
kind layer does. -/
theorem iec80000_13_dim_one_collision :
    ∃ a b : DimensionedKind, a.kind ≠ b.kind ∧ a.dim = b.dim ∧ a.dim = 1 :=
  ⟨informationContent, trafficIntensity, informationContent_ne_trafficIntensity, rfl, rfl⟩

/-- **The `T⁻¹` collision, on the standard.** There exist distinct IEC 80000-13 kinds with
the same dimension `T⁻¹` — the binary digit rate and the call intensity witness it, alongside
the transfer and modulation rates and the information rates. Dimension cannot separate them;
the kind layer does. -/
theorem iec80000_13_dim_collision :
    ∃ a b : DimensionedKind, a.kind ≠ b.kind ∧ a.dim = b.dim :=
  ⟨binaryDigitRate, callIntensity, binaryDigitRate_ne_callIntensity,
    binaryDigitRate_dim_eq_callIntensity_dim⟩

end PropertyKindCalculus.Iso80000.Part13

end Blanket
