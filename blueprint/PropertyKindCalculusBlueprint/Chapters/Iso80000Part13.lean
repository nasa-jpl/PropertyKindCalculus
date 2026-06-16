import Verso
import VersoManual
import VersoBlueprint
-- The Part-13 nodes link real declarations (the information-science dimensioned kinds, the
-- shannon/erlang/bit incommensurability at dimension one, the T⁻¹ rate collision, and the
-- digital-transmission defining-relation kind-laws), so this chapter imports the Part-13
-- modules of the `Iso80000` library.
import PropertyKindCalculus.Iso80000.Part13
import PropertyKindCalculus.Iso80000.Part13.DefiningRelations

open Verso.Genre
open Verso.Genre.Manual
open Informal

#doc (Manual) "IEC 80000-13 — Information science and technology" =>

The tenth and last part specified is IEC 80000-13, _Information science and technology_ —
the second IEC-published part, after electromagnetism. Every item — all of 13-1 … 13-42,
forty-two in all (the part uses flat item numbers, no sub-suffixes) — is catalogued: the
teletraffic quantities, storage and transfer, the powers and signal energy, and the
coding- and information-theory quantities — each carrying its exact source as data. Only
_citation locators_ are recorded; no normative content from the licensed standard is
reproduced. The defining _mathematics_ of selected remarks is specified in the sibling
module `Part13.DefiningRelations`.

Information science is where the _scale-spanning_ reduction (the _Scale-spanning units_
chapter, requirement _R13_) meets _human-selected counts of information_. Its
characteristic quantities are all _dimension one_ — and yet they carry special, mutually
_incommensurable_ units, and belong to distinct kinds. Information content and entropy are
measured in the _shannon_ (or hartley, or natural unit); traffic intensity in the _erlang_;
storage capacity in the _bit_. All are dimension one; the dimension functor collapses them
to a single point, and only the kind keeps the shannon of information from the erlang of
traffic from the bit of storage. The shannon, erlang, and bit are scale-spanning units in
exactly the sense of the candela and the mole: dimensionless references chosen by people.

# Quantity-kinds and units of IEC 80000-13

:::group "iso80000_part13"
Each catalogued kind reuses the {uses "def_dim"}[dimension functor] `dim` over PhysLib's
`Dimension`, here over mass, length, and time. Almost every quantity is dimension one; the
rates carry `T⁻¹`, the powers `M·L²·T⁻³`, the signal energy `M·L²·T⁻²`. Each unit is a
{uses "def_metrologicalUnit"}[metrological unit] of its kind; commensurability is a
type-level fact, so the shannon of information and the erlang of traffic are not
interchangeable though both are dimension one.
:::

:::definition "def_part13_catalogued_kind" (parent := "iso80000_part13") (lean := "PropertyKindCalculus.Iso80000.Part13.CataloguedKind")
A _catalogued kind_ pairs a dimensioned {uses "def_quantity"}[quantity]-kind with its
exact source in the series — the part, the printed item designation (e.g. "13-24"), the
principal quantity symbol, and the unit symbol (for the information quantities, the special
named unit — shannon, erlang, bit — rather than the bare `1`). The citation travels with
the kind as data.
:::

:::proof "def_part13_catalogued_kind"
Realized as `structure CataloguedKind` over a `DimensionedKind`, with `cite` rendering
e.g. `IEC 80000-13, Edition 2.0, 2025-02 item 13-24`. The `catalogue` lists all 42 items in
item order — the traffic quantities (13-1 … 13-8), storage (13-9, 13-10), the information
content and entropies (13-24 … 13-37), the rates (13-38 … 13-42), … — each paired with its
unit symbol.
:::

# Dimension one, three kind families, incommensurable special units (R13)

IEC 80000-13's characteristic quantities all live at dimension one — and this is exactly the
place the catalogue's thesis turns into a *unit* question. Three families share dimension
one but carry _different special units_, and belong to _different kinds_:

- _Information content and entropy_ (13-24 …) in the _shannon_ `Sh`, _hartley_ `Hart`, or
  _natural unit_ `nat` — alternative units of one kind, related by the logarithm base.
- _Traffic intensity_ (13-1 …) in the _erlang_ `E`.
- _Storage capacity_ (13-9, 13-10) in the _bit_ (or octet, or byte).

A dimension-only model sees one type, "a real number, dimension one", for all of them, and
would let a bit of storage be silently read as an erlang of traffic. The shannon, erlang,
and bit are _scale-spanning_ units (R13), human-selected references for a dimensionless
count — exactly like the candela (ISO 80000-7) and the mole (ISO 80000-9). The kind layer is
what keeps them apart.

:::group "iso80000_part13_units"
The dimension-one collision capstone, on _standard_ quantities: the {uses "def_dim"}[dimension
map] identifies information content, traffic intensity, and storage capacity, while the kind
layer keeps them apart, both as kinds and as {uses "def_metrologicalUnit"}[units] (the
shannon, the erlang, the bit).
:::

:::theorem "thm_part13_units" (parent := "iso80000_part13_units") (lean := "PropertyKindCalculus.Iso80000.Part13.shannon_erlang_not_commensurable") (tags := "capstone, proved") (effort := "small")
*The shannon of information content and the erlang of traffic intensity are not
commensurable, though both are dimension one (items 13-24, 13-1).* Two human-selected
dimensionless references for two different kinds — a bit of information is not an erlang of
traffic. The companion `shannon_bit_not_commensurable` separates information from storage.
This is the scale-spanning collision (R13) on information. Uses {uses "def_metrologicalUnit"}[the
metrological unit].
:::

:::proof "thm_part13_units"
`shannon_erlang_not_commensurable` and `shannon_bit_not_commensurable`, each by `decide`
after unfolding `MetrologicalUnit.Commensurable` on the dimension-one kinds. Axiom-free.
:::

:::theorem "thm_part13_dim_one" (parent := "iso80000_part13_units") (lean := "PropertyKindCalculus.Iso80000.Part13.iec80000_13_dim_one_collision") (tags := "proved") (effort := "small")
*The dimension-1 collision, on the standard.* There exist distinct IEC 80000-13 kinds with
the same dimension one — information content and traffic intensity witness it, alongside
storage capacity, the entropies, and the probabilities. With distinct special units (shannon,
erlang, bit), the dimension cannot separate them; the kind layer does. Uses {uses "def_dim"}[the
dimension map].
:::

:::proof "thm_part13_dim_one"
`iec80000_13_dim_one_collision`, witnessed by `⟨informationContent, trafficIntensity, …⟩`
with the kind distinction a `decide` and reflexivity. Axiom-free.
:::

# The information rates re-dimension to `T⁻¹`

Per-character entropies are dimension one, but the _per-second_ rates re-dimension to `T⁻¹`:
the average information rate, the average transinformation rate, the channel (time) capacity,
the bit and transfer rates, the call intensities. They collide there — distinct kinds, one
dimension — just as the dimension-one quantities collide at the point one.

:::theorem "thm_part13_rates" (parent := "iso80000_part13_units") (lean := "PropertyKindCalculus.Iso80000.Part13.iec80000_13_dim_collision") (tags := "proved") (effort := "small")
*The bit rate is not the call intensity, though both are `T⁻¹` (items 13-13, 13-7).* There
exist distinct IEC 80000-13 kinds with the same dimension `T⁻¹` — the bit rate and the call
intensity witness it, alongside the transfer and modulation rates and the information rates.
Dimension cannot separate them; the kind layer does. Uses {uses "def_dim"}[the dimension
map].
:::

:::proof "thm_part13_rates"
`iec80000_13_dim_collision`, witnessed by `⟨binaryDigitRate, callIntensity, …⟩`. The shared
dimension is `binaryDigitRate_dim_eq_callIntensity_dim`; the kind distinction is a `decide`.
Axiom-free.
:::

# The algebraic Remarks as kind-laws: digital transmission built by the kind algebra

Several Part-13 definitions state a quantity's defining relation _algebraically_. The signal
energy per binary digit is the _product_ of carrier power and the bit period (13-19,
`E_bit = P_c·T_bit`); the periods are _reciprocals_ of the rates (13-12, 13-14). Each is
specified as an R12 kind-law.

:::group "iso80000_part13_relations"
The product and reciprocal families carry the kind-laws. Two payoffs: digital transmission
is built from the kind algebra, and the signal energy per bit is `M·L²·T⁻²` _because_ it is
a power times a time, a checked computation.
:::

:::theorem "thm_part13_relations" (parent := "iso80000_part13_relations") (lean := "PropertyKindCalculus.Iso80000.Part13.DefiningRelations.signalEnergyOf_isProduct") (tags := "proved") (effort := "small")
*Signal energy per bit is carrier power × bit period — a verified construction (item
13-19).* A signal energy built as the product of a carrier power and a bit period carries its
product certificate by construction, over the `ℝ` carrier. The companion
`signalEnergy_dim_from_power_period` shows it is `M·L²·T⁻²` _because_ it is a power times a
time. Uses {uses "def_quotient_kind"}[the quotient kind-law].
:::

:::proof "thm_part13_relations"
`signalEnergyOf p t := Quantity.mul signalEnergy_prod_power_period p t`, and
`signalEnergyOf_isProduct` is `rfl`. The reciprocal kind-laws
`periodOfDataElements_recip_transferRate` and `periodOfBinaryDigits_recip_binaryDigitRate`
give the periods, with `periodOfDataElements_dim_from_transferRate` the dimension. Axiom-free.
:::

# Item index — IEC 80000-13

Every catalogued item of IEC 80000-13, indexed by its printed item number, with the
principal quantity symbol, the unit (the special named unit where the standard gives one),
and the PhysLib dimension this work assigns it. Each item number links to the formalized
result it participates in. Symbols and unit strings are _citation locators_; nothing
normative is reproduced.

:::table +header (align := left)
*
  * Item
  * Quantity
  * Symbol
  * Unit
  * Dimension
*
  * {bpref "thm_part13_units"}[13-1]
  * traffic intensity
  * `A`
  * `E`
  * `1`
*
  * {bpref "thm_part13_dim_one"}[13-2]
  * traffic offered intensity
  * `A_o`
  * `E`
  * `1`
*
  * {bpref "thm_part13_dim_one"}[13-3]
  * traffic carried intensity
  * `Y`
  * `E`
  * `1`
*
  * {bpref "thm_part13_dim_one"}[13-4]
  * mean queue length
  * `L`
  * `1`
  * `1`
*
  * {bpref "thm_part13_dim_one"}[13-5]
  * loss probability
  * `B`
  * `1`
  * `1`
*
  * {bpref "thm_part13_dim_one"}[13-6]
  * waiting probability
  * `W`
  * `1`
  * `1`
*
  * {bpref "thm_part13_rates"}[13-7]
  * call intensity
  * `λ`
  * `s⁻¹`
  * `T⁻¹`
*
  * {bpref "thm_part13_rates"}[13-8]
  * completed call intensity
  * `μ`
  * `s⁻¹`
  * `T⁻¹`
*
  * {bpref "thm_part13_units"}[13-9]
  * storage capacity
  * `M`
  * `bit`
  * `1`
*
  * {bpref "thm_part13_dim_one"}[13-10]
  * equivalent binary storage capacity
  * `M_e`
  * `bit`
  * `1`
*
  * {bpref "thm_part13_rates"}[13-11]
  * transfer rate
  * `r`
  * `s⁻¹`
  * `T⁻¹`
*
  * {bpref "thm_part13_relations"}[13-12]
  * period of data elements
  * `T`
  * `s`
  * `T`
*
  * {bpref "thm_part13_rates"}[13-13]
  * binary digit rate
  * `r_bit`
  * `bit/s`
  * `T⁻¹`
*
  * {bpref "thm_part13_relations"}[13-14]
  * period of binary digits
  * `T_bit`
  * `s`
  * `T`
*
  * {bpref "thm_part13_rates"}[13-15]
  * equivalent binary digit rate
  * `r_e`
  * `bit/s`
  * `T⁻¹`
*
  * {bpref "thm_part13_rates"}[13-16]
  * modulation rate
  * `r_m`
  * `Bd`
  * `T⁻¹`
*
  * {bpref "def_part13_catalogued_kind"}[13-17]
  * quantizing distortion
  * `T_Q`
  * `W`
  * `M·L²·T⁻³`
*
  * {bpref "thm_part13_relations"}[13-18]
  * carrier power
  * `P_c`
  * `W`
  * `M·L²·T⁻³`
*
  * {bpref "thm_part13_relations"}[13-19]
  * signal energy per binary digit
  * `E_bit`
  * `J`
  * `M·L²·T⁻²`
*
  * {bpref "thm_part13_dim_one"}[13-20]
  * error probability
  * `P`
  * `1`
  * `1`
*
  * {bpref "thm_part13_dim_one"}[13-21]
  * Hamming distance
  * `d_n`
  * `1`
  * `1`
*
  * {bpref "thm_part13_rates"}[13-22]
  * clock frequency
  * `f_cl`
  * `Hz`
  * `T⁻¹`
*
  * {bpref "thm_part13_dim_one"}[13-23]
  * decision content
  * `D_a`
  * `1`
  * `1`
*
  * {bpref "thm_part13_units"}[13-24]
  * information content
  * `I(x)`
  * `Sh`
  * `1`
*
  * {bpref "thm_part13_units"}[13-25]
  * entropy
  * `H`
  * `Sh`
  * `1`
*
  * {bpref "thm_part13_dim_one"}[13-26]
  * maximum entropy
  * `H_0`
  * `Sh`
  * `1`
*
  * {bpref "thm_part13_dim_one"}[13-27]
  * relative entropy
  * `H_r`
  * `1`
  * `1`
*
  * {bpref "thm_part13_dim_one"}[13-28]
  * redundancy
  * `R`
  * `Sh`
  * `1`
*
  * {bpref "thm_part13_dim_one"}[13-29]
  * relative redundancy
  * `r`
  * `1`
  * `1`
*
  * {bpref "thm_part13_dim_one"}[13-30]
  * joint information content
  * `I(x,y)`
  * `Sh`
  * `1`
*
  * {bpref "thm_part13_dim_one"}[13-31]
  * conditional information content
  * `I(x|y)`
  * `Sh`
  * `1`
*
  * {bpref "thm_part13_dim_one"}[13-32]
  * conditional entropy
  * `H(X|Y)`
  * `Sh`
  * `1`
*
  * {bpref "thm_part13_dim_one"}[13-33]
  * equivocation
  * `H_x(X|Y)`
  * `Sh`
  * `1`
*
  * {bpref "thm_part13_dim_one"}[13-34]
  * irrelevance
  * `H_y(Y|X)`
  * `Sh`
  * `1`
*
  * {bpref "thm_part13_dim_one"}[13-35]
  * transinformation content
  * `T(x,y)`
  * `Sh`
  * `1`
*
  * {bpref "thm_part13_dim_one"}[13-36]
  * mean transinformation content
  * `T`
  * `Sh`
  * `1`
*
  * {bpref "thm_part13_dim_one"}[13-37]
  * character mean entropy
  * `H′`
  * `Sh`
  * `1`
*
  * {bpref "thm_part13_rates"}[13-38]
  * average information rate
  * `H*`
  * `Sh/s`
  * `T⁻¹`
*
  * {bpref "thm_part13_dim_one"}[13-39]
  * character mean transinformation content
  * `T′`
  * `Sh`
  * `1`
*
  * {bpref "thm_part13_rates"}[13-40]
  * average transinformation rate
  * `T*`
  * `Sh/s`
  * `T⁻¹`
*
  * {bpref "thm_part13_dim_one"}[13-41]
  * channel capacity per character
  * `C′`
  * `Sh`
  * `1`
*
  * {bpref "thm_part13_rates"}[13-42]
  * channel time capacity
  * `C*`
  * `Sh/s`
  * `T⁻¹`
:::
