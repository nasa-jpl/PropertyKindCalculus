import Verso
import VersoManual
import VersoBlueprint
-- The directive that renders the tables.
import PropertyKindCalculusBlueprint.CrossRefTable
-- The typed cross-reference annotations, harvested at elaboration time.
import PropertyKindCalculus.CrossRefs
-- The chapters that define the blueprint nodes the rows link to; importing them
-- here puts those nodes in scope so each declaration resolves to its node label.
import PropertyKindCalculusBlueprint.Chapters.Spine
import PropertyKindCalculusBlueprint.Chapters.DedicatedKind
import PropertyKindCalculusBlueprint.Chapters.Units
import PropertyKindCalculusBlueprint.Chapters.Extensivity
-- Cross-layer targets (quantity dimension, dimension one, quantity calculus, the
-- ISQ, coherent units) live in the Dimension / Interaction / ISO 80000 chapters.
import PropertyKindCalculusBlueprint.Chapters.Dimension
import PropertyKindCalculusBlueprint.Chapters.Interaction
import PropertyKindCalculusBlueprint.Chapters.Iso80000
import PropertyKindCalculusBlueprint.Chapters.Iso80000Part3

open Verso.Genre
open Verso.Genre.Manual
open Informal
open PropertyKindCalculusBlueprint

#doc (Manual) "External Cross-References" =>

This work formalizes Dybkær's *Ontology on Property* and aligns its concepts with
the *International Vocabulary of Metrology* (VIM). The correspondence is recorded
as typed, declaration-indexed metadata — two attributes, `@[dybkaer …]` and
`@[vim4 …]`, attached to the declarations of the core spine — so the two index
tables below are *generated from the source*, not maintained by hand. Each row
maps an external locus to the external term and to this work's declaration, linked
to its definition in this blueprint. Only locators are recorded; no normative text
from either copyrighted source is reproduced.

# Dybkær — *An Ontology on Property*

Indexed by Dybkær section, with the term as printed and this work's corresponding
declaration.

:::crossrefs "dybkaer"
:::

# VIM 4 2CD — *International Vocabulary of Metrology*

Indexed by VIM 4 2CD clause. The 2CD is a restricted committee draft; only clause
numbers and terms are recorded.

The correspondence is mostly with this work's core spine — VIM's _quantity_,
_ratio_/_interval_/_ordinal quantity_, _measurement scale_, _value of a quantity_,
and the _measurement principle/method/procedure_ chain map directly to PKC
declarations. Three VIM concepts reach into the further layers: _quantity
dimension_ (1.9) and _quantity with the unit one_ (1.10) are the `Dimension`
layer's `dim` map and the dimension-one thesis; _quantity calculus_ (1.29) is the
`Interaction` algebra; the _international system of quantities_ (1.8) is the
ISO/IEC 80000 catalogue and the _coherent derived unit_ (1.15) the unit each
catalogued kind carries.

:::crossrefs "vim4"
:::

Many VIM clauses have no PKC counterpart, for two reasons. Some are *metrological-
procedure* concerns outside this ontology's scope — _true value_ (1.26),
_conventional value_ (1.27), _measurement result_ (2.10), _measured value_ (2.11),
_measurement model/function_ (2.12–2.13), _influence quantity_ (2.16),
_correction_ (2.17), and the _metrology_/_measurand_/_primary method_ terms (2.2,
2.3, 2.6, 2.8, 2.9). Others are *not yet formalized*: the _base_/_derived
quantity_ and _base_/_derived_/_off-system unit_ distinctions (1.6, 1.7,
1.13, 1.14, 1.18), _system of quantities_/_of units_ as first-class objects
(1.5, 1.16, 1.17, 1.19), _reference quantity_ (1.11), the _unit_/_numerical-value
equation_ forms (1.31, 1.32), and _conversion factor between units_ (1.22), whose
round-trip is a planned capstone.
