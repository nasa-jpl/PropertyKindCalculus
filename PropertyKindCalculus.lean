/-
# PropertyKindCalculus

A Lean formalization of Dybkær's *Ontology on Property* (2009), extended with
Flater's full tracking of kinds of quantities (NIST TN 1943, Appendix C).

This root module re-exports the Mathlib-free ontological spine. The examples
under `PropertyKindCalculus.Examples` and the later PhysLib-backed dimension/coherence
and soil-moisture model layers are built separately by the lake glob.
-/

import PropertyKindCalculus.Foundations
import PropertyKindCalculus.Scale
import PropertyKindCalculus.Kind
import PropertyKindCalculus.Specialization
import PropertyKindCalculus.Examination
import PropertyKindCalculus.PropertyValue
import PropertyKindCalculus.ValueScale
import PropertyKindCalculus.Unit
import PropertyKindCalculus.UnitPrefix
import PropertyKindCalculus.Extensivity
import PropertyKindCalculus.Quantity
import PropertyKindCalculus.QuantityClassification
import PropertyKindCalculus.QuantityRefinement
import PropertyKindCalculus.QuantityVector
