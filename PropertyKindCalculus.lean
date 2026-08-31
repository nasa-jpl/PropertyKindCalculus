/-
# PropertyKindCalculus

A Lean formalization of Dybkær's *Ontology on Property* (2009), extended with
Flater's full tracking of kinds of quantities (NIST TN 1943, Appendix C).

This root module re-exports the Mathlib-free ontological spine. The examples
under `PropertyKindCalculus.Examples` and the later PhysLib-backed dimension/coherence
layer are built separately by the lake glob. (The soil-moisture retrieval model is a
downstream application kept in a separate repository.)
-/

import PropertyKindCalculus.Foundations
import PropertyKindCalculus.Scale
import PropertyKindCalculus.Kind
import PropertyKindCalculus.DedicatedKind
import PropertyKindCalculus.Specialization
import PropertyKindCalculus.Examination
import PropertyKindCalculus.PropertyValue
import PropertyKindCalculus.NominalValue
import PropertyKindCalculus.ValueScale
import PropertyKindCalculus.Unit
import PropertyKindCalculus.UnitPrefix
import PropertyKindCalculus.Extensivity
import PropertyKindCalculus.Quantity
import PropertyKindCalculus.QuantityClassification
import PropertyKindCalculus.OperatorTable
import PropertyKindCalculus.Bounds
import PropertyKindCalculus.Axis
import PropertyKindCalculus.PartWhole
import PropertyKindCalculus.Decimal
import PropertyKindCalculus.IndividualQuantity
import PropertyKindCalculus.QuantityFunction
import PropertyKindCalculus.Complex
import PropertyKindCalculus.QuantityRefinement
import PropertyKindCalculus.QuantityVector
import PropertyKindCalculus.Frame
import PropertyKindCalculus.Provenance
import PropertyKindCalculus.Influence
