/-
# PropertyKindCalculus

A Lean formalization of Dybkær's *Ontology on Property* (2009), extended with
Flater's full tracking of kinds of quantities (NIST TN 1943, Appendix C).

This root module re-exports the Mathlib-free ontological spine. The examples
under `PropertyKindCalculus.Examples` and the later PhysLib-backed dimension/coherence
layer are built separately by the lake glob. (The soil-moisture retrieval model is a
downstream application kept in a separate repository.)
-/

module

public import PropertyKindCalculus.Foundations
public import PropertyKindCalculus.Mereology
public import PropertyKindCalculus.Scale
public import PropertyKindCalculus.Kind
public import PropertyKindCalculus.DedicatedKind
public import PropertyKindCalculus.Specialization
public import PropertyKindCalculus.Examination
public import PropertyKindCalculus.PropertyValue
public import PropertyKindCalculus.NominalValue
public import PropertyKindCalculus.ValueScale
public import PropertyKindCalculus.Unit
public import PropertyKindCalculus.UnitPrefix
public import PropertyKindCalculus.Extensivity
public import PropertyKindCalculus.Recarving
public import PropertyKindCalculus.InterfaceLedger
public import PropertyKindCalculus.Quantity
public import PropertyKindCalculus.Aggregation
public import PropertyKindCalculus.QuantityClassification
public import PropertyKindCalculus.OperatorTable
public import PropertyKindCalculus.SpecializationLift
public import PropertyKindCalculus.Bounds
public import PropertyKindCalculus.Level
public import PropertyKindCalculus.Axis
public import PropertyKindCalculus.PartWhole
public import PropertyKindCalculus.Decimal
public import PropertyKindCalculus.IndividualQuantity
public import PropertyKindCalculus.Composite
public import PropertyKindCalculus.QuantityFunction
public import PropertyKindCalculus.Measurand
public import PropertyKindCalculus.Complex
public import PropertyKindCalculus.QuantityRefinement
public import PropertyKindCalculus.QuantityVector
public import PropertyKindCalculus.Frame
public import PropertyKindCalculus.Provenance
public import PropertyKindCalculus.Influence

public section -- pkc-blanket
@[expose] section -- pkc-blanket-expose



end -- pkc-blanket-expose
end -- pkc-blanket
