/-
# Requirement annotations on the rendering layer — applied from afar

Attaches the `@[requirement …]` traceability attribute to the `DocGenMath`
declarations that discharge R25 (rendering ergonomics): a kinded definition renders
back as typeset mathematics from its own elaborated source, with the kind
bookkeeping suppressed. R25 was minted from the ForPhysLib benchmark's MR12 — the
requirement the benchmark scored ✅ for PKC and that the catalogue had nowhere to
record; see the blueprint's *Requirement validation* section.

A separate module (rather than a section of `Annotations`) because it is the one
place the Requirements library reaches into the `DocGenMath` library — the same
isolation discipline `DimensionAnnotations` and `UncertaintyAnnotations` follow for
their layers. `DocGenMath` depends only on the core spine and core `Lean`, so this
module stays Mathlib-free. The worked example's `exemplifies` annotation lives in
`ExampleAnnotations`, which already imports the `Examples` library that carries it.
-/

module

public import PropertyKindCalculus.DocGenMath
meta import PropertyKindCalculus.DocGenMath
public import PropertyKindCalculus.Requirements.Attributes
meta import PropertyKindCalculus.Requirements.Attributes

public section -- pkc-blanket
@[expose] section -- pkc-blanket-expose

namespace PropertyKindCalculus.DocGenMath

/-! ## Rendering ergonomics (R25) -/

attribute [requirement "R25" specifies "the presentation term language the elaborated definition is lifted into"]
  MathTerm
attribute [requirement "R25" implements "precedence-aware pretty-printing of a lifted definition to a LaTeX equation"]
  prettyEquation
attribute [requirement "R25" implements "the harvest of every @[pkc_math]-rendered declaration, for the index page"]
  pkcMathUses

end PropertyKindCalculus.DocGenMath

end -- pkc-blanket-expose
end -- pkc-blanket
