import Illuminate

/-!
# Lowe's ontological square, drawn

The four-category ontology of E. J. Lowe, *The Four-Category Ontology: A Metaphysical
Foundation for Natural Science* (Oxford University Press, 2005), Fig. 7.1: four corners,
numbered as Lowe numbers them, joined by two *characterized by* edges, two *instantiated
by* edges, and the *exemplified by* diagonal. Each corner carries Lowe's term above and
the calculus's own reading of that corner below.

The geometry is placed by hand rather than by the `CommDiag` grid combinator, whose cells
take a fixed 60-unit envelope and so overlap for labels of this width. Coordinates are
y-up (the SVG backend flips them); the lines are drawn in segments, leaving a gap for each
edge label exactly as the source figure does.
-/

open Illuminate

namespace PropertyKindCalculusBlueprint

/-- Lowe's own term for a corner. -/
private def loweStyle : TextStyle := { fontSize := 15, bold := true }

/-- The calculus's reading of that corner, set below Lowe's term. -/
private def readingStyle : TextStyle :=
  { fontSize := 13, italic := true, color := ⟨82, 82, 96, 1.0⟩ }

/-- An edge label, sitting in a gap in its edge. -/
private def edgeStyle : TextStyle := { fontSize := 12 }

private def rule : Stroke := { width := 1.1 }

private def say (s : String) (st : TextStyle) (x y : Float) : Diagram SVG :=
  Diagram.transform (Matrix.translate x y) (Diagram.text s st)

private def seg (x₁ y₁ x₂ y₂ : Float) : Diagram SVG :=
  Diagram.fromStroke (PathData.line ⟨x₁, y₁⟩ ⟨x₂, y₂⟩) rule

/-- A corner: Lowe's term, with the calculus's reading of it underneath. -/
private def corner (x y : Float) (lowe reading : String) : Diagram SVG :=
  Diagram.atop (say lowe loweStyle x (y + 9)) (say reading readingStyle x (y - 9))

/--
Lowe's ontological square with the calculus's vocabulary at each corner.
-/
def ontologicalSquare : Diagram SVG :=
  Diagram.pad 14 <| List.foldl Diagram.atop Diagram.empty [
    -- corners
    corner 0 130 "(3) Kinds" "sorts of system",
    corner 400 130 "(4) Attributes" "kinds-of-property",
    corner 0 0 "(1) Substances" "systems",
    corner 400 0 "(2) Modes" "individual quantities",
    -- top edge: kinds are characterized by attributes
    seg 59 130 148 130, seg 252 130 329 130,
    say "characterized by" edgeStyle 200 130,
    -- bottom edge: substances are characterized by modes
    seg 71 0 148 0, seg 252 0 322 0,
    say "characterized by" edgeStyle 200 0,
    -- left edge: kinds are instantiated by substances
    seg 0 104 0 75, seg 0 55 0 26,
    say "instantiated by" edgeStyle 0 65,
    -- right edge: attributes are instantiated by modes
    seg 400 104 400 75, seg 400 55 400 26,
    say "instantiated by" edgeStyle 400 65,
    -- the diagonal: attributes are exemplified by substances
    seg 335.3 109.0 249.5 81.1, seg 150.5 48.9 64.7 21.0,
    say "exemplified by" edgeStyle 200 65
  ]

end PropertyKindCalculusBlueprint
