module

public import Tools.Figures.Fmt

/-! The three layers and their two ladders (`make-three-layers-pkc.py`, line for line). -/

namespace Tools.Figures.ThreeLayers

def RED := "#E4002B"
def BLACK := "#000000"
def GRAY5 := "#767676"
def GRAY2 := "#C8C8C8"
def FAINT := "#F3F3F3"
def SANS := "Helvetica Neue, Helvetica, Arial, sans-serif"
def MONO := "SF Mono, Menlo, Consolas, monospace"
def W : Float := 960.0
def H : Float := 700.0
/-- `(top, bottom, margin name, subtitle for the notes column)`. -/
def BANDS : List (Float × Float × String × String) :=
  [(28.0, 196.0, "DIMENSION", "dimension layer — what the laws must satisfy"),
   (204.0, 388.0, "PROVENANCE", "provenance layer — what the source declares"),
   (396.0, 664.0, "COMPUTATION", "computation layer — what the code computes")]
def BAND_X0 : Float := 46.0
def NOTE_X : Float := 656.0
def LEAD : Float := 15.0
def P : String → Float × Float
  | "a" => (120.0, 262.0) | "b" => (170.0, 318.0) | "c" => (350.0, 288.0)
  | "e" => (400.0, 348.0) | _ => (560.0, 314.0)
def OCC : List (String × Float × Float) := [("product", 250.0, 288.0), ("additive", 478.0, 314.0)]
def OCC_HW : Float := 40.0
def DY_DIM : Float := -170.0
def DIMS : String → String
  | "a" => "L" | "b" => "T⁻¹" | _ => "L·T⁻¹"
def RULES : String → String
  | "product" => "add exponents" | _ => "same dimension"
def KINDS : String → String
  | "a" => "k₁" | "b" => "k₂" | _ => "k₃"
def TIERS : String → Option String
  | "a" => some "ingest" | "b" => some "ingest" | "e" => some "const" | _ => none
def T : List (String × Float × Float) :=
  [("a.re", 120.0, 440.0), ("a.im", 120.0, 470.0), ("b.re", 120.0, 510.0), ("b.im", 120.0, 540.0),
   ("ac", 215.0, 440.0), ("bd", 215.0, 470.0), ("ad", 215.0, 510.0), ("bc", 215.0, 540.0),
   ("c.re", 310.0, 455.0), ("c.im", 310.0, 525.0),
   ("e.re", 340.0, 590.0), ("e.im", 340.0, 620.0),
   ("y.re", 430.0, 490.0), ("y.im", 430.0, 566.0)]
def tpos (n : String) : Float × Float :=
  match T.find? (·.1 == n) with | some (_, x, y) => (x, y) | none => (0, 0)
def LEAVES : List String := ["a.re", "a.im", "b.re", "b.im", "e.re", "e.im"]
def INTERIOR : List String := ["ac", "bd", "ad", "bc"]
def ROOTS : List String := ["y.re", "y.im"]
def OPS : String → String
  | "ac" | "bd" | "ad" | "bc" => "×" | "c.re" => "−" | _ => "+"
def TAPE_EDGES : List (String × String) :=
  [("a.re", "ac"), ("b.re", "ac"), ("a.im", "bd"), ("b.im", "bd"),
   ("a.re", "ad"), ("b.im", "ad"), ("a.im", "bc"), ("b.re", "bc"),
   ("ac", "c.re"), ("bd", "c.re"), ("ad", "c.im"), ("bc", "c.im"),
   ("c.re", "y.re"), ("e.re", "y.re"), ("c.im", "y.im"), ("e.im", "y.im")]
def R_PAIRS : List (String × String) :=
  [("a", "a.re"), ("a", "a.im"), ("b", "b.re"), ("b", "b.im"), ("c", "c.re"), ("c", "c.im"),
   ("e", "e.re"), ("e", "e.im"), ("y", "y.re"), ("y", "y.im")]
def REALIZATIONS : List (String × Float × Float × Float × Float) :=
  [("product", 188.0, 422.0, 344.0, 556.0), ("additive", 404.0, 470.0, 458.0, 588.0)]

def f0 := fmtFixed 0
def f1 := fmtFixed 1

def txt (x y : Float) (s : String) (size : Float := 12.0) (fill := BLACK) (anchor := "start")
    (family : Option String := none) (weight : Option String := none)
    (style : Option String := none) (rotate : Option Float := none) (raw := false) : String :=
  s!"<text x=\"{f1 x}\" y=\"{f1 y}\" font-size=\"{f1 size}\" fill=\"{fill}\"" ++
    (if anchor != "start" then s!" text-anchor=\"{anchor}\"" else "") ++
    (family.map (s!" font-family=\"{·}\"")).getD "" ++
    (weight.map (s!" font-weight=\"{·}\"")).getD "" ++
    (style.map (s!" font-style=\"{·}\"")).getD "" ++
    (rotate.map fun r => s!" transform=\"rotate({f0 r} {f1 x} {f1 y})\"").getD "" ++
    ">" ++ (if raw then s else escape s) ++ "</text>"

def line (x1 y1 x2 y2 : Float) (stroke := BLACK) (w : Float := 1.4) (dash : Option String := none)
    (marker : Option String := none) : String :=
  s!"<line x1=\"{f1 x1}\" y1=\"{f1 y1}\" x2=\"{f1 x2}\" y2=\"{f1 y2}\" stroke=\"{stroke}\" stroke-width=\"{f1 w}\"" ++
    (dash.map (s!" stroke-dasharray=\"{·}\"")).getD "" ++
    (marker.map (s!" marker-end=\"url(#layers-{·})\"")).getD "" ++ "/>"

def circle (x y r : Float) (fill := BLACK) (stroke := BLACK) (w : Float := 1.4) : String :=
  s!"<circle cx=\"{f1 x}\" cy=\"{f1 y}\" r=\"{f1 r}\" fill=\"{fill}\" stroke=\"{stroke}\" stroke-width=\"{f1 w}\"/>"

def rrect (x0 y0 x1 y1 : Float) (fill := "none") (stroke := BLACK) (w : Float := 1.4)
    (dash : Option String := none) (r : Float := 6.0) : String :=
  s!"<rect x=\"{f1 x0}\" y=\"{f1 y0}\" width=\"{f1 (x1 - x0)}\" height=\"{f1 (y1 - y0)}\" rx=\"{f1 r}\" fill=\"{fill}\" stroke=\"{stroke}\" stroke-width=\"{f1 w}\"" ++
    (dash.map (s!" stroke-dasharray=\"{·}\"")).getD "" ++ "/>"

/-- A block of prose, one `<text>` per line; `!` leads a bold line, `#` the band's subtitle. -/
def wrap (x y : Float) (lines : List String) (size : Float := 11.5) (lead : Float := LEAD)
    (fill := BLACK) : String :=
  String.join <| lines.zipIdx.map fun (s, i) =>
    let yi := y + Float.ofNat i * lead
    if s.startsWith "#" then txt x yi (s.drop 1).toString (size := size) (fill := BLACK) (weight := "700")
    else if s.startsWith "!" then txt x yi (s.drop 1).toString (size := size) (fill := fill) (weight := "700")
    else txt x yi s (size := size) (fill := fill)

def defs : String :=
  "<defs>" ++
  "<marker id=\"layers-arrow\" viewBox=\"0 0 10 10\" refX=\"9\" refY=\"5\" markerWidth=\"7\" " ++
  "markerHeight=\"7\" orient=\"auto-start-reverse\">" ++
  s!"<path d=\"M 0 0 L 10 5 L 0 10 z\" fill=\"{GRAY5}\"/></marker>" ++
  "</defs>"

def bands : String :=
  String.join <| BANDS.zipIdx.map fun ((t, b, name, _), i) =>
    rrect BAND_X0 t (W - 14) b (fill := if i == 1 then FAINT else "none") (stroke := GRAY2) (w := 1.0) (r := 8) ++
    txt 30 ((t + b) / 2) name (size := 11.0) (fill := GRAY5) (weight := "700") (anchor := "middle") (rotate := some (-90))

def pillHw (s : String) : Float := 8.0 + 4.4 * Float.ofNat s.length

/-- A hyperedge as a small box; operands enter from the left, the result leaves right. -/
def hyperedge (name : String) (cx cy : Float) (operands : List String) (result : String)
    (dy : Float := 0.0) (label : Option String := none) (mono := true)
    (portHw : String → Float := fun _ => 13.0) : String :=
  let hw := OCC_HW; let hh : Float := 12.0
  rrect (cx - hw) (cy - hh + dy) (cx + hw) (cy + hh + dy) (stroke := BLACK) (w := 1.2) (r := 4) ++
  txt cx (cy + 4 + dy) (label.getD name) (size := 10.5) (anchor := "middle") (family := if mono then some MONO else none) ++
  String.join (operands.map fun op =>
    let (x, y) := P op
    line (x + portHw op) (y + dy) (cx - hw) (cy + dy) (w := 1.2)) ++
  (let (x, y) := P result
   line (cx + hw) (cy + dy) (x - portHw result) (y + dy) (w := 1.2))

def kindedNode (name : String) : String :=
  let (x, y) := P name
  circle x y 12.0 ++
  txt x (y + 4.5) name (size := 12.0) (fill := "#FFFFFF") (anchor := "middle") (family := MONO) (weight := "700") ++
  txt x (y - 17) (KINDS name) (size := 10.5) (anchor := "middle") (family := MONO) (fill := GRAY5) ++
  ((TIERS name).map fun t => txt x (y + 26) t (size := 9.5) (anchor := "middle") (fill := GRAY5) (style := "italic")).getD ""

def dimNode (name : String) : String :=
  let (x, y) := P name
  let y := y + DY_DIM
  let s := DIMS name
  let hw := pillHw s
  rrect (x - hw) (y - 11) (x + hw) (y + 11) (stroke := GRAY5) (w := 1.1) (r := 11) ++
  txt x (y + 4) s (size := 11.5) (anchor := "middle") (family := MONO)

def tapeVertex (name : String) : String :=
  let (x, y) := tpos name
  if LEAVES.contains name then
    circle x y 8.5 ++
    txt (x - 13) (y + 4) name (size := 10.5) (anchor := "end") (family := MONO) ++
    (if name.startsWith "e." then
      txt (x - 13) (y + 15) "const" (size := 9.0) (anchor := "end") (fill := GRAY5) (style := "italic") else "")
  else if INTERIOR.contains name then
    circle x y 8.5 (fill := "#FFFFFF") (stroke := GRAY5) (w := 1.4) ++
    txt x (y + 4) (OPS name) (size := 11.0) (anchor := "middle") (fill := GRAY5) (weight := "700") ++
    txt (x + 8) (y + 13) "τ" (size := 10.0) (fill := GRAY5) (style := "italic")
  else
    let isRoot := ROOTS.contains name
    (if isRoot then circle x y 12.0 (fill := "none") (stroke := BLACK) (w := 1.2) else "") ++
    circle x y 8.5 (fill := "#FFFFFF") ++
    txt x (y + 4) (OPS name) (size := 11.0) (anchor := "middle") (weight := "700") ++
    txt (x + (if isRoot then 18 else 13)) (y + 4) name (size := 10.5) (family := MONO)

def NODES : List String := ["a", "b", "c", "e", "y"]

/-- The figure, byte for byte what `make-three-layers-pkc.py` writes. -/
public def build : String :=
  let ky : Float := 686.0
  let (yx, yy) := P "y"
  s!"<svg xmlns=\"http://www.w3.org/2000/svg\" viewBox=\"0 0 {f0 W} {f0 H}\" font-family=\"{SANS}\">" ++
  s!"<rect width=\"{f0 W}\" height=\"{f0 H}\" fill=\"#FFFFFF\"/>" ++ defs ++ bands ++
  String.join (NODES.map dimNode) ++
  String.join (OCC.map fun (occ, cx, cy) =>
    let ops := if occ == "product" then ["a", "b"] else ["c", "e"]
    let res := if occ == "product" then "c" else "y"
    hyperedge occ cx cy ops res (dy := DY_DIM) (label := RULES occ) (mono := false)
      (portHw := fun n => pillHw (DIMS n))) ++
  String.join (NODES.map fun name =>
    let (x, y) := P name
    line x (y - 14) x (y + DY_DIM + 14) (stroke := GRAY5) (w := 1.0) (marker := "arrow")) ++
  String.join (OCC.map fun (_, cx, cy) =>
    line cx (cy - 13) cx (cy + DY_DIM + 13) (stroke := GRAY5) (w := 1.0) (marker := "arrow")) ++
  txt 568 178 "dim" (size := 10.5) (fill := GRAY5) (family := MONO) ++
  hyperedge "product" 250.0 288.0 ["a", "b"] "c" ++
  hyperedge "additive" 478.0 314.0 ["c", "e"] "y" ++
  String.join (NODES.map kindedNode) ++
  line (yx + 13) yy (yx + 48) yy (w := 1.2) (marker := "arrow") ++
  txt (yx + 52) (yy + 4) "exit" (size := 10.0) (fill := GRAY5) (style := "italic") ++
  String.join (REALIZATIONS.map fun (_, x0, y0, x1, y1) =>
    rrect x0 y0 x1 y1 (stroke := GRAY5) (w := 1.1) (dash := "2 3") (r := 8)) ++
  txt 188 570 "product ↦" (size := 9.5) (fill := GRAY5) (family := MONO) ++
  txt 188 582 "(ac−bd) + (ad+bc)j" (size := 9.5) (fill := GRAY5) (family := MONO) ++
  txt 404 602 "additive ↦ componentwise" (size := 9.5) (fill := GRAY5) (family := MONO) ++
  String.join (TAPE_EDGES.map fun (u, v) =>
    let (x1, y1) := tpos u; let (x2, y2) := tpos v
    line (x1 + 9) y1 (x2 - 9) y2 (w := 1.0)
      (stroke := if INTERIOR.contains u || INTERIOR.contains v then GRAY5 else BLACK)) ++
  String.join (T.map fun (name, _, _) => tapeVertex name) ++
  String.join (R_PAIRS.map fun (hn, tv) =>
    let (x1, y1) := P hn; let (x2, y2) := tpos tv
    line x1 (y1 + 13) x2 (y2 - 10) (stroke := RED) (w := 1.1) (dash := "4 3")) ++
  txt 392 406 "R" (size := 14.0) (fill := RED) (weight := "700") (style := "italic") ++
  wrap NOTE_X 50 [
    "#dimension layer — what the laws must satisfy",
    "!capstone 3 — dimensional homogeneity",
    "dim is a functor: each node to its dimension,",
    "each occurrence to its family's rule. The band",
    "is the hypergraph's image under dim; the",
    "capstone says the image is exact along every",
    "occurrence, so an output's dimension is",
    "computed from the sources' alone. A wrong",
    "edge, ω·τ → ω, has no image here: refuted."] (fill := GRAY5) ++
  wrap NOTE_X 228 [
    "#provenance layer — what the source declares",
    "!capstone 1 — the seal of a module",
    "The metrological provenance hypergraph; kinds",
    "originate here. Every leaf of an output's",
    "pedigree is a declared source — a checked",
    "ingest, a constant mint, an attestation — so",
    "no undeclared raw datum reaches y. Decided",
    "per boundary by the kernel; stated over this",
    "graph, not over the code."] ++
  wrap NOTE_X 420 [
    "#computation layer — what the code computes",
    "The computational tape graph, with no kinds of its own.",
    "!R — the kind-transporting weak bisimulation",
    "total: every observable vertex (a leaf, a root,",
    "an operand or result of a matched occurrence)",
    "has exactly one kinded partner;",
    "weak: the interior vertices τ of a carrier",
    "expansion are silent — no kinded node names ac;",
    "bi: every occurrence is realized by a sub-graph",
    "(down), every tape path between observable",
    "vertices projects to a hypergraph path (up).",
    "Not a bijection: one kinded operation is several",
    "carrier operations, and compaction merges.",
    "!capstone 2 — the seal of the computation",
    "The seal carried onto the tape at every carrier:",
    "y depends only on the images of its influencers."] (fill := GRAY5) ++
  circle 60 (ky - 4) 6.0 ++
  txt 72 ky "declared node / observable vertex" (size := 10.5) (fill := GRAY5) ++
  circle 280 (ky - 4) 6.0 (fill := "#FFFFFF") (stroke := GRAY5) ++
  txt 292 ky "silent interior vertex τ" (size := 10.5) (fill := GRAY5) ++
  rrect 440 (ky - 11) 464 (ky + 1) (stroke := GRAY5) (w := 1.1) (dash := "2 3") (r := 3) ++
  txt 472 ky "realization of one occurrence" (size := 10.5) (fill := GRAY5) ++
  line 650 (ky - 4) 680 (ky - 4) (stroke := RED) (w := 1.1) (dash := "4 3") ++
  txt 688 ky "R" (size := 10.5) (fill := RED) (weight := "700") (style := "italic") ++
  line 720 (ky - 4) 750 (ky - 4) (stroke := GRAY5) (w := 1.0) (marker := "arrow") ++
  txt 758 ky "dim, a functor along every occurrence" (size := 10.5) (fill := GRAY5) ++
  "</svg>"

end Tools.Figures.ThreeLayers
