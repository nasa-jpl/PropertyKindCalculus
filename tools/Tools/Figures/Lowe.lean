module

public import Tools.Figures.Fmt

/-! Lowe's square with the calculus's identifiers (`make-lowe-square-pkc.py`, line for line). -/

namespace Tools.Figures.Lowe

def RED := "#E4002B"
def BLACK := "#000000"
def GRAY5 := "#767676"
def SANS := "Helvetica Neue, Helvetica, Arial, sans-serif"
def MONO := "SF Mono, Menlo, Consolas, monospace"
def W : Float := 960.0
def H : Float := 440.0
def CXL : Float := 270.0
def CXR : Float := 760.0
def CYT : Float := 96.0
def CYB : Float := 266.0
def THIN : Float := 1.6
def THICK : Float := 4.8
def CARD_HW : Float := 106.0
def CARD_T : Float := CYB - 28.0
def CARD_B : Float := CYB + 62.0
def PLATE_DX : Float := 9.0
def PLATE_DY : Float := 26.0
def PLATES : List (String × Nat) := [("R=Float32", 3), ("R=Float", 2), ("R=ℝ", 1)]
def SLOT := "<...>"
def BRACE_W : Float := 18.0
def COL_ARMS_Y : Float := 66.0
def ROW_ARMS_X : Float := 190.0
def COLUMNS : List ((Float × Float) × String) :=
  [((205.0, 335.0), "substantial — systems"), ((645.0, 895.0), "non-substantial — properties")]
def ROWS : List ((Float × Float) × String) :=
  [((82.0, 135.0), "universals"), ((CARD_T, CARD_B + 3 * PLATE_DY), "particulars")]

def f1 := fmtFixed 1
def f2 := fmtFixed 2

def txt (x y : Float) (s : String) (size : Float := 12.0) (fill := BLACK) (anchor := "start")
    (family : Option String := none) (weight : Option String := none)
    (style : Option String := none) (raw := false) : String :=
  s!"<text x=\"{f1 x}\" y=\"{f1 y}\" font-size=\"{f1 size}\" fill=\"{fill}\"" ++
    (if anchor != "start" then s!" text-anchor=\"{anchor}\"" else "") ++
    (family.map (s!" font-family=\"{·}\"")).getD "" ++
    (weight.map (s!" font-weight=\"{·}\"")).getD "" ++
    (style.map (s!" font-style=\"{·}\"")).getD "" ++
    ">" ++ (if raw then s else escape s) ++ "</text>"

def line (x1 y1 x2 y2 : Float) (stroke := BLACK) (w : Float := THIN) (dash : Option String := none) : String :=
  s!"<line x1=\"{f1 x1}\" y1=\"{f1 y1}\" x2=\"{f1 x2}\" y2=\"{f1 y2}\" stroke=\"{stroke}\" stroke-width=\"{f2 w}\"" ++
    (dash.map (s!" stroke-dasharray=\"{·}\"")).getD "" ++ "/>"

def path (d : String) (stroke := GRAY5) (w : Float := 1.8) : String :=
  s!"<path d=\"{d}\" fill=\"none\" stroke=\"{stroke}\" stroke-width=\"{f2 w}\" stroke-linecap=\"round\" stroke-linejoin=\"round\"/>"

/-- A curly brace spanning `y0..y1`: arms at `xa`, cusp pointing left. -/
def braceV (xa y0 y1 : Float) (w : Float := BRACE_W) : String :=
  let xs := xa - w * 0.55; let xt := xa - w; let ym := (y0 + y1) / 2
  let q := min (w * 0.9) ((ym - y0) * 0.45)
  path (s!"M {f1 xa} {f1 y0} Q {f1 xs} {f1 y0} {f1 xs} {f1 (y0 + q)} " ++
    s!"L {f1 xs} {f1 (ym - q)} Q {f1 xs} {f1 ym} {f1 xt} {f1 ym} " ++
    s!"Q {f1 xs} {f1 ym} {f1 xs} {f1 (ym + q)} L {f1 xs} {f1 (y1 - q)} " ++
    s!"Q {f1 xs} {f1 y1} {f1 xa} {f1 y1}")

/-- A curly brace spanning `x0..x1`: arms at `ya`, cusp pointing up. -/
def braceH (ya x0 x1 : Float) (w : Float := BRACE_W) : String :=
  let ys := ya - w * 0.55; let yt := ya - w; let xm := (x0 + x1) / 2
  let q := min (w * 0.9) ((xm - x0) * 0.45)
  path (s!"M {f1 x0} {f1 ya} Q {f1 x0} {f1 ys} {f1 (x0 + q)} {f1 ys} " ++
    s!"L {f1 (xm - q)} {f1 ys} Q {f1 xm} {f1 ys} {f1 xm} {f1 yt} " ++
    s!"Q {f1 xm} {f1 ys} {f1 (xm + q)} {f1 ys} L {f1 (x1 - q)} {f1 ys} " ++
    s!"Q {f1 x1} {f1 ys} {f1 x1} {f1 ya}")

def scope : String :=
  String.join (COLUMNS.map fun ((x0, x1), head) =>
    braceH COL_ARMS_Y x0 x1 ++
      txt ((x0 + x1) / 2) (COL_ARMS_Y - BRACE_W - 8) head (size := 12.5) (fill := GRAY5) (anchor := "middle")) ++
  String.join (ROWS.map fun ((y0, y1), lab) =>
    braceV ROW_ARMS_X y0 y1 ++
      txt (ROW_ARMS_X - BRACE_W - 10) ((y0 + y1) / 2 + 4) lab (size := 12.5) (fill := GRAY5) (anchor := "end"))

def corner (cx cy : Float) (name ident : String) (color := BLACK) (identRaw := false) : String :=
  txt cx (cy - 1) name (size := 18) (weight := "700") (fill := color) (anchor := "middle") ++
  txt cx (cy + 17) ident (size := 13) (family := MONO) (fill := color) (anchor := "middle") (raw := identRaw) ++
  txt cx (cy + 35) SLOT (size := 12) (family := MONO) (fill := GRAY5) (anchor := "middle")

def edgeLabel (cx y0 : Float) (rel mech : String) (color := BLACK) : String :=
  txt cx y0 rel (size := 12.5) (style := "italic") (fill := GRAY5) (anchor := "middle") ++
  txt cx (y0 + 18) mech (size := 12.5) (fill := color) (anchor := "middle") (raw := true)

def mCornerStack : String :=
  let x0 := CXR - CARD_HW; let y0 := CARD_T
  let wd := 2 * CARD_HW; let ht := CARD_B - CARD_T
  String.join (PLATES.map fun (_, i) =>
    let fi := Float.ofNat i
    s!"<rect x=\"{f1 (x0 + fi * PLATE_DX)}\" y=\"{f1 (y0 + fi * PLATE_DY)}\" " ++
    s!"width=\"{f1 wd}\" height=\"{f1 ht}\" rx=\"4\" fill=\"#FFFFFF\" " ++
    s!"stroke=\"{GRAY5}\" stroke-width=\"1.1\" opacity=\"{f2 (1.0 - 0.17 * fi)}\"/>") ++
  s!"<rect x=\"{f1 x0}\" y=\"{f1 y0}\" width=\"{f1 wd}\" height=\"{f1 ht}\" rx=\"4\" fill=\"#FFFFFF\" stroke=\"{BLACK}\" stroke-width=\"1.8\"/>" ++
  String.join (PLATES.map fun (name, i) =>
    let fi := Float.ofNat i
    txt (x0 + fi * PLATE_DX + wd - 9) (y0 + fi * PLATE_DY + ht - 7) name (size := 11.5) (family := MONO) (fill := GRAY5) (anchor := "end")) ++
  corner CXR CYB "Modes"
    (s!"IndividualQuantity <tspan font-weight=\"700\">o</tspan> " ++
     s!"<tspan fill=\"{RED}\" font-weight=\"700\">k</tspan> " ++
     s!"<tspan fill=\"{GRAY5}\" font-weight=\"700\">R</tspan>") (identRaw := true) ++
  txt (x0 + wd - 9) (CARD_B - 8) "R=Int" (size := 11.5) (family := MONO) (fill := BLACK) (weight := "700") (anchor := "end") ++
  txt x0 (CARD_B + 3 * PLATE_DY + 22) "indexed by a carrier representation, R" (size := 12.5) (style := "italic") (fill := GRAY5)

def monoT (s : String) : String := s!"<tspan font-family=\"{MONO}\">{escape s}</tspan>"

/-- The figure, byte for byte what `make-lowe-square-pkc.py` writes. -/
public def build : String :=
  let f0 := fmtFixed 0
  let dash := "6 5"
  s!"<svg xmlns=\"http://www.w3.org/2000/svg\" viewBox=\"0 0 {f0 W} {f0 H}\" font-family=\"{SANS}\">" ++
  s!"<rect width=\"{f0 W}\" height=\"{f0 H}\" fill=\"#FFFFFF\"/>" ++
  scope ++
  line 338 CYT 455 CYT ++
  line 573 CYT 700 CYT ++
  edgeLabel 514 (CYT - 5) "characterized by" (monoT "DedicatedKind") ++
  line CXL 142 CXL 170 ++
  line CXL 216 CXL 246 ++
  edgeLabel CXL 189 "instantiated by" (monoT "Sorted.sortOf") ++
  line 338 CYB 425 CYB (w := THICK) ++
  line 557 CYB (CXR - CARD_HW) CYB (w := THICK) ++
  edgeLabel 491 (CYB - 13) "characterized by"
    s!"an object index, <tspan font-family=\"{MONO}\" font-weight=\"700\">o</tspan>" ++
  line CXR 142 CXR 170 (stroke := RED) (w := THICK) ++
  line CXR 216 CXR CARD_T (stroke := RED) (w := THICK) ++
  edgeLabel CXR 189 "instantiated by"
    s!"a kind index, <tspan font-family=\"{MONO}\" fill=\"{RED}\" font-weight=\"700\">k</tspan>" (color := RED) ++
  line 336.1 243.1 411.1 217.1 (stroke := GRAY5) (w := 1.4) (dash := dash) ++
  line 600.1 151.5 675.0 125.5 (stroke := GRAY5) (w := 1.4) (dash := dash) ++
  edgeLabel 505.6 180 "exemplified by"
    "<tspan font-style=\"italic\">derived</tspan> — either path around the square" ++
  corner CXL CYT "Kinds" "SortOfSystem" ++
  corner CXR CYT "Attributes" "KindOfProperty" (color := RED) ++
  corner CXL CYB "Substances" "o : O" ++
  mCornerStack ++
  line 60 424 92 424 (w := THICK) ++
  txt 100 428 "a heavy edge is a type index" (size := 12.5) (fill := GRAY5) ++
  "</svg>"

end Tools.Figures.Lowe
