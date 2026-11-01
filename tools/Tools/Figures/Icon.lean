module

public import Tools.Figures.Fmt

/-!
The PropertyKindCalculus mark, wordless: Lowe's square reduced to an icon (the Python
`pkc_icon.py`, line for line). Four corner nodes, Attributes in red, the two type indices at
three times the weight meeting at Modes, the diagonal dashed, plates behind Modes for the
carrier. Drawn about its square; `extent` reports the real bounding box.
-/

namespace Tools.Figures.Icon

public def RED := "#E4002B"
public def BLACK := "#000000"
public def GRAY5 := "#767676"

def NODE_R : Float := 0.085
def PLATE : Float := 0.32
def PLATE_STEP : Float := 0.05
def GAP : Float := 0.17

/-- `(left, top, right, bottom)` of the drawn mark, relative to its center. -/
public def extent (s : Float) : Float × Float × Float × Float :=
  let front := 0.5 + NODE_R
  let back := 0.5 + PLATE / 2 + 3 * PLATE_STEP
  (-s * front, -s * front, s * back, s * back)

/-- The wordless mark, its square of side `s` centered on `(cx, cy)`. -/
public def icon (cx cy s : Float) (red := RED) (black := BLACK) (gray := GRAY5) : String :=
  let f2 := fmtFixed 2
  let half := s / 2.0
  let xl := cx - half; let xr := cx + half; let yt := cy - half; let yb := cy + half
  let r := s * NODE_R
  let side := s * PLATE
  let gap := s * GAP
  let gapM := side / 2 + s * 0.03
  let thin := max 0.9 (s * 0.035)
  let thick := thin * 3.0
  let plates := [3, 2, 1].foldl (init := "") fun o (i : Nat) =>
    let d := Float.ofNat i * s * PLATE_STEP
    o ++ s!"<rect x=\"{f2 (xr - side / 2 + d)}\" y=\"{f2 (yb - side / 2 + d)}\" " ++
      s!"width=\"{f2 side}\" height=\"{f2 side}\" rx=\"{f2 (s * 0.035)}\" " ++
      s!"fill=\"#FFFFFF\" stroke=\"{gray}\" stroke-width=\"{f2 (thin * 0.8)}\" " ++
      s!"opacity=\"{f2 (1.0 - 0.18 * Float.ofNat i)}\"/>"
  let g := gap * 0.85
  plates ++
    s!"<line x1=\"{f2 (xl + gap)}\" y1=\"{f2 yt}\" x2=\"{f2 (xr - gap)}\" y2=\"{f2 yt}\" stroke=\"{black}\" stroke-width=\"{f2 thin}\"/>" ++
    s!"<line x1=\"{f2 xl}\" y1=\"{f2 (yt + gap)}\" x2=\"{f2 xl}\" y2=\"{f2 (yb - gap)}\" stroke=\"{black}\" stroke-width=\"{f2 thin}\"/>" ++
    s!"<line x1=\"{f2 (xl + gap)}\" y1=\"{f2 yb}\" x2=\"{f2 (xr - gapM)}\" y2=\"{f2 yb}\" stroke=\"{black}\" stroke-width=\"{f2 thick}\"/>" ++
    s!"<line x1=\"{f2 xr}\" y1=\"{f2 (yt + gap)}\" x2=\"{f2 xr}\" y2=\"{f2 (yb - gapM)}\" stroke=\"{red}\" stroke-width=\"{f2 thick}\"/>" ++
    s!"<line x1=\"{f2 (xl + g)}\" y1=\"{f2 (yb - g)}\" x2=\"{f2 (xr - g)}\" y2=\"{f2 (yt + g)}\" stroke=\"{gray}\" stroke-width=\"{f2 (thin * 0.9)}\" stroke-dasharray=\"{f2 (s * 0.07)} {f2 (s * 0.055)}\"/>" ++
    s!"<rect x=\"{f2 (xr - side / 2)}\" y=\"{f2 (yb - side / 2)}\" width=\"{f2 side}\" height=\"{f2 side}\" rx=\"{f2 (s * 0.035)}\" fill=\"#FFFFFF\" stroke=\"{black}\" stroke-width=\"{f2 (thin * 1.4)}\"/>" ++
    s!"<circle cx=\"{f2 xl}\" cy=\"{f2 yt}\" r=\"{f2 r}\" fill=\"{black}\"/>" ++
    s!"<circle cx=\"{f2 xr}\" cy=\"{f2 yt}\" r=\"{f2 r}\" fill=\"{red}\"/>" ++
    s!"<circle cx=\"{f2 xl}\" cy=\"{f2 yb}\" r=\"{f2 r}\" fill=\"{black}\"/>"

end Tools.Figures.Icon
