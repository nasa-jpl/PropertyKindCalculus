module

public import Tools.Figures.Fmt

/-!
What the calculus adds to TorchLean, layer by layer: the figure of the *Metrology on a Verified
Numerical Framework* chapter.

Two columns, five layers. The left column is what TorchLean provides at each layer, the right
column what PropertyKindCalculus builds on it. The middle layer is the alphabet of operations a
*certified fused kernel* may use: the operations TorchLean's kernel compiler `Program.of`
accepts in binary32 and binary64, and the ones the calculus's straight-line program adds. The
red chips are exactly the operations `Program.of` refuses; that is a measurement, kept in
`scratchpad/torchlean-retrospective/{trans,alpha}-probe.log` of the workspace, and the
chapter states it. Below them the left column lists the eager device-buffer operations this work
contributed, which run outside a kernel. A `#n` in the left column marks a change contributed to
TorchLean by this work.
-/

namespace Tools.Figures.Extension

def RED := "#E4002B"
def REDFILL := "#FDECEF"
def BLACK := "#000000"
def GRAY5 := "#767676"
def GRAY2 := "#C8C8C8"
def SANS := "Helvetica Neue, Helvetica, Arial, sans-serif"
def MONO := "SF Mono, Menlo, Consolas, monospace"
def W : Float := 960.0
def H : Float := 1007.0
def LX0 : Float := 150.0
def LX1 : Float := 512.0
def RX0 : Float := 548.0
def RX1 : Float := 946.0
def LEAD : Float := 15.0

def f0 := fmtFixed 0
def f1 := fmtFixed 1

def txt (x y : Float) (s : String) (size : Float := 11.5) (fill := BLACK) (anchor := "start")
    (family : Option String := none) (weight : Option String := none)
    (style : Option String := none) : String :=
  s!"<text x=\"{f1 x}\" y=\"{f1 y}\" font-size=\"{f1 size}\" fill=\"{fill}\"" ++
    (if anchor != "start" then s!" text-anchor=\"{anchor}\"" else "") ++
    (family.map (s!" font-family=\"{·}\"")).getD "" ++
    (weight.map (s!" font-weight=\"{·}\"")).getD "" ++
    (style.map (s!" font-style=\"{·}\"")).getD "" ++
    ">" ++ escape s ++ "</text>"

def line (x1 y1 x2 y2 : Float) (stroke := BLACK) (w : Float := 1.4)
    (marker : Option String := none) : String :=
  s!"<line x1=\"{f1 x1}\" y1=\"{f1 y1}\" x2=\"{f1 x2}\" y2=\"{f1 y2}\" stroke=\"{stroke}\" stroke-width=\"{f1 w}\"" ++
    (marker.map (s!" marker-end=\"url(#ext-{·})\"")).getD "" ++ "/>"

def rrect (x0 y0 x1 y1 : Float) (fill := "none") (stroke := BLACK) (w : Float := 1.4)
    (dash : Option String := none) (r : Float := 6.0) : String :=
  s!"<rect x=\"{f1 x0}\" y=\"{f1 y0}\" width=\"{f1 (x1 - x0)}\" height=\"{f1 (y1 - y0)}\" rx=\"{f1 r}\" fill=\"{fill}\" stroke=\"{stroke}\" stroke-width=\"{f1 w}\"" ++
    (dash.map (s!" stroke-dasharray=\"{·}\"")).getD "" ++ "/>"

/-- One `<text>` per line; a leading `!` makes the line bold. -/
def wrap (x y : Float) (lines : List String) (fill := BLACK) (size : Float := 11.5) : String :=
  String.join <| lines.zipIdx.map fun (s, i) =>
    let yi := y + Float.ofNat i * LEAD
    if s.startsWith "!" then txt x yi (s.drop 1).toString (size := size) (fill := fill) (weight := "700")
    else txt x yi s (size := size) (fill := fill)

/-- Chip half-width for a monospace label at 11 px. -/
def chipW (s : String) : Float := 16.0 + 6.8 * Float.ofNat s.length

/-- A row of chips from `x`, each `(label, style)`: `0` a TorchLean operation, `1` a TorchLean
operation contributed by this work, `2` an operation the calculus adds, `3` one both carry. -/
def chips (x y : Float) (cs : List (String × Nat)) : String := Id.run do
  let mut out := ""
  let mut cx := x
  for (s, k) in cs do
    let w := chipW s
    let (fill, stroke, ink) :=
      match k with
      | 0 => ("#FFFFFF", BLACK, BLACK)
      | 1 => ("#FFFFFF", RED, BLACK)
      | 2 => (RED, RED, "#FFFFFF")
      | _ => (REDFILL, RED, RED)
    out := out ++ rrect cx (y - 13) (cx + w) (y + 7) (fill := fill) (stroke := stroke) (w := 1.2) (r := 10) ++
      txt (cx + w / 2) (y + 1) s (size := 11.0) (fill := ink) (anchor := "middle") (family := MONO)
        (weight := if k == 2 then some "700" else none)
    cx := cx + w + 7
  return out

/-- `(layer name, top, bottom, TorchLean has a counterpart)`. A layer without one gets a dashed,
empty-handed left box: the census of TorchLean's source at the pinned revision found nothing
there (a measurement of the source text, recorded in the chapter, not a proof of absence). -/
def ROWS : List (String × Float × Float × Bool) :=
  [("Meaning", 52.0, 147.0, false), ("Uncertainty", 157.0, 237.0, true),
   ("Performance", 247.0, 387.0, false), ("Code generation", 397.0, 477.0, true),
   ("Kernel alphabet", 487.0, 727.0, true), ("Recording", 737.0, 817.0, true),
   ("Numbers", 827.0, 907.0, true)]

def top (name : String) : Float :=
  match ROWS.find? (·.1 == name) with | some (_, t, _, _) => t | none => 0

def defs : String :=
  "<defs><marker id=\"ext-arrow\" viewBox=\"0 0 10 10\" refX=\"9\" refY=\"5\" markerWidth=\"7\" " ++
  "markerHeight=\"7\" orient=\"auto-start-reverse\">" ++
  s!"<path d=\"M 0 0 L 10 5 L 0 10 z\" fill=\"{RED}\"/></marker></defs>"

def frame : String :=
  String.join <| ROWS.map fun (name, t, b, has) =>
    let mid := (t + b) / 2
    txt 22 (mid + 4) name (size := 12.0) (weight := "700") ++
    (if has then rrect LX0 t LX1 b
     else rrect LX0 t LX1 b (stroke := GRAY2) (w := 1.2) (dash := some "4 4")) ++
    rrect RX0 t RX1 b (fill := REDFILL) (stroke := RED) (w := 1.4) ++
    line (LX1 + 6) mid (RX0 - 4) mid (stroke := RED) (w := 1.6) (marker := some "arrow")

/-- The left and right text of a row, starting `dy` below its top. -/
def cell (name : String) (left right : List String) (dy : Float := 22.0) (leftFill := BLACK) : String :=
  wrap (LX0 + 14) (top name + dy) left (fill := leftFill) ++
  wrap (RX0 + 14) (top name + dy) right (fill := RED)

def body : String :=
  cell "Meaning" ["no counterpart: a tensor holds numbers,", "not quantities"]
    ["!each quantity carries its kind; erasing it costs nothing",
     "proved both ways (a weak bisimulation):",
     "every model step appears in the compiled program, and",
     "every program path traces back to the model, so it adds",
     "no input, constant or change of kind the model lacks"] (leftFill := GRAY5) ++
  cell "Uncertainty" ["!round-off error bounds",
     "for floating-point evaluation"]
    ["!measurement uncertainty: GUM ⊂ Willink ⊂ SSPRC",
     "coverage intervals; conformity assessment (JCGM 106)",
     "round-off charged to the uncertainty budget,",
     "in TorchLean's binary32 rounding vocabulary"] ++
  cell "Performance" ["no counterpart: no intensity, memory or",
     "platform-capacity accounting"]
    ["!arithmetic intensity computed from the recorded model",
     "eager vs fused gap reported; peak memory per strategy",
     "!tuned partitioning of each image tile:",
     "as many pieces as keep every core busy, as long as",
     "memory holds them and each piece repays its startup",
     "!fusion keeps intermediates in registers, not memory:",
     "!the speedup, proved to compute the same values",
     "!with the same meaning as the unfused model"] (leftFill := GRAY5) ++
  cell "Code generation" ["!certified kernel compiler",
     "a Lean scalar function becomes CUDA, proved",
     "to compute what the function computes",
     "one kernel per function; Julia only as a subprocess"]
    ["!one fused kernel for a whole model",
     "proved: the one program every target is printed from",
     "computes what the model computes;",
     "the CUDA, C and Julia printers and compilers are trusted"] ++
  -- Kernel alphabet
  (let t := top "Kernel alphabet"
   wrap (LX0 + 14) (t + 22) ["!what a certified binary32/64 kernel may use"] ++
   chips (LX0 + 14) (t + 50) [("+", 0), ("−", 0), ("×", 0), ("÷", 0), ("<", 0), ("if", 0)] ++
   chips (LX0 + 14) (t + 80) [("⌊u⌋ as index #44", 1), ("f64 on f32 #47", 1)] ++
   chips (LX0 + 14) (t + 110) [("else if #46", 1)] ++
   wrap (LX0 + 14) (t + 138) ["exp, log only by table search, ≤ 20-bit formats"] (fill := GRAY5) (size := 10.5) ++
   wrap (LX0 + 14) (t + 166) ["!on eager device buffers, outside a kernel"] ++
   chips (LX0 + 14) (t + 194) [("pow #52", 1), ("< ≤ > ≥ #52", 1), ("select #52", 1)] ++
   chips (LX0 + 14) (t + 224) [("table lookup #53", 1)] ++
   wrap (RX0 + 14) (t + 22) ["!what remote-sensing forward models add"] (fill := RED) ++
   chips (RX0 + 14) (t + 50) [("exp", 2), ("log", 2), ("sqrt", 2), ("|x|", 2), ("min", 2), ("max", 2)] ++
   chips (RX0 + 14) (t + 80) [("table fetch", 3)] ++
   wrap (RX0 + 14) (t + 110) ["attenuation, dielectric mixing, radiative transfer,",
     "calibration tables — in one certified fused kernel"] (fill := RED) (size := 10.5)) ++
  cell "Recording" ["!a tape of operations",
     "forward values and reverse-mode gradients",
     "a node recorded in linear time #51"]
    ["!the model records itself as it runs",
     "proved: the recording computes what the model computes",
     "repeated steps merged, proved to change no value"] ++
  cell "Numbers" ["!binary32 and binary64 formats, rounding spec",
     "executable binary32 with NaN and infinities",
     "Sterbenz's lemma, absorption test (with FloatLib)"]
    ["!one source, run at every precision",
     "binary32 rounding proved against the real numbers,",
     "overflow stated; executable ULP for adequacy;",
     "Float is the reference run"]

def legend : String :=
  let ky : Float := 949.0
  chips 22 ky [("op", 0)] ++
  txt 62 ky "TorchLean" (size := 10.5) (fill := GRAY5) ++
  chips 140 ky [("op", 1)] ++
  txt 180 ky "contributed to TorchLean (#n: its pull request)" (size := 10.5) (fill := GRAY5) ++
  chips 470 ky [("op", 2)] ++
  txt 510 ky "PropertyKindCalculus only" (size := 10.5) (fill := GRAY5) ++
  chips 680 ky [("op", 3)] ++
  txt 720 ky "both: TorchLean kernel, calculus semantics" (size := 10.5) (fill := GRAY5) ++
  txt 22 (ky + 30) ("Dashed box: no counterpart found in TorchLean's source. " ++
    "Red chips: operations TorchLean's kernel compiler refuses in binary32 and binary64;") (size := 10.5) (fill := GRAY5) ++
  txt 22 (ky + 45) ("its eager device and tape operations include exp, log and sqrt, so the extension is to " ++
    "one certified fused kernel holding a model's whole arithmetic.") (size := 10.5) (fill := GRAY5)

public def build : String :=
  s!"<svg xmlns=\"http://www.w3.org/2000/svg\" viewBox=\"0 0 {f0 W} {f0 H}\" " ++
  s!"font-family=\"{SANS}\" role=\"img\" aria-label=\"What PropertyKindCalculus adds beyond TorchLean, layer by layer\">" ++
  defs ++
  s!"<rect x=\"0\" y=\"0\" width=\"{f0 W}\" height=\"{f0 H}\" fill=\"#FFFFFF\"/>" ++
  txt (LX0 + (LX1 - LX0) / 2) 34 "What TorchLean provides" (size := 14.0) (anchor := "middle") (weight := "700") ++
  txt (RX0 + (RX1 - RX0) / 2) 34 "What PropertyKindCalculus adds beyond TorchLean" (size := 14.0) (fill := RED) (anchor := "middle") (weight := "700") ++
  frame ++ body ++ legend ++ "</svg>"

end Tools.Figures.Extension
