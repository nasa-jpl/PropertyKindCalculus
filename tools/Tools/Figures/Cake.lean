module

public import Tools.Figures.Fmt
public import Tools.Figures.Icon

/-!
The architecture cake (`make-architecture-cake.py`, line for line): the layers from the
mission's data product (deck) or a domain model (blueprint) down to the Lean kernel, each
band a logo, a name, a role and a chip of claims. The audience is read in exactly two
places — the top layer(s) and the TorchLean chip — and `layersFor_eq` says so.
-/

namespace Tools.Figures.Cake

def W := 1200
def RAIL_X := 26
def BAND_X0 : Float := 54
def BAND_X1 : Float := 772
def LOGO_X0 : Float := 66
def LOGO_W : Float := 180
def TEXT_X := 262
def CHIP_X : Float := 790
def PEER_GAP : Float := 8
def PEER_LOGO_W : Float := 100
def PEER_TEXT_DX : Float := 124
def RED := "#E4002B"
def BLACK := "#000000"
def GRAY5 := "#767676"
def GRAY3 := "#D5D5D5"
def GRAY1 := "#F9F9F9"
def TINT := "#FDF2F4"

public inductive Kind where | mission | base | floor deriving DecidableEq, Repr

/-- A chip line: plain, or with a bold head. -/
public inductive ChipLine where
  | plain (s : String)
  | headed (head rest : String)
  deriving DecidableEq, Repr

public structure Peer where
  logo : String
  name : String
  roles : List String
  deriving DecidableEq, Repr

public structure Layer where
  kind : Kind
  h : Nat
  logo : String := ""
  name : String := ""
  role : String := ""
  peers : Option (Peer × Peer) := none
  chip : List ChipLine
  deriving DecidableEq, Repr

open ChipLine in
@[expose] public def deckMissionLayers : List Layer := [
  { kind := .mission, h := 58, logo := "pixels",
    name := "the operational data product",
    role := "values · QC flags · provenance, per pixel",
    chip := [plain "■ the pixel's own conditions travel with it"] },
  { kind := .mission, h := 64, logo := "statement",
    name := "a trusted science algorithm, as configured for a run",
    role := "the scientist runs what operations runs, aside from the hardware",
    chip := [plain "■ every number's kind is derived, checked, or attested",
             plain "with a reason — or the build fails",
             plain "□ release: the scientist accepts every attestation"] }]

open ChipLine in
@[expose] public def blueprintModelLayer : Layer :=
  { kind := .mission, h := 64, logo := "statement",
    name := "a domain model written in the calculus",
    role := "its boundaries declared, audited, and decided by the build",
    chip := [plain "■ every number's kind is derived, checked, or attested",
             plain "with a reason — or the build fails"] }

open ChipLine in
@[expose] public def torchChip (audience : String) : List ChipLine :=
  if audience == "deck" then
    [plain "CPU ■ same binary, same inputs → same bits",
     plain "GPU ◪ same bits as CPU where the arithmetic matches;",
     plain "the iterative fit's run-to-run bits are unmeasured"]
  else
    [plain "■ one source, three carriers: ℝ to prove, FP32 to bound",
     plain "rounding, IEEE32Exec to run — bridged by refinement theorems"]

open ChipLine in
/-- The layers under the top one(s); `torch` is the one chip that reads the audience. -/
@[expose] public def baseLayersWith (torch : List ChipLine) : List Layer := [
  { kind := .base, h := 64, logo := "pkc",
    name := "PropertyKindCalculus",
    role := "a quantity carries its kind in its type — what the number is a value <i>of</i>",
    chip := [plain "■ each module declares its inputs → outputs, with kinds",
             plain "■ the build proves the code has exactly those",
             plain "■ modules compose by contract, across repositories"] },
  { kind := .base, h := 74,
    peers := some ({ logo := "physlib-logo.png", name := "PhysLib", roles := ["dimensions and units"] },
                   { logo := "cslib", name := "CSLib", roles := ["labelled transition systems", "and bisimulation"] }),
    chip := [headed "PhysLib " "■ dimensions checked at compile time:",
             plain "a dimensionally wrong formula does not build",
             headed "CSLib " "■ the kind-transporting weak bisimulation is one",
             plain "in the textbook sense — not a local re-definition"] },
  { kind := .base, h := 64, logo := "torchlean+floatlib",
    name := "TorchLean + FloatLib",
    role := "tensors, CPU and GPU execution · the executable float word, specified",
    chip := torch },
  { kind := .base, h := 56, logo := "mathlib",
    name := "Mathlib",
    role := "the mathematics the proofs cite",
    chip := [plain "proofs: checked by the kernel",
             plain "definitions: community peer review before merge"] },
  { kind := .floor, h := 92, logo := "lean",
    name := "the Lean kernel + three classical axioms",
    role := "the only thing that must be believed",
    chip := [plain "■ the build prints the axiom profile",
             plain "small enough to re-implement — two dozen independent",
             plain "checkers compete to reject bad proofs (Kernel Arena)"] }]

@[expose] public def topLayers (audience : String) : List Layer :=
  if audience == "deck" then deckMissionLayers else [blueprintModelLayer]

@[expose] public def layersFor (audience : String) : List Layer :=
  topLayers audience ++ baseLayersWith (torchChip audience)

/-- The audience is read in the top layer(s) and the TorchLean chip, nowhere else: every other
layer is the same list for every audience. -/
public theorem layersFor_eq (a : String) :
    layersFor a = topLayers a ++ baseLayersWith (torchChip a) := rfl

public theorem baseLayers_audience_free (a b : String) :
    (baseLayersWith (torchChip a)).map (fun l => { l with chip := [] }) =
      (baseLayersWith (torchChip b)).map (fun l => { l with chip := [] }) := rfl

def LEAN_MARK :=
  "M206.333 5.67949H105.667M206.333 5.67949L243.25 84.5M206.333 5.67949V84.5" ++
  "M243.25 84.5H317.549M243.25 84.5L279.667 163.321L280.889 163.318L317.549 84.5" ++
  "M206.333 84.5V163.321H5V5M206.333 84.5H105.667M317.549 84.5L353 5.67949" ++
  "M353 5.67949V164M353 5.67949H353.667L480.333 163.454H481V5"

def f1 := fmtFixed 1

/-- Standard base64 with padding (`base64.b64encode`). -/
public def base64 (bs : ByteArray) : String := Id.run do
  let tbl := "ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz0123456789+/".toList.toArray
  let ch (k : Nat) : Char := tbl[k % 64]!
  let mut out := ""
  let n := bs.size
  let mut i := 0
  while i + 2 < n do
    let a := bs[i]!.toNat; let b := bs[i+1]!.toNat; let c := bs[i+2]!.toNat
    out := out.push (ch (a >>> 2)) |>.push (ch (((a &&& 3) <<< 4) ||| (b >>> 4)))
      |>.push (ch (((b &&& 15) <<< 2) ||| (c >>> 6))) |>.push (ch (c &&& 63))
    i := i + 3
  if i + 1 == n then
    let a := bs[i]!.toNat
    out := out.push (ch (a >>> 2)) |>.push (ch ((a &&& 3) <<< 4)) |>.push '=' |>.push '='
  else if i + 2 == n then
    let a := bs[i]!.toNat; let b := bs[i+1]!.toNat
    out := out.push (ch (a >>> 2)) |>.push (ch (((a &&& 3) <<< 4) ||| (b >>> 4)))
      |>.push (ch ((b &&& 15) <<< 2)) |>.push '='
  return out

def mime (name : String) : String :=
  if name.endsWith ".png" then "image/png"
  else if name.endsWith ".jpg" || name.endsWith ".jpeg" then "image/jpeg"
  else "application/octet-stream"

/-- The logo files by name; `none` for a file that does not exist. -/
public abbrev Logos := String → Option ByteArray

def dataUri (logos : Logos) (name : String) : String :=
  s!"data:{mime name};base64,{base64 ((logos name).getD ByteArray.empty)}"

/-- An `<image>` box that letterboxes its content. -/
def image (logos : Logos) (name : String) (x y w h : Float) : String :=
  s!"<image href=\"{dataUri logos name}\" x=\"{f1 x}\" y=\"{f1 y}\" width=\"{f1 w}\" height=\"{f1 h}\" preserveAspectRatio=\"xMidYMid meet\"/>"

def leanLogo (cx cy w : Float) : String :=
  let s := w / 486.0
  let h := 169.0 * s
  let x := cx - w / 2.0; let y := cy - h / 2.0
  s!"<g transform=\"translate({f1 x},{f1 y}) scale({fmtFixed 4 s})\" fill=\"none\" stroke=\"{BLACK}\" stroke-width=\"10\" stroke-linecap=\"round\" stroke-linejoin=\"round\"><path d=\"{LEAN_MARK}\"/></g>"

/-- The product's slot: a raster tile, one cell flagged. -/
def pixelGrid (cx cy : Float) : String :=
  let cols := 5; let rows := 3; let s : Float := 9.0; let gap : Float := 3.0
  let w := Float.ofNat cols * s + Float.ofNat (cols - 1) * gap
  let h := Float.ofNat rows * s + Float.ofNat (rows - 1) * gap
  let x0 := cx - w / 2; let y0 := cy - h / 2
  String.join <| (List.range cols).flatMap fun i => (List.range rows).map fun j =>
    let hot := i == 3 && j == 1
    let fill := if hot then RED else "#FFFFFF"
    let stroke := if hot then RED else GRAY5
    s!"<rect x=\"{f1 (x0 + Float.ofNat i * (s + gap))}\" y=\"{f1 (y0 + Float.ofNat j * (s + gap))}\" " ++
    s!"width=\"9.0\" height=\"9.0\" rx=\"1.5\" fill=\"{fill}\" " ++
    s!"stroke=\"{stroke}\" stroke-width=\"1.1\"/>"

/-- The model's slot: a reviewed statement, with its check. -/
def statement (cx cy : Float) : String :=
  let w : Float := 54.0; let h : Float := 40.0
  let x0 := cx - w / 2; let y0 := cy - h / 2
  s!"<rect x=\"{f1 x0}\" y=\"{f1 y0}\" width=\"54.0\" height=\"40.0\" rx=\"3\" fill=\"#FFFFFF\" stroke=\"{GRAY5}\" stroke-width=\"1.2\"/>" ++
  String.join ([(0, 0.26), (1, 0.46), (2, 0.66)].map fun ((k, frac) : Nat × Float) =>
    let wide := if k != 2 then w - 16 else w - 30
    s!"<line x1=\"{f1 (x0 + 8)}\" y1=\"{f1 (y0 + h * frac)}\" x2=\"{f1 (x0 + 8 + wide)}\" y2=\"{f1 (y0 + h * frac)}\" stroke=\"{GRAY3}\" stroke-width=\"2.4\"/>") ++
  s!"<path d=\"M{f1 (x0 + w - 20)} {f1 (y0 + h - 12)} l5 6 l10 -13\" fill=\"none\" stroke=\"{RED}\" stroke-width=\"2.6\" stroke-linecap=\"round\" stroke-linejoin=\"round\"/>"

def wordmark (cx cy : Float) (text : String) : String :=
  s!"<text x=\"{f1 cx}\" y=\"{f1 (cy + 7)}\" text-anchor=\"middle\" font-size=\"26\" font-weight=\"700\" letter-spacing=\"-0.4\" fill=\"{BLACK}\">{escape text}</text>"

def tspans (lines : List ChipLine) (x y : Float) (size : Nat) (fill : String) (lead : Float) : String :=
  s!"<text x=\"{f1 x}\" y=\"{f1 y}\" font-size=\"{size}\" fill=\"{fill}\">" ++
  String.join (lines.zipIdx.map fun (l, i) =>
    let dy : Float := if i == 0 then 0 else lead
    match l with
    | .headed head rest =>
      s!"<tspan x=\"{f1 x}\" dy=\"{f1 dy}\"><tspan font-weight=\"700\" fill=\"{BLACK}\">{escape head}</tspan>{escape rest}</tspan>"
    | .plain s => s!"<tspan x=\"{f1 x}\" dy=\"{f1 dy}\">{escape s}</tspan>") ++
  "</text>"

/-- The role line, honoring a single `<i>…</i>` emphasis span. -/
def roleText (role : String) (x y : Float) : String :=
  match role.splitOn "<i>" with
  | [_] => s!"<text x=\"{f1 x}\" y=\"{f1 y}\" font-size=\"14\" fill=\"{GRAY5}\">{escape role}</text>"
  | head :: rest =>
    let rest := String.intercalate "<i>" rest
    match rest.splitOn "</i>" with
    | mid :: tail =>
      s!"<text x=\"{f1 x}\" y=\"{f1 y}\" font-size=\"14\" fill=\"{GRAY5}\">{escape head}<tspan font-style=\"italic\">{escape mid}</tspan>{escape (String.intercalate "</i>" tail)}</text>"
    | [] => ""
  | [] => ""

def logoSlot (logos : Logos) (logo : String) (lx lcx cy w : Float) : String :=
  if logo == "lean" then leanLogo lcx cy 118
  else if logo == "pkc" then
    let s : Float := 40.0
    let (x0, y0, x1, y1) := Icon.extent s
    Icon.icon (lcx - (x0 + x1) / 2) (cy - (y0 + y1) / 2) s
  else if logo == "torchlean+floatlib" then
    image logos "torchlean-logo.png" (lx + 8) (cy - 25) 78 50 ++
    image logos "floatlib-logo.png" (lx + 98) (cy - 25) 78 50
  else if logo == "mathlib" || logo == "cslib" then wordmark lcx cy logo
  else if logo == "pixels" then pixelGrid lcx cy
  else if logo == "statement" then statement lcx cy
  else if !logo.isEmpty then
    let h : Float := if w ≥ LOGO_W then 48 else 32
    image logos logo lx (cy - h / 2) w h
  else ""

def bandRect (x0 x1 y : Float) (h : Nat) (kind : Kind) : String :=
  let (fill, stroke, sw) : String × String × String := match kind with
    | .mission => (TINT, RED, "1.2") | .floor => ("#FFFFFF", BLACK, "2.2") | .base => (GRAY1, GRAY3, "1.2")
  s!"<rect x=\"{f1 x0}\" y=\"{f1 y}\" width=\"{f1 (x1 - x0)}\" height=\"{h}\" rx=\"6\" fill=\"{fill}\" stroke=\"{stroke}\" stroke-width=\"{sw}\"/>" ++
  (if kind == .mission then s!"<rect x=\"{f1 x0}\" y=\"{f1 y}\" width=\"5\" height=\"{h}\" fill=\"{RED}\"/>" else "")

/-- One of two libraries sharing a row. -/
def peerBand (logos : Logos) (peer : Peer) (x0 x1 y : Float) (h : Nat) (kind : Kind) : String :=
  let cy := y + Float.ofNat h / 2.0
  let lx := x0 + 10
  let tx := x0 + PEER_TEXT_DX
  let nameY := if peer.roles.length == 1 then cy - 4 else cy - 12
  bandRect x0 x1 y h kind ++
  logoSlot logos peer.logo lx (lx + PEER_LOGO_W / 2.0) cy PEER_LOGO_W ++
  s!"<text x=\"{f1 tx}\" y=\"{f1 nameY}\" font-size=\"19\" font-weight=\"700\" fill=\"{BLACK}\">{escape peer.name}</text>" ++
  String.join (peer.roles.zipIdx.map fun (role, i) => roleText role tx (nameY + 21 + 16 * Float.ofNat i))

/-- The figure for an audience, byte for byte what `make-architecture-cake.py` writes. -/
public def build (audience : String) (logos : Logos) : String := Id.run do
  let layers := layersFor audience
  let mut body := ""
  let mut y : Float := 4.0
  let mut floorCy : Option Float := none
  for layer in layers do
    let h := layer.h
    let cy := y + Float.ofNat h / 2.0
    let kind := layer.kind
    if kind == .floor then floorCy := some cy
    match layer.peers with
    | some (left, right) =>
      let mid := (BAND_X0 + BAND_X1) / 2.0
      body := body ++ peerBand logos left BAND_X0 (mid - PEER_GAP / 2.0) y h kind
      body := body ++ peerBand logos right (mid + PEER_GAP / 2.0) BAND_X1 y h kind
    | none =>
      body := body ++ bandRect BAND_X0 BAND_X1 y h kind
      body := body ++ logoSlot logos layer.logo LOGO_X0 (LOGO_X0 + LOGO_W / 2.0) cy LOGO_W
      let nameSize := if kind == .floor then 18 else 19
      let (nameY, roleY) := if kind == .floor then (cy - 14, cy + 8) else (cy - 4, cy + 17)
      body := body ++ s!"<text x=\"{TEXT_X}\" y=\"{f1 nameY}\" font-size=\"{nameSize}\" font-weight=\"700\" fill=\"{BLACK}\">{escape layer.name}</text>"
      body := body ++ roleText layer.role (Float.ofNat TEXT_X) roleY
    let chip := layer.chip
    let first := cy - Float.ofNat (chip.length - 1) * 7.5 + 5
    body := body ++ tspans chip CHIP_X first 14 (if kind == .floor then BLACK else GRAY5) 15
    y := y + Float.ofNat h + 5.0
  let bottom := y - 5.0
  let height := bottom + 4.0
  match logos "kernel-arena-banner.jpg", floorCy with
  | some _, some fcy =>
    let bw : Float := 132.0; let bh : Float := 72.0
    let bx := BAND_X1 - bw - 14; let yb := fcy - bh / 2.0
    body := body ++ s!"<clipPath id=\"cake-arenaclip\"><rect x=\"{f1 bx}\" y=\"{f1 yb}\" width=\"132.0\" height=\"72.0\" rx=\"5\"/></clipPath>"
    let arena := dataUri logos "kernel-arena-banner.jpg"
    body := body ++ s!"<image href=\"{arena}\" x=\"{f1 bx}\" y=\"{f1 yb}\" width=\"132.0\" height=\"72.0\" preserveAspectRatio=\"xMidYMid slice\" clip-path=\"url(#cake-arenaclip)\"/>"
    body := body ++ s!"<rect x=\"{f1 bx}\" y=\"{f1 yb}\" width=\"132.0\" height=\"72.0\" rx=\"5\" fill=\"none\" stroke=\"{GRAY3}\" stroke-width=\"1\"/>"
  | _, _ => pure ()
  body := body ++ s!"<defs><marker id=\"cake-arrow\" viewBox=\"0 0 10 10\" refX=\"9\" refY=\"5\" markerWidth=\"6\" markerHeight=\"6\" orient=\"auto-start-reverse\"><path d=\"M 0 0 L 10 5 L 0 10 z\" fill=\"{RED}\"/></marker></defs>"
  body := body ++ s!"<line x1=\"{RAIL_X}\" y1=\"20\" x2=\"{RAIL_X}\" y2=\"{f1 (bottom - 8)}\" stroke=\"{RED}\" stroke-width=\"2\" marker-end=\"url(#cake-arrow)\"/>"
  body := body ++ s!"<text transform=\"translate({RAIL_X - 8},{f1 (bottom / 2)}) rotate(-90)\" text-anchor=\"middle\" font-size=\"13\" font-weight=\"700\" fill=\"{RED}\" letter-spacing=\"1.6\">TRACEABLE DOWN TO</text>"
  let head :=
    s!"<svg xmlns=\"http://www.w3.org/2000/svg\" xmlns:xlink=\"http://www.w3.org/1999/xlink\" viewBox=\"0 0 {W} {fmtFixed 0 height}\" font-family=\"Helvetica Neue, Helvetica, Arial, sans-serif\">" ++
    s!"<rect width=\"{W}\" height=\"{fmtFixed 0 height}\" fill=\"#FFFFFF\"/>"
  return head ++ body ++ "</svg>"

/-- The logo sources every cake needs. -/
public def requiredLogos : List String := ["torchlean-logo.png", "floatlib-logo.png", "physlib-logo.png"]

end Tools.Figures.Cake
