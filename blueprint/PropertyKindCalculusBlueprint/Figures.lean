/-
# The figures: schematics inlined, captioned, numbered, listed, and cross-referenced

Three figures in this document are schematics rather than harvests: the architecture cake
(the stack a model's trust traces down through), Lowe's square labelled with the calculus's
identifiers, and the three layers a capstone is stated over. Each is emitted as SVG by a
generator under `scripts/figures/` into `figures/`, from where this module reads it at
compile time.

`:::svg_figure "key" Figures.constant` inlines the SVG with the directive's body under it:
the first paragraph is the caption — one sentence naming the figure, which is what the list
of figures shows — and any further paragraphs are the legend, rendered under the figure
only. The traversal gives the figure an anchor (`#figure-key`), records it under the
`figure` domain, and appends it to the figure registry in the traversal state; the HTML
render numbers it from that registry — *Figure n* in document order — so the number is never
typed by an author. `:::figure_list` renders the registry as the list of figures, each entry
linking to its figure and naming the section it sits in; `{figref "key"}[]` renders *Figure n*
as a link wherever the prose refers to a figure. The mechanism is the one Verso's own index
uses (`{index}` / `{theIndex}`): entries are saved during traversal, the table is assembled
from the state at render time.

Why a file and not a drawing: the generators carry raster logos and typographic detail
Illuminate does not express, and the same SVG is committed beside the JPL Gen-AI deck,
which the generator writes with `--out`. Why inline and not an `<img>`: the multi-page site
nests chapters two directories deep, so one relative path cannot resolve on every page,
and the single page has no directory at all.

`include_str` reads a figure when *this* module compiles, and Lake's trace does not see the
file: regenerating a figure does not rebuild this module on its own, which is why
`scripts/make-figures.sh` removes this module's build products after writing a changed
figure, and why `scripts/ci-pages.sh` runs `make-figures.sh --check` before a render.
-/

import VersoManual
import VersoBlueprint

open Lean Elab
open Verso Doc Elab ArgParse
open Verso.Genre (Manual)
open Verso.Genre.Manual
open Verso.Multi
open Verso.Output (Html)

namespace PropertyKindCalculusBlueprint

/-! ## The figures, as strings -/

namespace Figures

/-- The architecture cake, blueprint audience: `tools/Tools/Figures/Cake.lean` (`lake exe blueprint-figures`). -/
def architectureCake : String := include_str "../figures/architecture-cake.svg"

/-- Lowe's square with the calculus's identifiers: `tools/Tools/Figures/Lowe.lean` (`lake exe blueprint-figures`). -/
def loweSquare : String := include_str "../figures/lowe-square-pkc.svg"

/-- The three layers and their two ladders: `tools/Tools/Figures/ThreeLayers.lean` (`lake exe blueprint-figures`). -/
def threeLayers : String := include_str "../figures/three-layers-pkc.svg"

end Figures

/-! ## The figure registry

One entry per figure, saved into the traversal state under `figuresState` and read back at
render time. The block's internal id orders the registry as the document does: ids are
handed out in document order on the first traversal pass, which is also what Verso's own
index relies on. -/

/-- One figure, as the traversal records it. -/
structure FigureEntry where
  /-- The author's key, `"architecture-cake"`: the anchor is `figure-<key>`. -/
  key : String
  /-- The figure block's internal id, which orders the registry. -/
  id : InternalId
  /-- The caption, as the inlines of the directive's body. -/
  caption : Array (Verso.Doc.Inline Manual)
  /-- The enclosing section's number, `"2.3."`, once the traversal has assigned it. -/
  sectionNumber : Option String
  /-- The enclosing section's title (its short title when it has one). -/
  sectionTitle : String
deriving ToJson, FromJson

/-- The traversal-state slot the registry lives in. -/
def figuresState : Name := `PropertyKindCalculusBlueprint.figures

@[grind =]
theorem figuresState.isPublic : NameMap.isPublic figuresState := by grind [figuresState]

/-- The cross-reference domain figures are registered under, one object per key. -/
def figureDomain : Name := `PropertyKindCalculusBlueprint.figure

/-- The registry, in document order; empty before any figure has been traversed. -/
def registeredFigures (st : TraverseState) : Except String (Array FigureEntry) :=
  match st.get? figuresState with
  | none => .ok #[]
  | some (.error e) => .error e
  | some (.ok (xs : Array FigureEntry)) => .ok (xs.qsort fun a b => a.id < b.id)

/-- The one-based number of the figure registered under `key`, in document order. -/
def figureNumber (figs : Array FigureEntry) (key : String) : Option Nat :=
  figs.findIdx? (·.key == key) |>.map (· + 1)

/-- The caption proper is the directive's first paragraph: one sentence that names the figure,
which is what the list of figures shows. Any further paragraphs are the legend, rendered
under the figure only. -/
def captionOf (content : Array (Verso.Doc.Block Manual)) : Array (Verso.Doc.Inline Manual) :=
  match content[0]? with
  | some (Verso.Doc.Block.para inls) => inls
  | _ => #[]

/-- The legend: every block of the directive's body after the caption paragraph. -/
def legendOf (content : Array (Verso.Doc.Block Manual)) : Array (Verso.Doc.Block Manual) :=
  content.extract 1 content.size

/-- The section number of the traversal context, as the headings print it (`"2.3."`).
`TraverseContext.sectionNumber` includes the unnumbered root header, which would make every
section read as unnumbered; the root is dropped here, as Verso's own section registration
drops it. -/
def sectionNumberOf (ctxt : TraverseContext) : Option String :=
  let nums := (ctxt.headers[1:]).toArray.map fun (h : PartHeader) =>
    h.metadata.bind (·.assignedNumber)
  nums.mapM id |>.map sectionNumberString

/-- Record a figure in the registry, replacing an earlier record under the same key so that
repeated traversal passes converge. -/
def registerFigure (entry : FigureEntry) :
    ReaderT TraverseContext (StateT TraverseState (BuildLogT IO)) Unit := do
  let cur : Option (Except String (Array FigureEntry)) := (← get).get? figuresState
  match cur with
  | some (.error e) => reportError e
  | some (.ok xs) =>
    let xs := (xs.filter (·.key != entry.key)).push entry
    modify (·.set figuresState xs)
  | none => modify (·.set figuresState #[entry])

/-! ## The figure block -/

/-- Styling for a captioned figure and for the list of figures. -/
def figureCss : String := r##"
figure.pkc-figure {
  margin: 1.5rem 0;
}
figure.pkc-figure .diagram {
  margin: 0 auto;
}
figure.pkc-figure figcaption {
  margin-top: 0.6rem;
  font-size: 0.92em;
  line-height: 1.45;
}
figure.pkc-figure figcaption p {
  margin: 0.3rem 0;
}
.figure-label {
  font-weight: bold;
}
ol.figure-list {
  list-style: none;
  padding-left: 0;
}
ol.figure-list > li {
  margin-bottom: 0.7rem;
}
ol.figure-list .figure-where {
  opacity: 0.7;
  font-size: 0.9em;
}
"##

block_extension Block.figure (key : String) (svg : String) (cssWidth : String)
    (texWidth : String) where
  data := Json.arr #[.str key, .str svg, .str cssWidth, .str texWidth]
  extraCss := [figureCss]
  traverse id data content := do
    let .arr #[.str key, _, _, _] := data
      | reportError "Expected four-element JSON for figure"; return none
    let ctxt ← read
    let _ ← externalTag id ctxt.path s!"figure-{key}"
    modify fun st => st.saveDomainObject figureDomain key id |>.setDomainTitle figureDomain "Figures"
    -- A figure in the root part, above the first chapter, sits in the introduction; naming the
    -- whole document's title there would tell a reader nothing.
    let sectionTitle :=
      if ctxt.headers.size ≤ 1 then "the introduction"
      else
        ctxt.headers.back?.map (fun h => h.metadata.bind (·.shortTitle) |>.getD h.titleString)
          |>.getD ""
    registerFigure {
      key, id,
      caption := captionOf content,
      sectionNumber := sectionNumberOf ctxt,
      sectionTitle
    }
    pure none
  toHtml :=
    open Verso.Output.Html Doc.Html HtmlT in
    some <| fun goI goB id data content => do
      let .arr #[.str key, .str svg, .str css, _] := data
        | reportError "Expected four-element JSON for figure" *> pure .empty
      let st ← state
      let number ←
        match registeredFigures st with
        | .error e => reportError e; pure none
        | .ok figs => pure (figureNumber figs key)
      let label := number.map (s!"Figure {·}.") |>.getD "Figure."
      let caption ← (captionOf content).mapM goI
      let legend ← (legendOf content).mapM goB
      let attrs := #[("class", "pkc-figure")] ++ st.htmlId id
      pure <| .tag "figure" attrs {{
        <div class="diagram" style={{s!"width: {css}"}}>{{Html.text false svg}}</div>
        <figcaption>
          <p class="figure-caption"><span class="figure-label">{{Html.text true label}}</span> " " {{caption}}</p>
          {{legend}}
        </figcaption>
      }}
  usePackages := ["\\usepackage{svg}"]
  toTeX :=
    some <| fun goI goB _ data content => do
      let .arr #[.str key, .str svg, _, .str tex] := data
        | reportError "Expected four-element JSON for figure" *> pure .empty
      let filename ← modifyGet fun s =>
        let fn := extraFileName s.extraFiles s!"figure-{key}" "svg" svg
        (fn, { s with extraFiles := s.extraFiles.insert fn svg })
      let caption ← (captionOf content).mapM goI
      let legend ← (legendOf content).mapM goB
      pure <| .seq #[
        .raw s!"\\begin\{figure}[htbp]\\centering\\includesvg[width={tex}]\{{filename}}\\caption\{",
        .seq caption,
        .raw s!"}\\label\{figure-{key}}\n",
        .seq legend,
        .raw "\\end{figure}\n"]

/-! ## The list of figures -/

block_extension Block.figureList where
  traverse _ _ _ := pure none
  toHtml :=
    open Verso.Output.Html Doc.Html HtmlT in
    some <| fun goI _ _ _ _ => do
      let st ← state
      match registeredFigures st with
      | .error e => reportError e; pure .empty
      | .ok figs =>
        let items ← figs.mapIdxM fun i f => do
          let caption ← f.caption.mapM goI
          let label := Html.text true s!"Figure {i + 1}."
          let label ←
            match st.externalTags[f.id]? with
            | some dest => pure {{<a href={{dest.link}}>{{label}}</a>}}
            | none => reportError s!"No link target for figure '{f.key}'"; pure label
          let «where» := f.sectionNumber.map (· ++ " ") |>.getD ""
          pure {{
            <li>
              <span class="figure-label">{{label}}</span> " " {{caption}} " "
              <span class="figure-where">{{Html.text true s!"— in {«where»}{f.sectionTitle}"}}</span>
            </li>
          }}
        pure {{<ol class="figure-list">{{items}}</ol>}}
  toTeX :=
    some <| fun _ _ _ _ _ => pure (.raw "\\listoffigures\n")

/-! ## The `figref` role -/

private structure FigRefInfo where
  key : String
  dest : Option Link := none
deriving ToJson, FromJson

inline_extension Inline.figref (key : String) (dest : Option Link := none) where
  data := ToJson.toJson (FigRefInfo.mk key dest)
  traverse _ data _content := do
    match FromJson.fromJson? (α := FigRefInfo) data with
    | .error e => reportError e; pure none
    | .ok { key, dest := none } =>
      match (← get).resolveDomainObject figureDomain key with
      | .error _ => pure none
      | .ok dest => pure (some (.other (Inline.figref key (some dest)) #[]))
    | .ok { dest := some _, .. } => pure none
  toHtml :=
    open Verso.Output.Html Doc.Html HtmlT in
    some <| fun _goI _ data _content => do
      match FromJson.fromJson? (α := FigRefInfo) data with
      | .error e => reportError e; pure .empty
      | .ok { key, dest := none } =>
        reportError s!"No figure is registered under '{key}'"
        pure (Html.text true "Figure ?")
      | .ok { key, dest := some dest } =>
        let st ← state
        let number := (registeredFigures st).toOption.bind (figureNumber · key)
        let txt := number.map (s!"Figure {·}") |>.getD "the figure"
        pure {{<a href={{dest.link}} class="figref">{{Html.text true txt}}</a>}}
  toTeX :=
    some <| fun _ _ data _ => do
      match FromJson.fromJson? (α := FigRefInfo) data with
      | .error e => reportError e; pure .empty
      | .ok { key, .. } => pure (.raw s!"Figure~\\ref\{figure-{key}}")

structure FigRefArgs where
  key : String

section
variable [Monad m] [MonadError m]

def FigRefArgs.parse : ArgParse m FigRefArgs :=
  FigRefArgs.mk <$> .positional `key ValDesc.string

instance : FromArgs FigRefArgs m := ⟨FigRefArgs.parse⟩
end

/-- `{figref "key"}[]` renders *Figure n*, linked to the figure registered under `key`. The
number comes from the registry, so it follows the figure wherever the document moves it. -/
@[role]
def figref : RoleExpanderOf FigRefArgs
  | { key }, _content =>
    ``(Verso.Doc.Inline.other (Inline.figref $(quote key) none) #[])

/-! ## The directives -/

structure FigureConfig where
  /-- The figure's key: its anchor is `figure-<key>`, and `{figref "<key>"}[]` refers to it. -/
  key : String
  /-- The name of the `String` constant holding the SVG. -/
  figure : Ident
  /-- The CSS width of the inlined figure; `100%` when omitted. -/
  cssWidth : Option String
  /-- The LaTeX width of the included figure; `\textwidth` when omitted. -/
  texWidth : Option String

section
variable [Monad m] [MonadError m] [MonadInfoTree m] [MonadLiftT CoreM m] [MonadEnv m]
  [MonadFileMap m]

def FigureConfig.parse : ArgParse m FigureConfig :=
  FigureConfig.mk <$> .positional `key ValDesc.string
    <*> .positional `figure ValDesc.ident
    <*> .named' `cssWidth true
    <*> .named' `texWidth true

instance : FromArgs FigureConfig m := ⟨FigureConfig.parse⟩
end

unsafe def evalSvgUnsafe (stx : Syntax) : TermElabM String :=
  Term.evalTerm String (mkConst ``String) stx

@[implemented_by evalSvgUnsafe]
opaque evalSvg (stx : Syntax) : TermElabM String

/-- `:::svg_figure "three-layers" PropertyKindCalculusBlueprint.Figures.threeLayers` inlines the
SVG the named `String` constant holds, with the directive's body as its caption: the figure
is numbered in document order, anchored at `figure-three-layers`, listed by `:::figure_list`,
and referred to by `{figref "three-layers"}[]`. Optional `(cssWidth := "…")` and
`(texWidth := "…")` as for the `diagram` code block. A figure without a caption is refused:
the list of figures would have nothing to say about it. -/
@[directive]
def svg_figure : DirectiveExpanderOf FigureConfig
  | cfg, contents => do
    if contents.isEmpty then
      throwError "svg_figure \"{cfg.key}\": a figure needs a caption in the directive's body"
    let svg ← evalSvg cfg.figure
    let css := cfg.cssWidth.getD "100%"
    let tex := cfg.texWidth.getD "\\textwidth"
    let caption ← contents.mapM elabBlock
    ``(Verso.Doc.Block.other
        (Block.figure $(quote cfg.key) $(quote svg) $(quote css) $(quote tex)) #[$caption,*])

/-- The `figure_list` directive takes no arguments. -/
structure FigureListConfig where
  deriving Inhabited

section
variable [Monad m] [MonadError m]

def FigureListConfig.parse : ArgParse m FigureListConfig := pure {}

instance : FromArgs FigureListConfig m := ⟨FigureListConfig.parse⟩
end

/-- `:::figure_list` renders the list of figures: every `svg_figure` in the document, numbered
in document order, each linked to its figure and naming the section it sits in. Contents are
ignored. -/
@[directive]
def figure_list : DirectiveExpanderOf FigureListConfig
  | _, _contents =>
    ``(Verso.Doc.Block.other Block.figureList #[])

end PropertyKindCalculusBlueprint
