module

/-!
# `blueprint-print`: the print pass of the blueprint's PDF

    lake exe blueprint-print HTML_INPUT OUT_HTML
    lean --run tools/Tools/BlueprintPrint.lean HTML_INPUT OUT_HTML

Everything `html-to-pdf.py` did before handing a page to WeasyPrint, text to text:
`HTML_INPUT` is the self-contained single page (`html-single/index.html`, Verso's document
order) or a multi-page site directory, whose chapter and section pages are ordered by the
numbered table of contents. Each page is read by a tokenizer with the behaviour of Python's
`html.parser` as the Python used it — names lowercased, attributes re-serialized as
`k="v"` with their character references decoded, text with its references decoded,
comments and the doctype dropped, `<script>`/`<style>` content raw — and, unlike the Python,
every decoded text and attribute value is escaped again on the way out (`escapeText`,
`escapeAttr`: a decoded `&lt;i&gt;` in a code span would otherwise reach WeasyPrint as a tag
and vanish from the PDF; `escapeList_no_markup` is the guarantee) — the web-only chrome
is pruned structurally (`shouldDrop`), each page becomes a `<section class="chapter">`,
the heading outline is checked (`checkLevels`, reported on stderr) and renumbered to a
skip-free tree (`renumberLevels`), and the print CSS is added. The page written to
`OUT_HTML` is what shell then gives WeasyPrint (`render-pdf.sh`), the rendering edge that
stays.

`renumberLevels_idem` and `checkLevels_renumber` are the pass's theorems: renumbering is
idempotent and its output passes the nesting check. The whole pass is deliberately *not*
idempotent — it wraps each page in a `<section class="chapter">` and adds the CSS, so a
second application would wrap again; it is applied once, to Verso's output.

The input is bytes throughout (15 MB for the blueprint): every byte of markup is ASCII, and
the rest is copied as it is.
-/

namespace Tools.BlueprintPrint

/-! ## The heading outline, as a list of levels -/

/-- Pop the ancestor stack down to the nearest strictly shallower heading. -/
def popGe (lvl : Nat) : List Nat → List Nat
  | [] => []
  | t :: rest => if t ≥ lvl then popGe lvl rest else t :: rest

/-- Each opening heading becomes one deeper than its nearest shallower ancestor; `ctx` is the
stack of open ancestors, top first. -/
def renumberFrom (ctx : List Nat) : List Nat → List Nat
  | [] => []
  | lvl :: rest =>
    let ctx' := lvl :: popGe lvl ctx
    ctx'.length :: renumberFrom ctx' rest

def renumberLevels (ls : List Nat) : List Nat := renumberFrom [] ls

/-- The headings `renumberLevels` would change: `(index, source level, assigned level)`. -/
def checkFrom (ctx : List Nat) (i : Nat) : List Nat → List (Nat × Nat × Nat)
  | [] => []
  | lvl :: rest =>
    let ctx' := lvl :: popGe lvl ctx
    let a := ctx'.length
    (if a != lvl then [(i, lvl, a)] else []) ++ checkFrom ctx' (i + 1) rest

def checkLevels (ls : List Nat) : List (Nat × Nat × Nat) := checkFrom [] 0 ls

/-- The stack `[k, k-1, …, 1]`. -/
def desc : Nat → List Nat
  | 0 => []
  | n + 1 => (n + 1) :: desc n

theorem desc_length (k : Nat) : (desc k).length = k := by
  induction k with
  | zero => rfl
  | succ n ih => simp [desc, ih]

theorem popGe_length_le (lvl : Nat) (c : List Nat) : (popGe lvl c).length ≤ c.length := by
  induction c with
  | nil => simp [popGe]
  | cons t r ih => simp only [popGe]; split <;> simp <;> omega

theorem popGe_desc (a k : Nat) (ha : 1 ≤ a) (hk : a ≤ k + 1) :
    popGe a (desc k) = desc (a - 1) := by
  induction k with
  | zero =>
    have : a = 1 := by omega
    subst this; rfl
  | succ n ih =>
    simp only [desc, popGe]
    split
    · exact ih (by omega)
    · have : a = n + 2 := by omega
      subst this; simp [desc]

/-- Both passes at once: on the output of a pass whose stack has length `k`, a second pass's
stack is `desc k`, and it assigns every level to itself. -/
theorem renumberFrom_desc (ls : List Nat) : ∀ (i : Nat) (ctx : List Nat),
    renumberFrom (desc ctx.length) (renumberFrom ctx ls) = renumberFrom ctx ls ∧
    checkFrom (desc ctx.length) i (renumberFrom ctx ls) = [] := by
  induction ls with
  | nil => intro i ctx; exact ⟨rfl, rfl⟩
  | cons lvl rest ih =>
    intro i ctx
    simp only [renumberFrom, checkFrom]
    have hlen : (lvl :: popGe lvl ctx).length ≤ ctx.length + 1 := by
      simp only [List.length_cons]; have := popGe_length_le lvl ctx; omega
    have hpop : popGe (lvl :: popGe lvl ctx).length (desc ctx.length) =
        desc ((lvl :: popGe lvl ctx).length - 1) :=
      popGe_desc _ _ (by simp) hlen
    have hdesc : ((lvl :: popGe lvl ctx).length :: desc ((lvl :: popGe lvl ctx).length - 1)) =
        desc (lvl :: popGe lvl ctx).length := by
      simp only [List.length_cons, Nat.add_sub_cancel]; rfl
    rw [hpop, hdesc]
    have ih' := ih (i + 1) (lvl :: popGe lvl ctx)
    refine ⟨?_, ?_⟩
    · rw [desc_length, ih'.1]
    · rw [desc_length]; have h2 := ih'.2; simp only [List.length_cons] at h2 ⊢; simp [h2]

theorem renumberLevels_idem (ls : List Nat) :
    renumberLevels (renumberLevels ls) = renumberLevels ls :=
  (renumberFrom_desc ls 0 []).1

theorem checkLevels_renumber (ls : List Nat) : checkLevels (renumberLevels ls) = [] :=
  (renumberFrom_desc ls 0 []).2

/-! ## Bytes -/

abbrev B := ByteArray

@[inline] def at? (b : B) (i : Nat) : UInt8 := if h : i < b.size then b[i] else 0
def isAlpha (c : UInt8) : Bool := (65 ≤ c && c ≤ 90) || (97 ≤ c && c ≤ 122)
def isDigit (c : UInt8) : Bool := 48 ≤ c && c ≤ 57
def isWord (c : UInt8) : Bool := isAlpha c || isDigit c || c == 95
def isWs (c : UInt8) : Bool := c == 32 || c == 9 || c == 10 || c == 13 || c == 12
def lower (c : UInt8) : UInt8 := if 65 ≤ c && c ≤ 90 then c + 32 else c
def LT : UInt8 := 60
def GT : UInt8 := 62
def SLASH : UInt8 := 47
def AMP : UInt8 := 38
def DQ : UInt8 := 34
def SQ : UInt8 := 39
def EQ : UInt8 := 61

def str (s : String) : B := s.toUTF8

def lowerBytes (b : B) : B := Id.run do
  let mut out := ByteArray.emptyWithCapacity b.size
  for c in b do out := out.push (lower c)
  return out

/-- A dotted section number without its leading and trailing dots. -/
def stripDots (n : String) : String :=
  String.ofList (((n.toList.dropWhile (· == '.')).reverse.dropWhile (· == '.')).reverse)
instance : Append B := ⟨ByteArray.append⟩

/-- `lit` (ASCII) occurs at `i`. -/
def startsAt (b : B) (i : Nat) (lit : String) : Bool :=
  let l := lit.toUTF8
  i + l.size ≤ b.size && (List.range l.size).all fun k => b[i + k]! == l[k]!

/-- Case-insensitive `startsAt` (`lit` lowercase ASCII). -/
def startsAtCI (b : B) (i : Nat) (lit : String) : Bool :=
  let l := lit.toUTF8
  i + l.size ≤ b.size && (List.range l.size).all fun k => lower b[i + k]! == l[k]!

/-- Position of the first occurrence of `lit` at or after `i`. -/
partial def findFrom (b : B) (i : Nat) (lit : String) : Option Nat :=
  if i + lit.utf8ByteSize > b.size then none
  else if startsAt b i lit then some i else findFrom b (i + 1) lit

def slice (b : B) (i j : Nat) : B := b.extract i j

def toStr (b : B) : String := String.fromUTF8! b

/-- Python's `html.entities.html5`: every named character reference, the legacy ones also without
their semicolon, as `html.unescape` resolves them. Generated from CPython's table. -/
def html5_0 : Array (String × String) := #[
  ("AElig", "Æ"),
  ("AElig;", "Æ"),
  ("AMP", "&"),
  ("AMP;", "&"),
  ("Aacute", "Á"),
  ("Aacute;", "Á"),
  ("Abreve;", "Ă"),
  ("Acirc", "Â"),
  ("Acirc;", "Â"),
  ("Acy;", "А"),
  ("Afr;", "𝔄"),
  ("Agrave", "À"),
  ("Agrave;", "À"),
  ("Alpha;", "Α"),
  ("Amacr;", "Ā"),
  ("And;", "⩓"),
  ("Aogon;", "Ą"),
  ("Aopf;", "𝔸"),
  ("ApplyFunction;", "⁡"),
  ("Aring", "Å"),
  ("Aring;", "Å"),
  ("Ascr;", "𝒜"),
  ("Assign;", "≔"),
  ("Atilde", "Ã"),
  ("Atilde;", "Ã"),
  ("Auml", "Ä"),
  ("Auml;", "Ä"),
  ("Backslash;", "∖"),
  ("Barv;", "⫧"),
  ("Barwed;", "⌆"),
  ("Bcy;", "Б"),
  ("Because;", "∵"),
  ("Bernoullis;", "ℬ"),
  ("Beta;", "Β"),
  ("Bfr;", "𝔅"),
  ("Bopf;", "𝔹"),
  ("Breve;", "˘"),
  ("Bscr;", "ℬ"),
  ("Bumpeq;", "≎"),
  ("CHcy;", "Ч"),
  ("COPY", "©"),
  ("COPY;", "©"),
  ("Cacute;", "Ć"),
  ("Cap;", "⋒"),
  ("CapitalDifferentialD;", "ⅅ"),
  ("Cayleys;", "ℭ"),
  ("Ccaron;", "Č"),
  ("Ccedil", "Ç"),
  ("Ccedil;", "Ç"),
  ("Ccirc;", "Ĉ"),
  ("Cconint;", "∰"),
  ("Cdot;", "Ċ"),
  ("Cedilla;", "¸"),
  ("CenterDot;", "·"),
  ("Cfr;", "ℭ"),
  ("Chi;", "Χ"),
  ("CircleDot;", "⊙"),
  ("CircleMinus;", "⊖"),
  ("CirclePlus;", "⊕"),
  ("CircleTimes;", "⊗"),
  ("ClockwiseContourIntegral;", "∲"),
  ("CloseCurlyDoubleQuote;", "”"),
  ("CloseCurlyQuote;", "’"),
  ("Colon;", "∷"),
  ("Colone;", "⩴"),
  ("Congruent;", "≡"),
  ("Conint;", "∯"),
  ("ContourIntegral;", "∮"),
  ("Copf;", "ℂ"),
  ("Coproduct;", "∐"),
  ("CounterClockwiseContourIntegral;", "∳"),
  ("Cross;", "⨯"),
  ("Cscr;", "𝒞"),
  ("Cup;", "⋓"),
  ("CupCap;", "≍"),
  ("DD;", "ⅅ"),
  ("DDotrahd;", "⤑"),
  ("DJcy;", "Ђ"),
  ("DScy;", "Ѕ"),
  ("DZcy;", "Џ"),
  ("Dagger;", "‡"),
  ("Darr;", "↡"),
  ("Dashv;", "⫤"),
  ("Dcaron;", "Ď"),
  ("Dcy;", "Д"),
  ("Del;", "∇"),
  ("Delta;", "Δ"),
  ("Dfr;", "𝔇"),
  ("DiacriticalAcute;", "´"),
  ("DiacriticalDot;", "˙"),
  ("DiacriticalDoubleAcute;", "˝"),
  ("DiacriticalGrave;", "`"),
  ("DiacriticalTilde;", "˜"),
  ("Diamond;", "⋄"),
  ("DifferentialD;", "ⅆ"),
  ("Dopf;", "𝔻"),
  ("Dot;", "¨"),
  ("DotDot;", "⃜"),
  ("DotEqual;", "≐"),
  ("DoubleContourIntegral;", "∯"),
  ("DoubleDot;", "¨"),
  ("DoubleDownArrow;", "⇓"),
  ("DoubleLeftArrow;", "⇐"),
  ("DoubleLeftRightArrow;", "⇔"),
  ("DoubleLeftTee;", "⫤"),
  ("DoubleLongLeftArrow;", "⟸"),
  ("DoubleLongLeftRightArrow;", "⟺"),
  ("DoubleLongRightArrow;", "⟹"),
  ("DoubleRightArrow;", "⇒"),
  ("DoubleRightTee;", "⊨"),
  ("DoubleUpArrow;", "⇑"),
  ("DoubleUpDownArrow;", "⇕"),
  ("DoubleVerticalBar;", "∥"),
  ("DownArrow;", "↓"),
  ("DownArrowBar;", "⤓"),
  ("DownArrowUpArrow;", "⇵"),
  ("DownBreve;", "̑"),
  ("DownLeftRightVector;", "⥐"),
  ("DownLeftTeeVector;", "⥞"),
  ("DownLeftVector;", "↽"),
  ("DownLeftVectorBar;", "⥖"),
  ("DownRightTeeVector;", "⥟"),
  ("DownRightVector;", "⇁"),
  ("DownRightVectorBar;", "⥗"),
  ("DownTee;", "⊤"),
  ("DownTeeArrow;", "↧"),
  ("Downarrow;", "⇓"),
  ("Dscr;", "𝒟"),
  ("Dstrok;", "Đ"),
  ("ENG;", "Ŋ"),
  ("ETH", "Ð"),
  ("ETH;", "Ð"),
  ("Eacute", "É"),
  ("Eacute;", "É"),
  ("Ecaron;", "Ě"),
  ("Ecirc", "Ê"),
  ("Ecirc;", "Ê"),
  ("Ecy;", "Э"),
  ("Edot;", "Ė"),
  ("Efr;", "𝔈"),
  ("Egrave", "È"),
  ("Egrave;", "È"),
  ("Element;", "∈"),
  ("Emacr;", "Ē"),
  ("EmptySmallSquare;", "◻"),
  ("EmptyVerySmallSquare;", "▫"),
  ("Eogon;", "Ę"),
  ("Eopf;", "𝔼"),
  ("Epsilon;", "Ε"),
  ("Equal;", "⩵"),
  ("EqualTilde;", "≂"),
  ("Equilibrium;", "⇌"),
  ("Escr;", "ℰ"),
  ("Esim;", "⩳"),
  ("Eta;", "Η"),
  ("Euml", "Ë"),
  ("Euml;", "Ë"),
  ("Exists;", "∃"),
  ("ExponentialE;", "ⅇ"),
  ("Fcy;", "Ф"),
  ("Ffr;", "𝔉"),
  ("FilledSmallSquare;", "◼"),
  ("FilledVerySmallSquare;", "▪"),
  ("Fopf;", "𝔽"),
  ("ForAll;", "∀"),
  ("Fouriertrf;", "ℱ"),
  ("Fscr;", "ℱ"),
  ("GJcy;", "Ѓ"),
  ("GT", ">"),
  ("GT;", ">"),
  ("Gamma;", "Γ"),
  ("Gammad;", "Ϝ"),
  ("Gbreve;", "Ğ"),
  ("Gcedil;", "Ģ"),
  ("Gcirc;", "Ĝ"),
  ("Gcy;", "Г"),
  ("Gdot;", "Ġ"),
  ("Gfr;", "𝔊"),
  ("Gg;", "⋙"),
  ("Gopf;", "𝔾"),
  ("GreaterEqual;", "≥"),
  ("GreaterEqualLess;", "⋛"),
  ("GreaterFullEqual;", "≧"),
  ("GreaterGreater;", "⪢"),
  ("GreaterLess;", "≷"),
  ("GreaterSlantEqual;", "⩾"),
  ("GreaterTilde;", "≳"),
  ("Gscr;", "𝒢"),
  ("Gt;", "≫"),
  ("HARDcy;", "Ъ"),
  ("Hacek;", "ˇ"),
  ("Hat;", "^"),
  ("Hcirc;", "Ĥ"),
  ("Hfr;", "ℌ"),
  ("HilbertSpace;", "ℋ"),
  ("Hopf;", "ℍ"),
  ("HorizontalLine;", "─"),
  ("Hscr;", "ℋ"),
  ("Hstrok;", "Ħ"),
  ("HumpDownHump;", "≎")
]

def html5_1 : Array (String × String) := #[
  ("HumpEqual;", "≏"),
  ("IEcy;", "Е"),
  ("IJlig;", "Ĳ"),
  ("IOcy;", "Ё"),
  ("Iacute", "Í"),
  ("Iacute;", "Í"),
  ("Icirc", "Î"),
  ("Icirc;", "Î"),
  ("Icy;", "И"),
  ("Idot;", "İ"),
  ("Ifr;", "ℑ"),
  ("Igrave", "Ì"),
  ("Igrave;", "Ì"),
  ("Im;", "ℑ"),
  ("Imacr;", "Ī"),
  ("ImaginaryI;", "ⅈ"),
  ("Implies;", "⇒"),
  ("Int;", "∬"),
  ("Integral;", "∫"),
  ("Intersection;", "⋂"),
  ("InvisibleComma;", "⁣"),
  ("InvisibleTimes;", "⁢"),
  ("Iogon;", "Į"),
  ("Iopf;", "𝕀"),
  ("Iota;", "Ι"),
  ("Iscr;", "ℐ"),
  ("Itilde;", "Ĩ"),
  ("Iukcy;", "І"),
  ("Iuml", "Ï"),
  ("Iuml;", "Ï"),
  ("Jcirc;", "Ĵ"),
  ("Jcy;", "Й"),
  ("Jfr;", "𝔍"),
  ("Jopf;", "𝕁"),
  ("Jscr;", "𝒥"),
  ("Jsercy;", "Ј"),
  ("Jukcy;", "Є"),
  ("KHcy;", "Х"),
  ("KJcy;", "Ќ"),
  ("Kappa;", "Κ"),
  ("Kcedil;", "Ķ"),
  ("Kcy;", "К"),
  ("Kfr;", "𝔎"),
  ("Kopf;", "𝕂"),
  ("Kscr;", "𝒦"),
  ("LJcy;", "Љ"),
  ("LT", "<"),
  ("LT;", "<"),
  ("Lacute;", "Ĺ"),
  ("Lambda;", "Λ"),
  ("Lang;", "⟪"),
  ("Laplacetrf;", "ℒ"),
  ("Larr;", "↞"),
  ("Lcaron;", "Ľ"),
  ("Lcedil;", "Ļ"),
  ("Lcy;", "Л"),
  ("LeftAngleBracket;", "⟨"),
  ("LeftArrow;", "←"),
  ("LeftArrowBar;", "⇤"),
  ("LeftArrowRightArrow;", "⇆"),
  ("LeftCeiling;", "⌈"),
  ("LeftDoubleBracket;", "⟦"),
  ("LeftDownTeeVector;", "⥡"),
  ("LeftDownVector;", "⇃"),
  ("LeftDownVectorBar;", "⥙"),
  ("LeftFloor;", "⌊"),
  ("LeftRightArrow;", "↔"),
  ("LeftRightVector;", "⥎"),
  ("LeftTee;", "⊣"),
  ("LeftTeeArrow;", "↤"),
  ("LeftTeeVector;", "⥚"),
  ("LeftTriangle;", "⊲"),
  ("LeftTriangleBar;", "⧏"),
  ("LeftTriangleEqual;", "⊴"),
  ("LeftUpDownVector;", "⥑"),
  ("LeftUpTeeVector;", "⥠"),
  ("LeftUpVector;", "↿"),
  ("LeftUpVectorBar;", "⥘"),
  ("LeftVector;", "↼"),
  ("LeftVectorBar;", "⥒"),
  ("Leftarrow;", "⇐"),
  ("Leftrightarrow;", "⇔"),
  ("LessEqualGreater;", "⋚"),
  ("LessFullEqual;", "≦"),
  ("LessGreater;", "≶"),
  ("LessLess;", "⪡"),
  ("LessSlantEqual;", "⩽"),
  ("LessTilde;", "≲"),
  ("Lfr;", "𝔏"),
  ("Ll;", "⋘"),
  ("Lleftarrow;", "⇚"),
  ("Lmidot;", "Ŀ"),
  ("LongLeftArrow;", "⟵"),
  ("LongLeftRightArrow;", "⟷"),
  ("LongRightArrow;", "⟶"),
  ("Longleftarrow;", "⟸"),
  ("Longleftrightarrow;", "⟺"),
  ("Longrightarrow;", "⟹"),
  ("Lopf;", "𝕃"),
  ("LowerLeftArrow;", "↙"),
  ("LowerRightArrow;", "↘"),
  ("Lscr;", "ℒ"),
  ("Lsh;", "↰"),
  ("Lstrok;", "Ł"),
  ("Lt;", "≪"),
  ("Map;", "⤅"),
  ("Mcy;", "М"),
  ("MediumSpace;", " "),
  ("Mellintrf;", "ℳ"),
  ("Mfr;", "𝔐"),
  ("MinusPlus;", "∓"),
  ("Mopf;", "𝕄"),
  ("Mscr;", "ℳ"),
  ("Mu;", "Μ"),
  ("NJcy;", "Њ"),
  ("Nacute;", "Ń"),
  ("Ncaron;", "Ň"),
  ("Ncedil;", "Ņ"),
  ("Ncy;", "Н"),
  ("NegativeMediumSpace;", "​"),
  ("NegativeThickSpace;", "​"),
  ("NegativeThinSpace;", "​"),
  ("NegativeVeryThinSpace;", "​"),
  ("NestedGreaterGreater;", "≫"),
  ("NestedLessLess;", "≪"),
  ("NewLine;", "\n"),
  ("Nfr;", "𝔑"),
  ("NoBreak;", "⁠"),
  ("NonBreakingSpace;", " "),
  ("Nopf;", "ℕ"),
  ("Not;", "⫬"),
  ("NotCongruent;", "≢"),
  ("NotCupCap;", "≭"),
  ("NotDoubleVerticalBar;", "∦"),
  ("NotElement;", "∉"),
  ("NotEqual;", "≠"),
  ("NotEqualTilde;", "≂̸"),
  ("NotExists;", "∄"),
  ("NotGreater;", "≯"),
  ("NotGreaterEqual;", "≱"),
  ("NotGreaterFullEqual;", "≧̸"),
  ("NotGreaterGreater;", "≫̸"),
  ("NotGreaterLess;", "≹"),
  ("NotGreaterSlantEqual;", "⩾̸"),
  ("NotGreaterTilde;", "≵"),
  ("NotHumpDownHump;", "≎̸"),
  ("NotHumpEqual;", "≏̸"),
  ("NotLeftTriangle;", "⋪"),
  ("NotLeftTriangleBar;", "⧏̸"),
  ("NotLeftTriangleEqual;", "⋬"),
  ("NotLess;", "≮"),
  ("NotLessEqual;", "≰"),
  ("NotLessGreater;", "≸"),
  ("NotLessLess;", "≪̸"),
  ("NotLessSlantEqual;", "⩽̸"),
  ("NotLessTilde;", "≴"),
  ("NotNestedGreaterGreater;", "⪢̸"),
  ("NotNestedLessLess;", "⪡̸"),
  ("NotPrecedes;", "⊀"),
  ("NotPrecedesEqual;", "⪯̸"),
  ("NotPrecedesSlantEqual;", "⋠"),
  ("NotReverseElement;", "∌"),
  ("NotRightTriangle;", "⋫"),
  ("NotRightTriangleBar;", "⧐̸"),
  ("NotRightTriangleEqual;", "⋭"),
  ("NotSquareSubset;", "⊏̸"),
  ("NotSquareSubsetEqual;", "⋢"),
  ("NotSquareSuperset;", "⊐̸"),
  ("NotSquareSupersetEqual;", "⋣"),
  ("NotSubset;", "⊂⃒"),
  ("NotSubsetEqual;", "⊈"),
  ("NotSucceeds;", "⊁"),
  ("NotSucceedsEqual;", "⪰̸"),
  ("NotSucceedsSlantEqual;", "⋡"),
  ("NotSucceedsTilde;", "≿̸"),
  ("NotSuperset;", "⊃⃒"),
  ("NotSupersetEqual;", "⊉"),
  ("NotTilde;", "≁"),
  ("NotTildeEqual;", "≄"),
  ("NotTildeFullEqual;", "≇"),
  ("NotTildeTilde;", "≉"),
  ("NotVerticalBar;", "∤"),
  ("Nscr;", "𝒩"),
  ("Ntilde", "Ñ"),
  ("Ntilde;", "Ñ"),
  ("Nu;", "Ν"),
  ("OElig;", "Œ"),
  ("Oacute", "Ó"),
  ("Oacute;", "Ó"),
  ("Ocirc", "Ô"),
  ("Ocirc;", "Ô"),
  ("Ocy;", "О"),
  ("Odblac;", "Ő"),
  ("Ofr;", "𝔒"),
  ("Ograve", "Ò"),
  ("Ograve;", "Ò"),
  ("Omacr;", "Ō"),
  ("Omega;", "Ω"),
  ("Omicron;", "Ο"),
  ("Oopf;", "𝕆")
]

def html5_2 : Array (String × String) := #[
  ("OpenCurlyDoubleQuote;", "“"),
  ("OpenCurlyQuote;", "‘"),
  ("Or;", "⩔"),
  ("Oscr;", "𝒪"),
  ("Oslash", "Ø"),
  ("Oslash;", "Ø"),
  ("Otilde", "Õ"),
  ("Otilde;", "Õ"),
  ("Otimes;", "⨷"),
  ("Ouml", "Ö"),
  ("Ouml;", "Ö"),
  ("OverBar;", "‾"),
  ("OverBrace;", "⏞"),
  ("OverBracket;", "⎴"),
  ("OverParenthesis;", "⏜"),
  ("PartialD;", "∂"),
  ("Pcy;", "П"),
  ("Pfr;", "𝔓"),
  ("Phi;", "Φ"),
  ("Pi;", "Π"),
  ("PlusMinus;", "±"),
  ("Poincareplane;", "ℌ"),
  ("Popf;", "ℙ"),
  ("Pr;", "⪻"),
  ("Precedes;", "≺"),
  ("PrecedesEqual;", "⪯"),
  ("PrecedesSlantEqual;", "≼"),
  ("PrecedesTilde;", "≾"),
  ("Prime;", "″"),
  ("Product;", "∏"),
  ("Proportion;", "∷"),
  ("Proportional;", "∝"),
  ("Pscr;", "𝒫"),
  ("Psi;", "Ψ"),
  ("QUOT", "\""),
  ("QUOT;", "\""),
  ("Qfr;", "𝔔"),
  ("Qopf;", "ℚ"),
  ("Qscr;", "𝒬"),
  ("RBarr;", "⤐"),
  ("REG", "®"),
  ("REG;", "®"),
  ("Racute;", "Ŕ"),
  ("Rang;", "⟫"),
  ("Rarr;", "↠"),
  ("Rarrtl;", "⤖"),
  ("Rcaron;", "Ř"),
  ("Rcedil;", "Ŗ"),
  ("Rcy;", "Р"),
  ("Re;", "ℜ"),
  ("ReverseElement;", "∋"),
  ("ReverseEquilibrium;", "⇋"),
  ("ReverseUpEquilibrium;", "⥯"),
  ("Rfr;", "ℜ"),
  ("Rho;", "Ρ"),
  ("RightAngleBracket;", "⟩"),
  ("RightArrow;", "→"),
  ("RightArrowBar;", "⇥"),
  ("RightArrowLeftArrow;", "⇄"),
  ("RightCeiling;", "⌉"),
  ("RightDoubleBracket;", "⟧"),
  ("RightDownTeeVector;", "⥝"),
  ("RightDownVector;", "⇂"),
  ("RightDownVectorBar;", "⥕"),
  ("RightFloor;", "⌋"),
  ("RightTee;", "⊢"),
  ("RightTeeArrow;", "↦"),
  ("RightTeeVector;", "⥛"),
  ("RightTriangle;", "⊳"),
  ("RightTriangleBar;", "⧐"),
  ("RightTriangleEqual;", "⊵"),
  ("RightUpDownVector;", "⥏"),
  ("RightUpTeeVector;", "⥜"),
  ("RightUpVector;", "↾"),
  ("RightUpVectorBar;", "⥔"),
  ("RightVector;", "⇀"),
  ("RightVectorBar;", "⥓"),
  ("Rightarrow;", "⇒"),
  ("Ropf;", "ℝ"),
  ("RoundImplies;", "⥰"),
  ("Rrightarrow;", "⇛"),
  ("Rscr;", "ℛ"),
  ("Rsh;", "↱"),
  ("RuleDelayed;", "⧴"),
  ("SHCHcy;", "Щ"),
  ("SHcy;", "Ш"),
  ("SOFTcy;", "Ь"),
  ("Sacute;", "Ś"),
  ("Sc;", "⪼"),
  ("Scaron;", "Š"),
  ("Scedil;", "Ş"),
  ("Scirc;", "Ŝ"),
  ("Scy;", "С"),
  ("Sfr;", "𝔖"),
  ("ShortDownArrow;", "↓"),
  ("ShortLeftArrow;", "←"),
  ("ShortRightArrow;", "→"),
  ("ShortUpArrow;", "↑"),
  ("Sigma;", "Σ"),
  ("SmallCircle;", "∘"),
  ("Sopf;", "𝕊"),
  ("Sqrt;", "√"),
  ("Square;", "□"),
  ("SquareIntersection;", "⊓"),
  ("SquareSubset;", "⊏"),
  ("SquareSubsetEqual;", "⊑"),
  ("SquareSuperset;", "⊐"),
  ("SquareSupersetEqual;", "⊒"),
  ("SquareUnion;", "⊔"),
  ("Sscr;", "𝒮"),
  ("Star;", "⋆"),
  ("Sub;", "⋐"),
  ("Subset;", "⋐"),
  ("SubsetEqual;", "⊆"),
  ("Succeeds;", "≻"),
  ("SucceedsEqual;", "⪰"),
  ("SucceedsSlantEqual;", "≽"),
  ("SucceedsTilde;", "≿"),
  ("SuchThat;", "∋"),
  ("Sum;", "∑"),
  ("Sup;", "⋑"),
  ("Superset;", "⊃"),
  ("SupersetEqual;", "⊇"),
  ("Supset;", "⋑"),
  ("THORN", "Þ"),
  ("THORN;", "Þ"),
  ("TRADE;", "™"),
  ("TSHcy;", "Ћ"),
  ("TScy;", "Ц"),
  ("Tab;", "\t"),
  ("Tau;", "Τ"),
  ("Tcaron;", "Ť"),
  ("Tcedil;", "Ţ"),
  ("Tcy;", "Т"),
  ("Tfr;", "𝔗"),
  ("Therefore;", "∴"),
  ("Theta;", "Θ"),
  ("ThickSpace;", "  "),
  ("ThinSpace;", " "),
  ("Tilde;", "∼"),
  ("TildeEqual;", "≃"),
  ("TildeFullEqual;", "≅"),
  ("TildeTilde;", "≈"),
  ("Topf;", "𝕋"),
  ("TripleDot;", "⃛"),
  ("Tscr;", "𝒯"),
  ("Tstrok;", "Ŧ"),
  ("Uacute", "Ú"),
  ("Uacute;", "Ú"),
  ("Uarr;", "↟"),
  ("Uarrocir;", "⥉"),
  ("Ubrcy;", "Ў"),
  ("Ubreve;", "Ŭ"),
  ("Ucirc", "Û"),
  ("Ucirc;", "Û"),
  ("Ucy;", "У"),
  ("Udblac;", "Ű"),
  ("Ufr;", "𝔘"),
  ("Ugrave", "Ù"),
  ("Ugrave;", "Ù"),
  ("Umacr;", "Ū"),
  ("UnderBar;", "_"),
  ("UnderBrace;", "⏟"),
  ("UnderBracket;", "⎵"),
  ("UnderParenthesis;", "⏝"),
  ("Union;", "⋃"),
  ("UnionPlus;", "⊎"),
  ("Uogon;", "Ų"),
  ("Uopf;", "𝕌"),
  ("UpArrow;", "↑"),
  ("UpArrowBar;", "⤒"),
  ("UpArrowDownArrow;", "⇅"),
  ("UpDownArrow;", "↕"),
  ("UpEquilibrium;", "⥮"),
  ("UpTee;", "⊥"),
  ("UpTeeArrow;", "↥"),
  ("Uparrow;", "⇑"),
  ("Updownarrow;", "⇕"),
  ("UpperLeftArrow;", "↖"),
  ("UpperRightArrow;", "↗"),
  ("Upsi;", "ϒ"),
  ("Upsilon;", "Υ"),
  ("Uring;", "Ů"),
  ("Uscr;", "𝒰"),
  ("Utilde;", "Ũ"),
  ("Uuml", "Ü"),
  ("Uuml;", "Ü"),
  ("VDash;", "⊫"),
  ("Vbar;", "⫫"),
  ("Vcy;", "В"),
  ("Vdash;", "⊩"),
  ("Vdashl;", "⫦"),
  ("Vee;", "⋁"),
  ("Verbar;", "‖"),
  ("Vert;", "‖"),
  ("VerticalBar;", "∣"),
  ("VerticalLine;", "|"),
  ("VerticalSeparator;", "❘"),
  ("VerticalTilde;", "≀"),
  ("VeryThinSpace;", " ")
]

def html5_3 : Array (String × String) := #[
  ("Vfr;", "𝔙"),
  ("Vopf;", "𝕍"),
  ("Vscr;", "𝒱"),
  ("Vvdash;", "⊪"),
  ("Wcirc;", "Ŵ"),
  ("Wedge;", "⋀"),
  ("Wfr;", "𝔚"),
  ("Wopf;", "𝕎"),
  ("Wscr;", "𝒲"),
  ("Xfr;", "𝔛"),
  ("Xi;", "Ξ"),
  ("Xopf;", "𝕏"),
  ("Xscr;", "𝒳"),
  ("YAcy;", "Я"),
  ("YIcy;", "Ї"),
  ("YUcy;", "Ю"),
  ("Yacute", "Ý"),
  ("Yacute;", "Ý"),
  ("Ycirc;", "Ŷ"),
  ("Ycy;", "Ы"),
  ("Yfr;", "𝔜"),
  ("Yopf;", "𝕐"),
  ("Yscr;", "𝒴"),
  ("Yuml;", "Ÿ"),
  ("ZHcy;", "Ж"),
  ("Zacute;", "Ź"),
  ("Zcaron;", "Ž"),
  ("Zcy;", "З"),
  ("Zdot;", "Ż"),
  ("ZeroWidthSpace;", "​"),
  ("Zeta;", "Ζ"),
  ("Zfr;", "ℨ"),
  ("Zopf;", "ℤ"),
  ("Zscr;", "𝒵"),
  ("aacute", "á"),
  ("aacute;", "á"),
  ("abreve;", "ă"),
  ("ac;", "∾"),
  ("acE;", "∾̳"),
  ("acd;", "∿"),
  ("acirc", "â"),
  ("acirc;", "â"),
  ("acute", "´"),
  ("acute;", "´"),
  ("acy;", "а"),
  ("aelig", "æ"),
  ("aelig;", "æ"),
  ("af;", "⁡"),
  ("afr;", "𝔞"),
  ("agrave", "à"),
  ("agrave;", "à"),
  ("alefsym;", "ℵ"),
  ("aleph;", "ℵ"),
  ("alpha;", "α"),
  ("amacr;", "ā"),
  ("amalg;", "⨿"),
  ("amp", "&"),
  ("amp;", "&"),
  ("and;", "∧"),
  ("andand;", "⩕"),
  ("andd;", "⩜"),
  ("andslope;", "⩘"),
  ("andv;", "⩚"),
  ("ang;", "∠"),
  ("ange;", "⦤"),
  ("angle;", "∠"),
  ("angmsd;", "∡"),
  ("angmsdaa;", "⦨"),
  ("angmsdab;", "⦩"),
  ("angmsdac;", "⦪"),
  ("angmsdad;", "⦫"),
  ("angmsdae;", "⦬"),
  ("angmsdaf;", "⦭"),
  ("angmsdag;", "⦮"),
  ("angmsdah;", "⦯"),
  ("angrt;", "∟"),
  ("angrtvb;", "⊾"),
  ("angrtvbd;", "⦝"),
  ("angsph;", "∢"),
  ("angst;", "Å"),
  ("angzarr;", "⍼"),
  ("aogon;", "ą"),
  ("aopf;", "𝕒"),
  ("ap;", "≈"),
  ("apE;", "⩰"),
  ("apacir;", "⩯"),
  ("ape;", "≊"),
  ("apid;", "≋"),
  ("apos;", "'"),
  ("approx;", "≈"),
  ("approxeq;", "≊"),
  ("aring", "å"),
  ("aring;", "å"),
  ("ascr;", "𝒶"),
  ("ast;", "*"),
  ("asymp;", "≈"),
  ("asympeq;", "≍"),
  ("atilde", "ã"),
  ("atilde;", "ã"),
  ("auml", "ä"),
  ("auml;", "ä"),
  ("awconint;", "∳"),
  ("awint;", "⨑"),
  ("bNot;", "⫭"),
  ("backcong;", "≌"),
  ("backepsilon;", "϶"),
  ("backprime;", "‵"),
  ("backsim;", "∽"),
  ("backsimeq;", "⋍"),
  ("barvee;", "⊽"),
  ("barwed;", "⌅"),
  ("barwedge;", "⌅"),
  ("bbrk;", "⎵"),
  ("bbrktbrk;", "⎶"),
  ("bcong;", "≌"),
  ("bcy;", "б"),
  ("bdquo;", "„"),
  ("becaus;", "∵"),
  ("because;", "∵"),
  ("bemptyv;", "⦰"),
  ("bepsi;", "϶"),
  ("bernou;", "ℬ"),
  ("beta;", "β"),
  ("beth;", "ℶ"),
  ("between;", "≬"),
  ("bfr;", "𝔟"),
  ("bigcap;", "⋂"),
  ("bigcirc;", "◯"),
  ("bigcup;", "⋃"),
  ("bigodot;", "⨀"),
  ("bigoplus;", "⨁"),
  ("bigotimes;", "⨂"),
  ("bigsqcup;", "⨆"),
  ("bigstar;", "★"),
  ("bigtriangledown;", "▽"),
  ("bigtriangleup;", "△"),
  ("biguplus;", "⨄"),
  ("bigvee;", "⋁"),
  ("bigwedge;", "⋀"),
  ("bkarow;", "⤍"),
  ("blacklozenge;", "⧫"),
  ("blacksquare;", "▪"),
  ("blacktriangle;", "▴"),
  ("blacktriangledown;", "▾"),
  ("blacktriangleleft;", "◂"),
  ("blacktriangleright;", "▸"),
  ("blank;", "␣"),
  ("blk12;", "▒"),
  ("blk14;", "░"),
  ("blk34;", "▓"),
  ("block;", "█"),
  ("bne;", "=⃥"),
  ("bnequiv;", "≡⃥"),
  ("bnot;", "⌐"),
  ("bopf;", "𝕓"),
  ("bot;", "⊥"),
  ("bottom;", "⊥"),
  ("bowtie;", "⋈"),
  ("boxDL;", "╗"),
  ("boxDR;", "╔"),
  ("boxDl;", "╖"),
  ("boxDr;", "╓"),
  ("boxH;", "═"),
  ("boxHD;", "╦"),
  ("boxHU;", "╩"),
  ("boxHd;", "╤"),
  ("boxHu;", "╧"),
  ("boxUL;", "╝"),
  ("boxUR;", "╚"),
  ("boxUl;", "╜"),
  ("boxUr;", "╙"),
  ("boxV;", "║"),
  ("boxVH;", "╬"),
  ("boxVL;", "╣"),
  ("boxVR;", "╠"),
  ("boxVh;", "╫"),
  ("boxVl;", "╢"),
  ("boxVr;", "╟"),
  ("boxbox;", "⧉"),
  ("boxdL;", "╕"),
  ("boxdR;", "╒"),
  ("boxdl;", "┐"),
  ("boxdr;", "┌"),
  ("boxh;", "─"),
  ("boxhD;", "╥"),
  ("boxhU;", "╨"),
  ("boxhd;", "┬"),
  ("boxhu;", "┴"),
  ("boxminus;", "⊟"),
  ("boxplus;", "⊞"),
  ("boxtimes;", "⊠"),
  ("boxuL;", "╛"),
  ("boxuR;", "╘"),
  ("boxul;", "┘"),
  ("boxur;", "└"),
  ("boxv;", "│"),
  ("boxvH;", "╪"),
  ("boxvL;", "╡"),
  ("boxvR;", "╞"),
  ("boxvh;", "┼")
]

def html5_4 : Array (String × String) := #[
  ("boxvl;", "┤"),
  ("boxvr;", "├"),
  ("bprime;", "‵"),
  ("breve;", "˘"),
  ("brvbar", "¦"),
  ("brvbar;", "¦"),
  ("bscr;", "𝒷"),
  ("bsemi;", "⁏"),
  ("bsim;", "∽"),
  ("bsime;", "⋍"),
  ("bsol;", "\\"),
  ("bsolb;", "⧅"),
  ("bsolhsub;", "⟈"),
  ("bull;", "•"),
  ("bullet;", "•"),
  ("bump;", "≎"),
  ("bumpE;", "⪮"),
  ("bumpe;", "≏"),
  ("bumpeq;", "≏"),
  ("cacute;", "ć"),
  ("cap;", "∩"),
  ("capand;", "⩄"),
  ("capbrcup;", "⩉"),
  ("capcap;", "⩋"),
  ("capcup;", "⩇"),
  ("capdot;", "⩀"),
  ("caps;", "∩︀"),
  ("caret;", "⁁"),
  ("caron;", "ˇ"),
  ("ccaps;", "⩍"),
  ("ccaron;", "č"),
  ("ccedil", "ç"),
  ("ccedil;", "ç"),
  ("ccirc;", "ĉ"),
  ("ccups;", "⩌"),
  ("ccupssm;", "⩐"),
  ("cdot;", "ċ"),
  ("cedil", "¸"),
  ("cedil;", "¸"),
  ("cemptyv;", "⦲"),
  ("cent", "¢"),
  ("cent;", "¢"),
  ("centerdot;", "·"),
  ("cfr;", "𝔠"),
  ("chcy;", "ч"),
  ("check;", "✓"),
  ("checkmark;", "✓"),
  ("chi;", "χ"),
  ("cir;", "○"),
  ("cirE;", "⧃"),
  ("circ;", "ˆ"),
  ("circeq;", "≗"),
  ("circlearrowleft;", "↺"),
  ("circlearrowright;", "↻"),
  ("circledR;", "®"),
  ("circledS;", "Ⓢ"),
  ("circledast;", "⊛"),
  ("circledcirc;", "⊚"),
  ("circleddash;", "⊝"),
  ("cire;", "≗"),
  ("cirfnint;", "⨐"),
  ("cirmid;", "⫯"),
  ("cirscir;", "⧂"),
  ("clubs;", "♣"),
  ("clubsuit;", "♣"),
  ("colon;", ":"),
  ("colone;", "≔"),
  ("coloneq;", "≔"),
  ("comma;", ","),
  ("commat;", "@"),
  ("comp;", "∁"),
  ("compfn;", "∘"),
  ("complement;", "∁"),
  ("complexes;", "ℂ"),
  ("cong;", "≅"),
  ("congdot;", "⩭"),
  ("conint;", "∮"),
  ("copf;", "𝕔"),
  ("coprod;", "∐"),
  ("copy", "©"),
  ("copy;", "©"),
  ("copysr;", "℗"),
  ("crarr;", "↵"),
  ("cross;", "✗"),
  ("cscr;", "𝒸"),
  ("csub;", "⫏"),
  ("csube;", "⫑"),
  ("csup;", "⫐"),
  ("csupe;", "⫒"),
  ("ctdot;", "⋯"),
  ("cudarrl;", "⤸"),
  ("cudarrr;", "⤵"),
  ("cuepr;", "⋞"),
  ("cuesc;", "⋟"),
  ("cularr;", "↶"),
  ("cularrp;", "⤽"),
  ("cup;", "∪"),
  ("cupbrcap;", "⩈"),
  ("cupcap;", "⩆"),
  ("cupcup;", "⩊"),
  ("cupdot;", "⊍"),
  ("cupor;", "⩅"),
  ("cups;", "∪︀"),
  ("curarr;", "↷"),
  ("curarrm;", "⤼"),
  ("curlyeqprec;", "⋞"),
  ("curlyeqsucc;", "⋟"),
  ("curlyvee;", "⋎"),
  ("curlywedge;", "⋏"),
  ("curren", "¤"),
  ("curren;", "¤"),
  ("curvearrowleft;", "↶"),
  ("curvearrowright;", "↷"),
  ("cuvee;", "⋎"),
  ("cuwed;", "⋏"),
  ("cwconint;", "∲"),
  ("cwint;", "∱"),
  ("cylcty;", "⌭"),
  ("dArr;", "⇓"),
  ("dHar;", "⥥"),
  ("dagger;", "†"),
  ("daleth;", "ℸ"),
  ("darr;", "↓"),
  ("dash;", "‐"),
  ("dashv;", "⊣"),
  ("dbkarow;", "⤏"),
  ("dblac;", "˝"),
  ("dcaron;", "ď"),
  ("dcy;", "д"),
  ("dd;", "ⅆ"),
  ("ddagger;", "‡"),
  ("ddarr;", "⇊"),
  ("ddotseq;", "⩷"),
  ("deg", "°"),
  ("deg;", "°"),
  ("delta;", "δ"),
  ("demptyv;", "⦱"),
  ("dfisht;", "⥿"),
  ("dfr;", "𝔡"),
  ("dharl;", "⇃"),
  ("dharr;", "⇂"),
  ("diam;", "⋄"),
  ("diamond;", "⋄"),
  ("diamondsuit;", "♦"),
  ("diams;", "♦"),
  ("die;", "¨"),
  ("digamma;", "ϝ"),
  ("disin;", "⋲"),
  ("div;", "÷"),
  ("divide", "÷"),
  ("divide;", "÷"),
  ("divideontimes;", "⋇"),
  ("divonx;", "⋇"),
  ("djcy;", "ђ"),
  ("dlcorn;", "⌞"),
  ("dlcrop;", "⌍"),
  ("dollar;", "$"),
  ("dopf;", "𝕕"),
  ("dot;", "˙"),
  ("doteq;", "≐"),
  ("doteqdot;", "≑"),
  ("dotminus;", "∸"),
  ("dotplus;", "∔"),
  ("dotsquare;", "⊡"),
  ("doublebarwedge;", "⌆"),
  ("downarrow;", "↓"),
  ("downdownarrows;", "⇊"),
  ("downharpoonleft;", "⇃"),
  ("downharpoonright;", "⇂"),
  ("drbkarow;", "⤐"),
  ("drcorn;", "⌟"),
  ("drcrop;", "⌌"),
  ("dscr;", "𝒹"),
  ("dscy;", "ѕ"),
  ("dsol;", "⧶"),
  ("dstrok;", "đ"),
  ("dtdot;", "⋱"),
  ("dtri;", "▿"),
  ("dtrif;", "▾"),
  ("duarr;", "⇵"),
  ("duhar;", "⥯"),
  ("dwangle;", "⦦"),
  ("dzcy;", "џ"),
  ("dzigrarr;", "⟿"),
  ("eDDot;", "⩷"),
  ("eDot;", "≑"),
  ("eacute", "é"),
  ("eacute;", "é"),
  ("easter;", "⩮"),
  ("ecaron;", "ě"),
  ("ecir;", "≖"),
  ("ecirc", "ê"),
  ("ecirc;", "ê"),
  ("ecolon;", "≕"),
  ("ecy;", "э"),
  ("edot;", "ė"),
  ("ee;", "ⅇ"),
  ("efDot;", "≒"),
  ("efr;", "𝔢"),
  ("eg;", "⪚")
]

def html5_5 : Array (String × String) := #[
  ("egrave", "è"),
  ("egrave;", "è"),
  ("egs;", "⪖"),
  ("egsdot;", "⪘"),
  ("el;", "⪙"),
  ("elinters;", "⏧"),
  ("ell;", "ℓ"),
  ("els;", "⪕"),
  ("elsdot;", "⪗"),
  ("emacr;", "ē"),
  ("empty;", "∅"),
  ("emptyset;", "∅"),
  ("emptyv;", "∅"),
  ("emsp13;", " "),
  ("emsp14;", " "),
  ("emsp;", " "),
  ("eng;", "ŋ"),
  ("ensp;", " "),
  ("eogon;", "ę"),
  ("eopf;", "𝕖"),
  ("epar;", "⋕"),
  ("eparsl;", "⧣"),
  ("eplus;", "⩱"),
  ("epsi;", "ε"),
  ("epsilon;", "ε"),
  ("epsiv;", "ϵ"),
  ("eqcirc;", "≖"),
  ("eqcolon;", "≕"),
  ("eqsim;", "≂"),
  ("eqslantgtr;", "⪖"),
  ("eqslantless;", "⪕"),
  ("equals;", "="),
  ("equest;", "≟"),
  ("equiv;", "≡"),
  ("equivDD;", "⩸"),
  ("eqvparsl;", "⧥"),
  ("erDot;", "≓"),
  ("erarr;", "⥱"),
  ("escr;", "ℯ"),
  ("esdot;", "≐"),
  ("esim;", "≂"),
  ("eta;", "η"),
  ("eth", "ð"),
  ("eth;", "ð"),
  ("euml", "ë"),
  ("euml;", "ë"),
  ("euro;", "€"),
  ("excl;", "!"),
  ("exist;", "∃"),
  ("expectation;", "ℰ"),
  ("exponentiale;", "ⅇ"),
  ("fallingdotseq;", "≒"),
  ("fcy;", "ф"),
  ("female;", "♀"),
  ("ffilig;", "ﬃ"),
  ("fflig;", "ﬀ"),
  ("ffllig;", "ﬄ"),
  ("ffr;", "𝔣"),
  ("filig;", "ﬁ"),
  ("fjlig;", "fj"),
  ("flat;", "♭"),
  ("fllig;", "ﬂ"),
  ("fltns;", "▱"),
  ("fnof;", "ƒ"),
  ("fopf;", "𝕗"),
  ("forall;", "∀"),
  ("fork;", "⋔"),
  ("forkv;", "⫙"),
  ("fpartint;", "⨍"),
  ("frac12", "½"),
  ("frac12;", "½"),
  ("frac13;", "⅓"),
  ("frac14", "¼"),
  ("frac14;", "¼"),
  ("frac15;", "⅕"),
  ("frac16;", "⅙"),
  ("frac18;", "⅛"),
  ("frac23;", "⅔"),
  ("frac25;", "⅖"),
  ("frac34", "¾"),
  ("frac34;", "¾"),
  ("frac35;", "⅗"),
  ("frac38;", "⅜"),
  ("frac45;", "⅘"),
  ("frac56;", "⅚"),
  ("frac58;", "⅝"),
  ("frac78;", "⅞"),
  ("frasl;", "⁄"),
  ("frown;", "⌢"),
  ("fscr;", "𝒻"),
  ("gE;", "≧"),
  ("gEl;", "⪌"),
  ("gacute;", "ǵ"),
  ("gamma;", "γ"),
  ("gammad;", "ϝ"),
  ("gap;", "⪆"),
  ("gbreve;", "ğ"),
  ("gcirc;", "ĝ"),
  ("gcy;", "г"),
  ("gdot;", "ġ"),
  ("ge;", "≥"),
  ("gel;", "⋛"),
  ("geq;", "≥"),
  ("geqq;", "≧"),
  ("geqslant;", "⩾"),
  ("ges;", "⩾"),
  ("gescc;", "⪩"),
  ("gesdot;", "⪀"),
  ("gesdoto;", "⪂"),
  ("gesdotol;", "⪄"),
  ("gesl;", "⋛︀"),
  ("gesles;", "⪔"),
  ("gfr;", "𝔤"),
  ("gg;", "≫"),
  ("ggg;", "⋙"),
  ("gimel;", "ℷ"),
  ("gjcy;", "ѓ"),
  ("gl;", "≷"),
  ("glE;", "⪒"),
  ("gla;", "⪥"),
  ("glj;", "⪤"),
  ("gnE;", "≩"),
  ("gnap;", "⪊"),
  ("gnapprox;", "⪊"),
  ("gne;", "⪈"),
  ("gneq;", "⪈"),
  ("gneqq;", "≩"),
  ("gnsim;", "⋧"),
  ("gopf;", "𝕘"),
  ("grave;", "`"),
  ("gscr;", "ℊ"),
  ("gsim;", "≳"),
  ("gsime;", "⪎"),
  ("gsiml;", "⪐"),
  ("gt", ">"),
  ("gt;", ">"),
  ("gtcc;", "⪧"),
  ("gtcir;", "⩺"),
  ("gtdot;", "⋗"),
  ("gtlPar;", "⦕"),
  ("gtquest;", "⩼"),
  ("gtrapprox;", "⪆"),
  ("gtrarr;", "⥸"),
  ("gtrdot;", "⋗"),
  ("gtreqless;", "⋛"),
  ("gtreqqless;", "⪌"),
  ("gtrless;", "≷"),
  ("gtrsim;", "≳"),
  ("gvertneqq;", "≩︀"),
  ("gvnE;", "≩︀"),
  ("hArr;", "⇔"),
  ("hairsp;", " "),
  ("half;", "½"),
  ("hamilt;", "ℋ"),
  ("hardcy;", "ъ"),
  ("harr;", "↔"),
  ("harrcir;", "⥈"),
  ("harrw;", "↭"),
  ("hbar;", "ℏ"),
  ("hcirc;", "ĥ"),
  ("hearts;", "♥"),
  ("heartsuit;", "♥"),
  ("hellip;", "…"),
  ("hercon;", "⊹"),
  ("hfr;", "𝔥"),
  ("hksearow;", "⤥"),
  ("hkswarow;", "⤦"),
  ("hoarr;", "⇿"),
  ("homtht;", "∻"),
  ("hookleftarrow;", "↩"),
  ("hookrightarrow;", "↪"),
  ("hopf;", "𝕙"),
  ("horbar;", "―"),
  ("hscr;", "𝒽"),
  ("hslash;", "ℏ"),
  ("hstrok;", "ħ"),
  ("hybull;", "⁃"),
  ("hyphen;", "‐"),
  ("iacute", "í"),
  ("iacute;", "í"),
  ("ic;", "⁣"),
  ("icirc", "î"),
  ("icirc;", "î"),
  ("icy;", "и"),
  ("iecy;", "е"),
  ("iexcl", "¡"),
  ("iexcl;", "¡"),
  ("iff;", "⇔"),
  ("ifr;", "𝔦"),
  ("igrave", "ì"),
  ("igrave;", "ì"),
  ("ii;", "ⅈ"),
  ("iiiint;", "⨌"),
  ("iiint;", "∭"),
  ("iinfin;", "⧜"),
  ("iiota;", "℩"),
  ("ijlig;", "ĳ"),
  ("imacr;", "ī"),
  ("image;", "ℑ"),
  ("imagline;", "ℐ")
]

def html5_6 : Array (String × String) := #[
  ("imagpart;", "ℑ"),
  ("imath;", "ı"),
  ("imof;", "⊷"),
  ("imped;", "Ƶ"),
  ("in;", "∈"),
  ("incare;", "℅"),
  ("infin;", "∞"),
  ("infintie;", "⧝"),
  ("inodot;", "ı"),
  ("int;", "∫"),
  ("intcal;", "⊺"),
  ("integers;", "ℤ"),
  ("intercal;", "⊺"),
  ("intlarhk;", "⨗"),
  ("intprod;", "⨼"),
  ("iocy;", "ё"),
  ("iogon;", "į"),
  ("iopf;", "𝕚"),
  ("iota;", "ι"),
  ("iprod;", "⨼"),
  ("iquest", "¿"),
  ("iquest;", "¿"),
  ("iscr;", "𝒾"),
  ("isin;", "∈"),
  ("isinE;", "⋹"),
  ("isindot;", "⋵"),
  ("isins;", "⋴"),
  ("isinsv;", "⋳"),
  ("isinv;", "∈"),
  ("it;", "⁢"),
  ("itilde;", "ĩ"),
  ("iukcy;", "і"),
  ("iuml", "ï"),
  ("iuml;", "ï"),
  ("jcirc;", "ĵ"),
  ("jcy;", "й"),
  ("jfr;", "𝔧"),
  ("jmath;", "ȷ"),
  ("jopf;", "𝕛"),
  ("jscr;", "𝒿"),
  ("jsercy;", "ј"),
  ("jukcy;", "є"),
  ("kappa;", "κ"),
  ("kappav;", "ϰ"),
  ("kcedil;", "ķ"),
  ("kcy;", "к"),
  ("kfr;", "𝔨"),
  ("kgreen;", "ĸ"),
  ("khcy;", "х"),
  ("kjcy;", "ќ"),
  ("kopf;", "𝕜"),
  ("kscr;", "𝓀"),
  ("lAarr;", "⇚"),
  ("lArr;", "⇐"),
  ("lAtail;", "⤛"),
  ("lBarr;", "⤎"),
  ("lE;", "≦"),
  ("lEg;", "⪋"),
  ("lHar;", "⥢"),
  ("lacute;", "ĺ"),
  ("laemptyv;", "⦴"),
  ("lagran;", "ℒ"),
  ("lambda;", "λ"),
  ("lang;", "⟨"),
  ("langd;", "⦑"),
  ("langle;", "⟨"),
  ("lap;", "⪅"),
  ("laquo", "«"),
  ("laquo;", "«"),
  ("larr;", "←"),
  ("larrb;", "⇤"),
  ("larrbfs;", "⤟"),
  ("larrfs;", "⤝"),
  ("larrhk;", "↩"),
  ("larrlp;", "↫"),
  ("larrpl;", "⤹"),
  ("larrsim;", "⥳"),
  ("larrtl;", "↢"),
  ("lat;", "⪫"),
  ("latail;", "⤙"),
  ("late;", "⪭"),
  ("lates;", "⪭︀"),
  ("lbarr;", "⤌"),
  ("lbbrk;", "❲"),
  ("lbrace;", "{"),
  ("lbrack;", "["),
  ("lbrke;", "⦋"),
  ("lbrksld;", "⦏"),
  ("lbrkslu;", "⦍"),
  ("lcaron;", "ľ"),
  ("lcedil;", "ļ"),
  ("lceil;", "⌈"),
  ("lcub;", "{"),
  ("lcy;", "л"),
  ("ldca;", "⤶"),
  ("ldquo;", "“"),
  ("ldquor;", "„"),
  ("ldrdhar;", "⥧"),
  ("ldrushar;", "⥋"),
  ("ldsh;", "↲"),
  ("le;", "≤"),
  ("leftarrow;", "←"),
  ("leftarrowtail;", "↢"),
  ("leftharpoondown;", "↽"),
  ("leftharpoonup;", "↼"),
  ("leftleftarrows;", "⇇"),
  ("leftrightarrow;", "↔"),
  ("leftrightarrows;", "⇆"),
  ("leftrightharpoons;", "⇋"),
  ("leftrightsquigarrow;", "↭"),
  ("leftthreetimes;", "⋋"),
  ("leg;", "⋚"),
  ("leq;", "≤"),
  ("leqq;", "≦"),
  ("leqslant;", "⩽"),
  ("les;", "⩽"),
  ("lescc;", "⪨"),
  ("lesdot;", "⩿"),
  ("lesdoto;", "⪁"),
  ("lesdotor;", "⪃"),
  ("lesg;", "⋚︀"),
  ("lesges;", "⪓"),
  ("lessapprox;", "⪅"),
  ("lessdot;", "⋖"),
  ("lesseqgtr;", "⋚"),
  ("lesseqqgtr;", "⪋"),
  ("lessgtr;", "≶"),
  ("lesssim;", "≲"),
  ("lfisht;", "⥼"),
  ("lfloor;", "⌊"),
  ("lfr;", "𝔩"),
  ("lg;", "≶"),
  ("lgE;", "⪑"),
  ("lhard;", "↽"),
  ("lharu;", "↼"),
  ("lharul;", "⥪"),
  ("lhblk;", "▄"),
  ("ljcy;", "љ"),
  ("ll;", "≪"),
  ("llarr;", "⇇"),
  ("llcorner;", "⌞"),
  ("llhard;", "⥫"),
  ("lltri;", "◺"),
  ("lmidot;", "ŀ"),
  ("lmoust;", "⎰"),
  ("lmoustache;", "⎰"),
  ("lnE;", "≨"),
  ("lnap;", "⪉"),
  ("lnapprox;", "⪉"),
  ("lne;", "⪇"),
  ("lneq;", "⪇"),
  ("lneqq;", "≨"),
  ("lnsim;", "⋦"),
  ("loang;", "⟬"),
  ("loarr;", "⇽"),
  ("lobrk;", "⟦"),
  ("longleftarrow;", "⟵"),
  ("longleftrightarrow;", "⟷"),
  ("longmapsto;", "⟼"),
  ("longrightarrow;", "⟶"),
  ("looparrowleft;", "↫"),
  ("looparrowright;", "↬"),
  ("lopar;", "⦅"),
  ("lopf;", "𝕝"),
  ("loplus;", "⨭"),
  ("lotimes;", "⨴"),
  ("lowast;", "∗"),
  ("lowbar;", "_"),
  ("loz;", "◊"),
  ("lozenge;", "◊"),
  ("lozf;", "⧫"),
  ("lpar;", "("),
  ("lparlt;", "⦓"),
  ("lrarr;", "⇆"),
  ("lrcorner;", "⌟"),
  ("lrhar;", "⇋"),
  ("lrhard;", "⥭"),
  ("lrm;", "‎"),
  ("lrtri;", "⊿"),
  ("lsaquo;", "‹"),
  ("lscr;", "𝓁"),
  ("lsh;", "↰"),
  ("lsim;", "≲"),
  ("lsime;", "⪍"),
  ("lsimg;", "⪏"),
  ("lsqb;", "["),
  ("lsquo;", "‘"),
  ("lsquor;", "‚"),
  ("lstrok;", "ł"),
  ("lt", "<"),
  ("lt;", "<"),
  ("ltcc;", "⪦"),
  ("ltcir;", "⩹"),
  ("ltdot;", "⋖"),
  ("lthree;", "⋋"),
  ("ltimes;", "⋉"),
  ("ltlarr;", "⥶"),
  ("ltquest;", "⩻"),
  ("ltrPar;", "⦖"),
  ("ltri;", "◃")
]

def html5_7 : Array (String × String) := #[
  ("ltrie;", "⊴"),
  ("ltrif;", "◂"),
  ("lurdshar;", "⥊"),
  ("luruhar;", "⥦"),
  ("lvertneqq;", "≨︀"),
  ("lvnE;", "≨︀"),
  ("mDDot;", "∺"),
  ("macr", "¯"),
  ("macr;", "¯"),
  ("male;", "♂"),
  ("malt;", "✠"),
  ("maltese;", "✠"),
  ("map;", "↦"),
  ("mapsto;", "↦"),
  ("mapstodown;", "↧"),
  ("mapstoleft;", "↤"),
  ("mapstoup;", "↥"),
  ("marker;", "▮"),
  ("mcomma;", "⨩"),
  ("mcy;", "м"),
  ("mdash;", "—"),
  ("measuredangle;", "∡"),
  ("mfr;", "𝔪"),
  ("mho;", "℧"),
  ("micro", "µ"),
  ("micro;", "µ"),
  ("mid;", "∣"),
  ("midast;", "*"),
  ("midcir;", "⫰"),
  ("middot", "·"),
  ("middot;", "·"),
  ("minus;", "−"),
  ("minusb;", "⊟"),
  ("minusd;", "∸"),
  ("minusdu;", "⨪"),
  ("mlcp;", "⫛"),
  ("mldr;", "…"),
  ("mnplus;", "∓"),
  ("models;", "⊧"),
  ("mopf;", "𝕞"),
  ("mp;", "∓"),
  ("mscr;", "𝓂"),
  ("mstpos;", "∾"),
  ("mu;", "μ"),
  ("multimap;", "⊸"),
  ("mumap;", "⊸"),
  ("nGg;", "⋙̸"),
  ("nGt;", "≫⃒"),
  ("nGtv;", "≫̸"),
  ("nLeftarrow;", "⇍"),
  ("nLeftrightarrow;", "⇎"),
  ("nLl;", "⋘̸"),
  ("nLt;", "≪⃒"),
  ("nLtv;", "≪̸"),
  ("nRightarrow;", "⇏"),
  ("nVDash;", "⊯"),
  ("nVdash;", "⊮"),
  ("nabla;", "∇"),
  ("nacute;", "ń"),
  ("nang;", "∠⃒"),
  ("nap;", "≉"),
  ("napE;", "⩰̸"),
  ("napid;", "≋̸"),
  ("napos;", "ŉ"),
  ("napprox;", "≉"),
  ("natur;", "♮"),
  ("natural;", "♮"),
  ("naturals;", "ℕ"),
  ("nbsp", " "),
  ("nbsp;", " "),
  ("nbump;", "≎̸"),
  ("nbumpe;", "≏̸"),
  ("ncap;", "⩃"),
  ("ncaron;", "ň"),
  ("ncedil;", "ņ"),
  ("ncong;", "≇"),
  ("ncongdot;", "⩭̸"),
  ("ncup;", "⩂"),
  ("ncy;", "н"),
  ("ndash;", "–"),
  ("ne;", "≠"),
  ("neArr;", "⇗"),
  ("nearhk;", "⤤"),
  ("nearr;", "↗"),
  ("nearrow;", "↗"),
  ("nedot;", "≐̸"),
  ("nequiv;", "≢"),
  ("nesear;", "⤨"),
  ("nesim;", "≂̸"),
  ("nexist;", "∄"),
  ("nexists;", "∄"),
  ("nfr;", "𝔫"),
  ("ngE;", "≧̸"),
  ("nge;", "≱"),
  ("ngeq;", "≱"),
  ("ngeqq;", "≧̸"),
  ("ngeqslant;", "⩾̸"),
  ("nges;", "⩾̸"),
  ("ngsim;", "≵"),
  ("ngt;", "≯"),
  ("ngtr;", "≯"),
  ("nhArr;", "⇎"),
  ("nharr;", "↮"),
  ("nhpar;", "⫲"),
  ("ni;", "∋"),
  ("nis;", "⋼"),
  ("nisd;", "⋺"),
  ("niv;", "∋"),
  ("njcy;", "њ"),
  ("nlArr;", "⇍"),
  ("nlE;", "≦̸"),
  ("nlarr;", "↚"),
  ("nldr;", "‥"),
  ("nle;", "≰"),
  ("nleftarrow;", "↚"),
  ("nleftrightarrow;", "↮"),
  ("nleq;", "≰"),
  ("nleqq;", "≦̸"),
  ("nleqslant;", "⩽̸"),
  ("nles;", "⩽̸"),
  ("nless;", "≮"),
  ("nlsim;", "≴"),
  ("nlt;", "≮"),
  ("nltri;", "⋪"),
  ("nltrie;", "⋬"),
  ("nmid;", "∤"),
  ("nopf;", "𝕟"),
  ("not", "¬"),
  ("not;", "¬"),
  ("notin;", "∉"),
  ("notinE;", "⋹̸"),
  ("notindot;", "⋵̸"),
  ("notinva;", "∉"),
  ("notinvb;", "⋷"),
  ("notinvc;", "⋶"),
  ("notni;", "∌"),
  ("notniva;", "∌"),
  ("notnivb;", "⋾"),
  ("notnivc;", "⋽"),
  ("npar;", "∦"),
  ("nparallel;", "∦"),
  ("nparsl;", "⫽⃥"),
  ("npart;", "∂̸"),
  ("npolint;", "⨔"),
  ("npr;", "⊀"),
  ("nprcue;", "⋠"),
  ("npre;", "⪯̸"),
  ("nprec;", "⊀"),
  ("npreceq;", "⪯̸"),
  ("nrArr;", "⇏"),
  ("nrarr;", "↛"),
  ("nrarrc;", "⤳̸"),
  ("nrarrw;", "↝̸"),
  ("nrightarrow;", "↛"),
  ("nrtri;", "⋫"),
  ("nrtrie;", "⋭"),
  ("nsc;", "⊁"),
  ("nsccue;", "⋡"),
  ("nsce;", "⪰̸"),
  ("nscr;", "𝓃"),
  ("nshortmid;", "∤"),
  ("nshortparallel;", "∦"),
  ("nsim;", "≁"),
  ("nsime;", "≄"),
  ("nsimeq;", "≄"),
  ("nsmid;", "∤"),
  ("nspar;", "∦"),
  ("nsqsube;", "⋢"),
  ("nsqsupe;", "⋣"),
  ("nsub;", "⊄"),
  ("nsubE;", "⫅̸"),
  ("nsube;", "⊈"),
  ("nsubset;", "⊂⃒"),
  ("nsubseteq;", "⊈"),
  ("nsubseteqq;", "⫅̸"),
  ("nsucc;", "⊁"),
  ("nsucceq;", "⪰̸"),
  ("nsup;", "⊅"),
  ("nsupE;", "⫆̸"),
  ("nsupe;", "⊉"),
  ("nsupset;", "⊃⃒"),
  ("nsupseteq;", "⊉"),
  ("nsupseteqq;", "⫆̸"),
  ("ntgl;", "≹"),
  ("ntilde", "ñ"),
  ("ntilde;", "ñ"),
  ("ntlg;", "≸"),
  ("ntriangleleft;", "⋪"),
  ("ntrianglelefteq;", "⋬"),
  ("ntriangleright;", "⋫"),
  ("ntrianglerighteq;", "⋭"),
  ("nu;", "ν"),
  ("num;", "#"),
  ("numero;", "№"),
  ("numsp;", " "),
  ("nvDash;", "⊭"),
  ("nvHarr;", "⤄"),
  ("nvap;", "≍⃒"),
  ("nvdash;", "⊬"),
  ("nvge;", "≥⃒")
]

def html5_8 : Array (String × String) := #[
  ("nvgt;", ">⃒"),
  ("nvinfin;", "⧞"),
  ("nvlArr;", "⤂"),
  ("nvle;", "≤⃒"),
  ("nvlt;", "<⃒"),
  ("nvltrie;", "⊴⃒"),
  ("nvrArr;", "⤃"),
  ("nvrtrie;", "⊵⃒"),
  ("nvsim;", "∼⃒"),
  ("nwArr;", "⇖"),
  ("nwarhk;", "⤣"),
  ("nwarr;", "↖"),
  ("nwarrow;", "↖"),
  ("nwnear;", "⤧"),
  ("oS;", "Ⓢ"),
  ("oacute", "ó"),
  ("oacute;", "ó"),
  ("oast;", "⊛"),
  ("ocir;", "⊚"),
  ("ocirc", "ô"),
  ("ocirc;", "ô"),
  ("ocy;", "о"),
  ("odash;", "⊝"),
  ("odblac;", "ő"),
  ("odiv;", "⨸"),
  ("odot;", "⊙"),
  ("odsold;", "⦼"),
  ("oelig;", "œ"),
  ("ofcir;", "⦿"),
  ("ofr;", "𝔬"),
  ("ogon;", "˛"),
  ("ograve", "ò"),
  ("ograve;", "ò"),
  ("ogt;", "⧁"),
  ("ohbar;", "⦵"),
  ("ohm;", "Ω"),
  ("oint;", "∮"),
  ("olarr;", "↺"),
  ("olcir;", "⦾"),
  ("olcross;", "⦻"),
  ("oline;", "‾"),
  ("olt;", "⧀"),
  ("omacr;", "ō"),
  ("omega;", "ω"),
  ("omicron;", "ο"),
  ("omid;", "⦶"),
  ("ominus;", "⊖"),
  ("oopf;", "𝕠"),
  ("opar;", "⦷"),
  ("operp;", "⦹"),
  ("oplus;", "⊕"),
  ("or;", "∨"),
  ("orarr;", "↻"),
  ("ord;", "⩝"),
  ("order;", "ℴ"),
  ("orderof;", "ℴ"),
  ("ordf", "ª"),
  ("ordf;", "ª"),
  ("ordm", "º"),
  ("ordm;", "º"),
  ("origof;", "⊶"),
  ("oror;", "⩖"),
  ("orslope;", "⩗"),
  ("orv;", "⩛"),
  ("oscr;", "ℴ"),
  ("oslash", "ø"),
  ("oslash;", "ø"),
  ("osol;", "⊘"),
  ("otilde", "õ"),
  ("otilde;", "õ"),
  ("otimes;", "⊗"),
  ("otimesas;", "⨶"),
  ("ouml", "ö"),
  ("ouml;", "ö"),
  ("ovbar;", "⌽"),
  ("par;", "∥"),
  ("para", "¶"),
  ("para;", "¶"),
  ("parallel;", "∥"),
  ("parsim;", "⫳"),
  ("parsl;", "⫽"),
  ("part;", "∂"),
  ("pcy;", "п"),
  ("percnt;", "%"),
  ("period;", "."),
  ("permil;", "‰"),
  ("perp;", "⊥"),
  ("pertenk;", "‱"),
  ("pfr;", "𝔭"),
  ("phi;", "φ"),
  ("phiv;", "ϕ"),
  ("phmmat;", "ℳ"),
  ("phone;", "☎"),
  ("pi;", "π"),
  ("pitchfork;", "⋔"),
  ("piv;", "ϖ"),
  ("planck;", "ℏ"),
  ("planckh;", "ℎ"),
  ("plankv;", "ℏ"),
  ("plus;", "+"),
  ("plusacir;", "⨣"),
  ("plusb;", "⊞"),
  ("pluscir;", "⨢"),
  ("plusdo;", "∔"),
  ("plusdu;", "⨥"),
  ("pluse;", "⩲"),
  ("plusmn", "±"),
  ("plusmn;", "±"),
  ("plussim;", "⨦"),
  ("plustwo;", "⨧"),
  ("pm;", "±"),
  ("pointint;", "⨕"),
  ("popf;", "𝕡"),
  ("pound", "£"),
  ("pound;", "£"),
  ("pr;", "≺"),
  ("prE;", "⪳"),
  ("prap;", "⪷"),
  ("prcue;", "≼"),
  ("pre;", "⪯"),
  ("prec;", "≺"),
  ("precapprox;", "⪷"),
  ("preccurlyeq;", "≼"),
  ("preceq;", "⪯"),
  ("precnapprox;", "⪹"),
  ("precneqq;", "⪵"),
  ("precnsim;", "⋨"),
  ("precsim;", "≾"),
  ("prime;", "′"),
  ("primes;", "ℙ"),
  ("prnE;", "⪵"),
  ("prnap;", "⪹"),
  ("prnsim;", "⋨"),
  ("prod;", "∏"),
  ("profalar;", "⌮"),
  ("profline;", "⌒"),
  ("profsurf;", "⌓"),
  ("prop;", "∝"),
  ("propto;", "∝"),
  ("prsim;", "≾"),
  ("prurel;", "⊰"),
  ("pscr;", "𝓅"),
  ("psi;", "ψ"),
  ("puncsp;", " "),
  ("qfr;", "𝔮"),
  ("qint;", "⨌"),
  ("qopf;", "𝕢"),
  ("qprime;", "⁗"),
  ("qscr;", "𝓆"),
  ("quaternions;", "ℍ"),
  ("quatint;", "⨖"),
  ("quest;", "?"),
  ("questeq;", "≟"),
  ("quot", "\""),
  ("quot;", "\""),
  ("rAarr;", "⇛"),
  ("rArr;", "⇒"),
  ("rAtail;", "⤜"),
  ("rBarr;", "⤏"),
  ("rHar;", "⥤"),
  ("race;", "∽̱"),
  ("racute;", "ŕ"),
  ("radic;", "√"),
  ("raemptyv;", "⦳"),
  ("rang;", "⟩"),
  ("rangd;", "⦒"),
  ("range;", "⦥"),
  ("rangle;", "⟩"),
  ("raquo", "»"),
  ("raquo;", "»"),
  ("rarr;", "→"),
  ("rarrap;", "⥵"),
  ("rarrb;", "⇥"),
  ("rarrbfs;", "⤠"),
  ("rarrc;", "⤳"),
  ("rarrfs;", "⤞"),
  ("rarrhk;", "↪"),
  ("rarrlp;", "↬"),
  ("rarrpl;", "⥅"),
  ("rarrsim;", "⥴"),
  ("rarrtl;", "↣"),
  ("rarrw;", "↝"),
  ("ratail;", "⤚"),
  ("ratio;", "∶"),
  ("rationals;", "ℚ"),
  ("rbarr;", "⤍"),
  ("rbbrk;", "❳"),
  ("rbrace;", "}"),
  ("rbrack;", "]"),
  ("rbrke;", "⦌"),
  ("rbrksld;", "⦎"),
  ("rbrkslu;", "⦐"),
  ("rcaron;", "ř"),
  ("rcedil;", "ŗ"),
  ("rceil;", "⌉"),
  ("rcub;", "}"),
  ("rcy;", "р"),
  ("rdca;", "⤷"),
  ("rdldhar;", "⥩"),
  ("rdquo;", "”")
]

def html5_9 : Array (String × String) := #[
  ("rdquor;", "”"),
  ("rdsh;", "↳"),
  ("real;", "ℜ"),
  ("realine;", "ℛ"),
  ("realpart;", "ℜ"),
  ("reals;", "ℝ"),
  ("rect;", "▭"),
  ("reg", "®"),
  ("reg;", "®"),
  ("rfisht;", "⥽"),
  ("rfloor;", "⌋"),
  ("rfr;", "𝔯"),
  ("rhard;", "⇁"),
  ("rharu;", "⇀"),
  ("rharul;", "⥬"),
  ("rho;", "ρ"),
  ("rhov;", "ϱ"),
  ("rightarrow;", "→"),
  ("rightarrowtail;", "↣"),
  ("rightharpoondown;", "⇁"),
  ("rightharpoonup;", "⇀"),
  ("rightleftarrows;", "⇄"),
  ("rightleftharpoons;", "⇌"),
  ("rightrightarrows;", "⇉"),
  ("rightsquigarrow;", "↝"),
  ("rightthreetimes;", "⋌"),
  ("ring;", "˚"),
  ("risingdotseq;", "≓"),
  ("rlarr;", "⇄"),
  ("rlhar;", "⇌"),
  ("rlm;", "‏"),
  ("rmoust;", "⎱"),
  ("rmoustache;", "⎱"),
  ("rnmid;", "⫮"),
  ("roang;", "⟭"),
  ("roarr;", "⇾"),
  ("robrk;", "⟧"),
  ("ropar;", "⦆"),
  ("ropf;", "𝕣"),
  ("roplus;", "⨮"),
  ("rotimes;", "⨵"),
  ("rpar;", ")"),
  ("rpargt;", "⦔"),
  ("rppolint;", "⨒"),
  ("rrarr;", "⇉"),
  ("rsaquo;", "›"),
  ("rscr;", "𝓇"),
  ("rsh;", "↱"),
  ("rsqb;", "]"),
  ("rsquo;", "’"),
  ("rsquor;", "’"),
  ("rthree;", "⋌"),
  ("rtimes;", "⋊"),
  ("rtri;", "▹"),
  ("rtrie;", "⊵"),
  ("rtrif;", "▸"),
  ("rtriltri;", "⧎"),
  ("ruluhar;", "⥨"),
  ("rx;", "℞"),
  ("sacute;", "ś"),
  ("sbquo;", "‚"),
  ("sc;", "≻"),
  ("scE;", "⪴"),
  ("scap;", "⪸"),
  ("scaron;", "š"),
  ("sccue;", "≽"),
  ("sce;", "⪰"),
  ("scedil;", "ş"),
  ("scirc;", "ŝ"),
  ("scnE;", "⪶"),
  ("scnap;", "⪺"),
  ("scnsim;", "⋩"),
  ("scpolint;", "⨓"),
  ("scsim;", "≿"),
  ("scy;", "с"),
  ("sdot;", "⋅"),
  ("sdotb;", "⊡"),
  ("sdote;", "⩦"),
  ("seArr;", "⇘"),
  ("searhk;", "⤥"),
  ("searr;", "↘"),
  ("searrow;", "↘"),
  ("sect", "§"),
  ("sect;", "§"),
  ("semi;", ";"),
  ("seswar;", "⤩"),
  ("setminus;", "∖"),
  ("setmn;", "∖"),
  ("sext;", "✶"),
  ("sfr;", "𝔰"),
  ("sfrown;", "⌢"),
  ("sharp;", "♯"),
  ("shchcy;", "щ"),
  ("shcy;", "ш"),
  ("shortmid;", "∣"),
  ("shortparallel;", "∥"),
  ("shy", "­"),
  ("shy;", "­"),
  ("sigma;", "σ"),
  ("sigmaf;", "ς"),
  ("sigmav;", "ς"),
  ("sim;", "∼"),
  ("simdot;", "⩪"),
  ("sime;", "≃"),
  ("simeq;", "≃"),
  ("simg;", "⪞"),
  ("simgE;", "⪠"),
  ("siml;", "⪝"),
  ("simlE;", "⪟"),
  ("simne;", "≆"),
  ("simplus;", "⨤"),
  ("simrarr;", "⥲"),
  ("slarr;", "←"),
  ("smallsetminus;", "∖"),
  ("smashp;", "⨳"),
  ("smeparsl;", "⧤"),
  ("smid;", "∣"),
  ("smile;", "⌣"),
  ("smt;", "⪪"),
  ("smte;", "⪬"),
  ("smtes;", "⪬︀"),
  ("softcy;", "ь"),
  ("sol;", "/"),
  ("solb;", "⧄"),
  ("solbar;", "⌿"),
  ("sopf;", "𝕤"),
  ("spades;", "♠"),
  ("spadesuit;", "♠"),
  ("spar;", "∥"),
  ("sqcap;", "⊓"),
  ("sqcaps;", "⊓︀"),
  ("sqcup;", "⊔"),
  ("sqcups;", "⊔︀"),
  ("sqsub;", "⊏"),
  ("sqsube;", "⊑"),
  ("sqsubset;", "⊏"),
  ("sqsubseteq;", "⊑"),
  ("sqsup;", "⊐"),
  ("sqsupe;", "⊒"),
  ("sqsupset;", "⊐"),
  ("sqsupseteq;", "⊒"),
  ("squ;", "□"),
  ("square;", "□"),
  ("squarf;", "▪"),
  ("squf;", "▪"),
  ("srarr;", "→"),
  ("sscr;", "𝓈"),
  ("ssetmn;", "∖"),
  ("ssmile;", "⌣"),
  ("sstarf;", "⋆"),
  ("star;", "☆"),
  ("starf;", "★"),
  ("straightepsilon;", "ϵ"),
  ("straightphi;", "ϕ"),
  ("strns;", "¯"),
  ("sub;", "⊂"),
  ("subE;", "⫅"),
  ("subdot;", "⪽"),
  ("sube;", "⊆"),
  ("subedot;", "⫃"),
  ("submult;", "⫁"),
  ("subnE;", "⫋"),
  ("subne;", "⊊"),
  ("subplus;", "⪿"),
  ("subrarr;", "⥹"),
  ("subset;", "⊂"),
  ("subseteq;", "⊆"),
  ("subseteqq;", "⫅"),
  ("subsetneq;", "⊊"),
  ("subsetneqq;", "⫋"),
  ("subsim;", "⫇"),
  ("subsub;", "⫕"),
  ("subsup;", "⫓"),
  ("succ;", "≻"),
  ("succapprox;", "⪸"),
  ("succcurlyeq;", "≽"),
  ("succeq;", "⪰"),
  ("succnapprox;", "⪺"),
  ("succneqq;", "⪶"),
  ("succnsim;", "⋩"),
  ("succsim;", "≿"),
  ("sum;", "∑"),
  ("sung;", "♪"),
  ("sup1", "¹"),
  ("sup1;", "¹"),
  ("sup2", "²"),
  ("sup2;", "²"),
  ("sup3", "³"),
  ("sup3;", "³"),
  ("sup;", "⊃"),
  ("supE;", "⫆"),
  ("supdot;", "⪾"),
  ("supdsub;", "⫘"),
  ("supe;", "⊇"),
  ("supedot;", "⫄"),
  ("suphsol;", "⟉"),
  ("suphsub;", "⫗"),
  ("suplarr;", "⥻"),
  ("supmult;", "⫂"),
  ("supnE;", "⫌")
]

def html5_10 : Array (String × String) := #[
  ("supne;", "⊋"),
  ("supplus;", "⫀"),
  ("supset;", "⊃"),
  ("supseteq;", "⊇"),
  ("supseteqq;", "⫆"),
  ("supsetneq;", "⊋"),
  ("supsetneqq;", "⫌"),
  ("supsim;", "⫈"),
  ("supsub;", "⫔"),
  ("supsup;", "⫖"),
  ("swArr;", "⇙"),
  ("swarhk;", "⤦"),
  ("swarr;", "↙"),
  ("swarrow;", "↙"),
  ("swnwar;", "⤪"),
  ("szlig", "ß"),
  ("szlig;", "ß"),
  ("target;", "⌖"),
  ("tau;", "τ"),
  ("tbrk;", "⎴"),
  ("tcaron;", "ť"),
  ("tcedil;", "ţ"),
  ("tcy;", "т"),
  ("tdot;", "⃛"),
  ("telrec;", "⌕"),
  ("tfr;", "𝔱"),
  ("there4;", "∴"),
  ("therefore;", "∴"),
  ("theta;", "θ"),
  ("thetasym;", "ϑ"),
  ("thetav;", "ϑ"),
  ("thickapprox;", "≈"),
  ("thicksim;", "∼"),
  ("thinsp;", " "),
  ("thkap;", "≈"),
  ("thksim;", "∼"),
  ("thorn", "þ"),
  ("thorn;", "þ"),
  ("tilde;", "˜"),
  ("times", "×"),
  ("times;", "×"),
  ("timesb;", "⊠"),
  ("timesbar;", "⨱"),
  ("timesd;", "⨰"),
  ("tint;", "∭"),
  ("toea;", "⤨"),
  ("top;", "⊤"),
  ("topbot;", "⌶"),
  ("topcir;", "⫱"),
  ("topf;", "𝕥"),
  ("topfork;", "⫚"),
  ("tosa;", "⤩"),
  ("tprime;", "‴"),
  ("trade;", "™"),
  ("triangle;", "▵"),
  ("triangledown;", "▿"),
  ("triangleleft;", "◃"),
  ("trianglelefteq;", "⊴"),
  ("triangleq;", "≜"),
  ("triangleright;", "▹"),
  ("trianglerighteq;", "⊵"),
  ("tridot;", "◬"),
  ("trie;", "≜"),
  ("triminus;", "⨺"),
  ("triplus;", "⨹"),
  ("trisb;", "⧍"),
  ("tritime;", "⨻"),
  ("trpezium;", "⏢"),
  ("tscr;", "𝓉"),
  ("tscy;", "ц"),
  ("tshcy;", "ћ"),
  ("tstrok;", "ŧ"),
  ("twixt;", "≬"),
  ("twoheadleftarrow;", "↞"),
  ("twoheadrightarrow;", "↠"),
  ("uArr;", "⇑"),
  ("uHar;", "⥣"),
  ("uacute", "ú"),
  ("uacute;", "ú"),
  ("uarr;", "↑"),
  ("ubrcy;", "ў"),
  ("ubreve;", "ŭ"),
  ("ucirc", "û"),
  ("ucirc;", "û"),
  ("ucy;", "у"),
  ("udarr;", "⇅"),
  ("udblac;", "ű"),
  ("udhar;", "⥮"),
  ("ufisht;", "⥾"),
  ("ufr;", "𝔲"),
  ("ugrave", "ù"),
  ("ugrave;", "ù"),
  ("uharl;", "↿"),
  ("uharr;", "↾"),
  ("uhblk;", "▀"),
  ("ulcorn;", "⌜"),
  ("ulcorner;", "⌜"),
  ("ulcrop;", "⌏"),
  ("ultri;", "◸"),
  ("umacr;", "ū"),
  ("uml", "¨"),
  ("uml;", "¨"),
  ("uogon;", "ų"),
  ("uopf;", "𝕦"),
  ("uparrow;", "↑"),
  ("updownarrow;", "↕"),
  ("upharpoonleft;", "↿"),
  ("upharpoonright;", "↾"),
  ("uplus;", "⊎"),
  ("upsi;", "υ"),
  ("upsih;", "ϒ"),
  ("upsilon;", "υ"),
  ("upuparrows;", "⇈"),
  ("urcorn;", "⌝"),
  ("urcorner;", "⌝"),
  ("urcrop;", "⌎"),
  ("uring;", "ů"),
  ("urtri;", "◹"),
  ("uscr;", "𝓊"),
  ("utdot;", "⋰"),
  ("utilde;", "ũ"),
  ("utri;", "▵"),
  ("utrif;", "▴"),
  ("uuarr;", "⇈"),
  ("uuml", "ü"),
  ("uuml;", "ü"),
  ("uwangle;", "⦧"),
  ("vArr;", "⇕"),
  ("vBar;", "⫨"),
  ("vBarv;", "⫩"),
  ("vDash;", "⊨"),
  ("vangrt;", "⦜"),
  ("varepsilon;", "ϵ"),
  ("varkappa;", "ϰ"),
  ("varnothing;", "∅"),
  ("varphi;", "ϕ"),
  ("varpi;", "ϖ"),
  ("varpropto;", "∝"),
  ("varr;", "↕"),
  ("varrho;", "ϱ"),
  ("varsigma;", "ς"),
  ("varsubsetneq;", "⊊︀"),
  ("varsubsetneqq;", "⫋︀"),
  ("varsupsetneq;", "⊋︀"),
  ("varsupsetneqq;", "⫌︀"),
  ("vartheta;", "ϑ"),
  ("vartriangleleft;", "⊲"),
  ("vartriangleright;", "⊳"),
  ("vcy;", "в"),
  ("vdash;", "⊢"),
  ("vee;", "∨"),
  ("veebar;", "⊻"),
  ("veeeq;", "≚"),
  ("vellip;", "⋮"),
  ("verbar;", "|"),
  ("vert;", "|"),
  ("vfr;", "𝔳"),
  ("vltri;", "⊲"),
  ("vnsub;", "⊂⃒"),
  ("vnsup;", "⊃⃒"),
  ("vopf;", "𝕧"),
  ("vprop;", "∝"),
  ("vrtri;", "⊳"),
  ("vscr;", "𝓋"),
  ("vsubnE;", "⫋︀"),
  ("vsubne;", "⊊︀"),
  ("vsupnE;", "⫌︀"),
  ("vsupne;", "⊋︀"),
  ("vzigzag;", "⦚"),
  ("wcirc;", "ŵ"),
  ("wedbar;", "⩟"),
  ("wedge;", "∧"),
  ("wedgeq;", "≙"),
  ("weierp;", "℘"),
  ("wfr;", "𝔴"),
  ("wopf;", "𝕨"),
  ("wp;", "℘"),
  ("wr;", "≀"),
  ("wreath;", "≀"),
  ("wscr;", "𝓌"),
  ("xcap;", "⋂"),
  ("xcirc;", "◯"),
  ("xcup;", "⋃"),
  ("xdtri;", "▽"),
  ("xfr;", "𝔵"),
  ("xhArr;", "⟺"),
  ("xharr;", "⟷"),
  ("xi;", "ξ"),
  ("xlArr;", "⟸"),
  ("xlarr;", "⟵"),
  ("xmap;", "⟼"),
  ("xnis;", "⋻"),
  ("xodot;", "⨀"),
  ("xopf;", "𝕩"),
  ("xoplus;", "⨁"),
  ("xotime;", "⨂"),
  ("xrArr;", "⟹"),
  ("xrarr;", "⟶"),
  ("xscr;", "𝓍"),
  ("xsqcup;", "⨆")
]

def html5_11 : Array (String × String) := #[
  ("xuplus;", "⨄"),
  ("xutri;", "△"),
  ("xvee;", "⋁"),
  ("xwedge;", "⋀"),
  ("yacute", "ý"),
  ("yacute;", "ý"),
  ("yacy;", "я"),
  ("ycirc;", "ŷ"),
  ("ycy;", "ы"),
  ("yen", "¥"),
  ("yen;", "¥"),
  ("yfr;", "𝔶"),
  ("yicy;", "ї"),
  ("yopf;", "𝕪"),
  ("yscr;", "𝓎"),
  ("yucy;", "ю"),
  ("yuml", "ÿ"),
  ("yuml;", "ÿ"),
  ("zacute;", "ź"),
  ("zcaron;", "ž"),
  ("zcy;", "з"),
  ("zdot;", "ż"),
  ("zeetrf;", "ℨ"),
  ("zeta;", "ζ"),
  ("zfr;", "𝔷"),
  ("zhcy;", "ж"),
  ("zigrarr;", "⇝"),
  ("zopf;", "𝕫"),
  ("zscr;", "𝓏"),
  ("zwj;", "‍"),
  ("zwnj;", "‌")
]

def html5 : Array (String × String) :=
  html5_0 ++ html5_1 ++ html5_2 ++ html5_3 ++ html5_4 ++ html5_5 ++ html5_6 ++ html5_7 ++ html5_8 ++ html5_9 ++ html5_10 ++ html5_11

/-- `html._invalid_charrefs`: the numeric references Windows-1252 and the spec remap. -/
def invalidCharrefs : List (Nat × String) := [(0, "�"), (13, "\r"), (128, "€"), (129, ""), (130, "‚"), (131, "ƒ"), (132, "„"), (133, "…"), (134, "†"), (135, "‡"), (136, "ˆ"), (137, "‰"), (138, "Š"), (139, "‹"), (140, "Œ"), (141, ""), (142, "Ž"), (143, ""), (144, ""), (145, "‘"), (146, "’"), (147, "“"), (148, "”"), (149, "•"), (150, "–"), (151, "—"), (152, "˜"), (153, "™"), (154, "š"), (155, "›"), (156, "œ"), (157, ""), (158, "ž"), (159, "Ÿ")]

/-- `html._invalid_codepoints`: numeric references that decode to nothing. -/
def invalidCodepoints : List Nat := [1, 2, 3, 4, 5, 6, 7, 8, 11, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 159, 64976, 64977, 64978, 64979, 64980, 64981, 64982, 64983, 64984, 64985, 64986, 64987, 64988, 64989, 64990, 64991, 64992, 64993, 64994, 64995, 64996, 64997, 64998, 64999, 65000, 65001, 65002, 65003, 65004, 65005, 65006, 65007, 65534, 65535, 131070, 131071, 196606, 196607, 262142, 262143, 327678, 327679, 393214, 393215, 458750, 458751, 524286, 524287, 589822, 589823, 655358, 655359, 720894, 720895, 786430, 786431, 851966, 851967, 917502, 917503, 983038, 983039, 1048574, 1048575, 1114110, 1114111]

/-- `html.unescape` for a reference at `i` (the `&`): the replacement and the index after it.
Named: `&name;` or `&name` as the table has it, else the longest table prefix of the run with
the rest kept literally; numeric: decimal and hex, with the spec's remaps. -/
def charref (b : B) (i : Nat) : Option (B × Nat) :=
  let j := i + 1
  if at? b j == 35 then  -- '#'
    let hex := at? b (j + 1) == 120 || at? b (j + 1) == 88
    let k0 := if hex then j + 2 else j + 1
    let rec digits (k acc n : Nat) (fuel : Nat) : Nat × Nat × Nat :=
      match fuel with
      | 0 => (acc, k, n)
      | fuel + 1 =>
        let c := at? b k
        if isDigit c then digits (k + 1) (acc * (if hex then 16 else 10) + (c.toNat - 48)) (n + 1) fuel
        else if hex && 97 ≤ lower c && lower c ≤ 102 then
          digits (k + 1) (acc * 16 + (lower c).toNat - 87) (n + 1) fuel
        else (acc, k, n)
    let (v, k, n) := digits k0 0 0 40
    if n == 0 then none
    else
      let k := if at? b k == 59 then k + 1 else k
      let r := match invalidCharrefs.lookup v with
        | some r => str r
        | none =>
          if (0xD800 ≤ v && v ≤ 0xDFFF) || v > 0x10FFFF then str "\uFFFD"
          else if invalidCodepoints.contains v then ByteArray.empty
          else str (Char.ofNat v).toString
      some (r, k)
  else
    -- the run [^\t\n\f <&#;]{1,32} and an optional ';'
    let rec run (k n : Nat) (fuel : Nat) : Nat :=
      match fuel with
      | 0 => k
      | fuel + 1 =>
        let c := at? b k
        if n < 32 && k < b.size && !(c == 9 || c == 10 || c == 12 || c == 32 || c == LT || c == AMP || c == 35 || c == 59)
        then run (k + 1) (n + 1) fuel else k
    let e := run j 0 33
    if e == j then none
    else
      let e := if at? b e == 59 then e + 1 else e
      let s := toStr (slice b j e)
      match html5.find? (·.1 == s) with
      | some (_, r) => some (str r, e)
      | none =>
        let rec prefixes (x : Nat) (fuel : Nat) : Option (B × Nat) :=
          match fuel with
          | 0 => none
          | fuel + 1 =>
            if x < 2 then none
            else
              let pre := String.ofList (s.toList.take x)
              match html5.find? (·.1 == pre) with
              | some (_, r) => some (str r, j + pre.utf8ByteSize)
              | none => prefixes (x - 1) fuel
        prefixes (s.length - 1) 40

/-- Decode the references in `b[i:j]` (text or an attribute value). -/
partial def unescape (b : B) (i j : Nat) : B := Id.run do
  let mut out := ByteArray.emptyWithCapacity (j - i)
  let mut k := i
  while k < j do
    if b[k]! == AMP then
      match charref b k with
      | some (r, k') => if k' ≤ j then out := out ++ r; k := k' else out := out.push AMP; k := k + 1
      | none => out := out.push AMP; k := k + 1
    else
      out := out.push b[k]!; k := k + 1
  return out

/-- An attribute as `html.parser` hands it on: lowercased name, decoded value or `none`. -/
structure Attr where
  name : B
  value : Option B

/-- A start tag's attributes from `i` (after the name) to the closing `>`; `(attrs, selfClosing, after)`. -/
partial def parseAttrs (b : B) (i : Nat) : Option (List Attr × Bool × Nat) := Id.run do
  let mut k := i
  let mut attrs : Array Attr := #[]
  let n := b.size
  while k < n do
    -- separators: whitespace, and a '/' not followed by '>'
    while k < n && (isWs b[k]! || (b[k]! == SLASH && at? b (k + 1) != GT)) do k := k + 1
    if k ≥ n then return none
    if b[k]! == GT then return some (attrs.toList, false, k + 1)
    if b[k]! == SLASH && at? b (k + 1) == GT then return some (attrs.toList, true, k + 2)
    -- name: [^\s/>][^\s/=>]*
    let n0 := k
    k := k + 1
    while k < n && !(isWs b[k]! || b[k]! == SLASH || b[k]! == EQ || b[k]! == GT) do k := k + 1
    let name := lowerBytes (slice b n0 k)
    -- optional value: \s*=+\s*(quoted | unquoted)
    let mut m := k
    while m < n && isWs b[m]! do m := m + 1
    if m < n && b[m]! == EQ then
      while m < n && b[m]! == EQ do m := m + 1
      while m < n && isWs b[m]! do m := m + 1
      if m < n && (b[m]! == DQ || b[m]! == SQ) then
        let q := b[m]!
        let v0 := m + 1
        let mut e := v0
        while e < n && b[e]! != q do e := e + 1
        if e ≥ n then return none
        attrs := attrs.push { name, value := some (unescape b v0 e) }
        k := e + 1
      else
        let v0 := m
        let mut e := m
        while e < n && !(isWs b[e]! || b[e]! == GT) do e := e + 1
        attrs := attrs.push { name, value := some (unescape b v0 e) }
        k := e
    else
      attrs := attrs.push { name, value := none }
  return none

/-! ### Escaping on output

`html.parser` hands text and attribute values on decoded; the page written for WeasyPrint is
HTML again, so what was `&lt;`, `&gt;`, `&amp;` (and `&quot;` in a value) in Verso's output must
be so again, or a code span's `<i>` becomes an element. -/

/-- The escape of one byte of text: `&`, `<` and `>` as references, every other byte as it is. -/
def escapeByte (c : UInt8) : List UInt8 :=
  if c == AMP then [38, 97, 109, 112, 59]      -- &amp;
  else if c == LT then [38, 108, 116, 59]       -- &lt;
  else if c == GT then [38, 103, 116, 59]       -- &gt;
  else [c]

def escapeList (l : List UInt8) : List UInt8 := l.flatMap escapeByte

/-- Escaped text holds no `<` and no `>`: nothing in it can open or close a tag. -/
theorem escapeList_no_markup (l : List UInt8) : ∀ c ∈ escapeList l, c ≠ LT ∧ c ≠ GT := by
  intro c hc
  simp only [escapeList, List.mem_flatMap] at hc
  obtain ⟨a, _, ha⟩ := hc
  unfold escapeByte at ha
  split at ha
  · simp at ha; rcases ha with rfl | rfl | rfl | rfl | rfl <;> decide
  · split at ha
    · simp at ha; rcases ha with rfl | rfl | rfl | rfl <;> decide
    · split at ha
      · simp at ha; rcases ha with rfl | rfl | rfl | rfl <;> decide
      · simp at ha; subst ha; constructor <;> intro h <;> simp_all

def escapeText (b : B) : B := (escapeList b.toList).toByteArray

/-- An attribute value between double quotes: `escapeText` and `"` as `&quot;`. -/
def escapeAttr (b : B) : B :=
  (b.toList.flatMap fun c => if c == 34 then [38, 113, 117, 111, 116, 59] else escapeByte c).toByteArray  -- &quot;

def attrStr (attrs : List Attr) : B :=
  attrs.foldl (init := ByteArray.empty) fun o a =>
    o ++ str " " ++ a.name ++ str "=\"" ++ (a.value.map escapeAttr).getD (str "None") ++ str "\""

def attrGet (attrs : List Attr) (name : String) : Option B :=
  (attrs.reverse.find? (·.name == str name)).bind (·.value)  -- `dict(attrs)`: the last wins

def contains (hay : B) (needle : String) : Bool := (findFrom hay 0 needle).isSome
def endsWith (b : B) (suffix : String) : Bool :=
  let s := suffix.toUTF8
  b.size ≥ s.size && startsAt b (b.size - s.size) suffix

/-- The web-only chrome pruned from the body, as the Python's `_should_drop`. -/
def shouldDrop (tag : B) (attrs : List Attr) : Bool :=
  let cls := (attrGet attrs "class").getD ByteArray.empty
  let idv := (attrGet attrs "id").getD ByteArray.empty
  tag == str "script" || tag == str "template" || tag == str "header" ||
  (tag == str "nav" && idv == str "toc") ||
  contains cls "bp_external_decl_body" || contains cls "bp_graph" || contains cls "bp_summary" ||
  endsWith idv "--Dependency-Graph" || endsWith idv "--Blueprint-Summary"

structure Extracted where
  head : B
  body : B

/-- `BodyExtractor.feed`: the head's content and the body's content with the chrome pruned. -/
partial def extract (b : B) : Extracted := Id.run do
  let n := b.size
  let mut head := ByteArray.emptyWithCapacity 65536
  let mut body := ByteArray.emptyWithCapacity n
  let mut inHead := false
  let mut inBody := false
  let mut dropTag : Option B := none
  let mut dropCount := 0
  let mut cdata : Option B := none
  let mut i := 0
  while i < n do
    -- text up to the next markup
    let mut j := i
    match cdata with
    | some t =>
      while j < n && !(b[j]! == LT && at? b (j + 1) == SLASH && startsAtCI b (j + 2) (toStr t) &&
          (let c := at? b (j + 2 + t.size); c == GT || isWs c)) do j := j + 1
    | none =>
      while j < n && b[j]! != LT do j := j + 1
    if j > i then
      let data := if cdata.isSome then slice b i j else escapeText (unescape b i j)
      if inBody && dropTag.isNone then body := body ++ data
      if inHead then head := head ++ data
      i := j
    if i ≥ n then break
    -- markup at i (a '<')
    if startsAt b i "<!--" then
      i := match findFrom b (i + 4) "-->" with | some e => e + 3 | none => n
    else if at? b (i + 1) == 33 || at? b (i + 1) == 63 then  -- <! or <?
      i := match findFrom b (i + 2) ">" with | some e => e + 1 | none => n
    else if at? b (i + 1) == SLASH && isAlpha (at? b (i + 2)) then
      let mut k := i + 2
      while k < n && isWord b[k]! || at? b k == 45 || at? b k == 46 || at? b k == 58 do k := k + 1
      let tag := lowerBytes (slice b (i + 2) k)
      i := match findFrom b k ">" with | some e => e + 1 | none => n
      if cdata.isSome then cdata := none
      if tag == str "body" then inBody := false
      else if tag == str "head" then inHead := false
      else if inBody && dropTag.isSome then
        if some tag == dropTag then
          dropCount := dropCount - 1
          if dropCount == 0 then dropTag := none
      else
        if inBody then body := body ++ str "</" ++ tag ++ str ">"
        if inHead then head := head ++ str "</" ++ tag ++ str ">"
    else if isAlpha (at? b (i + 1)) then
      let mut k := i + 1
      while k < n && isWord b[k]! || at? b k == 45 || at? b k == 46 || at? b k == 58 do k := k + 1
      let tag := lowerBytes (slice b (i + 1) k)
      match parseAttrs b k with
      | none =>
        -- not a tag after all: the '<' is text
        if inBody && dropTag.isNone then body := body.push LT
        if inHead then head := head.push LT
        i := i + 1
      | some (attrs, selfClosing, after) =>
        i := after
        if selfClosing then
          if !(inBody && dropTag.isSome) then
            if inBody then body := body ++ str "<" ++ tag ++ attrStr attrs ++ str "/>"
            else if inHead then head := head ++ str "<" ++ tag ++ attrStr attrs ++ str "/>"
        else
          if tag == str "script" || tag == str "style" then cdata := some tag
          if tag == str "body" then inBody := true
          else if tag == str "head" then inHead := true
          else
            if inBody then
              if dropTag.isSome then
                if some tag == dropTag then dropCount := dropCount + 1
              else if shouldDrop tag attrs then
                dropTag := some tag; dropCount := 1
              else body := body ++ str "<" ++ tag ++ attrStr attrs ++ str ">"
            if inHead then head := head ++ str "<" ++ tag ++ attrStr attrs ++ str ">"
    else
      -- a lone '<' is text
      if inBody && dropTag.isNone then body := body.push LT
      if inHead then head := head.push LT
      i := i + 1
  return { head, body }

/-- The opening headings of `body` in order: `(index of the level digit, level, attrs)`, and
every heading tag position (`(index of the digit, isClose)`), as the two Python regexes see them. -/
partial def headingTags (body : B) : List (Nat × Bool) := Id.run do
  let mut out : Array (Nat × Bool) := #[]
  let n := body.size
  let mut i := 0
  while i + 2 < n do
    if body[i]! == LT then
      let (k, close) := if at? body (i + 1) == SLASH then (i + 2, true) else (i + 1, false)
      if lower (at? body k) == 104 && 49 ≤ at? body (k + 1) && at? body (k + 1) ≤ 54 &&
          !isWord (at? body (k + 2)) then
        out := out.push (k + 1, close)
    i := i + 1
  return out.toList

/-- The `id` of the heading whose level digit is at `d` (`\bid="…"` within the tag). -/
partial def headingId (body : B) (d : Nat) : Option B := Id.run do
  let mut e := d
  while e < body.size && body[e]! != GT do e := e + 1
  let mut k := d + 1
  while k + 4 < e do
    if startsAt body k "id=\"" && (k == 0 || !isWord body[k - 1]!) then
      let mut q := k + 4
      while q < e && body[q]! != DQ do q := q + 1
      return some (slice body (k + 4) q)
    k := k + 1
  return none

/-- `_renumber_headings`: rewrite every `<hN`/`</hN` with the assigned level. -/
def renumber (body : B) (tags : List (Nat × Bool)) : B := Id.run do
  let opens := tags.filterMap fun (d, close) => if close then none else some (body[d]!.toNat - 48)
  let assigned := renumberLevels opens
  let mut out := body
  let mut stack : List Nat := []
  let mut rest := assigned
  for (d, close) in tags do
    if close then
      match stack with
      | a :: s => out := out.set! d (48 + a).toUInt8; stack := s
      | [] => pure ()
    else
      match rest with
      | a :: r => out := out.set! d (48 + a).toUInt8; stack := a :: stack; rest := r
      | [] => pure ()
  return out

def printCss : String := r##"
    <style>
      @page {
        size: letter;
        margin: 2cm 1.8cm 2cm 1.8cm;
        @bottom-center { content: counter(page); font-size: 9pt; color: #666; }
        @footnote { border-top: 0.5pt solid #999; padding-top: 6pt; margin-top: 10pt; }
      }

      /* ── Margin notes → footnotes ──
         Verso lays its margin notes (citations included) out entirely under
         `@media screen` and `@container` rules; WeasyPrint renders print media and
         implements no container queries, so without the rules below each note's full
         text flows inline, mid-sentence. WeasyPrint implements CSS-GCPM footnotes,
         so the print form of a margin note is a numbered footnote at the bottom of
         its page (the @footnote area above draws the separator rule). */
      .marginalia .note { float: footnote; font-size: 9pt; line-height: 1.4; }
      /* Footnotes bring their own call mark and marker, so the screen design's
         CSS-counter pair (superscript mark in the text, number on the note) is
         suppressed in print. */
      .marginalia::after { content: none !important; }
      .marginalia .note::before { content: none !important; }
      .marginalia .note::footnote-call {
        content: counter(footnote);
        vertical-align: super;
        font-size: 0.7em;
        font-weight: bold;
      }
      .marginalia .note::footnote-marker {
        content: counter(footnote) ". ";
        font-weight: bold;
      }

      /* ── Hide web-only chrome ──
         The chrome / declaration-body / dashboard subtrees that pollute the outline
         are removed *structurally* by the Python post-processor (BodyExtractor); the
         rules below are a visual fallback for anything left in the body that should
         not print but carries no heading (so it never reaches the bookmark outline).
         Note: CSS display:none alone does NOT suffice for the outline — WeasyPrint
         still emits PDF bookmarks for hidden headings, which is why the offending
         elements are pruned from the DOM rather than only hidden here. */
      header,
      nav#toc,
      nav.toc,
      #toc,
      .toc-backdrop,
      .prev-next-buttons,
      .nav_buttons,
      .permalink-widget,
      label#toggle-toc-click,
      #toggle-toc,
      .search-box,
      .search-wrapper,
      .bp_inline_preview_panel,
      script,
      template,
      .bp_external_decl_body,
      pre.docstring,
      [class*="bp_graph"],
      [class*="bp_summary"],
      [id$="--Dependency-Graph"],
      [id$="--Blueprint-Summary"] { display: none !important; }

      /* ── Undo the sidebar-offset layout ── */
      .with-toc { margin-top: 0 !important; }
      .with-toc > main { padding-left: 0 !important; }
      .content-wrapper { max-width: 100% !important; padding: 0 !important; }
      main { margin: 0 !important; max-width: 100% !important; }

      /* ── Typography ── */
      body {
        font-family: system-ui, -apple-system, "Segoe UI", sans-serif;
        font-size: 11pt;
        line-height: 1.5;
        color: #222;
      }
      h1 { font-size: 18pt; page-break-before: always; margin-top: 0; }
      h1:first-of-type { page-break-before: avoid; }
      /* Start every section (a chapter's `#` heading, an h2 after renormalization)
         on a fresh page, as requested for the printed blueprint. */
      h2 { font-size: 14pt; margin-top: 0; page-break-before: always; }
      h3 { font-size: 12pt; }

      /* ── Code blocks ── */
      pre, code { font-size: 9pt; }
      pre {
        background: #f5f5f5;
        border: 1px solid #ddd;
        border-radius: 4px;
        padding: 0.6em 0.8em;
        overflow-x: hidden;
        word-wrap: break-word;
        white-space: pre-wrap;
      }

      /* ── Tables ── */
      table { page-break-inside: avoid; border-collapse: collapse; width: 100%; }
      td, th { padding: 0.3em 0.5em; border: 1px solid #ddd; }
      th { background: #f0f0f0; font-weight: 600; }

      /* ── Images ── */
      img, svg { max-width: 100%; }

      /* ── Page-break hints ── */
      .chapter { page-break-before: always; }
      .chapter:first-child { page-break-before: avoid; }
      h2, h3 { page-break-after: avoid; }

      /* ── Links: show URL in parentheses for external links ── */
      a[href^="http"]::after { content: " (" attr(href) ")"; font-size: 8pt; color: #666; }
      a[href^="http"] { word-break: break-all; }
      /* But not for anchors within the doc */
      a[href^="#"]::after, a[href^="find/"]::after { content: none; }
    </style>
    "##

/-- The merged page for a list of pages' contents, and the nesting problems found. -/
def merge (pages : List B) : B × List String := Id.run do
  let parts := pages.map extract
  let headHtml := (parts.head?.map (·.head)).getD ByteArray.empty
  let mut body := ByteArray.empty
  let mut first := true
  for p in parts do
    if !first then body := body ++ str "<div style=\"page-break-before: always;\"></div>"
    first := false
    body := body ++ str "<section class=\"chapter\">" ++ p.body ++ str "</section>"
  let tags := headingTags body
  let opens := tags.filter (!·.2)
  let problems := (checkLevels (opens.map fun (d, _) => body[d]!.toNat - 48)).map fun (i, lvl, a) =>
    let d := (opens[i]?.map (·.1)).getD 0
    let where_ := match headingId body d with | some id => "#" ++ toStr id | none => "(no id)"
    s!"<h{lvl}> {where_} should be <h{a}>"
  let bodyHtml := renumber body tags
  let out := str "<!DOCTYPE html>\n<html lang=\"en\"><head><meta charset=\"utf-8\">\n" ++ headHtml ++
    str "\n" ++ str printCss ++ str "\n</head>\n<body>\n" ++ bodyHtml ++ str "\n</body></html>"
  return (out, problems)

/-! ## Pages -/

/-- `(dotted number, href)` of every table-of-contents row on a page. -/
partial def navRows (b : B) : List (String × String) := Id.run do
  let mut out : Array (String × String) := #[]
  let mut i := 0
  let key := "<td class=\"num\">"
  while true do
    match findFrom b i key with
    | none => break
    | some p =>
      let mut k := p + key.utf8ByteSize
      let n0 := k
      while k < b.size && (isDigit b[k]! || b[k]! == 46) do k := k + 1
      let num := toStr (slice b n0 k)
      if k > n0 && startsAt b k "</td>" then
        let mut m := k + 5
        while m < b.size && isWs b[m]! do m := m + 1
        if startsAt b m "<td><a href=\"" then
          let h0 := m + 13
          let mut e := h0
          while e < b.size && b[e]! != DQ do e := e + 1
          out := out.push (num, toStr (slice b h0 e))
      i := p + 1
  return out.toList

def numKey (n : String) : List Nat :=
  ((stripDots n).splitOn ".").map (·.toNat!)

def keyLt : List Nat → List Nat → Bool
  | [], [] => false
  | [], _ :: _ => true
  | _ :: _, [] => false
  | a :: as, b :: bs => a < b || (a == b && keyLt as bs)

/-- `_resolve_page`: a nav href, relative to the page it is on, to an `index.html` under `root`. -/
def resolvePage (fromIndex : System.FilePath) (href : String) (root : System.FilePath) :
    IO (Option System.FilePath) := do
  let target := ((href.splitOn "#").headD "").splitOn "?" |>.headD ""
  if target.isEmpty then return none
  let dest := (fromIndex.parent.getD ".") / target
  if !(← dest.pathExists) then return none
  let mut dest ← IO.FS.realPath dest
  if ← dest.isDir then dest := dest / "index.html"
  let rootR ← IO.FS.realPath root
  if !(dest.toString.startsWith (rootR.toString ++ "/")) then return none
  if ← dest.isDir then return none
  if ← dest.pathExists then return some dest else return none

partial def indexFiles (dir : System.FilePath) : IO (List System.FilePath) := do
  let mut out := []
  for e in ← dir.readDir do
    if ← e.path.isDir then out := out ++ (← indexFiles e.path)
    else if e.fileName == "index.html" then out := e.path :: out
  return out

/-- `find_all_pages`: a file as is; a site directory ordered by its numbered table of contents. -/
def findAllPages (input : System.FilePath) : IO (List System.FilePath) := do
  if !(← input.isDir) then return [input]
  let rootIndex := input / "index.html"
  if !(← rootIndex.pathExists) then
    IO.eprintln s!"Error: {rootIndex} not found"; IO.Process.exit 1
  let mut pageOfNum : List (String × System.FilePath) := []
  for idx in (← indexFiles input).mergeSort (fun a b => a.toString ≤ b.toString) do
    let text ← IO.FS.readBinFile idx
    for (num, href) in navRows text do
      let num := stripDots num
      if pageOfNum.all (·.1 != num) then
        if let some page ← resolvePage idx href input then
          pageOfNum := pageOfNum ++ [(num, page)]
  let mut pages := [rootIndex]
  let mut seen := [← IO.FS.realPath rootIndex]
  for (_, page) in pageOfNum.mergeSort (fun a b => keyLt (numKey a.1) (numKey b.1) || numKey a.1 == numKey b.1) do
    let rp ← IO.FS.realPath page
    if !seen.contains rp then
      seen := rp :: seen; pages := pages ++ [page]
  if pages.length == 1 then
    IO.eprintln "warning: no numbered table-of-contents found; rendering the root page only"
  return pages

def main (args : List String) : IO UInt32 := do
  match args with
  | [input, output] =>
    let inputP : System.FilePath := input
    let pages ← findAllPages inputP
    let baseDir := if ← inputP.isDir then inputP else inputP.parent.getD "."
    IO.println s!"Found {pages.length} HTML page(s); base {baseDir}"
    let mut contents := []
    for p in pages do contents := contents ++ [← IO.FS.readBinFile p]
    let (merged, problems) := merge contents
    if problems.isEmpty then
      IO.eprintln "heading-nesting check: PASS — the source outline is already properly nested; the _renumber_headings fallback made no changes."
    else
      IO.eprintln s!"heading-nesting check: MIS-NESTED — {problems.length} problem(s) in the source outline; the _renumber_headings fallback re-levelled them so the PDF bookmark tree stays well-formed (see verso-blueprint #130):"
      for p in problems.take 20 do IO.eprintln s!"  • {p}"
      if problems.length > 20 then IO.eprintln s!"  … and {problems.length - 20} more"
    if let some d := (output : System.FilePath).parent then IO.FS.createDirAll d
    IO.FS.writeBinFile output merged
    IO.println s!"Print page written: {output} ({merged.size / 1024} KB)"
    return 0
  | _ =>
    IO.eprintln "usage: blueprint-print HTML_INPUT OUT_HTML"; return 2

end Tools.BlueprintPrint

public def main (args : List String) : IO UInt32 := Tools.BlueprintPrint.main args
