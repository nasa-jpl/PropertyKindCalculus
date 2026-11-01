module

/-!
# `file-links`: make Verso `html-multi` output navigable over `file://`

    lean --run tools/Tools/FileLinks.lean HTML_MULTI_DIR [--strict]
    lake exe file-links HTML_MULTI_DIR [--strict]

Verso writes every internal link as a *directory* URL with a trailing slash
(`Chapter/#anchor`), resolved through a per-page `<base href>` naming the site root. A web
server maps `Chapter/` to `Chapter/index.html`; a browser opening a `file://` directory URL
shows the folder instead. This pass rewrites the link *targets* to spell out `index.html`:

    Chapter/#anchor            -> Chapter/index.html#anchor
    Chapter/Section/#anchor     -> Chapter/Section/index.html#anchor
    find/?domain=...            -> find/index.html?domain=...
    ./   ./../   ""             -> index.html            (home links: the base is the root)
    #anchor                     -> index.html#anchor     (a root-page anchor)

Left alone: the `<base href>` tag, external and non-navigational schemes (`://`, `mailto:`,
`data:`, `javascript:`), the bare `#` (a script hook), a bare `?query`, and every href that
already names a file (assets, `.html`). Over HTTP `Chapter/index.html` resolves as `Chapter/`
did, so the pass is safe for the served site too.

Everything is defined over `List Char`, where the proofs live, and wrapped in `String` at the
edge. The page is tokenised into text and `href="…"` pieces (`tokenize`, `render` its inverse on
what it produces), each non-`<base>` href rewritten by `fixChars`: `fixSegs` on the path's
`/`-segments, suffix (`#…`, `?…`) kept. The theorems are the rerun's: `fixHref_idem` (every href
value is a fixpoint after one rewrite) and `rewriteHtml_idem` (a second pass over a rewritten
page changes nothing — its tokens are the first pass's, `tokenize_render`). The run also decides
`fixHref (fixHref h) == fixHref h` on every href it rewrites, failing loudly if that ever broke.
Every rewritten target is then looked up under `HTML_MULTI_DIR` — against the root, which the
`<base>` names, with `.`/`..` resolved as a browser would (`targetFile`); a missing one is
reported, and fails the run under `--strict`. The tool imports nothing beyond the core toolchain,
so it runs before anything is built.
-/

namespace Tools.FileLinks

/-! ## Segments -/

/-- Split on one character; `splitChar c l` is never empty, and no piece contains `c`. -/
def splitChar (c : Char) : List Char → List (List Char)
  | [] => [[]]
  | x :: xs =>
    let r := splitChar c xs
    if x = c then [] :: r
    else match r with
      | [] => [[x]]
      | s :: rest => (x :: s) :: rest

/-- The pieces joined back with `c` between them. -/
def joinChar (c : Char) : List (List Char) → List Char
  | [] => []
  | [s] => s
  | s :: ss => s ++ c :: joinChar c ss

theorem splitChar_ne_nil (c : Char) (l : List Char) : splitChar c l ≠ [] := by
  induction l with
  | nil => simp [splitChar]
  | cons x xs ih =>
    simp only [splitChar]
    split
    · simp
    · split <;> simp

theorem not_mem_of_mem_splitChar {c : Char} {l s : List Char} (h : s ∈ splitChar c l) : c ∉ s := by
  induction l generalizing s with
  | nil => simp [splitChar] at h; simp [h]
  | cons x xs ih =>
    simp only [splitChar] at h
    split at h
    · rcases List.mem_cons.1 h with rfl | h
      · simp
      · exact ih h
    · rename_i hx
      split at h
      · rename_i hr; exact absurd hr (splitChar_ne_nil c xs)
      · rename_i t rest hr
        rcases List.mem_cons.1 h with rfl | h
        · have : t ∈ splitChar c xs := by rw [hr]; exact List.mem_cons_self
          have := ih this
          intro hm
          rcases List.mem_cons.1 hm with hc | hc
          · exact hx hc.symm
          · exact this hc
        · exact ih (by rw [hr]; exact List.mem_cons_of_mem _ h)

theorem mem_of_mem_splitChar {c x : Char} {l s : List Char} (hs : s ∈ splitChar c l) (hx : x ∈ s) :
    x ∈ l := by
  induction l generalizing s with
  | nil => simp [splitChar] at hs; simp [hs] at hx
  | cons y ys ih =>
    simp only [splitChar] at hs
    split at hs
    · rcases List.mem_cons.1 hs with rfl | hs
      · simp at hx
      · exact List.mem_cons_of_mem _ (ih hs hx)
    · split at hs
      · rename_i hr; exact absurd hr (splitChar_ne_nil c ys)
      · rename_i t rest hr
        rcases List.mem_cons.1 hs with rfl | hs
        · rcases List.mem_cons.1 hx with rfl | hx
          · exact List.mem_cons_self
          · exact List.mem_cons_of_mem _
              (ih (by rw [hr]; exact List.mem_cons_self) hx)
        · exact List.mem_cons_of_mem _ (ih (by rw [hr]; exact List.mem_cons_of_mem _ hs) hx)

theorem mem_joinChar {c x : Char} {ss : List (List Char)} (h : x ∈ joinChar c ss) :
    x = c ∨ ∃ s ∈ ss, x ∈ s := by
  induction ss with
  | nil => simp [joinChar] at h
  | cons s ss ih =>
    match ss, ih with
    | [], _ => right; exact ⟨s, List.mem_cons_self, by simpa [joinChar] using h⟩
    | t :: ts, ih =>
      simp only [joinChar, List.mem_append, List.mem_cons] at h
      rcases h with h | h | h
      · right; exact ⟨s, List.mem_cons_self, h⟩
      · left; exact h
      · rcases ih h with h | ⟨u, hu, hx⟩
        · left; exact h
        · right; exact ⟨u, List.mem_cons_of_mem _ hu, hx⟩

theorem splitChar_append_of_not_mem {c : Char} {s l : List Char} (hs : c ∉ s) :
    splitChar c (s ++ l) =
      (s ++ (splitChar c l).headD []) :: (splitChar c l).tail := by
  induction s with
  | nil =>
    simp only [List.nil_append]
    rcases h : splitChar c l with _ | ⟨t, rest⟩
    · exact absurd h (splitChar_ne_nil c l)
    · simp
  | cons x xs ih =>
    have hx : x ≠ c := fun h => hs (h ▸ List.mem_cons_self)
    have hxs : c ∉ xs := fun h => hs (List.mem_cons_of_mem _ h)
    simp only [List.cons_append, splitChar, ih hxs, hx, ↓reduceIte]

theorem splitChar_joinChar {c : Char} {ss : List (List Char)} (hne : ss ≠ [])
    (h : ∀ s ∈ ss, c ∉ s) : splitChar c (joinChar c ss) = ss := by
  induction ss with
  | nil => exact absurd rfl hne
  | cons s ss ih =>
    match ss, ih with
    | [], _ =>
      simp only [joinChar]
      rw [← List.append_nil s, splitChar_append_of_not_mem (h s List.mem_cons_self)]
      simp [splitChar]
    | t :: ts, ih =>
      simp only [joinChar]
      rw [splitChar_append_of_not_mem (h s List.mem_cons_self)]
      have := ih (by simp) (fun u hu => h u (List.mem_cons_of_mem _ hu))
      simp only [splitChar, this, ↓reduceIte]
      simp

theorem joinChar_eq_nil {c : Char} {ss : List (List Char)} (h : joinChar c ss = []) :
    ss = [] ∨ ss = [[]] := by
  match ss with
  | [] => left; rfl
  | [s] => right; simp [joinChar] at h; simp [h]
  | s :: t :: ts => simp [joinChar] at h

/-- A path segment that only climbs or stays: `.` or `..`. -/
def isDots (s : List Char) : Bool := s = ['.'] || s = ['.', '.']

/-- `index.html`, the file a directory URL names. -/
def idx : List Char := "index.html".toList

/-- The rewrite on a path's `/`-separated segments. A directory path ends in the empty
segment; one made only of dots is a home link. Anything else is a file and stays. -/
def fixSegs (segs : List (List Char)) : List (List Char) :=
  match segs.getLast? with
  | some [] =>
      if segs.dropLast ≠ [] ∧ segs.dropLast.all isDots then [idx] else segs.dropLast ++ [idx]
  | _ => segs

theorem idx_ne_nil : idx ≠ [] := by decide

theorem fixSegs_idem (s : List (List Char)) : fixSegs (fixSegs s) = fixSegs s := by
  by_cases h : s.getLast? = some []
  · have hs : fixSegs s =
        (if s.dropLast ≠ [] ∧ s.dropLast.all isDots then [idx]
         else s.dropLast ++ [idx]) := by
      simp [fixSegs, h]
    rw [hs]; split <;> simp [fixSegs, idx_ne_nil]
  · have hs : fixSegs s = s := by
      unfold fixSegs; split <;> simp_all
    rw [hs, hs]

theorem mem_of_mem_dropLast {α} {x : α} {l : List α} (h : x ∈ l.dropLast) : x ∈ l := by
  induction l with
  | nil => simp at h
  | cons y ys ih =>
    cases ys with
    | nil => simp at h
    | cons z zs =>
      rw [List.dropLast_cons_cons] at h
      rcases List.mem_cons.1 h with rfl | h
      · exact List.mem_cons_self
      · exact List.mem_cons_of_mem _ (ih h)

theorem mem_fixSegs {s : List Char} {ss : List (List Char)} (h : s ∈ fixSegs ss) :
    s ∈ ss ∨ s = idx := by
  unfold fixSegs at h
  split at h
  · split at h
    · right; simpa using h
    · simp only [List.mem_append, List.mem_singleton] at h
      rcases h with h | h
      · left; exact mem_of_mem_dropLast h
      · right; exact h
  · left; exact h

theorem fixSegs_ne_nil {ss : List (List Char)} (h : ss ≠ []) : fixSegs ss ≠ [] := by
  unfold fixSegs; split
  · split <;> simp
  · exact h

/-- The rewritten path of a nonempty path is nonempty. -/
theorem joinChar_fixSegs_ne_nil {ss : List (List Char)} (h : ss ≠ []) :
    joinChar '/' (fixSegs ss) ≠ [] := by
  intro hj
  rcases joinChar_eq_nil hj with h1 | h1
  · exact fixSegs_ne_nil h h1
  · unfold fixSegs at h1
    split at h1
    · split at h1
      · simp at h1; exact idx_ne_nil h1
      · rcases List.append_eq_singleton_iff.1 h1 with ⟨_, h2⟩ | ⟨_, h2⟩
        · simp at h2; exact idx_ne_nil h2
        · simp at h2
    · rename_i hl; subst h1; simp at hl

/-! ## One href -/

/-- The href stops being a path at its first `#` or `?`. -/
def inPath (c : Char) : Bool := c != '#' && c != '?'

/-- `(path, suffix)`: the href up to its first `#` or `?`, and the rest. -/
def splitSuffix (v : List Char) : List Char × List Char :=
  (v.takeWhile inPath, v.dropWhile inPath)

/-- `://` occurs. -/
def hasSep : List Char → Bool
  | ':' :: '/' :: '/' :: _ => true
  | _ :: rest => hasSep rest
  | [] => false

/-- An external or non-navigational href. -/
def hasScheme (v : List Char) : Bool :=
  hasSep v || ["mailto", "data", "javascript"].any fun s => s.toList == v.takeWhile (· != ':')

/-- The rewrite of one href value (`fix_href` of the Python pass, rule for rule). -/
def fixChars (v : List Char) : List Char :=
  if v = [] then idx
  else if v = ['#'] then v
  else if v.head? = some '#' then idx ++ v
  else if hasScheme v then v
  else if v.takeWhile inPath = [] then v
  else joinChar '/' (fixSegs (splitChar '/' (v.takeWhile inPath))) ++ v.dropWhile inPath

theorem takeWhile_append_of_all {p : Char → Bool} {a b : List Char} (ha : ∀ x ∈ a, p x)
    (hb : b = [] ∨ ∃ y ys, b = y :: ys ∧ ¬ p y) :
    a.takeWhile p ++ b = a ++ b ∧ (a ++ b).takeWhile p = a ∧ (a ++ b).dropWhile p = b := by
  induction a with
  | nil =>
    refine ⟨rfl, ?_, ?_⟩ <;> rcases hb with rfl | ⟨y, ys, rfl, hy⟩ <;>
      simp_all [List.takeWhile_cons_of_neg, List.dropWhile_cons_of_neg]
  | cons x xs ih =>
    have hx := ha x List.mem_cons_self
    obtain ⟨h1, h2, h3⟩ := ih (fun y hy => ha y (List.mem_cons_of_mem _ hy))
    simp [List.takeWhile_cons_of_pos hx, List.dropWhile_cons_of_pos hx, h1, h2, h3]

theorem mem_takeWhile {p : Char → Bool} {l : List Char} {x : Char} (h : x ∈ l.takeWhile p) :
    p x ∧ x ∈ l := by
  induction l with
  | nil => simp at h
  | cons y ys ih =>
    by_cases hy : p y
    · rw [List.takeWhile_cons_of_pos hy] at h
      rcases List.mem_cons.1 h with rfl | h
      · exact ⟨hy, List.mem_cons_self⟩
      · exact ⟨(ih h).1, List.mem_cons_of_mem _ (ih h).2⟩
    · rw [List.takeWhile_cons_of_neg hy] at h; simp at h

theorem dropWhile_shape (p : Char → Bool) (l : List Char) :
    l.dropWhile p = [] ∨ ∃ y ys, l.dropWhile p = y :: ys ∧ ¬ p y := by
  induction l with
  | nil => left; rfl
  | cons x xs ih =>
    by_cases hx : p x
    · rw [List.dropWhile_cons_of_pos hx]; exact ih
    · right; exact ⟨x, xs, List.dropWhile_cons_of_neg hx, hx⟩

theorem mem_of_mem_dropWhile {p : Char → Bool} {l : List Char} {x : Char}
    (h : x ∈ l.dropWhile p) : x ∈ l := by
  induction l with
  | nil => simp at h
  | cons y ys ih =>
    by_cases hy : p y
    · rw [List.dropWhile_cons_of_pos hy] at h; exact List.mem_cons_of_mem _ (ih h)
    · rw [List.dropWhile_cons_of_neg hy] at h; exact h

theorem idx_inPath : ∀ x ∈ idx, inPath x := by decide
theorem idx_no_slash : '/' ∉ idx := by decide
theorem idx_no_quote : '"' ∉ idx := by decide

/-- The characters of a rewritten href come from the href, from `index.html`, or are `/`. -/
theorem mem_fixChars {v : List Char} {x : Char} (h : x ∈ fixChars v) :
    x ∈ v ∨ x ∈ idx ∨ x = '/' := by
  unfold fixChars at h
  split at h
  · right; left; exact h
  split at h
  · left; exact h
  split at h
  · rcases List.mem_append.1 h with h | h
    · right; left; exact h
    · left; exact h
  split at h
  · left; exact h
  split at h
  · left; exact h
  · rcases List.mem_append.1 h with h | h
    · rcases mem_joinChar h with rfl | ⟨s, hs, hx⟩
      · right; right; rfl
      · rcases mem_fixSegs hs with hs | rfl
        · left; exact (mem_takeWhile (mem_of_mem_splitChar hs hx)).2
        · right; left; exact hx
    · left; exact mem_of_mem_dropWhile h

/-- The rewritten branch, spelled out. -/
theorem fixChars_eq_of_path {v : List Char} (h1 : v ≠ []) (h2 : v ≠ ['#'])
    (h3 : v.head? ≠ some '#') (h4 : hasScheme v = false) (h5 : v.takeWhile inPath ≠ []) :
    fixChars v = joinChar '/' (fixSegs (splitChar '/' (v.takeWhile inPath))) ++ v.dropWhile inPath := by
  simp [fixChars, h1, h2, h3, h4, h5]

theorem fixChars_idx : fixChars idx = idx := by decide

/-- A rewritten path with its suffix is a fixpoint: the shape every rewrite produces. -/
theorem fixChars_fixpoint {ss : List (List Char)} {suffix : List Char} (hss : ss ≠ [])
    (hin : ∀ s ∈ ss, ∀ x ∈ s, inPath x) (hsl : ∀ s ∈ ss, '/' ∉ s)
    (hsuf : suffix = [] ∨ ∃ y ys, suffix = y :: ys ∧ ¬ inPath y) :
    fixChars (joinChar '/' (fixSegs ss) ++ suffix) = joinChar '/' (fixSegs ss) ++ suffix := by
  have hp'_ne : joinChar '/' (fixSegs ss) ≠ [] := joinChar_fixSegs_ne_nil hss
  have hp'_in : ∀ x ∈ joinChar '/' (fixSegs ss), inPath x := by
    intro x hx
    rcases mem_joinChar hx with rfl | ⟨s, hs, hxs⟩
    · decide
    · rcases mem_fixSegs hs with hs | rfl
      · exact hin s hs x hxs
      · exact idx_inPath x hxs
  have hne : joinChar '/' (fixSegs ss) ++ suffix ≠ [] := by simp [hp'_ne]
  have hne2 : joinChar '/' (fixSegs ss) ++ suffix ≠ ['#'] := by
    intro h
    rcases List.append_eq_singleton_iff.1 h with ⟨h, _⟩ | ⟨h, _⟩
    · exact hp'_ne h
    · have := hp'_in '#' (by rw [h]; exact List.mem_cons_self); simp [inPath] at this
  have hne3 : (joinChar '/' (fixSegs ss) ++ suffix).head? ≠ some '#' := by
    intro h
    cases hp : joinChar '/' (fixSegs ss) with
    | nil => exact hp'_ne hp
    | cons c cs =>
      rw [hp] at h; simp at h
      have := hp'_in c (by rw [hp]; exact List.mem_cons_self); rw [h] at this
      simp [inPath] at this
  by_cases hs : hasScheme (joinChar '/' (fixSegs ss) ++ suffix)
  · unfold fixChars; simp only [hne, hne2, hne3, hs, ↓reduceIte]
  · have hsplit := takeWhile_append_of_all hp'_in hsuf
    rw [fixChars_eq_of_path hne hne2 hne3 (by simpa using hs) (by rw [hsplit.2.1]; exact hp'_ne),
      hsplit.2.1, hsplit.2.2]
    have hnoslash : ∀ s ∈ fixSegs ss, '/' ∉ s := by
      intro s hs
      rcases mem_fixSegs hs with hs | rfl
      · exact hsl s hs
      · exact idx_no_slash
    rw [splitChar_joinChar (fixSegs_ne_nil hss) hnoslash, fixSegs_idem]

theorem fixChars_idem (v : List Char) : fixChars (fixChars v) = fixChars v := by
  by_cases h1 : v = []
  · subst h1; simp only [fixChars, ite_true]; exact fixChars_idx
  by_cases h2 : v = ['#']
  · subst h2; simp [fixChars]
  by_cases h3 : v.head? = some '#'
  · have hv : fixChars v = idx ++ v := by simp [fixChars, h1, h2, h3]
    rw [hv]
    obtain ⟨rest, rfl⟩ : ∃ rest, v = '#' :: rest := by
      cases v with
      | nil => exact absurd rfl h1
      | cons c cs => simp at h3; exact ⟨cs, by rw [h3]⟩
    have hidx : joinChar '/' (fixSegs [idx]) = idx := by
      simp [fixSegs, idx_ne_nil, joinChar]
    rw [← hidx]
    exact fixChars_fixpoint (by simp) (by simpa using idx_inPath) (by simpa using idx_no_slash)
      (Or.inr ⟨'#', rest, rfl, by decide⟩)
  by_cases h4 : hasScheme v
  · simp [fixChars, h1, h2, h3, h4]
  by_cases h5 : v.takeWhile inPath = []
  · have : fixChars v = v := by simp [fixChars, h1, h2, h3, h4, h5]
    rw [this, this]
  rw [fixChars_eq_of_path h1 h2 h3 (by simpa using h4) h5]
  exact fixChars_fixpoint (splitChar_ne_nil _ _)
    (fun s hs x hx => (mem_takeWhile (mem_of_mem_splitChar hs hx)).1)
    (fun s hs => not_mem_of_mem_splitChar hs) (dropWhile_shape inPath v)

/-! ## One page -/

/-- A page is text and `href="…"` attributes; `base` marks the `<base href>`, left alone. -/
inductive Piece
  | text (t : List Char)
  | href (base : Bool) (v : List Char)
  deriving Repr, DecidableEq

/-- `href="`. -/
def pat : List Char := "href=\"".toList

/-- The text before an href, reversed, ends in `<base `. -/
def isBase (acc : List Char) : Bool := " esab<".toList.isPrefixOf acc

/-- Left to right: at `href="` take the value up to the closing quote; an unterminated one
is text to the end. `acc` is the text passed over, reversed. -/
def tokenize (acc l : List Char) : List Piece :=
  if _hp : pat.isPrefixOf l then
    match _hd : (l.drop pat.length).dropWhile (· != '"') with
    | '"' :: after =>
      .text acc.reverse :: .href (isBase acc) ((l.drop pat.length).takeWhile (· != '"')) :: tokenize [] after
    | _ => [.text (acc.reverse ++ l)]
  else match l with
    | [] => [.text acc.reverse]
    | c :: rest => tokenize (c :: acc) rest
termination_by l.length
decreasing_by
  · have h1 : pat.length ≤ l.length := (List.isPrefixOf_iff_prefix.1 _hp).length_le
    have h2 := congrArg List.length _hd
    have h3 := congrArg List.length (List.takeWhile_append_dropWhile (p := (· != '"')) (l := l.drop pat.length))
    simp only [List.length_cons, List.length_drop, List.length_append] at h2 h3
    have : pat.length = 6 := by decide
    omega
  · simp

/-- The page back from its pieces. -/
def render : List Piece → List Char
  | [] => []
  | .text t :: ps => t ++ render ps
  | .href _ v :: ps => pat ++ v ++ '"' :: render ps

/-- An href's new value: a `<base>` keeps its own, any other goes through `fixChars`. -/
def fixVal (base : Bool) (v : List Char) : List Char := bif base then v else fixChars v

theorem fixVal_idem (b : Bool) (v : List Char) : fixVal b (fixVal b v) = fixVal b v := by
  cases b <;> simp [fixVal, fixChars_idem]

/-- The rewrite of one piece. -/
def fixPiece : Piece → Piece
  | .text t => .text t
  | .href b v => .href b (fixVal b v)

theorem fixPiece_idem (p : Piece) : fixPiece (fixPiece p) = fixPiece p := by
  cases p <;> simp [fixPiece, fixVal_idem]

/-- The rewritten page. -/
def rewriteChars (html : List Char) : List Char := render ((tokenize [] html).map fixPiece)

theorem pat_length : pat.length = 6 := by decide

theorem render_tokenize (acc l : List Char) : render (tokenize acc l) = acc.reverse ++ l := by
  induction acc, l using tokenize.induct with
  | case1 acc l hp after hd ih =>
    rw [tokenize]; simp only [hp, ↓reduceDIte]
    split
    · rename_i after' h
      rw [hd] at h; cases h
      simp only [render, ih, List.reverse_nil, List.nil_append]
      have h1 : pat ++ l.drop pat.length = l := by
        have := List.take_append_drop pat.length l
        rwa [← List.prefix_iff_eq_take.1 (List.isPrefixOf_iff_prefix.1 hp)] at this
      have h2 := List.takeWhile_append_dropWhile (p := (· != '"')) (l := l.drop pat.length)
      rw [hd] at h2
      simp only [List.append_assoc]; rw [h2, h1]
    · exfalso; simp_all
  | case2 acc l hp hne =>
    rw [tokenize]; simp only [hp, ↓reduceDIte]
    first
    | simp [render]
    | (split
       · rename_i after h; exact absurd h (hne after)
       · simp [render])
  | case3 acc hp => rw [tokenize]; simp [hp, render]
  | case4 acc c rest hp ih => rw [tokenize]; simp [hp, ih]

/-! ## The second run -/

/-- No `href="` starts inside `t` when `s` follows it. -/
def NoOcc (t s : List Char) : Prop := ∀ i, i < t.length → ¬ pat <+: (t ++ s).drop i

theorem noOcc_nil (s : List Char) : NoOcc [] s := fun _ h => absurd h (Nat.not_lt_zero _)

theorem noOcc_cons {c : Char} {t s : List Char} (h : NoOcc (c :: t) s) : NoOcc t s :=
  fun i hi => h (i + 1) (by simp; omega)

theorem noOcc_head {c : Char} {t s : List Char} (h : NoOcc (c :: t) s) :
    pat.isPrefixOf (c :: (t ++ s)) = false := by
  rw [Bool.eq_false_iff]
  intro hp
  exact h 0 (by simp) (by simpa using List.isPrefixOf_iff_prefix.1 hp)

/-- The tokenizer walks over text that starts no href. -/
theorem tokenize_text {t : List Char} : ∀ {s acc : List Char}, NoOcc t s →
    tokenize acc (t ++ s) = tokenize (t.reverse ++ acc) s := by
  induction t with
  | nil => intros; simp
  | cons c t ih =>
    intro s acc h
    rw [List.cons_append, tokenize]
    simp only [noOcc_head h, Bool.false_eq_true, ↓reduceDIte]
    rw [ih (noOcc_cons h)]; simp

/-- Whether `href="` starts inside `t` is settled by `t` and the `href="` that follows it. -/
theorem noOcc_pat {t s s' : List Char} (h : NoOcc t (pat ++ s)) : NoOcc t (pat ++ s') := by
  intro i hi hpre
  apply h i hi
  rw [List.drop_append_of_le_length (by omega)] at hpre ⊢
  rw [← List.append_assoc] at hpre ⊢
  have hlen : pat.length ≤ (t.drop i ++ pat).length := by simp
  rw [List.prefix_iff_eq_take, List.take_append_of_le_length hlen] at hpre ⊢
  exact hpre

theorem noOcc_snoc {acc rest : List Char} {c : Char} (h : NoOcc acc.reverse (c :: rest))
    (hp : ¬ pat.isPrefixOf (c :: rest) = true) : NoOcc (c :: acc).reverse rest := by
  intro i hi hpre
  simp only [List.reverse_cons, List.length_append, List.length_singleton] at hi
  rw [List.reverse_cons, List.append_assoc, List.singleton_append] at hpre
  by_cases hlt : i < acc.reverse.length
  · exact h i hlt hpre
  · have hi' : i = acc.reverse.length := by omega
    rw [hi', List.drop_append_of_le_length (Nat.le_refl _), List.drop_length, List.nil_append] at hpre
    exact hp (List.isPrefixOf_iff_prefix.2 hpre)

theorem no_quote_takeWhile (l : List Char) : '"' ∉ l.takeWhile (· != '"') := fun h => by
  have := (mem_takeWhile h).1; simp at this

theorem no_quote_fixVal {b : Bool} {v : List Char} (h : '"' ∉ v) : '"' ∉ fixVal b v := by
  cases b
  · intro hx
    rcases mem_fixChars (by simpa [fixVal] using hx) with hx | hx | hx
    · exact h hx
    · exact idx_no_quote hx
    · exact absurd hx (by decide)
  · simpa [fixVal] using h

/-- A rewritten page tokenises into the rewritten pieces: the second run sees what the first
produced. -/
theorem tokenize_render (acc l : List Char) (h : NoOcc acc.reverse l) :
    tokenize [] (render ((tokenize acc l).map fixPiece)) = (tokenize acc l).map fixPiece := by
  induction acc, l using tokenize.induct with
  | case1 acc l hp after hd ih =>
    have h1 : pat ++ l.drop pat.length = l := by
      have := List.take_append_drop pat.length l
      rwa [← List.prefix_iff_eq_take.1 (List.isPrefixOf_iff_prefix.1 hp)] at this
    have h2 := List.takeWhile_append_dropWhile (p := (· != '"')) (l := l.drop pat.length)
    rw [hd] at h2
    have e : tokenize acc l = .text acc.reverse ::
        .href (isBase acc) ((l.drop pat.length).takeWhile (· != '"')) :: tokenize [] after := by
      rw [tokenize]; simp only [hp, ↓reduceDIte]
      split
      · rename_i after' h'; rw [hd] at h'; cases h'; rfl
      · exfalso; simp_all
    rw [e]
    simp only [List.map_cons, fixPiece, render]
    · have hnq := no_quote_fixVal (b := isBase acc) (no_quote_takeWhile (l.drop pat.length))
      have hocc : NoOcc acc.reverse (pat ++ (fixVal (isBase acc) ((l.drop pat.length).takeWhile (· != '"'))
          ++ '"' :: render ((tokenize [] after).map fixPiece))) := by
        apply noOcc_pat (s := l.drop pat.length)
        rw [h1]; exact h
      simp only [List.append_assoc]; rw [tokenize_text hocc]
      simp only [List.reverse_reverse, List.append_nil]
      have hpre : pat.isPrefixOf (pat ++ (fixVal (isBase acc) ((l.drop pat.length).takeWhile (· != '"'))
          ++ '"' :: render ((tokenize [] after).map fixPiece))) = true :=
        List.isPrefixOf_iff_prefix.2 (List.prefix_append _ _)
      have hsplit := takeWhile_append_of_all (p := (· != '"')) (fun x hx => by
          have : x ≠ '"' := fun e => by rw [e] at hx; exact hnq hx
          simpa using this)
        (Or.inr ⟨'"', render ((tokenize [] after).map fixPiece), rfl, by simp⟩)
      have e2 : tokenize acc (pat ++ (fixVal (isBase acc) ((l.drop pat.length).takeWhile (· != '"'))
          ++ '"' :: render ((tokenize [] after).map fixPiece))) =
          .text acc.reverse :: .href (isBase acc) (fixVal (isBase acc) ((l.drop pat.length).takeWhile (· != '"')))
            :: tokenize [] (render ((tokenize [] after).map fixPiece)) := by
        rw [tokenize]; simp only [hpre, ↓reduceDIte, List.drop_left]
        split
        · rename_i after'' h''
          rw [List.drop_left, hsplit.2.2] at h''; cases h''
          rw [hsplit.2.1]
        · exfalso; rename_i h''; simp_all [hsplit.2.2]
      rw [e2, ih (noOcc_nil _)]
  | case2 acc l hp hne =>
    have e : tokenize acc l = [.text (acc.reverse ++ l)] := by
      rw [tokenize]; simp only [hp, ↓reduceDIte]
      all_goals first | rfl | (split <;> simp_all)
    rw [e]
    simp only [List.map_cons, List.map_nil, fixPiece, render, List.append_nil]
    rw [tokenize_text h]; simpa using e
  | case3 acc hp =>
    have e : tokenize acc [] = [.text acc.reverse] := by rw [tokenize]; simp [hp]
    rw [e]
    simp only [List.map_cons, List.map_nil, fixPiece, render, List.append_nil]
    have := tokenize_text (acc := []) h
    simp only [List.append_nil, List.reverse_reverse] at this
    rw [this]; try rw [e]
  | case4 acc c rest hp ih =>
    have e : tokenize acc (c :: rest) = tokenize (c :: acc) rest := by rw [tokenize]; simp [hp]
    rw [e]; exact ih (noOcc_snoc h hp)

theorem rewriteChars_idem (html : List Char) : rewriteChars (rewriteChars html) = rewriteChars html := by
  unfold rewriteChars
  rw [tokenize_render [] html (noOcc_nil _), List.map_map]
  congr 1
  apply List.map_congr_left
  intro p _
  exact fixPiece_idem p

/-! ## Strings -/

/-- The rewrite of one href value. -/
def fixHref (v : String) : String := String.ofList (fixChars v.toList)

theorem fixHref_idem (h : String) : fixHref (fixHref h) = fixHref h := by
  simp [fixHref, String.toList_ofList, fixChars_idem]

/-- The rewritten page and the hrefs it rewrote (old, new). -/
def rewriteHtml (html : String) : String × List (String × String) :=
  let toks := tokenize [] html.toList
  (String.ofList (rewriteChars html.toList),
   toks.filterMap fun
     | .href false v =>
       let n := fixChars v
       if n == v then none else some (String.ofList v, String.ofList n)
     | _ => none)

theorem rewriteHtml_idem (html : String) :
    (rewriteHtml (rewriteHtml html).1).1 = (rewriteHtml html).1 := by
  unfold rewriteHtml
  simp only [String.toList_ofList, rewriteChars_idem]

/-! ## The run -/

partial def htmlFiles (dir : System.FilePath) (rel : String) : IO (List String) := do
  let mut out := []
  for e in ← (dir / rel).readDir do
    let r := if rel == "." then e.fileName else rel ++ "/" ++ e.fileName
    if (← (dir / r).isDir) then out := out ++ (← htmlFiles dir r)
    else if e.fileName.endsWith ".html" then out := r :: out
  return out

/-- The file a rewritten href names under the site root. Every page's `<base href>` names the
root, so an href is root-relative wherever the page sits; empty and `.` segments are skipped, each
`..` pops the preceding segment and never climbs above the root — a browser's resolution. -/
def targetFile (new : String) : String :=
  let segs := (splitChar '/' (new.toList.takeWhile inPath)).foldl (init := ([] : List (List Char)))
    fun stack seg =>
      if seg = [] ∨ seg = ['.'] then stack
      else if seg = ['.', '.'] then stack.drop 1
      else seg :: stack
  String.ofList (joinChar '/' segs.reverse)

def main (args : List String) : IO UInt32 := do
  let strict := args.contains "--strict"
  match args.filter (· != "--strict") with
  | [root] =>
    let dir : System.FilePath := root
    if !(← dir.isDir) then
      IO.eprintln s!"not a directory: {root}"; return 1
    let mut changed := 0
    let mut missing : List (String × String) := []
    for f in (← htmlFiles dir ".").mergeSort (· ≤ ·) do
      let text ← IO.FS.readFile (dir / f)
      let (new, done) := rewriteHtml text
      for (old, n) in done do
        if fixHref n != n then
          IO.eprintln s!"file-links: rewrite not idempotent on {f}: {old} -> {n} -> {fixHref n}"
          return 1
        if !(← (dir / targetFile n).pathExists) then missing := (f, n) :: missing
      if new != text then
        IO.FS.writeFile (dir / f) new; changed := changed + 1
    IO.println s!"file-links: rewrote directory links in {changed} html file(s) under {root}"
    if !missing.isEmpty then
      IO.eprintln s!"file-links: {missing.length} rewritten target(s) name no file under {root}:"
      for (f, n) in missing.reverse.take 20 do IO.eprintln s!"  {f}: {n}"
      if strict then return 1
    return 0
  | _ =>
    IO.eprintln "usage: file-links HTML_MULTI_DIR [--strict]"; return 2

end Tools.FileLinks

public def main (args : List String) : IO UInt32 := Tools.FileLinks.main args
