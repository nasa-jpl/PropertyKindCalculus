module

/-!
Fixed-point formatting of a double with the semantics of Python's `f"{x:.Nf}"`: the
*exact* binary value is rounded to `N` decimals, ties to even, and a negative value that
rounds to zero keeps its sign. The figures' generators were Python; their committed bytes
depend on this and nothing else about floats.
-/

namespace Tools.Figures

/-- `(m, e)` with `x = m · 2^e` exactly (finite `x`). -/
public def floatParts (x : Float) : Nat × Int :=
  let bits := x.toBits
  let expo := ((bits >>> 52) &&& 0x7FF).toNat
  let frac := (bits &&& 0xFFFFFFFFFFFFF).toNat
  if expo == 0 then (frac, -1074) else (frac + 2 ^ 52, (expo : Int) - 1075)

/-- Round the exact rational `num / den` to the nearest integer, ties to even. -/
public def roundHalfEven (num den : Nat) : Nat :=
  let q := num / den
  let r := num % den
  if 2 * r > den then q + 1
  else if 2 * r == den then (if q % 2 == 1 then q + 1 else q)
  else q

/-- Python's `f"{x:.{d}f}"` for a finite `x`. -/
public def fmtFixed (d : Nat) (x : Float) : String :=
  let neg := x.toBits >>> 63 != 0
  let (m, e) := floatParts x
  let (num, den) : Nat × Nat :=
    if e ≥ 0 then (m * 2 ^ e.toNat * 10 ^ d, 1) else (m * 10 ^ d, 2 ^ (-e).toNat)
  let digits := toString (roundHalfEven num den)
  let digits := if digits.length ≤ d then
      String.ofList (List.replicate (d + 1 - digits.length) '0') ++ digits else digits
  let cs := digits.toList
  let int := String.ofList (cs.take (cs.length - d))
  let body := if d == 0 then int else int ++ "." ++ String.ofList (cs.drop (cs.length - d))
  if neg then "-" ++ body else body

/-- `xml.sax.saxutils.escape`: `&`, `<`, `>`. -/
public def escape (s : String) : String :=
  s.foldl (init := "") fun acc c =>
    match c with
    | '&' => acc ++ "&amp;" | '<' => acc ++ "&lt;" | '>' => acc ++ "&gt;" | c => acc.push c

end Tools.Figures
