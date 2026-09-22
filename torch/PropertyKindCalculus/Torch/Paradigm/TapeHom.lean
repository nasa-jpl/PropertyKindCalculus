/-
`paradigm.tape_hom` — **tape-parity as one `NumCarrier`-homomorphism, closed by a tactic**.

`paradigm.tape_parity` proves that each `NumCarrier` operation on the tape carrier
`TapeBuilder s` preserves the `Evaluates` bridge to the eager `Tensor Float s` carrier, one
`Evaluates_*` lemma per operation (`Evaluates_add`, …, `Evaluates_exp`, plus the two leaf
formers). Read together, those lemmas *are* the statement that `Evaluates` is a
`NumCarrier`-homomorphism from the tape carrier to the eager carrier. This module makes that
reading a **named object** and supplies the **closure driver** that a per-kernel tape-parity
proof needs, so a kernel's parity is one line and names no op tree.

Two pieces:

* `IsNumCarrierHom R` bundles the per-operation preservation facts of a relation
  `R : TapeBuilder s → Tensor Float s → Prop` into a single record, and
  `Evaluates.isNumCarrierHom` is the witness that `Evaluates` is one — the homomorphism as
  one object that a future certified carrier pair keys on, rather than folklore scattered
  across the individual `Evaluates_*` lemmas.

* `tape_hom [defs…]` is a macro tactic. It `simp only`s an erase-set — the kernel's own
  authored (`…Q`) and derived (naked) definition **names, to unfold, never to restate a body** —
  together with the `@[simp] rfl` magnitude-erasure lemmas (`Quantity.add_magnitude`, …), which
  exposes the identical `+ − × ÷ exp √` op tree on *both* carriers; then it closes the goal
  congruence by congruence with the `Evaluates_*` alphabet, leaves and literal constants
  included. So the residual per-kernel cost of a parity proof is an `unfold` list — the kernel's
  own def names — and never a re-authored `+ − × exp` witness (`METROLOGICAL_RIGOR.md` §12).

**Honest ceiling — a tactic, not a free theorem.** Lean 4 has no relational parametricity, so
this is not the single quantified lemma "for every carrier-polymorphic `f`,
`Evaluates (f leaves) (f eager)`". `tape_hom` instead *discharges the statement for the concrete
kernel in hand* by unfolding that kernel's own definition and walking the exposed op tree with
the homomorphism alphabet. The general, reusable objects are therefore the named homomorphism
and the closure procedure; the per-kernel residual is the `unfold` list.

The negative probe in the test suite keeps it honest: with a deliberately wrong eager
right-hand side the exposed heads disagree, so the `Evaluates_*` step cannot unify and the
tactic fails to close — it cannot rubber-stamp a false parity. (That failure is *clean* only
when the caller has made the tape ops `local irreducible`, as `paradigm.tape_parity`'s clients
already do; the tactic assembles only `rfl` erasures and `Evaluates_*` applications, so a bug
in it yields a failed proof, never an unsound one.)

Plain (not a `module`) file: imports the parity alphabet and the core magnitude-erasure lemmas.
-/

module

public import PropertyKindCalculus.Torch.Paradigm.TapeParity
public import PropertyKindCalculus.Quantity
public import PropertyKindCalculus.QuantityClassification
public import PropertyKindCalculus.QuantityFunction
public import PropertyKindCalculus.OperatorTable

public section -- pkc-blanket
@[expose] section -- pkc-blanket-expose

open Spec TorchLean
open TorchLean TorchLean.Tensor
open Runtime.Autograd
open PropertyKindCalculus
open PropertyKindCalculus.Paradigm (TapeBuilder)
open PropertyKindCalculus.Paradigm.TapeParity

namespace PropertyKindCalculus.Paradigm.TapeParity

variable {s : Shape}

/-! ## The homomorphism as one object -/

/-- **`Evaluates` is a `NumCarrier`-homomorphism, bundled.** A relation
`R : TapeBuilder s → Tensor Float s → Prop` respects every `NumCarrier` operation — sending
each tape op to the matching elementwise `Spec` op — and both leaf formers. This is the
per-operation content of `paradigm.tape_parity`'s `Evaluates_*` lemmas collected into a single
named record, so the homomorphism is one object that future certified carrier pairs (a lax
enclosure relation for interval/error carriers, an equality for exact ones) can key on and
replay with the same closure tactic. -/
structure IsNumCarrierHom (R : TapeBuilder s → Tensor Float s → Prop) : Prop where
  /-- A named input leaf relates to exactly its own tensor. -/
  leaf  : ∀ (v : Tensor Float s) (name : Option String) (rg : Bool),
            R (⟨TapeM.leaf v (name := name) (requiresGrad := rg)⟩ : TapeBuilder s) v
  /-- A constant leaf relates to the filled tensor. -/
  const : ∀ (x : Float), R (TapeBuilder.const (s := s) x) (Tensor.full s x)
  /-- `+` maps to `addSpec`. -/
  add   : ∀ {x y : TapeBuilder s} {vx vy : Tensor Float s},
            R x vx → R y vy → R (x + y) (addSpec vx vy)
  /-- `−` maps to `subSpec`. -/
  sub   : ∀ {x y : TapeBuilder s} {vx vy : Tensor Float s},
            R x vx → R y vy → R (x - y) (subSpec vx vy)
  /-- `×` maps to `mulSpec`. -/
  mul   : ∀ {x y : TapeBuilder s} {vx vy : Tensor Float s},
            R x vx → R y vy → R (x * y) (mulSpec vx vy)
  /-- `÷` maps to `divSpec`. -/
  div   : ∀ {x y : TapeBuilder s} {vx vy : Tensor Float s},
            R x vx → R y vy → R (x / y) (divSpec vx vy)
  /-- `min` maps to `minSpec`. -/
  min   : ∀ {x y : TapeBuilder s} {vx vy : Tensor Float s},
            R x vx → R y vy → R (Min.min x y) (minSpec vx vy)
  /-- `max` maps to `maxSpec`. -/
  max   : ∀ {x y : TapeBuilder s} {vx vy : Tensor Float s},
            R x vx → R y vy → R (Max.max x y) (maxSpec vx vy)
  /-- `sqrt` maps to the clamped `sqrtSpec`. -/
  sqrt  : ∀ {x : TapeBuilder s} {vx : Tensor Float s},
            R x vx → R (MathCarrier.sqrt x) (sqrtSpec vx)
  /-- `exp` maps to `expSpec`. -/
  exp   : ∀ {x : TapeBuilder s} {vx : Tensor Float s},
            R x vx → R (MathCarrier.exp x) (expSpec vx)

/-- **`Evaluates` is that homomorphism** — assembled verbatim from the per-op `Evaluates_*`
lemmas of `paradigm.tape_parity`. The named witness the `tape_hom` machinery and future
carriers refer to. -/
theorem Evaluates.isNumCarrierHom : IsNumCarrierHom (@Evaluates s) where
  leaf v name rg := Evaluates_leaf v name rg
  const x := Evaluates_const x
  add hx hy := Evaluates_add hx hy
  sub hx hy := Evaluates_sub hx hy
  mul hx hy := Evaluates_mul hx hy
  div hx hy := Evaluates_div hx hy
  min hx hy := Evaluates_min hx hy
  max hx hy := Evaluates_max hx hy
  sqrt hx := Evaluates_sqrt hx
  exp hx := Evaluates_exp hx

end PropertyKindCalculus.Paradigm.TapeParity

/-! ## The closure tactic -/

open Lean Elab Tactic in
/-- **`tape_hom [defs…]`** — close a tape-parity goal
`Evaluates (f leaves) (f eager)` in one line.

The bracketed `defs…` are the kernel's own definition names (its authored `…Q` form and its
naked `.magnitude` derivation), named **only to unfold** — no body is restated. `tape_hom`
`simp only`s them together with the `@[simp] rfl` magnitude-erasure lemmas, which pushes
`.magnitude` through the kinded operator algebra and exposes the identical `+ − × ÷ exp √` op
tree on both the tape and eager carriers; it then closes the goal congruence by congruence with
the `Evaluates_*` homomorphism alphabet (leaves and literal constants included).

It fails to close a *false* parity: after the erase-set the exposed op heads disagree with a
wrong eager right-hand side, so the `Evaluates_*` step will not unify — `tape_hom` cannot
rubber-stamp a parity that does not hold (that failure is clean when the caller has the tape ops
`local irreducible`). -/
macro "tape_hom" " [" names:Lean.Parser.Tactic.simpLemma,* "]" : tactic =>
  `(tactic|
    (simp only [$names,*, Quantity.add_magnitude, Quantity.sub_magnitude,
        Quantity.mul_magnitude, Quantity.div_magnitude,
        Quantity.exp_magnitude, Quantity.sqrt_magnitude,
        OperatorTable.hmul_magnitude, OperatorTable.hdiv_magnitude,
        Quantity.mulK_magnitude, Quantity.divK_magnitude]
     repeat' first
       | apply Evaluates_add | apply Evaluates_sub | apply Evaluates_mul
       | apply Evaluates_div | apply Evaluates_min | apply Evaluates_max
       | apply Evaluates_sqrt | apply Evaluates_exp
       | apply Evaluates_leaf | apply Evaluates_const
       | assumption))

end -- pkc-blanket-expose
end -- pkc-blanket
