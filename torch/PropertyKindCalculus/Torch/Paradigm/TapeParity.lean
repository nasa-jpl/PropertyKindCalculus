/-
`paradigm.tape_parity` — **parity by construction, as a theorem** (WO3, README §3.2).

`dielectric_tape.lean` instantiates the branchless ε kernel at the tape carrier and a runtime
gate (`dielectric_tape_example`) checks it matches the scalar spec. This module makes that a
*proof* rather than a numerical gate, for the SM kernel itself: it shows the tape-carrier
program computes **exactly** the elementwise `Spec` tensor expression of the same source — so
"parity is a `rfl`, not a hope."

THE BRIDGE. We relate a tape-carrier value `b : TapeBuilder s` to the tensor it computes with

  `Evaluates b v`  :=  on *any* tape, running `b` succeeds, its result node carries `v`, and the
                       run only *extends* the tape (every earlier node's value survives).

Each `NumCarrier` operation on `TapeBuilder` preserves `Evaluates` with the matching `Spec`
op (`Evaluates a va → Evaluates b vb → Evaluates (a + b) (addSpec va vb)`, etc.), proved from
the forward-value faithfulness lemmas of `paradigm.tape_faithful` (`add_value`, …) plus a
`TapeM`→`Tape` run bridge. A composite kernel's parity is then the mechanical chaining of these
— shown here for the real SM kernels `nkToEps` (complex-permittivity assembly) and `mixedNK`
(the branchless dry/wet moisture collapse, the WO1 control-flow→data-flow rewrite).

The `Spec` tensor expression on the right is exactly what the *same* source term computes at the
eager `Tensor Float s` carrier; the agreement needs **no** numerical side conditions (both use
the same clamped `sqrtSpec`, the same `min`/`max`), so it holds for symbolic inputs.

Plain (not a `module`) file: imports the tape carrier and the faithfulness lemmas.
-/
import PropertyKindCalculus.Torch.Paradigm.TapeCarrier
import PropertyKindCalculus.Torch.Paradigm.TapeFaithful

open Spec TorchLean
open TorchLean TorchLean.Tensor
open Runtime.Autograd
open PropertyKindCalculus.Paradigm.TapeFaithful

namespace PropertyKindCalculus.Paradigm.TapeParity

open PropertyKindCalculus.Paradigm
open PropertyKindCalculus.Paradigm.TapeBuilder

set_option linter.unusedSimpArgs false

variable {s : Shape}

/-! ## The `TapeM`→`Tape` run bridge

`TapeM.X` is the `StateT` wrapper of the pure `Tape.X`. When the pure op succeeds, the wrapped
op's `.run` yields the same node id and tape. Every `TapeM` op shares one `StateT`-over-`Result`
threading pattern `patt`; `patt_run_ok` reduces it with a single `simp` set, and each op is that
pattern by definitional unfolding. -/

/-- The `StateT`-over-`Result` threading shared by every `TapeM` builder op. -/
def patt (g : Tape Float → Result (Tape Float × Nat)) : TapeM Float Nat := do
  let tt ← get; let (t', id) ← liftM (g tt); set t'; pure id

/-- When the wrapped pure op succeeds, `patt`'s `.run` yields the same id and tape. The one
`simp` set that unfolds the whole `StateT`/`Except` plumbing (no error branch, so it closes). -/
theorem patt_run_ok (g : Tape Float → Result (Tape Float × Nat)) (t t' : Tape Float) (id : Nat)
    (h : g t = .ok (t', id)) : (patt g).run t = .ok (id, t') := by
  unfold patt
  simp only [TapeM.run, StateT.run, StateT.bind, StateT.pure, StateT.lift, StateT.map,
    bind, Bind.bind, pure, Pure.pure, Functor.map, MonadState.get, MonadStateOf.get, getThe,
    StateT.get, MonadStateOf.set, set, StateT.set, monadLift, MonadLift.monadLift, liftM,
    Except.bind, Except.pure, h]

theorem add_run_ok (t t' : Tape Float) (aId bId id : Nat)
    (h : Tape.add (t := t) (s := s) aId bId = .ok (t', id)) :
    (TapeM.add (α := Float) (s := s) aId bId).run t = .ok (id, t') :=
  patt_run_ok (fun tt => Tape.add (t := tt) (s := s) aId bId) t t' id h
theorem sub_run_ok (t t' : Tape Float) (aId bId id : Nat)
    (h : Tape.sub (t := t) (s := s) aId bId = .ok (t', id)) :
    (TapeM.sub (α := Float) (s := s) aId bId).run t = .ok (id, t') :=
  patt_run_ok (fun tt => Tape.sub (t := tt) (s := s) aId bId) t t' id h
theorem mul_run_ok (t t' : Tape Float) (aId bId id : Nat)
    (h : Tape.mul (t := t) (s := s) aId bId = .ok (t', id)) :
    (TapeM.mul (α := Float) (s := s) aId bId).run t = .ok (id, t') :=
  patt_run_ok (fun tt => Tape.mul (t := tt) (s := s) aId bId) t t' id h
theorem div_run_ok (t t' : Tape Float) (aId bId id : Nat)
    (h : Tape.div (t := t) (s := s) aId bId = .ok (t', id)) :
    (TapeM.div (α := Float) (s := s) aId bId).run t = .ok (id, t') :=
  patt_run_ok (fun tt => Tape.div (t := tt) (s := s) aId bId) t t' id h
theorem min_run_ok (t t' : Tape Float) (aId bId id : Nat)
    (h : Tape.min (t := t) (s := s) aId bId = .ok (t', id)) :
    (TapeM.min (α := Float) (s := s) aId bId).run t = .ok (id, t') :=
  patt_run_ok (fun tt => Tape.min (t := tt) (s := s) aId bId) t t' id h
theorem max_run_ok (t t' : Tape Float) (aId bId id : Nat)
    (h : Tape.max (t := t) (s := s) aId bId = .ok (t', id)) :
    (TapeM.max (α := Float) (s := s) aId bId).run t = .ok (id, t') :=
  patt_run_ok (fun tt => Tape.max (t := tt) (s := s) aId bId) t t' id h
/-- Unary run bridge: `TapeM.sqrt` is the same `patt` threading over the single-input
`Tape.sqrt` (so `patt_run_ok` applies verbatim). -/
theorem sqrt_run_ok (t t' : Tape Float) (aId id : Nat)
    (h : Tape.sqrt (t := t) (s := s) aId = .ok (t', id)) :
    (TapeM.sqrt (α := Float) (s := s) aId).run t = .ok (id, t') :=
  patt_run_ok (fun tt => Tape.sqrt (t := tt) (s := s) aId) t t' id h

/-- `TapeM.exp` is the same `patt` threading over `Tape.exp` — the transcendental the AVS
forward model `exp(−2·b·ndvi)` names. -/
theorem exp_run_ok (t t' : Tape Float) (aId id : Nat)
    (h : Tape.exp (t := t) (s := s) aId = .ok (t', id)) :
    (TapeM.exp (α := Float) (s := s) aId).run t = .ok (id, t') :=
  patt_run_ok (fun tt => Tape.exp (t := tt) (s := s) aId) t t' id h

/-! ## `Evaluates` and its compositional skeleton -/

/-- `requireValue` succeeding pins the id in range (a stored node exists). -/
theorem requireValue_lt_of_ok (t : Tape Float) (id : Nat) {v : Tensor Float s}
    (h : t.requireValue (s := s) id = .ok v) : id < t.size := by
  by_contra hge
  rw [not_lt] at hge
  have : t.getValue? id = none := by
    simp only [Tape.getValue?, Tape.getNode?, Option.map_eq_none_iff]
    exact Array.getElem?_eq_none (by simpa [Tape.size] using hge)
  rw [Tape.requireValue, this] at h
  simp at h

/-- `t'` extends `t`: it is at least as large and preserves every earlier node's value. The
append-monotone closure of `FrameOver`; transitive, so frames chain across a kernel. -/
def Extends (t' t : Tape Float) : Prop :=
  t.size ≤ t'.size ∧ FrameOver t' t

theorem Extends.refl (t : Tape Float) : Extends t t :=
  ⟨Nat.le_refl _, fun _ _ => _root_.rfl⟩

theorem Extends.trans {a b c : Tape Float} (hab : Extends a b) (hbc : Extends b c) :
    Extends a c := by
  refine ⟨Nat.le_trans hbc.1 hab.1, ?_⟩
  intro s id hid
  have h1 : b.requireValue (s := s) id = c.requireValue (s := s) id := hbc.2 id hid
  have h2 : a.requireValue (s := s) id = b.requireValue (s := s) id :=
    hab.2 id (Nat.lt_of_lt_of_le hid hbc.1)
  rw [h2, h1]

/-- An `addNode`-style op (delivers its new value at `t.size`, frames `t`) extends `t`. -/
theorem extends_of_value {t t' : Tape Float} {v : Tensor Float s}
    (hval : t'.requireValue t.size = .ok v) (hframe : FrameOver t' t) : Extends t' t :=
  ⟨Nat.le_of_lt (requireValue_lt_of_ok t' t.size hval), hframe⟩

/-- **The carrier-to-tensor bridge.** On any tape, running `b` succeeds with a node carrying
`v`, the node id is in range, and the run only extends the tape. -/
def Evaluates (b : TapeBuilder s) (v : Tensor Float s) : Prop :=
  ∀ (t : Tape Float), ∃ (id : Nat) (t' : Tape Float),
    b.run t = .ok (id, t') ∧ id < t'.size ∧
    t'.requireValue (s := s) id = .ok v ∧ Extends t' t

/-- Reduce `(bin f x y).run` given the three sub-runs (the carrier's binary-op threading). -/
theorem bin_run (f : Nat → Nat → TapeM Float Nat) (x y : TapeBuilder s)
    (t tA tB t' : Tape Float) (idA idB id : Nat)
    (hx : x.run t = .ok (idA, tA)) (hy : y.run tA = .ok (idB, tB))
    (hf : (f idA idB).run tB = .ok (id, t')) :
    (TapeBuilder.bin f x y).run t = .ok (id, t') := by
  unfold TapeBuilder.bin
  simp only [TapeM.run, StateT.run, StateT.bind, StateT.pure, StateT.lift, StateT.map,
    bind, Bind.bind, pure, Pure.pure, Functor.map, Except.bind, Except.pure, hx, hy]
  exact hf

/-- Reduce `(un f x).run` given the operand sub-run (the carrier's unary-op threading). -/
theorem un_run (f : Nat → TapeM Float Nat) (x : TapeBuilder s)
    (t tA t' : Tape Float) (idA id : Nat)
    (hx : x.run t = .ok (idA, tA)) (hf : (f idA).run tA = .ok (id, t')) :
    (TapeBuilder.un f x).run t = .ok (id, t') := by
  unfold TapeBuilder.un
  simp only [TapeM.run, StateT.run, StateT.bind, StateT.pure, StateT.lift, StateT.map,
    bind, Bind.bind, pure, Pure.pure, Functor.map, Except.bind, Except.pure, hx]
  exact hf

/-- **Generic op-preservation.** If a tape op is forward-faithful to a `Spec` op (delivers
`sop va vb` at the new id, framing the tape), then the carrier's `bin` of it preserves
`Evaluates` with `sop`. Instantiated per op below. -/
theorem Evaluates_bin
    (top : Nat → Nat → TapeM Float Nat) (sop : Tensor Float s → Tensor Float s → Tensor Float s)
    (hfaith : ∀ (tt : Tape Float) (aId bId : Nat) {va vb : Tensor Float s},
      tt.requireValue aId = .ok va → tt.requireValue bId = .ok vb →
      ∃ t', (top aId bId).run tt = .ok (tt.size, t') ∧
            t'.requireValue tt.size = .ok (sop va vb) ∧ FrameOver t' tt)
    {x y : TapeBuilder s} {vx vy : Tensor Float s}
    (hx : Evaluates x vx) (hy : Evaluates y vy) :
    Evaluates (TapeBuilder.bin top x y) (sop vx vy) := by
  intro t
  obtain ⟨idA, tA, hxr, hxlt, hxv, hxe⟩ := hx t
  obtain ⟨idB, tB, hyr, hylt, hyv, hye⟩ := hy tA
  have hAinB : tB.requireValue idA = .ok vx := (hye.2 idA hxlt).trans hxv
  obtain ⟨t', htopr, htopv, htopf⟩ := hfaith tB idA idB hAinB hyv
  refine ⟨tB.size, t', bin_run top x y t tA tB t' idA idB tB.size hxr hyr htopr,
    requireValue_lt_of_ok t' tB.size htopv, htopv, ?_⟩
  exact (extends_of_value htopv htopf).trans (hye.trans hxe)

/-- Unary analogue of `Evaluates_bin`. -/
theorem Evaluates_un
    (top : Nat → TapeM Float Nat) (sop : Tensor Float s → Tensor Float s)
    (hfaith : ∀ (tt : Tape Float) (xId : Nat) {vx : Tensor Float s},
      tt.requireValue xId = .ok vx →
      ∃ t', (top xId).run tt = .ok (tt.size, t') ∧
            t'.requireValue tt.size = .ok (sop vx) ∧ FrameOver t' tt)
    {x : TapeBuilder s} {vx : Tensor Float s}
    (hx : Evaluates x vx) :
    Evaluates (TapeBuilder.un top x) (sop vx) := by
  intro t
  obtain ⟨idA, tA, hxr, hxlt, hxv, hxe⟩ := hx t
  obtain ⟨t', htopr, htopv, htopf⟩ := hfaith tA idA hxv
  refine ⟨tA.size, t', un_run top x t tA t' idA tA.size hxr htopr,
    requireValue_lt_of_ok t' tA.size htopv, htopv, ?_⟩
  exact (extends_of_value htopv htopf).trans hxe

/-! ## Per-op `Evaluates` lemmas (the reusable parity alphabet) -/

/-- **A leaf evaluates to its own tensor.** An input tensor entered as a named `TapeM.leaf`
(as the ε kernel's `soilMoisture`/`clayFraction` are) reads back as exactly that tensor. -/
theorem Evaluates_leaf (v : Tensor Float s) (name : Option String := none) (rg : Bool := true) :
    Evaluates (⟨TapeM.leaf v (name := name) (requiresGrad := rg)⟩ : TapeBuilder s) v := by
  intro t
  have hval : (Tape.leaf (t := t) v (name := name) (requiresGrad := rg)).1.requireValue
      (s := s) t.size = .ok v := leaf_value t v name rg
  refine ⟨t.size, (Tape.leaf (t := t) v (name := name) (requiresGrad := rg)).1,
    ?_, ?_, hval, extends_of_value hval (frameOver_addNode t _)⟩
  · unfold TapeM.leaf Tape.leaf Tape.addNode; rfl
  · exact requireValue_lt_of_ok _ t.size hval

/-- A constant leaf evaluates to the filled tensor — the `fill`-valued instance of a leaf. -/
theorem Evaluates_const (x : Float) : Evaluates (TapeBuilder.const (s := s) x) (Tensor.full s x) :=
  Evaluates_leaf (Tensor.full s x)

/-- Per-op faithfulness in the `Evaluates_bin` shape: the `TapeM` op's `.run` delivers its
`Spec` value at the new id, framing the tape. Folds tape_faithful's `add_value` with the
`TapeM`→`Tape` run bridge. -/
theorem faith_add (tt : Tape Float) (aId bId : Nat) {va vb : Tensor Float s}
    (ha : tt.requireValue aId = .ok va) (hb : tt.requireValue bId = .ok vb) :
    ∃ t', (TapeM.add (s := s) aId bId).run tt = .ok (tt.size, t') ∧
          t'.requireValue tt.size = .ok (addSpec va vb) ∧ FrameOver t' tt := by
  obtain ⟨t', he, hv, hf⟩ := add_value tt aId bId ha hb
  exact ⟨t', add_run_ok tt t' aId bId tt.size he, hv, hf⟩

theorem faith_sub (tt : Tape Float) (aId bId : Nat) {va vb : Tensor Float s}
    (ha : tt.requireValue aId = .ok va) (hb : tt.requireValue bId = .ok vb) :
    ∃ t', (TapeM.sub (s := s) aId bId).run tt = .ok (tt.size, t') ∧
          t'.requireValue tt.size = .ok (subSpec va vb) ∧ FrameOver t' tt := by
  obtain ⟨t', he, hv, hf⟩ := sub_value tt aId bId ha hb
  exact ⟨t', sub_run_ok tt t' aId bId tt.size he, hv, hf⟩

theorem faith_mul (tt : Tape Float) (aId bId : Nat) {va vb : Tensor Float s}
    (ha : tt.requireValue aId = .ok va) (hb : tt.requireValue bId = .ok vb) :
    ∃ t', (TapeM.mul (s := s) aId bId).run tt = .ok (tt.size, t') ∧
          t'.requireValue tt.size = .ok (mulSpec va vb) ∧ FrameOver t' tt := by
  obtain ⟨t', he, hv, hf⟩ := mul_value tt aId bId ha hb
  exact ⟨t', mul_run_ok tt t' aId bId tt.size he, hv, hf⟩

theorem faith_div (tt : Tape Float) (aId bId : Nat) {va vb : Tensor Float s}
    (ha : tt.requireValue aId = .ok va) (hb : tt.requireValue bId = .ok vb) :
    ∃ t', (TapeM.div (s := s) aId bId).run tt = .ok (tt.size, t') ∧
          t'.requireValue tt.size = .ok (divSpec va vb) ∧ FrameOver t' tt := by
  obtain ⟨t', he, hv, hf⟩ := div_value tt aId bId ha hb
  exact ⟨t', div_run_ok tt t' aId bId tt.size he, hv, hf⟩

theorem faith_min (tt : Tape Float) (aId bId : Nat) {va vb : Tensor Float s}
    (ha : tt.requireValue aId = .ok va) (hb : tt.requireValue bId = .ok vb) :
    ∃ t', (TapeM.min (s := s) aId bId).run tt = .ok (tt.size, t') ∧
          t'.requireValue tt.size = .ok (minSpec va vb) ∧ FrameOver t' tt := by
  obtain ⟨t', he, hv, hf⟩ := min_value tt aId bId ha hb
  exact ⟨t', min_run_ok tt t' aId bId tt.size he, hv, hf⟩

theorem faith_max (tt : Tape Float) (aId bId : Nat) {va vb : Tensor Float s}
    (ha : tt.requireValue aId = .ok va) (hb : tt.requireValue bId = .ok vb) :
    ∃ t', (TapeM.max (s := s) aId bId).run tt = .ok (tt.size, t') ∧
          t'.requireValue tt.size = .ok (maxSpec va vb) ∧ FrameOver t' tt := by
  obtain ⟨t', he, hv, hf⟩ := max_value tt aId bId ha hb
  exact ⟨t', max_run_ok tt t' aId bId tt.size he, hv, hf⟩

theorem faith_sqrt (tt : Tape Float) (xId : Nat) {vx : Tensor Float s}
    (hx : tt.requireValue xId = .ok vx) :
    ∃ t', (TapeM.sqrt (s := s) xId).run tt = .ok (tt.size, t') ∧
          t'.requireValue tt.size = .ok (sqrtSpec vx) ∧ FrameOver t' tt := by
  obtain ⟨t', he, hv, hf⟩ := sqrt_value tt xId hx
  exact ⟨t', sqrt_run_ok tt t' xId tt.size he, hv, hf⟩

theorem faith_exp (tt : Tape Float) (xId : Nat) {vx : Tensor Float s}
    (hx : tt.requireValue xId = .ok vx) :
    ∃ t', (TapeM.exp (s := s) xId).run tt = .ok (tt.size, t') ∧
          t'.requireValue tt.size = .ok (expSpec vx) ∧ FrameOver t' tt := by
  obtain ⟨t', he, hv, hf⟩ := exp_value tt xId hx
  exact ⟨t', exp_run_ok tt t' xId tt.size he, hv, hf⟩

theorem Evaluates_add {x y : TapeBuilder s} {vx vy : Tensor Float s}
    (hx : Evaluates x vx) (hy : Evaluates y vy) : Evaluates (x + y) (addSpec vx vy) :=
  Evaluates_bin (TapeM.add (s := s)) addSpec faith_add hx hy

theorem Evaluates_sub {x y : TapeBuilder s} {vx vy : Tensor Float s}
    (hx : Evaluates x vx) (hy : Evaluates y vy) : Evaluates (x - y) (subSpec vx vy) :=
  Evaluates_bin (TapeM.sub (s := s)) subSpec faith_sub hx hy

theorem Evaluates_mul {x y : TapeBuilder s} {vx vy : Tensor Float s}
    (hx : Evaluates x vx) (hy : Evaluates y vy) : Evaluates (x * y) (mulSpec vx vy) :=
  Evaluates_bin (TapeM.mul (s := s)) mulSpec faith_mul hx hy

theorem Evaluates_div {x y : TapeBuilder s} {vx vy : Tensor Float s}
    (hx : Evaluates x vx) (hy : Evaluates y vy) : Evaluates (x / y) (divSpec vx vy) :=
  Evaluates_bin (TapeM.div (s := s)) divSpec faith_div hx hy

theorem Evaluates_min {x y : TapeBuilder s} {vx vy : Tensor Float s}
    (hx : Evaluates x vx) (hy : Evaluates y vy) : Evaluates (Min.min x y) (minSpec vx vy) :=
  Evaluates_bin (TapeM.min (s := s)) minSpec faith_min hx hy

theorem Evaluates_max {x y : TapeBuilder s} {vx vy : Tensor Float s}
    (hx : Evaluates x vx) (hy : Evaluates y vy) : Evaluates (Max.max x y) (maxSpec vx vy) :=
  Evaluates_bin (TapeM.max (s := s)) maxSpec faith_max hx hy

/-- The unary `sqrt` op preserves `Evaluates` with the clamped `sqrtSpec` — the one
transcendental the Mironov ε kernel names (six times, through `nkOfEps`'s three real roots). -/
theorem Evaluates_sqrt {x : TapeBuilder s} {vx : Tensor Float s}
    (hx : Evaluates x vx) : Evaluates (PropertyKindCalculus.MathCarrier.sqrt x) (sqrtSpec vx) :=
  Evaluates_un (TapeM.sqrt (s := s)) sqrtSpec faith_sqrt hx

/-- The unary `exp` op preserves `Evaluates` with `expSpec` — the AVS forward model's vegetation
attenuation `exp(−2·b·ndvi)` (the one transcendental beyond `sqrt` the WO kernels name). -/
theorem Evaluates_exp {x : TapeBuilder s} {vx : Tensor Float s}
    (hx : Evaluates x vx) : Evaluates (PropertyKindCalculus.MathCarrier.exp x) (expSpec vx) :=
  Evaluates_un (TapeM.exp (s := s)) expSpec faith_exp hx

end PropertyKindCalculus.Paradigm.TapeParity
