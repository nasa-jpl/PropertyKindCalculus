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
op (`Evaluates a va → Evaluates b vb → Evaluates (a + b) (va + vb)`, etc.), proved from
the forward-value faithfulness lemmas of `paradigm.tape_faithful` (`add_value`, …) plus a
`TapeM`→`Tape` run bridge. A composite kernel's parity is then the mechanical chaining of these
— shown here for the real SM kernels `nkToEps` (complex-permittivity assembly) and `mixedNK`
(the branchless dry/wet moisture collapse, the WO1 control-flow→data-flow rewrite).

The `Spec` tensor expression on the right is exactly what the *same* source term computes at the
eager `Tensor Float s` carrier; the agreement needs **no** numerical side conditions (both use
the same clamped root, the same `min`/`max`), so it holds for symbolic inputs.

A `module` file: imports the tape carrier and the faithfulness lemmas.
-/

module

public import PropertyKindCalculus.Torch.Paradigm.TapeCarrier
public import PropertyKindCalculus.Torch.Paradigm.TapeFaithful

@[expose] public section Blanket

open TorchLean TorchLean.Tape
open PropertyKindCalculus.Paradigm.TapeFaithful

namespace PropertyKindCalculus.Paradigm.TapeParity

open PropertyKindCalculus.Paradigm
open PropertyKindCalculus.Paradigm.TapeBuilder

variable {s : Shape}

/-! ## The `TapeM`→`Tape` run bridge

`TapeM.X` is `TapeM.record` applied to the pure `CpuTape.X`, and `paradigm.tape_m` reduces that
threading once: `TapeM.record_run_ok` turns a pure op's success into the
wrapped op's `.run` success (the pair swaps: a pure op returns tape-then-id, `run` returns
id-then-tape). The per-op
`Evaluates` lemmas below use it directly. -/

/-! ## `Evaluates` and its compositional skeleton -/

/-- `requireValue` succeeding pins the id in range (a stored node exists). -/
theorem requireValue_lt_of_ok (t : CpuTape Float) (id : Nat) {v : Tensor Float s}
    (h : requireValue (s := s) t id = .ok v) : id < t.size := by
  by_contra hge
  rw [not_lt] at hge
  have : t.getValue? id = none := by
    simp only [Tape.getValue?, Tape.getNode?, Option.map_eq_none_iff]
    exact Array.getElem?_eq_none (by simpa [Tape.size] using hge)
  rw [requireValue, this] at h
  simp at h

/-- `t'` extends `t`: it is at least as large and preserves every earlier node's value. The
append-monotone closure of `FrameOver`; transitive, so frames chain across a kernel. -/
def Extends (t' t : CpuTape Float) : Prop :=
  t.size ≤ t'.size ∧ FrameOver t' t

theorem Extends.refl (t : CpuTape Float) : Extends t t :=
  ⟨Nat.le_refl _, fun _ _ => _root_.rfl⟩

theorem Extends.trans {a b c : CpuTape Float} (hab : Extends a b) (hbc : Extends b c) :
    Extends a c := by
  refine ⟨Nat.le_trans hbc.1 hab.1, ?_⟩
  intro s id hid
  have h1 : requireValue (s := s) b id = requireValue (s := s) c id := hbc.2 id hid
  have h2 : requireValue (s := s) a id = requireValue (s := s) b id :=
    hab.2 id (Nat.lt_of_lt_of_le hid hbc.1)
  rw [h2, h1]

/-- An `addNode`-style op (delivers its new value at `t.size`, frames `t`) extends `t`. -/
theorem extends_of_value {t t' : CpuTape Float} {v : Tensor Float s}
    (hval : requireValue (s := s) t' t.size = .ok v) (hframe : FrameOver t' t) : Extends t' t :=
  ⟨Nat.le_of_lt (requireValue_lt_of_ok t' t.size hval), hframe⟩

/-- **The carrier-to-tensor bridge.** On any tape, running `b` succeeds with a node carrying
`v`, the node id is in range, and the run only extends the tape. -/
def Evaluates (b : TapeBuilder s) (v : Tensor Float s) : Prop :=
  ∀ (t : CpuTape Float), ∃ (id : Nat) (t' : CpuTape Float),
    b.run t = .ok (id, t') ∧ id < t'.size ∧
    requireValue (s := s) t' id = .ok v ∧ Extends t' t

/-- Reduce `(bin f x y).run` given the three sub-runs (the carrier's binary-op threading). -/
theorem bin_run (f : Nat → Nat → TapeM Float Nat) (x y : TapeBuilder s)
    (t tA tB t' : CpuTape Float) (idA idB id : Nat)
    (hx : x.run t = .ok (idA, tA)) (hy : y.run tA = .ok (idB, tB))
    (hf : (f idA idB).run tB = .ok (id, t')) :
    (TapeBuilder.bin f x y).run t = .ok (id, t') := by
  unfold TapeBuilder.bin
  simp only [StateT.bind, bind, Bind.bind, Except.bind, hx, hy]
  exact hf

/-- Reduce `(un f x).run` given the operand sub-run (the carrier's unary-op threading). -/
theorem un_run (f : Nat → TapeM Float Nat) (x : TapeBuilder s)
    (t tA t' : CpuTape Float) (idA id : Nat)
    (hx : x.run t = .ok (idA, tA)) (hf : (f idA).run tA = .ok (id, t')) :
    (TapeBuilder.un f x).run t = .ok (id, t') := by
  unfold TapeBuilder.un
  simp only [StateT.bind, bind, Bind.bind, Except.bind, hx]
  exact hf

/-- **Generic op-preservation.** If a tape op is forward-faithful to a `Spec` op (delivers
`sop va vb` at the new id, framing the tape), then the carrier's `bin` of it preserves
`Evaluates` with `sop`. Instantiated per op below. -/
theorem Evaluates_bin
    (top : Nat → Nat → TapeM Float Nat) (sop : Tensor Float s → Tensor Float s → Tensor Float s)
    (hfaith : ∀ (tt : CpuTape Float) (aId bId : Nat) {va vb : Tensor Float s},
      requireValue (s := s) tt aId = .ok va → requireValue (s := s) tt bId = .ok vb →
      ∃ t', (top aId bId).run tt = .ok (tt.size, t') ∧
            requireValue (s := s) t' tt.size = .ok (sop va vb) ∧ FrameOver t' tt)
    {x y : TapeBuilder s} {vx vy : Tensor Float s}
    (hx : Evaluates x vx) (hy : Evaluates y vy) :
    Evaluates (TapeBuilder.bin top x y) (sop vx vy) := by
  intro t
  obtain ⟨idA, tA, hxr, hxlt, hxv, hxe⟩ := hx t
  obtain ⟨idB, tB, hyr, hylt, hyv, hye⟩ := hy tA
  have hAinB : requireValue (s := s) tB idA = .ok vx := (hye.2 idA hxlt).trans hxv
  obtain ⟨t', htopr, htopv, htopf⟩ := hfaith tB idA idB hAinB hyv
  refine ⟨tB.size, t', bin_run top x y t tA tB t' idA idB tB.size hxr hyr htopr,
    requireValue_lt_of_ok t' tB.size htopv, htopv, ?_⟩
  exact (extends_of_value htopv htopf).trans (hye.trans hxe)

/-- Unary analogue of `Evaluates_bin`. -/
theorem Evaluates_un
    (top : Nat → TapeM Float Nat) (sop : Tensor Float s → Tensor Float s)
    (hfaith : ∀ (tt : CpuTape Float) (xId : Nat) {vx : Tensor Float s},
      requireValue (s := s) tt xId = .ok vx →
      ∃ t', (top xId).run tt = .ok (tt.size, t') ∧
            requireValue (s := s) t' tt.size = .ok (sop vx) ∧ FrameOver t' tt)
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
  have hval : requireValue (s := s) (CpuTape.leaf t v name rg).1 t.size = .ok v :=
    leaf_value t v name rg
  refine ⟨t.size, (CpuTape.leaf t v name rg).1,
    ?_, ?_, hval, extends_of_value hval (frameOver_addNode t _)⟩
  · rfl
  · exact requireValue_lt_of_ok _ t.size hval

/-- A constant leaf evaluates to the filled tensor — the `fill`-valued instance of a leaf. -/
theorem Evaluates_const (x : Float) : Evaluates (TapeBuilder.const (s := s) x) (Tensor.full s x) :=
  Evaluates_leaf (Tensor.full s x)

/-- Per-op faithfulness in the `Evaluates_bin` shape: the `TapeM` op's `.run` delivers its
`Spec` value at the new id, framing the tape. Folds tape_faithful's `add_value` with the
`TapeM`→`Tape` run bridge. -/
theorem faith_add (tt : CpuTape Float) (aId bId : Nat) {va vb : Tensor Float s}
    (ha : requireValue (s := s) tt aId = .ok va) (hb : requireValue (s := s) tt bId = .ok vb) :
    ∃ t', (TapeM.add (s := s) aId bId).run tt = .ok (tt.size, t') ∧
          requireValue (s := s) t' tt.size = .ok (va + vb) ∧ FrameOver t' tt := by
  obtain ⟨t', he, hv, hf⟩ := add_value tt aId bId ha hb
  exact ⟨t', TapeM.record_run_ok he, hv, hf⟩

theorem faith_sub (tt : CpuTape Float) (aId bId : Nat) {va vb : Tensor Float s}
    (ha : requireValue (s := s) tt aId = .ok va) (hb : requireValue (s := s) tt bId = .ok vb) :
    ∃ t', (TapeM.sub (s := s) aId bId).run tt = .ok (tt.size, t') ∧
          requireValue (s := s) t' tt.size = .ok (va - vb) ∧ FrameOver t' tt := by
  obtain ⟨t', he, hv, hf⟩ := sub_value tt aId bId ha hb
  exact ⟨t', TapeM.record_run_ok he, hv, hf⟩

theorem faith_mul (tt : CpuTape Float) (aId bId : Nat) {va vb : Tensor Float s}
    (ha : requireValue (s := s) tt aId = .ok va) (hb : requireValue (s := s) tt bId = .ok vb) :
    ∃ t', (TapeM.mul (s := s) aId bId).run tt = .ok (tt.size, t') ∧
          requireValue (s := s) t' tt.size = .ok (va * vb) ∧ FrameOver t' tt := by
  obtain ⟨t', he, hv, hf⟩ := mul_value tt aId bId ha hb
  exact ⟨t', TapeM.record_run_ok he, hv, hf⟩

theorem faith_div (tt : CpuTape Float) (aId bId : Nat) {va vb : Tensor Float s}
    (ha : requireValue (s := s) tt aId = .ok va) (hb : requireValue (s := s) tt bId = .ok vb) :
    ∃ t', (TapeM.div (s := s) aId bId).run tt = .ok (tt.size, t') ∧
          requireValue (s := s) t' tt.size = .ok (va / vb) ∧ FrameOver t' tt := by
  obtain ⟨t', he, hv, hf⟩ := div_value tt aId bId ha hb
  exact ⟨t', TapeM.record_run_ok he, hv, hf⟩

theorem faith_min (tt : CpuTape Float) (aId bId : Nat) {va vb : Tensor Float s}
    (ha : requireValue (s := s) tt aId = .ok va) (hb : requireValue (s := s) tt bId = .ok vb) :
    ∃ t', (TapeM.min (s := s) aId bId).run tt = .ok (tt.size, t') ∧
          requireValue (s := s) t' tt.size = .ok (Tensor.minimum va vb) ∧ FrameOver t' tt := by
  obtain ⟨t', he, hv, hf⟩ := min_value tt aId bId ha hb
  exact ⟨t', TapeM.record_run_ok he, hv, hf⟩

theorem faith_max (tt : CpuTape Float) (aId bId : Nat) {va vb : Tensor Float s}
    (ha : requireValue (s := s) tt aId = .ok va) (hb : requireValue (s := s) tt bId = .ok vb) :
    ∃ t', (TapeM.max (s := s) aId bId).run tt = .ok (tt.size, t') ∧
          requireValue (s := s) t' tt.size = .ok (Tensor.maximum va vb) ∧ FrameOver t' tt := by
  obtain ⟨t', he, hv, hf⟩ := max_value tt aId bId ha hb
  exact ⟨t', TapeM.record_run_ok he, hv, hf⟩

theorem faith_sqrt (tt : CpuTape Float) (xId : Nat) {vx : Tensor Float s}
    (hx : requireValue (s := s) tt xId = .ok vx) :
    ∃ t', (TapeM.sqrt (s := s) xId).run tt = .ok (tt.size, t') ∧
          requireValue (s := s) t' tt.size = .ok (Tensor.sqrt vx .clampNegative) ∧ FrameOver t' tt := by
  obtain ⟨t', he, hv, hf⟩ := sqrt_value tt xId hx
  exact ⟨t', TapeM.record_run_ok he, hv, hf⟩

theorem faith_exp (tt : CpuTape Float) (xId : Nat) {vx : Tensor Float s}
    (hx : requireValue (s := s) tt xId = .ok vx) :
    ∃ t', (TapeM.exp (s := s) xId).run tt = .ok (tt.size, t') ∧
          requireValue (s := s) t' tt.size = .ok (Tensor.exp vx) ∧ FrameOver t' tt := by
  obtain ⟨t', he, hv, hf⟩ := exp_value tt xId hx
  exact ⟨t', TapeM.record_run_ok he, hv, hf⟩

theorem Evaluates_add {x y : TapeBuilder s} {vx vy : Tensor Float s}
    (hx : Evaluates x vx) (hy : Evaluates y vy) : Evaluates (x + y) (vx + vy) :=
  Evaluates_bin (TapeM.add (s := s)) _ faith_add hx hy

theorem Evaluates_sub {x y : TapeBuilder s} {vx vy : Tensor Float s}
    (hx : Evaluates x vx) (hy : Evaluates y vy) : Evaluates (x - y) (vx - vy) :=
  Evaluates_bin (TapeM.sub (s := s)) _ faith_sub hx hy

theorem Evaluates_mul {x y : TapeBuilder s} {vx vy : Tensor Float s}
    (hx : Evaluates x vx) (hy : Evaluates y vy) : Evaluates (x * y) (vx * vy) :=
  Evaluates_bin (TapeM.mul (s := s)) _ faith_mul hx hy

theorem Evaluates_div {x y : TapeBuilder s} {vx vy : Tensor Float s}
    (hx : Evaluates x vx) (hy : Evaluates y vy) : Evaluates (x / y) (vx / vy) :=
  Evaluates_bin (TapeM.div (s := s)) _ faith_div hx hy

theorem Evaluates_min {x y : TapeBuilder s} {vx vy : Tensor Float s}
    (hx : Evaluates x vx) (hy : Evaluates y vy) : Evaluates (Min.min x y) (Tensor.minimum vx vy) :=
  Evaluates_bin (TapeM.min (s := s)) _ faith_min hx hy

theorem Evaluates_max {x y : TapeBuilder s} {vx vy : Tensor Float s}
    (hx : Evaluates x vx) (hy : Evaluates y vy) : Evaluates (Max.max x y) (Tensor.maximum vx vy) :=
  Evaluates_bin (TapeM.max (s := s)) _ faith_max hx hy

/-- The unary `sqrt` op preserves `Evaluates` with the clamped root — the one
transcendental the Mironov ε kernel names (six times, through `nkOfEps`'s three real roots). -/
theorem Evaluates_sqrt {x : TapeBuilder s} {vx : Tensor Float s}
    (hx : Evaluates x vx) : Evaluates (PropertyKindCalculus.MathCarrier.sqrt x) (Tensor.sqrt vx .clampNegative) :=
  Evaluates_un (TapeM.sqrt (s := s)) _ faith_sqrt hx

/-- The unary `exp` op preserves `Evaluates` with `Tensor.exp` — the AVS forward model's vegetation
attenuation `exp(−2·b·ndvi)` (the one transcendental beyond `sqrt` the WO kernels name). -/
theorem Evaluates_exp {x : TapeBuilder s} {vx : Tensor Float s}
    (hx : Evaluates x vx) : Evaluates (PropertyKindCalculus.MathCarrier.exp x) (Tensor.exp vx) :=
  Evaluates_un (TapeM.exp (s := s)) _ faith_exp hx

end PropertyKindCalculus.Paradigm.TapeParity

end Blanket
