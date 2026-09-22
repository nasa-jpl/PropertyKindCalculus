/-
# Scale types — Dybkær's operator-based division of ⟨property⟩

Dybkær (2009), Chapter 12 (esp. Figure 12.21): the top concept ⟨property⟩ is
generically divided according to which sets of algebraic operators are *allowed*
between properties of the kind:

| operators | scale (Dybkær term)                | section        |
|-----------|------------------------------------|----------------|
| `=, ≠`    | nominal                            | §12.4          |
| `<, >`    | ordinal                            | §12.5 / §12.16 |
| `+, −`    | differential / interval            | §12.6 / §12.19 |
| `×, ÷`    | rational / ratio                   | §12.7 / §12.20 |

This is the organizing axis a description logic (OWL2) **cannot** represent: it
is about which *operations* are *defined* for a kind, and DL has no operations.
Here it is a first-class datum that later gates the algebra on a `Quantity`.
-/

module

public section -- pkc-blanket
@[expose] section -- pkc-blanket-expose

namespace PropertyKindCalculus

/-- The four operator-based scale types of Dybkær Fig. 12.21. -/
inductive ScaleType
  /-- §12.4 nominal — only `=, ≠` (classification; no order, no magnitude). -/
  | nominal
  /-- §12.16 ordinal — adds `<, >` (rankable, but not subtractive). -/
  | ordinal
  /-- §12.19 interval — adds `+, −` (subtractive, but not divisible). -/
  | interval
  /-- §12.20 ratio — adds `×, ÷` (divisible; an absolute zero). -/
  | ratio
deriving DecidableEq, Repr

namespace ScaleType

/-- Operator-richness rank: `nominal ⊏ ordinal ⊏ interval ⊏ ratio`. -/
def rank : ScaleType → Nat
  | nominal  => 0
  | ordinal  => 1
  | interval => 2
  | ratio    => 3

instance : LE ScaleType := ⟨fun a b => a.rank ≤ b.rank⟩

theorem le_def {a b : ScaleType} : a ≤ b ↔ a.rank ≤ b.rank := Iff.rfl

protected theorem le_refl (a : ScaleType) : a ≤ a := Nat.le_refl _

protected theorem le_trans {a b c : ScaleType} (h₁ : a ≤ b) (h₂ : b ≤ c) : a ≤ c :=
  Nat.le_trans h₁ h₂

protected theorem le_antisymm {a b : ScaleType} (h₁ : a ≤ b) (h₂ : b ≤ a) : a = b := by
  have h : a.rank = b.rank := Nat.le_antisymm h₁ h₂
  cases a <;> cases b <;> simp_all [rank]

/-! ## Which operations are *defined* at each scale (cumulative) -/

/-- `<, >` available from ordinal upward (§12.16). -/
def AllowsOrder : ScaleType → Prop
  | nominal => False
  | _       => True

/-- `+, −` available from interval upward (§12.19). -/
def AllowsDifference : ScaleType → Prop
  | interval => True
  | ratio    => True
  | _        => False

/-- `×, ÷` available only at ratio scale (§12.20). -/
def AllowsRatio : ScaleType → Prop
  | ratio => True
  | _     => False

/-- **§13.3.1** — a kind has *magnitude* (is a kind-of-quantity, not merely
nominal) iff its scale is at least ordinal. -/
def HasMagnitude (s : ScaleType) : Prop := s ≠ nominal

/-- Meta-theorem OWL2's reasoner cannot even phrase: a richer scale licenses
every operation a poorer one does. (Monotonicity of operator availability.) -/
theorem allows_mono {a b : ScaleType} (h : a ≤ b) :
    (AllowsOrder a → AllowsOrder b)
      ∧ (AllowsDifference a → AllowsDifference b)
      ∧ (AllowsRatio a → AllowsRatio b) := by
  cases a <;> cases b <;>
    simp_all [AllowsOrder, AllowsDifference, AllowsRatio, le_def, rank]

end ScaleType

end PropertyKindCalculus

end -- pkc-blanket-expose
end -- pkc-blanket
