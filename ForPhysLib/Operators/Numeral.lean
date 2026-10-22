/-
# The numeral action — one scoped `SMul`, shared by every adopted directory

A dimensionless numeral scales a quantity without changing its kind: the `½` of every
energy, the `nᵢ + ½` of the oscillator's eigenvalues, the `β` and `γ` of a boost, the
`2π` of a period. Every campaign directory needs the action and it is the same action
in each, so it is defined once here and opened where it is used — scoped like the
operator table's instances (`open scoped ForPhysLib.Operators.Numeral`), never global.

The honesty is the table's: the action is the Mathlib-interface tier
([MR30](../REQUIREMENTS.md#mr30-the-unkinded-surface-is-measured)) — a dimensioned
magnitude smuggled in as a bare numeral is what the boundary audit measures, not what
the type prevents. The mint is *attested*, not raw, so the one `[carrierVocab]` site
survives `#kind_mint_ratchet`: the reason column carries the adjudication, and
`Audits/Numeral.lean` pins the row once for all the directories that open it.
-/

module

public import PropertyKindCalculus.BoundaryAudit
meta import PropertyKindCalculus.BoundaryAudit

@[expose] public section

namespace ForPhysLib.Operators.Numeral

open PropertyKindCalculus

/-- A dimensionless numeral scales a quantity without changing its kind. The action is
the Mathlib-interface tier (MR30) — a dimensioned magnitude smuggled in as a bare
numeral is what the audit measures, not what the type prevents — and the mint is
attested, not raw, so the tier survives the mint ratchet. -/
@[carrierVocab]
scoped instance numeralSMul {k : KindOfProperty} {R : Type} [Mul R] :
    SMul R (Quantity k R) :=
  ⟨fun c q => .attest "a dimensionless numeral scales; the kind is unchanged"
    (c * q.magnitude)⟩

end ForPhysLib.Operators.Numeral
