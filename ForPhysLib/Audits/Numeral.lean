/-
# Stage 4 — audits for the shared numeral action

`Operators/Numeral.lean` is one declaration opened by every adopted directory (and Exhibit C), and each
directory's audit scopes its own namespace, so the row is pinned here, once, beside the
gates the directories run:

  * `#kind_boundary_audit` **pinned**: the single `[carrierVocab]` site, attested.
  * `#kind_boundary_clean` and `#kind_mint_ratchet` **silent**: they throw on violation
    and print nothing on a clean scope. The ratchet is why the mint is *attested*, not
    raw — a raw `⟨…⟩` here would fail the build, not re-pin.
-/

module

public import ForPhysLib.Operators.Numeral
public import PropertyKindCalculus.BoundaryAudit
-- Private scope only: `findDocString?` returns `none` for an imported declaration, and the audit prints each tagged declaration's docstring. `import all` restores them.
import all ForPhysLib.Operators.Numeral

@[expose] public section

namespace ForPhysLib.Audits.Numeral

open PropertyKindCalculus

/-! ## The boundary audit, pinned -/

/--
info: boundary audit:
[carrierVocab] ForPhysLib.Operators.Numeral.numeralSMul — attests: (kind-parametric) ‹a dimensionless numeral scales; the kind is unchanged›
1 boundary site(s), all tagged — clean
-/
#guard_msgs (whitespace := lax) in
#kind_boundary_audit ForPhysLib.Operators.Numeral

/--
info: tagged boundary crossings:
[carrierVocab] ForPhysLib.Operators.Numeral.numeralSMul — A dimensionless numeral scales a quantity without changing its kind. The action is
-/
#guard_msgs (whitespace := lax) in
#kind_crossings ForPhysLib.Operators.Numeral

/-! ## The gates that cannot be re-blessed — silent on a clean scope -/

#guard_msgs in #kind_boundary_clean ForPhysLib.Operators.Numeral
#guard_msgs in #kind_mint_ratchet ForPhysLib.Operators.Numeral

end ForPhysLib.Audits.Numeral
