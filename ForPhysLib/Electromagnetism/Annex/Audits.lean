/-
# Stage 4 — audits for the RF/AC annex

The annex's kinded surface under CI, in the directory discipline:

  * `#kind_boundary_audit` **pinned** over the annex namespace — the phasor ingests,
    the conjugation crossing, and the two quadrature constructions, each with its
    tier. A new untagged site breaks the pin.
  * `#kind_boundary_clean` and `#kind_mint_ratchet` **silent** — the quadrature
    constructions are *attested*, never raw; the ratchet enforces it.
  * `#kind_dimensional_clean` **silent** over the whole annex: the ten Stage-1 edge
    laws (consumed and authored alike) coherent in the catalogue's dimension group.

The annex has no upstream module, so there is no `checked_by` delta: nothing here
checks a PhysLib TODO — the directory *is* the proposed capability.
-/

import ForPhysLib.Electromagnetism.Annex.Circuits
import ForPhysLib.Electromagnetism.Annex.Levels
import PropertyKindCalculus.BoundaryAudit
import PropertyKindCalculus.KindLedger
import PropertyKindCalculus.DimensionalCoverage

namespace ForPhysLib.Electromagnetism.Annex.Audits

open PropertyKindCalculus

/--
info: boundary audit:
[kindCrossing] ForPhysLib.Electromagnetism.Annex.Circuits.apparentFromQ — attests: Kinds.apparentPower ‹S² = P² + Q² — powers orthogonal, combined in quadrature›
[kindCrossing] ForPhysLib.Electromagnetism.Annex.Circuits.conjQ — attests: Kinds.electricCurrentPhasor ‹Î* — conjugation changes the phase's sign, not the kind›
[kindCrossing] ForPhysLib.Electromagnetism.Annex.Circuits.nonActiveFromQ — attests: Kinds.nonActivePower ‹√(S² − P²) — 6-61's defining residual›
[kindIngest] ForPhysLib.Electromagnetism.Annex.Circuits.currentPhasorQ — attests: Kinds.electricCurrentPhasor ‹a current phasor›
[kindIngest] ForPhysLib.Electromagnetism.Annex.Circuits.voltagePhasorQ — attests: Kinds.voltagePhasor ‹a voltage phasor — the complex amplitude at the catalogue's own item›
5 boundary site(s), all tagged — clean
-/
#guard_msgs (whitespace := lax) in
#kind_boundary_audit ForPhysLib.Electromagnetism.Annex

/--
info: tagged boundary crossings:
[kindCrossing] ForPhysLib.Electromagnetism.Annex.Circuits.apparentFromQ — What *is* licensed: `S = √(P² + Q²)` — the quadrature combination, with the law
[kindCrossing] ForPhysLib.Electromagnetism.Annex.Circuits.conjQ — `Î*` — complex conjugation: carrier-level, kind-preserving. The complex power's
[kindCrossing] ForPhysLib.Electromagnetism.Annex.Circuits.nonActiveFromQ — The catalogue's own residual — 6-61: `Q = √(S² − P²)`, the non-active power.
[kindIngest] ForPhysLib.Electromagnetism.Annex.Circuits.currentPhasorQ — A current phasor, read at 6-49.
[kindIngest] ForPhysLib.Electromagnetism.Annex.Circuits.voltagePhasorQ — A voltage phasor, read at 6-50.
-/
#guard_msgs (whitespace := lax) in
#kind_crossings ForPhysLib.Electromagnetism.Annex

#guard_msgs in #kind_boundary_clean ForPhysLib.Electromagnetism.Annex
#guard_msgs in #kind_mint_ratchet ForPhysLib.Electromagnetism.Annex
#guard_msgs in #kind_dimensional_clean ForPhysLib.Electromagnetism.Annex

end ForPhysLib.Electromagnetism.Annex.Audits
