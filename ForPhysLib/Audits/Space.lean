/-
# Stage 4 — audits and the API map, for `Physlib/SpaceAndTime/Space`

The top rung of [the adoption ladder](../PLAN.md#stage-4-audits-and-the-api-map): the
directory's kinded surface put under CI. Four gates, each in the discipline its command
enforces —

  * `#kind_boundary_audit` **pinned**: the enumeration of every mint and erasure, with
    the tier that sanctions it — a new untagged interior mint breaks the pin
    ([MR29](../REQUIREMENTS.md#mr29-every-satisfied-requirement-has-a-machine-checkable-witness)).
  * `#kind_boundary_clean` and `#kind_mint_ratchet` **silent**: they throw on violation
    and print nothing on a clean scope, so neither can be re-blessed by re-pinning.
  * `#kind_unkinded` over two declared contracts: the *interior* scope gated empty, and
    the *ingest boundary* *measured* — eight naked positions, all of them `Space d`
    points or the one emitted `ℝ`: exactly the Mathlib-interface tier
    ([MR30](../REQUIREMENTS.md#mr30-the-unkinded-surface-is-measured)) — unkinded by
    design, counted rather than hidden.

The API-map half of the stage is the `checked_by:` field: the proposed delta to the
directory's `API-map.yaml` sits beside this file as `Space.checked_by.yaml`, pointing the
map's existing prose requirements at the modules whose builds now check them.
-/

import ForPhysLib.Operators.Space
import PropertyKindCalculus.BoundaryAudit
import PropertyKindCalculus.KindLedger

namespace ForPhysLib.Audits.Space

open PropertyKindCalculus

/-! ## The boundary audit, pinned -/

/--
info: boundary audit:
[kindCrossing] ForPhysLib.Kinded.Space.lengthOf — attests: Kinds.Space.length ‹the norm of a displacement read as bare length — the directory's own ‖·‖›
[kindEmission] ForPhysLib.Kinded.Space.rawDistance — erases (emission-only)
[kindIngest] ForPhysLib.Kinded.Space.displacementQ — mints: Kinds.Space.displacement
[kindIngest] ForPhysLib.Kinded.Space.distanceQ — mints: Kinds.Space.distance
[kindIngest] ForPhysLib.Kinded.Space.positionQ — mints: Kinds.Space.positionVector
5 boundary site(s), all tagged — clean
-/
#guard_msgs (whitespace := lax) in
#kind_boundary_audit ForPhysLib.Kinded.Space

/--
info: tagged boundary crossings:
[kindCrossing] ForPhysLib.Kinded.Space.lengthOf — A displacement's norm, crossed to bare **length** — item 3-1.1, the genus. The mint
[kindEmission] ForPhysLib.Kinded.Space.rawDistance — The emission boundary, stated once as a `def` so it carries its tier: downstream
[kindIngest] ForPhysLib.Kinded.Space.displacementQ — The torsor's vector between two points: a **displacement** — item 3-1.11, examined
[kindIngest] ForPhysLib.Kinded.Space.distanceQ — The directory's metric, read at its kind: `dist p q` is a **distance** — item 3-1.8,
[kindIngest] ForPhysLib.Kinded.Space.positionQ — A point of `Space d`, read from the conventional origin `Origin.lean` fixes: a
-/
#guard_msgs (whitespace := lax) in
#kind_crossings ForPhysLib.Kinded.Space

/-! ## The gates that cannot be re-blessed — silent on a clean scope -/

#guard_msgs in #kind_boundary_clean ForPhysLib.Kinded.Space
#guard_msgs in #kind_boundary_clean ForPhysLib.Operators.Space
#guard_msgs in #kind_mint_ratchet ForPhysLib.Kinded.Space
#guard_msgs in #kind_mint_ratchet ForPhysLib.Operators.Space

/-! ## The unkinded ledger — the interior gated, the boundary measured -/

/-- The interior scope: everything authored *inside* the calculus — the crossing and the
table composite. Gated empty: a naked binder added here is a build failure. -/
def interiorScope : Provenance.Contract Provenance.NodeId Provenance.KindRef where
  name := "SpaceAndTime/Space kinded interior"
  members := [``ForPhysLib.Operators.Space.spanArea, ``ForPhysLib.Kinded.Space.lengthOf]
  ports := []
  exits := []

/--
info: unkinded ledger of 'SpaceAndTime/Space kinded interior':
unkinded: none — every position carries a kind
-/
#guard_msgs in #kind_unkinded interiorScope

/-- info: unkinded-clean: every position of 'SpaceAndTime/Space kinded interior' carries a kind -/
#guard_msgs in #kind_unkinded_clean interiorScope

/-- The ingest boundary: the Stage-2 mints where PhysLib's carriers enter and the one
emission where a naked `ℝ` leaves. Its ledger is *not* empty and must not be gated —
`Space d` points are carriers, not quantities, and the API map's own prose ("arbitrary
but fixed choice of length unit and origin") is why they stay unkinded. MR30's tier
discipline: measured, so growth is visible; never hidden behind a gate it would fail. -/
def ingestBoundary : Provenance.Contract Provenance.NodeId Provenance.KindRef where
  name := "SpaceAndTime/Space ingest boundary"
  members := [``ForPhysLib.Kinded.Space.distanceQ, ``ForPhysLib.Kinded.Space.positionQ, ``ForPhysLib.Kinded.Space.displacementQ, ``ForPhysLib.Kinded.Space.rawDistance]
  ports := []
  exits := []

/--

info: unkinded ledger of 'SpaceAndTime/Space ingest boundary':
unkinded: 8 position(s), 7 flow(s)
unkinded input distanceQ/p : Space d
unkinded input distanceQ/q : Space d
unkinded flow: distanceQ/p ⇒ distanceQ/result
unkinded flow: distanceQ/q ⇒ distanceQ/result
unkinded input positionQ/p : Space d
unkinded flow: positionQ/p ⇒ positionQ/result
unkinded input displacementQ/p : Space d
unkinded input displacementQ/q : Space d
unkinded flow: displacementQ/p ⇒ displacementQ/result
unkinded flow: displacementQ/q ⇒ displacementQ/result
unkinded input rawDistance/p : Space d
unkinded input rawDistance/q : Space d
unkinded output rawDistance/result : ℝ
unkinded flow: rawDistance/p ⇒ rawDistance/dq
unkinded flow: rawDistance/q ⇒ rawDistance/dq
-/
#guard_msgs (whitespace := lax) in #kind_unkinded ingestBoundary

end ForPhysLib.Audits.Space
