/-
# Validation probes — the flow-digraph theorems, the kind graph, and the SCC gate

Three dangers closed for the `Graph` library:

  * **vacuity** — the flow-digraph theorems are applied at the core influence probes'
    concrete graph: the sound direction of sensitivity scoping produces an actual
    non-reachability fact, the acyclicity bridge an actual partial order;
  * **dead executability** — the kind-level component computation is driven at a
    hand-built graph with a known cluster, and at a crafted laundering loop harvested
    from this very file (two `ReciprocalKind` hypotheses closing a cycle between two
    role-distinct kinds), where the `#kind_scc` report finds the cluster and the
    `#kind_scc_clean` gate throws unless the cluster is declared as an allow group;
  * **silent axioms** — the bridge theorems' profiles are pinned.
-/

import PropertyKindCalculus.Graph
import PropertyKindCalculus.Tests.Core.Influence

namespace PropertyKindCalculus.Tests.Graph

open PropertyKindCalculus Provenance
open PropertyKindCalculus.Tests.Influence (G)

/-! ### The flow-digraph theorems, applied -/

-- Sensitivity scoping's sound direction: the probe's `false` is a non-reachability
-- theorem about the value flow.
example : ¬(G.flowDigraph).Reachable "cfg" "out" :=
  not_reachable_of_mayInfluence_eq_false (by decide)

-- And its converse reading: the probe's `true` is a reachability witness.
example : (G.flowDigraph).Reachable "in1" "out" :=
  mayInfluence_iff.mp (by decide)

-- The acyclicity bridge, applied: influence on the probe graph is a partial order.
example : IsPartialOrder String (G.flowDigraph).Reachable :=
  Provenance.Acyclic.isPartialOrder (by decide)

-- Budgets are finite sums, applied: on the (executably) acyclic probe graph, the
-- incidence-quiver paths between any two vertices form a finite type.
example (v w : Provenance.IncidenceVert G) : Finite (Quiver.Path v w) :=
  Provenance.Acyclic.finite_incidencePath (by decide) v w

/-! ### The kind-level component computation, hand-built -/

/-- Three kinds, a two-kind cycle, and a tail: cluster `{0, 1}`, hierarchy edge to
`2`. -/
def kg : KindGraph :=
  { kinds := #[`kA, `kB, `kC]
    edges := #[⟨0, 1, `auth, `viaK⟩, ⟨1, 0, `auth, `viaK⟩, ⟨1, 2, `auth, `viaK⟩] }

#guard kg.interderivable 0 1
#guard !(kg.interderivable 1 2)
#guard kg.clusters.map (·.size) == #[2, 1]
#guard kg.acyclicB == false
#guard (kg.hierarchyEdges.map fun e => (e.src, e.dst)) == #[(1, 2)]

/-! ### The SCC report and gate on a crafted laundering loop

Two role-distinct kinds wired into a cycle by two `ReciprocalKind` hypotheses — every
step licensed, no attest anywhere — plus a third kind derivable from the cluster. The
scan reads hypothesis binders, so no witness needs to be provable for the loop to be
visible, which is the point: the *rules* close the cycle before any value walks it. -/

/-- A probe kind. -/
def kX : KindOfProperty := { id := "kX", scale := .ratio }
/-- A probe kind, role-distinct from `kX`. -/
def kY : KindOfProperty := { id := "kY", scale := .ratio }
/-- A probe kind downstream of the cluster. -/
def kZ : KindOfProperty := { id := "kZ", scale := .ratio }

theorem xToY (_h : ReciprocalKind kX kY) : True := trivial
theorem yToX (_h : ReciprocalKind kY kX) : True := trivial
theorem yToZ (_h : ReciprocalKind kY kZ) : True := trivial

/--
info: kind graph — 3 kind(s), 3 licensed derivation edge(s), 1 inter-derivable cluster(s) of size ≥ 2, 0 within-kind edge(s)
  ⚠ {kX, kY}
      kX → kY [ReciprocalKind] (PropertyKindCalculus.Tests.Graph.xToY)
      kY → kX [ReciprocalKind] (PropertyKindCalculus.Tests.Graph.yToX)
-/
#guard_msgs in #kind_scc PropertyKindCalculus.Tests.Graph

/--
error: kind-level SCC: 1 undeclared inter-derivable cluster(s)
  ⚠ {kX, kY}
      kX → kY [ReciprocalKind] (PropertyKindCalculus.Tests.Graph.xToY)
      kY → kX [ReciprocalKind] (PropertyKindCalculus.Tests.Graph.yToX)

Each cluster's kinds can be manufactured from one another by licensed derivations alone — no attest, no review. If the cluster is intentional (representation variants of one role), declare it: `#kind_scc_clean … (kindA kindB)`. If it is not, one of the printed witness registrations merges two roles and must be split or retired.
-/
#guard_msgs in #kind_scc_clean PropertyKindCalculus.Tests.Graph

-- Declared, the same cluster passes the gate.
#kind_scc_clean PropertyKindCalculus.Tests.Graph (kX kY)

/-! ### Axiom profiles -/

/-- info: 'PropertyKindCalculus.Provenance.mem_influencedFrom_iff' depends on axioms: [propext,
Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Provenance.mem_influencedFrom_iff

/-- info: 'PropertyKindCalculus.Provenance.mem_ancestorsOf_iff' depends on axioms: [propext,
Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Provenance.mem_ancestorsOf_iff

/-- info: 'PropertyKindCalculus.Provenance.mayInfluence_iff' depends on axioms: [propext,
Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Provenance.mayInfluence_iff

/-- info: 'PropertyKindCalculus.Provenance.acyclic_iff_isAcyclic' depends on axioms: [propext,
Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Provenance.acyclic_iff_isAcyclic

/-- info: 'PropertyKindCalculus.Provenance.Acyclic.finite_incidencePath' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms Provenance.Acyclic.finite_incidencePath

end PropertyKindCalculus.Tests.Graph
