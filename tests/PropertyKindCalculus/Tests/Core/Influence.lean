/-
# Validation probes — the influence queries

The disjunctive closure and the query vocabulary on it, driven at a small well-formed
graph whose answers are computed by hand: a two-step chain with an attested constant, a
gated ingest, an unused configuration port (the discriminating case — it is a source and
still influences nothing), and an exit crossed mid-pedigree. Every query is exercised
with an exact expected value, so a closure that over- or under-approximates fails here,
not in a downstream repository.
-/

import PropertyKindCalculus

namespace PropertyKindCalculus.Tests.Influence

open PropertyKindCalculus Provenance

/-- The probe graph: `mid ← in1 · att`, `out ← mid · gat`, with `cfg` a declared but
unused configuration port and `mid` a marked exit. -/
def G : Provenance String String where
  ports := [⟨"in1", "kA", .input⟩, ⟨"cfg", "kB", .config⟩, ⟨"out", "kC", .output⟩]
  intros := [⟨"mid", "kB", .derived⟩, ⟨"att", "kA", .attested "vendor table reviewed"⟩,
    ⟨"gat", "kB", .gated⟩]
  occurrences := [
    ⟨.product, [("in1", "kA"), ("att", "kA")], "mid", "kB", "probe", .anonymous⟩,
    ⟨.product, [("mid", "kB"), ("gat", "kB")], "out", "kC", "probe", .anonymous⟩]
  exits := ["mid"]

#guard G.wellFormed

-- Forward: the descendant cone follows the wiring; the unused config port reaches
-- nothing; the closure includes its own start.
#guard (G.influencedFrom ["in1"]).contains "mid"
#guard (G.influencedFrom ["in1"]).contains "out"
#guard G.mayInfluence "in1" "out"
#guard G.mayInfluence "att" "out"
#guard !(G.mayInfluence "cfg" "out")
#guard G.mayInfluence "cfg" "cfg"
#guard G.confounded "out" "in1" "gat"
#guard !(G.confounded "out" "in1" "cfg")

-- Backward: the pedigree of the output is everything but the unused port.
#guard (G.ancestorsOf ["out"]).contains "in1"
#guard (G.ancestorsOf ["out"]).contains "att"
#guard (G.ancestorsOf ["out"]).contains "gat"
#guard (G.ancestorsOf ["out"]).contains "mid"
#guard !((G.ancestorsOf ["out"]).contains "cfg")

-- The budget term list: exactly the sources the output rests on, in source order.
#guard G.influencers "out" == ["in1", "att", "gat"]

-- The assumption ledger and the trust decomposition, exact.
#guard (G.assumptionLedger "out").ports == [⟨"in1", "kA", .input⟩]
#guard (G.assumptionLedger "out").gated == ["gat"]
#guard (G.assumptionLedger "out").attested == [("att", "vendor table reviewed")]
#guard (G.trustSplit "out").derived == ["mid"]
#guard (G.trustSplit "out").gated == ["gat"]
#guard (G.trustSplit "out").attested == [("att", "vendor table reviewed")]
#guard (G.trustSplit "out").exited == ["mid"]

-- The propagation relation of the declared boundary: the input reaches the output, the
-- configuration port reaches nothing.
def C : Provenance.Contract String String where
  name := "probe"
  members := []
  ports := [⟨"in1", "kA", .input⟩, ⟨"cfg", "kB", .config⟩, ⟨"out", "kC", .output⟩]
  exits := ["mid"]

#guard C.propagation G == [("in1", "out")]

-- Change impact: the cone of the attested constant is what its re-review reopens, and
-- the version diff finds exactly the re-attested node.
#guard G.revalidationCone ["att"] == ["att", "mid", "out"]

/-- The same graph with the attested constant re-reviewed under a new reason. -/
def G2 : Provenance String String :=
  { G with intros := [⟨"mid", "kB", .derived⟩, ⟨"att", "kA", .attested "re-reviewed"⟩,
      ⟨"gat", "kB", .gated⟩] }

#guard Provenance.changedNodes G G2 == ["att"]
#guard Provenance.impactedBy G G2 == ["att", "mid", "out"]

-- Acyclicity: the probe graph has none of its values feeding themselves; the two-copy
-- loop below does, so the check is discriminating. Kernel-checked once.
#guard G.successors "in1" == ["mid"]
#guard G.acyclic
example : G.Acyclic := by decide

/-- Two copies feeding each other — the cycle `acyclic` must refuse. -/
def Gcyc : Provenance String String where
  ports := [⟨"a", "k", .input⟩]
  intros := [⟨"b", "k", .derived⟩]
  occurrences := [
    ⟨.copy, [("a", "k")], "b", "k", "probe", .anonymous⟩,
    ⟨.copy, [("b", "k")], "a", "k", "probe", .anonymous⟩]
  exits := []

#guard !Gcyc.acyclic

end PropertyKindCalculus.Tests.Influence
