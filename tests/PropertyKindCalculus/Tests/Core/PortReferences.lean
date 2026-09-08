/-
# Core-tier probes — the reference vocabulary (`KindRef`, `NodeRef`, `Level`, `NodeId`)

The typed identity vocabulary behind `Provenance`'s two parameters (`Provenance.lean`,
"The reference vocabulary"): equality is structural and by resolved name — never by
rendering — and a rendering is derived, caller-parameterized display. The probes pin the
two properties every consumer leans on: references that denote different things are
unequal however alike they render, and the established rendering grammar
(`level/root.path`, `" → "`, `", "`, `#ordinal`) is reproduced from structure. Kernel
reducibility is exercised with `by decide` because the graph-decide commands put these
comparisons in front of the kernel, not just the evaluator.
-/
import PropertyKindCalculus.Provenance

namespace PropertyKindCalculus.Tests.PortReferences
open PropertyKindCalculus.Provenance

/-! ## Equality is by referent, not by rendering -/

-- Two kind declarations sharing a last component are different kinds …
#guard (KindRef.decl `A.qcK == KindRef.decl `B.qcK) == false
-- … even though they render alike.
#guard (KindRef.decl `A.qcK).render == "qcK" && (KindRef.decl `B.qcK).render == "qcK"
-- A dot-suffix relationship is not a match: the suffix tolerance has no structural analog.
#guard (KindRef.decl `Retrieval.rK == KindRef.decl `rK) == false
-- A declaration and a param rendering identically stay distinct classes.
#guard (KindRef.decl (.mkSimple "k") == KindRef.param "k") == false

-- The binder named `result` and the result node are different roots: the reserved-word
-- collision is unrepresentable.
#guard (NodeId.binder "result" == NodeId.result) == false
-- A binder and a `let` sharing a name are distinct references.
#guard (NodeRef.binder "x" == NodeRef.letBound "x") == false

-- Signature and tuple kinds compare componentwise.
#guard (KindRef.sig [.decl `aK, .decl `bK] == KindRef.sig [.decl `aK, .decl `bK]) == true
#guard (KindRef.sig [.decl `aK, .decl `bK] == KindRef.sig [.decl `aK, .decl `cK]) == false
#guard (KindRef.sig [.decl `aK] == KindRef.tuple [.decl `aK]) == false

-- Node identity is stable under call-site growth: the ordinal is always present, and
-- only the rendering collapses it.
#guard ((NodeId.binder "x").within `M.step == (NodeId.binder "x").within `M.step 1) == true
#guard ((NodeId.binder "x").within `M.step 1 == (NodeId.binder "x").within `M.step 2) == false
-- A member-shared address and an instance-scoped node differ by scope, not by spelling.
#guard ((NodeId.config `C).shared `M.step == (NodeId.config `C).within `M.step) == false

/-! ## The kernel reduces the comparisons -/

example : (KindRef.sig [.decl `A.b, .param "k"] == KindRef.sig [.decl `A.b, .param "k"])
    = true := by decide
example : (KindRef.decl `A.qcK == KindRef.decl `B.qcK) = false := by decide
example : ((NodeId.letBound "flag").within `M.step ==
    (NodeId.letBound "flag").within `M.step) = true := by decide

/-! ## The rendering grammar is reproduced from structure -/

#guard NodeRef.render (.result none) == "result"
#guard NodeRef.render (.result (some 2)) == "result.2"
#guard NodeRef.render (.fresh 3) == "_3"
#guard NodeRef.render (.const `Config.geometry) == "Config.geometry"
#guard (KindRef.sig [.decl `paramB, .decl `vegetationIndex]).render
    == "paramB → vegetationIndex"
#guard (KindRef.tuple [.decl `aK, .decl `bK]).render == "aK, bK"
#guard KindRef.unkinded.render == "_"

-- level/root.path, with the ordinal shown or collapsed by the caller's level naming
#guard ((NodeId.binder "span").field "lo" |>.field "q" |>.within `M.step 2).render
    (Level.render true) == "step#2/span.lo.q"
#guard ((NodeId.binder "span").field "lo" |>.within `M.step).render
    (Level.render false) == "step/span.lo"
#guard ((NodeId.config `Cfg.geom).field "angle" |>.shared `M.step).render
    (Level.render true) == "step/Cfg.geom.angle"
#guard (NodeId.resultAt 1 |>.within `M.retrieve).render (Level.render false)
    == "retrieve/result.1"

#guard lastComponent `A.b.c == "c"
#guard lastComponent (.mkSimple "solo") == "solo"

end PropertyKindCalculus.Tests.PortReferences
