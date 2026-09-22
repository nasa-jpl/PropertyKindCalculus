/-
# ForPhysLib.Kinds — Stage 0, the kind vocabulary

One module per PhysLib directory: `KindOfProperty` declarations, Mathlib-free, each
lookup *being* the corresponding entry of PKC's `Iso80000` catalogue (the identification
recorded definitionally in Stage 1) rather than designed. See [PLAN.md](ForPhysLib/PLAN.md#stage-0-the-kind-vocabulary).

  * `Space` — the vocabulary of `Physlib/SpaceAndTime/Space`, the plan's first directory.
-/

module

public import ForPhysLib.Kinds.Space

public section -- pkc-blanket
@[expose] section -- pkc-blanket-expose



end -- pkc-blanket-expose
end -- pkc-blanket
