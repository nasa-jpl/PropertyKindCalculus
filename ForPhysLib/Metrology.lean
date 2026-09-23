/-
# ForPhysLib.Metrology — Stage 1, the metrology annex

One module per PhysLib directory: the Stage-0 kinds paired with their PhysLib `Dimension`
as `DimensionedKind`s, the directory's kind algebra authored, and
`#kind_dimensional_coverage` pinned over it — dimension claims a build can fail on, at
zero cost to existing code. See [PLAN.md](ForPhysLib/PLAN.md#stage-1-the-metrology-annex).

  * `Space` — the annex for `Physlib/SpaceAndTime/Space`, with the Stage-0 lookup proved
    against `Iso80000.Part3` by `decide`.
-/

module

public import ForPhysLib.Metrology.Space

@[expose] public section



