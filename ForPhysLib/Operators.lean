/-
# Stage 3 aggregator — the operator tables, per adopted directory

One module per adopted PhysLib directory: the directory's kind algebra registered as
`KindMul`/`KindDiv` instances, so `*` and `/` elaborate through the curated table and an
unregistered pair fails to elaborate. See
`PLAN.md`, [Stage 3](PLAN.md#stage-3-the-operator-table).
-/

module

public import ForPhysLib.Operators.Space

public section -- pkc-blanket
@[expose] section -- pkc-blanket-expose



end -- pkc-blanket-expose
end -- pkc-blanket
