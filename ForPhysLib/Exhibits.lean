/-
# The exhibits

Seven, per [PLAN.md](PLAN.md#exhibits-to-build), each producing build artifacts — a
`#check_failure`, a theorem exhibiting the wrong answer, or an `example` showing that
something which should be rejected type-checks — against the real PhysLib sources. The
first six probe the *kind* and *object* layers; the seventh, Composition, probes the
mereology: which quantities of a whole come from its parts.
-/

module

public import ForPhysLib.Exhibits.RigidBody
public import ForPhysLib.Exhibits.ReferenceFrame
public import ForPhysLib.Exhibits.HarmonicOscillator
public import ForPhysLib.Exhibits.TwoRovers
public import ForPhysLib.Exhibits.Electromagnetism
public import ForPhysLib.Exhibits.PointParticle
public import ForPhysLib.Exhibits.Composition

public section -- pkc-blanket
@[expose] section -- pkc-blanket-expose



end -- pkc-blanket-expose
end -- pkc-blanket
