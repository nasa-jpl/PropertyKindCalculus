/-
# The exhibits

Seven, per [PLAN.md](PLAN.md#exhibits-to-build), each producing build artifacts — a
`#check_failure`, a theorem exhibiting the wrong answer, or an `example` showing that
something which should be rejected type-checks — against the real PhysLib sources. The
first six probe the *kind* and *object* layers; the seventh, Composition, probes the
mereology: which quantities of a whole come from its parts.
-/
import ForPhysLib.Exhibits.RigidBody
import ForPhysLib.Exhibits.ReferenceFrame
import ForPhysLib.Exhibits.HarmonicOscillator
import ForPhysLib.Exhibits.TwoRovers
import ForPhysLib.Exhibits.Electromagnetism
import ForPhysLib.Exhibits.PointParticle
import ForPhysLib.Exhibits.Composition
