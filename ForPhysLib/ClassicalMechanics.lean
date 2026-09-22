/-
# The third campaign directory — `Physlib/ClassicalMechanics`, two subtrees mirrored

The three-directory campaign's third directory (see `PLAN.md`): the
`HarmonicOscillator` subtree (with `Solution.lean` and `Geometric/`) and the
`RigidBody` subtree, one shared vocabulary. `Feasibility.lean` answers the capability
questions first; the ladder stages follow it here.
-/

module

public import ForPhysLib.ClassicalMechanics.Feasibility
public import ForPhysLib.ClassicalMechanics.Kinds
public import ForPhysLib.ClassicalMechanics.Metrology
public import ForPhysLib.ClassicalMechanics.Kinded
public import ForPhysLib.ClassicalMechanics.Operators
public import ForPhysLib.ClassicalMechanics.Audits
public import ForPhysLib.ClassicalMechanics.SolidSphereInertia

public section -- pkc-blanket
@[expose] section -- pkc-blanket-expose



end -- pkc-blanket-expose
end -- pkc-blanket
