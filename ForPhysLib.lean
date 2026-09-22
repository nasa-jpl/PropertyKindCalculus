/-
# ForPhysLib — a metrology layer proposed to PhysLib

The root of the proposal. The argument itself is prose, in four documents beside this file:

  * `ForPhysLib/README.md`       — the overview, readable in ten minutes
  * `ForPhysLib/REQUIREMENTS.md` — 31+1 requirements in 9 tiers (MR32 appended), each with a stable heading
  * `ForPhysLib/MOTIVATION.md`   — the reasons, strongest first
  * `ForPhysLib/PLAN.md`         — the staged adoption ladder and the exhibits to build

This module is the buildable part: everything the documents claim about *PKC* is checked here,
so a claim that stops being true stops compiling. Claims about *PhysLib* were read from source
and are not yet probes — converting them is rule 2 of `PLAN.md`'s rules of engagement.

Build with `lake build ForPhysLib`.
-/

module

public import ForPhysLib.CaseStudies
public import ForPhysLib.Kinds
public import ForPhysLib.Examination
public import ForPhysLib.Metrology
public import ForPhysLib.Kinded
public import ForPhysLib.Operators
public import ForPhysLib.Audits
public import ForPhysLib.Exhibits
public import ForPhysLib.QuantumMechanics
public import ForPhysLib.Electromagnetism
public import ForPhysLib.ClassicalMechanics
public import ForPhysLib.Scorecard

public section -- pkc-blanket
@[expose] section -- pkc-blanket-expose



end -- pkc-blanket-expose
end -- pkc-blanket
