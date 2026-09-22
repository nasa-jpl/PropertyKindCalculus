/-
# Stage 0 — the examinations that individuate `Kinds.Space`

The mirror of `ForPhysLib.Kinds.Space`, file for file, under the organising rule of
[the plan](../PLAN.md#stage-0-the-kind-vocabulary): *a kind lives in the file named by its
own examination principle*. The kinds carry their principle as a terminological string;
this file declares the principles as objects (Dybkær §7.5), proves each link
(`examinedBy`), and derives the distinctness the vocabulary rests on — kinds are
individuated **not by fiat but by how they are examined**.

The principles are, like the kinds, the catalogue's own — each `def` *is* the entry
from `Iso80000.Part3`'s `LengthPrinciple` namespace, so nothing can drift. -/

module

public import ForPhysLib.Kinds.Space

public section -- pkc-blanket
@[expose] section -- pkc-blanket-expose

namespace ForPhysLib.Examination.Space

open PropertyKindCalculus ForPhysLib.Kinds.Space

/-- Distance — the shortest path length between two points (`Dist`, the metric). -/
def shortestPath : ExaminationPrinciple := Iso80000.Part3.LengthPrinciple.shortestPath

/-- Position vector — from the chosen origin (`Origin.lean`'s conventional zero). -/
def fromOrigin : ExaminationPrinciple := Iso80000.Part3.LengthPrinciple.fromOrigin

/-- Displacement — between two points (the torsor's free vectors). -/
def betweenPoints : ExaminationPrinciple := Iso80000.Part3.LengthPrinciple.betweenPoints

/-- The metric's kind is examined by the shortest path. -/
theorem distance_examinedBy : distance.examinedBy shortestPath := rfl

/-- A point's kind is examined from the origin. -/
theorem positionVector_examinedBy : positionVector.examinedBy fromOrigin := rfl

/-- A translation's kind is examined between two points. -/
theorem displacement_examinedBy : displacement.examinedBy betweenPoints := rfl

/-- **§7.5, applied**: position and displacement are distinct *because* their examinations
differ — the general theorem instantiated, not a fresh `decide`. This is the same fact
`Kinds.Space.positionVector_ne_displacement` decides; here it is *derived from the
principle*, which is the mirror's point. -/
theorem positionVector_ne_displacement_by_examination : positionVector ≠ displacement :=
  KindOfProperty.distinct_of_examPrinciple (by decide)

end ForPhysLib.Examination.Space

end -- pkc-blanket-expose
end -- pkc-blanket
