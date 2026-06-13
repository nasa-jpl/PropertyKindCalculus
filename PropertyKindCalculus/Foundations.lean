/-
# Foundations — system and object

Dybkær, *An Ontology on Property for Physical, Chemical, and Biological Systems*
(2009), Chapter 3.
-/

namespace PropertyKindCalculus

/-- **§3.3 system** — "part or phenomenon of the perceivable or conceivable
world consisting of a demarcated arrangement of a set of elements and a set of
relationships or processes between these elements."

Modelled abstractly by identity here; the mereological structure needed for
extensivity (§13.5) is added in a later module. -/
structure System where
  id : String
deriving DecidableEq, Repr

/-- **§3.3 Note 6** — 'object' is given as a synonym of 'system'. We keep the
synonym so that the *instance* layer can read as "characterizes an object". -/
abbrev Object := System

end PropertyKindCalculus
