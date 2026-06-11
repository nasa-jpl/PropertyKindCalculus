/-
# KindCalculus

A Lean formalization of Dybkær's *Ontology on Property* (2009), extended with
Flater's full tracking of kinds of quantities (NIST TN 1943, Appendix C).

This root module re-exports the Mathlib-free ontological spine. The examples
under `KindCalculus.Examples` and the later PhysLib-backed dimension/coherence
and soil-moisture model layers are built separately by the lake glob.
-/

import KindCalculus.Foundations
import KindCalculus.Scale
import KindCalculus.Kind
import KindCalculus.Specialization
