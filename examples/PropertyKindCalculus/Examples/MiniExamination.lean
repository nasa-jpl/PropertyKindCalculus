/-
# Worked example: examination as a defining aspect

Demonstrates, as *checked* facts, the two roles the examination chain plays
(Dybkær Ch. 7; VIM4 2CD 2.4, 2.5, 2.7):

  1. **The refinement chain.** A concrete procedure *refines* a method, which
     *refines* a principle; refinement is reflexive-transitively closed, and every
     layer rests on the *same* base principle (`Refines.basePrinciple_eq`) — the
     forgetful projection `basePrinciple` is invariant along refinement.
  2. **The defining aspect.** Width and height share a *scale* (both ratio) and
     will share a *dimension* (both lengths), yet they are *distinct kinds* — and
     the reason is precisely that they are examined by different principles
     (`distinct_of_examPrinciple`, §7.5). Dimension and scale alone cannot tell
     them apart; the examination principle does.

Like `MiniLengthWidth`, this module is part of the separate `Examples` library
and imports the core `PropertyKindCalculus` library as any downstream consumer would.
-/

module

public import PropertyKindCalculus

@[expose] public section Blanket

namespace PropertyKindCalculus.Examples.Examination

open PropertyKindCalculus

/-! ## (1) The examination refinement chain (procedure ⊑ method ⊑ principle) -/

/-- The principle by which a *width* is examined (its terminological id matches
the `examPrinciple` link on the `width` kind below). -/
def widthPrinciple : ExaminationPrinciple := { id := "caliper-perpendicular" }

/-- A method based on that principle: a perpendicular caliper traverse. -/
def widthMethod : ExaminationMethod :=
  { id := "iso-width-method", principle := widthPrinciple }

/-- A concrete, application-specific procedure based on that method. -/
def widthProcedure : ExaminationProcedure :=
  { id := "iso-width-procedure-v1", method := widthMethod }

-- the procedure refines its method, and the method refines its principle …
example : Refines (.procedure widthProcedure) (.method widthMethod) :=
  Refines.of_basedOn (.procedure_method widthProcedure)

example : Refines (.method widthMethod) (.principle widthPrinciple) :=
  Refines.of_basedOn (.method_principle widthMethod)

-- … so by transitivity the procedure refines the principle directly.
example : Refines (.procedure widthProcedure) (.principle widthPrinciple) :=
  Refines.trans
    (Refines.of_basedOn (.procedure_method widthProcedure))
    (Refines.of_basedOn (.method_principle widthMethod))

-- coherence: every layer of the chain rests on the SAME base principle.
example :
    (ExaminationItem.procedure widthProcedure).basePrinciple
      = (ExaminationItem.principle widthPrinciple).basePrinciple :=
  Refines.basePrinciple_eq
    (Refines.trans
      (Refines.of_basedOn (.procedure_method widthProcedure))
      (Refines.of_basedOn (.method_principle widthMethod)))

-- the base principle computes to the principle we started from.
example : (ExaminationItem.procedure widthProcedure).basePrinciple = widthPrinciple := rfl

/-! ## (2) The examination principle individuates kinds -/

/-- The broad rational kind-of-quantity of dimension length. -/
def length : KindOfProperty := { id := "length", scale := .ratio }

/-- `width`, examined perpendicular to the object. -/
def width : KindOfProperty :=
  { id := "width", scale := .ratio, examPrinciple := some "caliper-perpendicular" }

/-- `height`, examined vertically — same scale, *different* examination principle. -/
def height : KindOfProperty :=
  { id := "height", scale := .ratio, examPrinciple := some "caliper-vertical" }

-- width and height share a scale (and will share a dimension) …
example : width.scale = height.scale := rfl

-- … yet they are DISTINCT kinds, and the reason is exactly that they are
--    examined by different principles — not an accident of their id strings.
example : width ≠ height :=
  KindOfProperty.distinct_of_examPrinciple (by decide)

-- the `width` kind is examined by the principle at the base of its whole
-- procedure chain — the structured examination layer links back to the kind.
example : width.examinedBy (ExaminationItem.procedure widthProcedure).basePrinciple := rfl

end PropertyKindCalculus.Examples.Examination

end Blanket
