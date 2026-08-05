/-
# Validation probes — the generated self-index

The indexes are *derived*: every row is computed from the environment, so a renamed declaration
changes the table and a declaration that stops being (say) a kind crossing leaves it. That is the
property worth having, and it is also the property that makes the harvest easy to break silently —
a membership test that stops matching produces an **empty table**, which renders as "there are none"
rather than as a failure.

So this probe authors a small closed world — three kinds with one authored edge between them, a
system, a component, a dedicated kind, a kinded record, a kinded operation, and one site of each
boundary tier — and pins the rendered index of each. The pins are what turn "the table came back
empty" into a build failure.

Two of the traps this guards are invisible from the source:

  * enumerating a `TagAttribute` (`@[pkc_math_config]`) requires walking every imported module,
    because `registerTagAttribute` sets `addImportedFn := fun _ _ => pure {}` — the obvious
    `getState` read returns only the current module's tags. The `pkc-math-config` pin below fails
    if that walk is ever simplified back to a `getState`.
  * a structure field projection satisfies the kinded-operation criterion literally, so the
    operations table must exclude projections or every record field is listed twice. The
    `operations` pin fixes the expected membership.
-/
import PropertyKindCalculus.Index
import PropertyKindCalculus.DocGenMath

namespace PropertyKindCalculus.Tests.Index

open PropertyKindCalculus

/-! ## A closed world to index -/

/-- A probe kind standing for a gain. -/
def gainKind : KindOfProperty := { id := "probe gain", scale := .ratio }
/-- A probe kind standing for an input signal. -/
def signalKind : KindOfProperty := { id := "probe signal", scale := .ratio }
/-- A probe kind standing for the product of a gain and a signal. -/
def outputKind : KindOfProperty := { id := "probe output", scale := .ratio }

/-- The one authored edge of this world: gain times signal yields output. -/
theorem gain_times_signal : ProductKind gainKind signalKind outputKind := ⟨rfl, rfl, rfl⟩

/-- The probe system. -/
def probeSystem : System := ⟨"probe system"⟩
/-- The probe component. -/
def probeComponent : Component := ⟨"probe component"⟩
/-- The probe dedicated kind — `probe system — probe component ; probe output`. -/
def probeDedicated : DedicatedKind := outputKind.dedicatedTo probeSystem probeComponent

/-- A kinded record: two quantities at different kinds, one carrying fixed notation. -/
structure ProbePair (α : Type) where
  /-- The gain factor. -/
  gain : Quantity gainKind α
  /-- The input signal. -/
  signal : Quantity signalKind α

attribute [pkc_math_symbol "g"] ProbePair.gain

/-- A configuration type, to exercise the tag-attribute enumeration. -/
@[pkc_math_config]
structure ProbeConfig (α : Type) where
  /-- The sole configured constant. -/
  offset : Quantity outputKind α

/-- A tagged crossing minting the probe output kind. -/
@[kindCrossing]
def probeCrossing (x : Float) : Quantity outputKind Float := ⟨x⟩

/-- A kinded operation that reaches the calculus through the authored crossing — the case the
operations table's *Crossings* column exists to report. -/
def probeFromRaw (x : Float) : Quantity outputKind Float := probeCrossing x

/-- A carrier-vocabulary exception on the probe kinds. -/
@[carrierVocab]
def probeVocab (a b : Quantity gainKind Float) : Quantity gainKind Float :=
  ⟨min a.magnitude b.magnitude⟩

/-- An emission boundary out of the probe world. -/
@[kindEmission]
def probeEmission (x : Quantity outputKind Float) : Float := x.magnitude

/-! ## The pinned indexes

Each pin fixes both the row count and the content. A harvest that silently stops matching shows up
as `(0 row(s))` and fails here. -/

/--
info: Kinds of property (3 row(s))
Kind | Identity | Scale | Algebra | Theorems
gainKind | probe gain | ratio | gainKind · signalKind → outputKind | gain_times_signal
outputKind | probe output | ratio | gainKind · signalKind → outputKind | gain_times_signal
signalKind | probe signal | ratio | gainKind · signalKind → outputKind | gain_times_signal
-/
#guard_msgs in
#pkc_index "kinds" PropertyKindCalculus.Tests.Index

/--
info: Systems (1 row(s))
System | Identity | Dedicated kinds | Theorems
probeSystem | probe system | probeDedicated |
-/
#guard_msgs in
#pkc_index "systems" PropertyKindCalculus.Tests.Index

/--
info: Dedicated kinds-of-property (1 row(s))
Dedicated kind | System | Component | Kind of property | Theorems
probeDedicated | probeSystem | probeComponent | outputKind |
-/
#guard_msgs in
#pkc_index "dedicated-kinds" PropertyKindCalculus.Tests.Index

/--
info: Authored kind crossings (3 row(s))
Site | Tier | Kinds minted | What it does
probeCrossing | kindCrossing | outputKind | A tagged crossing minting the probe output kind.
probeEmission | kindEmission |  | An emission boundary out of the probe world.
probeVocab | carrierVocab | gainKind | A carrier-vocabulary exception on the probe kinds.
-/
#guard_msgs in
#pkc_index "crossings" PropertyKindCalculus.Tests.Index

/-! The record table is one row *per field*, with the record named only on its first — hence three
rows for two records. `ProbeConfig` appears here as well as in the configuration-types index, and
that is not a duplicate: it genuinely is a kinded record and genuinely is a configuration type. -/

/--
info: Kinded records (3 row(s))
Record | Field | Carrier | Kind | Notation
ProbeConfig | offset | Quantity | outputKind |
ProbePair | gain | Quantity | gainKind | g
 | signal | Quantity | signalKind |
-/
#guard_msgs in
#pkc_index "records" PropertyKindCalculus.Tests.Index

/-! Three operations, and the two exclusions are as load-bearing as the inclusions: `ProbePair.gain`
and `ProbeConfig.offset` are *projections*, so they are not listed (they are already record rows),
and `probeEmission` returns a bare `Float`, so it is not kinded. `probeFromRaw` shows the *Crossings*
column doing its job — it reaches the calculus only through the authored `probeCrossing`. -/

/--
info: Kinded operations (3 row(s))
Operation | Argument kinds | Result kind | Crossings
probeCrossing |  | outputKind |
probeFromRaw |  | outputKind | probeCrossing
probeVocab | gainKind, gainKind | gainKind |
-/
#guard_msgs in
#pkc_index "operations" PropertyKindCalculus.Tests.Index

/--
info: Configuration types (1 row(s))
Type | What it is
ProbeConfig | A configuration type, to exercise the tag-attribute enumeration.
-/
#guard_msgs in
#pkc_index "pkc-math-config" PropertyKindCalculus.Tests.Index

/--
info: Fixed notation (1 row(s))
Declaration | Renders as | Layout
gain | g | function head
-/
#guard_msgs in
#pkc_index "pkc-math-symbol" PropertyKindCalculus.Tests.Index

end PropertyKindCalculus.Tests.Index
