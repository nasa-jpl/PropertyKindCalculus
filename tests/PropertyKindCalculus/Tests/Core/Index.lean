/-
# Validation probes — the generated self-index

The indexes are *derived*: every row is computed from the environment, so a renamed declaration
changes the table and a declaration that stops being (say) a kind crossing leaves it. That is the
property worth having, and it is also the property that makes the harvest easy to break silently —
a membership test that stops matching produces an **empty table**, which renders as "there are none"
rather than as a failure.

So this probe authors a small closed world — three kinds with one authored edge between them, a
sort, a system, a component, a dedicated kind, a kinded record, a kinded operation, and one site of each
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

/-- The probe sort of system — what the dedicated kind is dedicated to. -/
def probeSort : SortOfSystem := ⟨"probe sort"⟩
/-- The probe system — a particular; nothing dedicates to it, which the three-column
`systems` pin below fixes. -/
def probeSystem : System := ⟨"probe system"⟩
/-- The probe component. -/
def probeComponent : Component := ⟨"probe component"⟩
/-- The probe dedicated kind — `probe sort — probe component ; probe output`. -/
def probeDedicated : DedicatedKind := outputKind.dedicatedTo probeSort probeComponent

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

/-- A tagged crossing minting the probe output kind from an already-kinded gain value.

`@[kindCrossing]`'s `add` requires a kinded argument (a crossing goes FROM something already
kinded), so this is not the raw-`Float` mint it once was; `probeIngest` below is that shape's
correct home instead. -/
@[kindCrossing]
def probeCrossing (g : Quantity gainKind Float) : Quantity outputKind Float := ⟨g.magnitude⟩

/-- A checked ingest mint: a raw carrier value enters the calculus as the probe output kind,
admitted by an inline (trivial, here) check. -/
@[kindIngest]
def probeIngest (x : Float) : Quantity outputKind Float := ⟨x⟩

/-- A kinded operation that reaches the calculus through the authored crossing — the case the
operations table's *Crossings* column exists to report. -/
def probeFromRaw (g : Quantity gainKind Float) : Quantity outputKind Float := probeCrossing g

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
info: Sorts of system (1 row(s))
Sort | Identity | Dedicated kinds | Theorems
probeSort | probe sort | probeDedicated |
-/
#guard_msgs in
#pkc_index "sorts" PropertyKindCalculus.Tests.Index

/--
info: Systems (1 row(s))
System | Identity | Theorems
probeSystem | probe system |
-/
#guard_msgs in
#pkc_index "systems" PropertyKindCalculus.Tests.Index

/--
info: Dedicated kinds-of-property (1 row(s))
Dedicated kind | Sort of system | Component | Kind of property | Theorems
probeDedicated | probeSort | probeComponent | outputKind |
-/
#guard_msgs in
#pkc_index "dedicated-kinds" PropertyKindCalculus.Tests.Index

/--
info: Authored kind crossings (4 row(s))
Site | Tier | Kinds minted | What it does
probeCrossing | kindCrossing | outputKind | A tagged crossing minting the probe output kind from an already-kinded gain value.
probeEmission | kindEmission |  | An emission boundary out of the probe world.
probeIngest | kindIngest | outputKind | A checked ingest mint: a raw carrier value enters the calculus as the probe output kind, admitted by an inline (trivial, here) check.
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

/-! Four operations, and the two exclusions are as load-bearing as the inclusions: `ProbePair.gain`
and `ProbeConfig.offset` are *projections*, so they are not listed (they are already record rows),
and `probeEmission` returns a bare `Float`, so it is not kinded. `probeFromRaw` shows the *Crossings*
column doing its job — it reaches the calculus only through the authored `probeCrossing`; `probeIngest`
is the ingest tier's own operation, with no argument kind (nothing was kinded on the way in). -/

/--
info: Kinded operations (4 row(s))
Operation | Argument kinds | Result kind | Crossings
probeCrossing | gainKind | outputKind |
probeFromRaw | gainKind | outputKind | probeCrossing
probeIngest |  | outputKind |
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

/-! ## The theorem edge — membership by type, like the ontology tables -/

/-- The probe forward: a signal becomes an output. -/
def probeFwdStep (x : Quantity signalKind Int) : Quantity outputKind Int := ⟨x.magnitude⟩

/-- The probe retrieval, inverting the forward. -/
def probeInvStep (y : Quantity outputKind Int) : Quantity signalKind Int := ⟨y.magnitude⟩

/-- The witness: the retrieval recovers the signal the forward consumed. -/
theorem probeInvStep_probeFwdStep (x : Quantity signalKind Int) :
    probeInvStep (probeFwdStep x) = x := rfl

/-- The forward's declared boundary. -/
def probeFwdBoundary :
    Provenance.Contract Provenance.NodeId Provenance.KindRef where
  name := "probe forward"
  members := [``probeFwdStep]
  ports := [⟨(Provenance.NodeId.binder "x").within ``probeFwdStep,
              .decl ``signalKind, .input⟩,
            ⟨Provenance.NodeId.result.within ``probeFwdStep,
              .decl ``outputKind, .output⟩]
  exits := []

/-- The retrieval's declared boundary. -/
def probeInvBoundary :
    Provenance.Contract Provenance.NodeId Provenance.KindRef where
  name := "probe retrieval"
  members := [``probeInvStep]
  ports := [⟨(Provenance.NodeId.binder "y").within ``probeInvStep,
              .decl ``outputKind, .input⟩,
            ⟨Provenance.NodeId.result.within ``probeInvStep,
              .decl ``signalKind, .output⟩]
  exits := []

/-- The one theorem edge of this world. -/
def probeRetrievalInvertsForward : Provenance.Relation where
  left := ``probeInvBoundary
  right := ``probeFwdBoundary
  kind := .inverts
  witness := ``probeInvStep_probeFwdStep
  claim := "the probe retrieval recovers the signal the forward consumed"

/-- A deliberately broken edge kept as a counterexample: the `relations` table renders it
with its mark (a table renders what is declared), while the `contracts` edge join and the
`provenance-coverage` table below leave it out — a misdeclaration is not a witness. -/
@[kindCounterexample]
def probeKeptBrokenEdge : Provenance.Relation :=
  { probeRetrievalInvertsForward with witness := ``probeFwdStep }

/--
info: Theorem edges between boundaries (2 row(s))
Edge | Claim | Witness | Clauses | In the author's words
probeKeptBrokenEdge | 'probe retrieval' inverts 'probe forward' | probeFwdStep | counterexample | the probe retrieval recovers the signal the forward consumed
probeRetrievalInvertsForward | 'probe retrieval' inverts 'probe forward' | probeInvStep_probeFwdStep |  | the probe retrieval recovers the signal the forward consumed
-/
#guard_msgs in
#pkc_index "relations" PropertyKindCalculus.Tests.Index

/-! ## The boundary table and the absences beside it

Membership by type again: both declared contracts are rows, each carrying the one real
theorem edge — the counterexample is not in the join. The coverage table renders what is
*absent*: no budget attaches to either produced port, and the row count in the title is
the claim, so a new unwitnessed boundary or unbudgeted output fails the pin. -/

/--
info: Declared boundaries (2 row(s))
Contract | Boundary | Interface | Members | Clauses | Theorem edges
probeFwdBoundary | 'probe forward' | 2 ports (0 params), 0 exits | 1 |  | probeRetrievalInvertsForward
probeInvBoundary | 'probe retrieval' | 2 ports (0 params), 0 exits | 1 |  | probeRetrievalInvertsForward
-/
#guard_msgs in
#pkc_index "contracts" PropertyKindCalculus.Tests.Index

/--
info: Provenance coverage absences (2 row(s))
Absence | Contract | At
no uncertainty budget | probeFwdBoundary | probeFwdStep/result : outputKind
no uncertainty budget | probeInvBoundary | probeInvStep/result : signalKind
-/
#guard_msgs in
#pkc_index "provenance-coverage" PropertyKindCalculus.Tests.Index

/-! ## The prose grammar

The `What it does` column of the tables above is a docstring quoted verbatim, so it arrives as
markdown. `parseProse` is what stops the markers reaching the page, and its two interesting cases are
both invisible from a table that looks fine:

  * spans **nest** — a docstring lead-in is routinely `**… the *branched* … **`, and a flattening
    parser puts the inner markers back on the page while the outer ones disappear, which looks like
    a *partial* fix rather than a broken one;
  * an unterminated delimiter must degrade to literal text. A parser that instead runs to the end of
    the string silently deletes the rest of the cell, and a cell that is merely *shorter* than it
    should be is not something a reader can notice.
-/

open PropertyKindCalculus.Index

/-- A parse rendered compactly, so the pins below diff on structure rather than on `Repr`'s
fully-qualified constructor names. -/
private partial def runsText (rs : Array ProseRun) : String :=
  "[" ++ String.intercalate ", " (rs.toList.map go) ++ "]"
where
  go : ProseRun → String
    | .text s   => s!"“{s}”"
    | .code s   => s!"code “{s}”"
    | .emph c   => "emph " ++ runsText c
    | .strong c => "strong " ++ runsText c

/-- info: "[strong [“a ”, emph [“b”], “ ”, code “c”], “ tail”]" -/
#guard_msgs in
#eval runsText (parseProse "**a *b* `c`** tail")

/-- info: "[“a lone * asterisk and a lone ` tick”]" -/
#guard_msgs in
#eval runsText (parseProse "a lone * asterisk and a lone ` tick")

/-- info: "[“plain sentence.”]" -/
#guard_msgs in
#eval runsText (parseProse "plain sentence.")

/-! ## Truncating a quoted docstring

A cell wider than its column is cut, and the cut used to be made on characters — which is blind to
the markup, so it landed inside a code span as readily as between two words and left an unpaired
backtick on the page. Markdown that no longer parses, from a cut that looked fine when it was made.

Cutting on *runs* instead is what the pins below fix, and each is a way that cut can still go wrong.
A code span cannot be trimmed to fit — half an identifier is a different, non-existent one — so it
has to be dropped whole. A paragraph that is entirely one span has to be truncated *inside* the span,
or it degrades to nothing at all. And the cut must not leave a span closing on a space: `*b *` is a
literal asterisk to markdown, not emphasis, so the trailing whitespace has to go with the cut. -/

/-- info: "alpha …" -/
#guard_msgs in
#eval summarize "alpha `beta gamma delta` omega" 12

/-- info: "**alpha** …" -/
#guard_msgs in
#eval summarize "**alpha beta gamma**" 8

/-- info: "a *b* …" -/
#guard_msgs in
#eval summarize "a *b `c d e` f* tail" 6

/-! Below the budget nothing is touched, and the budget is spent on what a reader sees: the six
`*` and two `` ` `` of the first pin are notation, so its 54 characters are 48 wide. The second is
the reason `summarize` reads a paragraph rather than a line — the body is the author's, not the
column's. -/

/-- info: "**A quantity (R10).** A magnitude of a fixed kind `k`." -/
#guard_msgs in
#eval summarize "**A quantity (R10).** A magnitude of a fixed kind `k`."

/-- info: 48 -/
#guard_msgs in
#eval summaryWidth "**A quantity (R10).** A magnitude of a fixed kind `k`."

/-- info: "Summary." -/
#guard_msgs in
#eval summarize "Summary.\n\nBody paragraph."

end PropertyKindCalculus.Tests.Index
