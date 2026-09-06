import Verso
import VersoManual
import VersoBlueprint
-- The extensivity nodes below now link real declarations, so this chapter imports
-- the (Mathlib-free, core) `Extensivity` module.
import PropertyKindCalculus.Extensivity
-- Further nodes below link declarations outside that module, each for a stated reason:
-- `Recarving` and `InterfaceLedger` (core, but their own modules), `AggregationLaws` (the
-- weighted mean over `ℝ` and the transport laws, all needing Mathlib), and the §13.5.2
-- predicate, which lives with the uncertainty it is about.
import PropertyKindCalculus.Recarving
import PropertyKindCalculus.InterfaceLedger
import PropertyKindCalculus.AggregationLaws
import PropertyKindCalculus.Uncertainty.QuasiExtensive
import PropertyKindCalculus.Uncertainty.Adequacy.MeanBound
-- The carving/oneness discussion below cites Marmodoro, so the chapter imports the
-- blueprint's `References`.
import PropertyKindCalculusBlueprint.References

open Verso.Genre
open Verso.Genre.Manual
open Informal

#doc (Manual) "Extensivity" =>

Dybkær §13.5 divides kinds-of-quantity "according to physical (and arithmetic)
additivity", presenting Bunge's four types: _unconditionally extensive_ (§13.5.1, the
value for the total equals the arithmetic sum over the parts), _quasiextensive_
(§13.5.2, approximately equal — an uncertainty question, not a mereological one),
_conditionally extensive_ (§13.5.3, the addition exists but the total may differ "due
to the respective internal and environmental conditions" — volume on mixing), and
_intensive_ (§13.5.4, no physical addition, the value "invariant with the extent of a
system of constant composition"). These are quantified arithmetic laws over the
mereology of systems — again something a description logic cannot state — and all four
are _realized_, sorry-free: three of them in the Mathlib-free `Extensivity` module
— the predicates over the `Mereology` module's carving, the two inductions that lift a
single split to the whole tree, and a checked witness for each — and §13.5.2 in
`Uncertainty.QuasiExtensive`, because "approximately" is a claim about measurement and
not about the mereology.

Four cases Bunge's four do not name are added. A value the parts do not determine at
all (_whole-proper_); a value that adds only about a _shared parameter_ — an axis, a
frame, a reference point — where the parallel-axis theorem lives and the transport
tower with it; a _weighted mean_, which is neither a sum nor a shared constant and
whose license is that the total weight is not zero; and a value that reads no part at
all but an _interface_ between two, whose additivity is purchased by a cancellation
law. The chapter closes on what a carving cannot say at all: how many parts there
are.

# Extensive and conditionally-extensive kinds (Dybkær §13.5)

:::group "extensivity"
Mass is extensive: the mass of a whole is the sum of the masses of its parts.
Volume on mixing is not: ethanol and water mix sub-additively. Tracking which
kinds are extensive is a precondition for soundly aggregating measurements.
:::

:::definition "def_extensiveKind" (parent := "extensivity") (lean := "PropertyKindCalculus.Extensive")
A kind is _extensive_ when, for any {uses "def_decomposition"}[carving] of a
{uses "def_system"}[system] into parts, the quantity of the whole equals the sum
over the parts — the mereological structure the foundations chapter supplies.
:::

:::proof "def_extensiveKind"
Realized as `Extensive k m`, a predicate over a kind `k` and a measurement `m`
(the property value observed on each node of a `Decomposition`): it asserts that
every part is measured as a value of kind `k`, and that the numeral on a disjoint
union is the sum of the numerals on its two parts.
:::

:::theorem "thm_extensive_additive" (parent := "extensivity") (lean := "PropertyKindCalculus.extensive_additive") (tags := "capstone, proved") (effort := "medium")
*Extensive aggregation.* For an extensive kind $`k` and a system decomposed into
parts $`s_1, \dots, s_n`,
$$`\mathrm{value}_k\Bigl(\bigsqcup_i s_i\Bigr) = \sum_i \mathrm{value}_k(s_i).`
The $`\forall`-quantified additivity law itself — not a single instance — is the
deliverable, and it is exactly what OWL2 has no vocabulary for. Builds on {uses "def_extensiveKind"}[extensive kinds].
:::

:::proof "thm_extensive_additive"
Proved in the `Extensivity` module by induction on the `Decomposition`: at a leaf
the law is reflexivity; at a union the single-split `additive` field plus the two
induction hypotheses give the numeral of the whole as the sum of the leaf sums.
:::

:::theorem "thm_mixing_subadditive" (parent := "extensivity") (lean := "PropertyKindCalculus.mixing_subadditive") (tags := "proved") (effort := "small")
*Counterexample — volume on mixing is not extensive.* Volume fails the additivity
law for a water/ethanol mixture: the volume of the mixture is strictly less than
the sum of the component volumes. Stating the negation keeps the extensive
predicate honest. Uses {uses "def_extensiveKind"}[extensive kinds].
:::

:::proof "thm_mixing_subadditive"
Proved in the `Extensivity` module. 50 mL of water and 50 mL of ethanol measure
96 mL when mixed; the strict inequality $`96 < 50 + 50` is `by decide`, and the
same `volMix` measurement witnesses $`\neg\,\mathrm{Extensive}\ \mathrm{volume}` by
refuting its `additive` field on that two-part decomposition.
:::

# Intensity, whole-properness, and what a carving cannot say

A `Decomposition` is a _carving_ and not a census. Nothing in it fixes how many parts a
system has, and every law of this chapter is quantified over all carvings rather than
stated for one — which is why the $`\forall`-quantified form is the deliverable: a total
that depends on how the whole was cut is not a total. That is Marmodoro's point about
physical structure, which "unites" without bringing a count principle with it, so that
"It is an open question how many entities a physical structure is"
{Manual.citep marmodoro_whole_but_not_one}[]. What a carving therefore cannot supply is
the _whole_; that arrives with a sort of system (the foundations chapter) and its
aggregation license (the object-type chapter).

Additivity is one answer to what composition does to a value, and the alternatives are not
the absence of an answer. Both below are stated against the same measurement, so a model that
claims one is claiming something refutable.

:::definition "def_intensiveKind" (parent := "extensivity") (lean := "PropertyKindCalculus.Intensive")
A kind is _intensive_ (§13.5.4) when composing two parts *that already agree* leaves the
value where it was: temperature, density, the angular velocity of a rigid body. The
hypothesis is Dybkær's own, read literally — his definition asks that the value be
"invariant with the extent of a system of constant composition", and _of constant
composition_ is the clause a shorter phrasing drops. Without it the law would assert that
mixing water at 20 °C with water at 80 °C leaves either reading intact.
:::

:::proof "def_intensiveKind"
Realized as `Intensive k m`, the same shape as {uses "def_extensiveKind"}[extensivity] with
the additivity field replaced by a conditional constancy field. What the structure says
about parts that _disagree_ is nothing at all: an intensive kind licenses no reading of the
whole from unequal parts, which is a narrower claim than a total law and an honest one.
:::

:::theorem "thm_intensive_uniform" (parent := "extensivity") (lean := "PropertyKindCalculus.intensive_uniform") (tags := "capstone, proved") (effort := "medium")
*Intensive aggregation.* For an intensive kind, a whole all of whose atomic parts read
$`v` reads $`v` itself, over any carving and to any depth. Builds on {uses "def_intensiveKind"}[intensive kinds].
:::

:::proof "thm_intensive_uniform"
By induction on the decomposition, exactly as the extensive capstone: at a leaf the
hypothesis is the conclusion; at a union the two induction hypotheses make the parts agree,
which is what the conditional constancy field consumes. The leaf-wise quantifier is
`Decomposition.Forall` — extensivity reaches its leaves through arithmetic (`leafSum`) and
intensivity has no arithmetic to reach them with.
:::

:::theorem "thm_not_extensive_of_intensive" (parent := "extensivity") (lean := "PropertyKindCalculus.not_extensive_of_intensive") (tags := "proved") (effort := "small")
*The branches exclude each other.* An intensive kind is not extensive as soon as two parts
agree on a *nonzero* value: additivity doubles it, constancy keeps it, and only
$`0 = 0 + 0` satisfies both. Uses {uses "def_intensiveKind"}[intensive kinds] and
{uses "def_extensiveKind"}[extensive kinds].
:::

:::proof "thm_not_extensive_of_intensive"
Cancellation on $`v + v = v + 0`. The nonzero hypothesis is stated rather than assumed
away, because a kind whose every reading is zero really does satisfy both laws, vacuously.
The library's witness is density: two parcels of one homogeneous fluid read 1000 kg/m³ and
so does the parcel they compose, which refutes additivity outright.
:::

:::definition "def_wholeProper" (parent := "extensivity") (lean := "PropertyKindCalculus.WholeProper")
A kind is _whole-proper_ when the value of the whole is produced by *no* aggregation over
the parts: neither by summing them nor by sharing a common reading with them. The
normal-mode frequency of a coupled pair is the standard case — a lone oscillator has no
normal mode, so there is nothing to sum and nothing to inherit. Bunge's four types do not
name this case; under the formalizations here it satisfies none of them, and in particular
it is not intensive, the value not being invariant with the extent of the system.
:::

:::proof "def_wholeProper"
A `Prop` structure whose two refutation fields are *exhibited*, as pairs of atomic parts,
rather than stated as negated universals: a negated universal is satisfied by a measurement
that is merely undefined somewhere, while a witness pins the failure to two parts a reader
can point at. What names the case is Marmodoro's distinction rather than Dybkær's vocabulary: her
structural powers constitute a whole out of parts, where the substantial power "*is* the
electron" {Manual.citep marmodoro_whole_but_not_one}[] — borne by the whole, and by nothing
the whole is made of.
:::

:::theorem "thm_normalMode_wholeProper" (parent := "extensivity") (lean := "PropertyKindCalculus.normalMode_wholeProper") (tags := "proved") (effort := "small")
*The whole-proper case is occupied.* Two oscillators at $`\omega_0 = 10` rad/s, coupled so the
upper normal mode sits at $`\omega_+ = 14` rad/s: the pair's reading is neither the parts'
sum (20) nor their common value (10). Uses {uses "def_wholeProper"}[whole-proper kinds].
:::

:::proof "thm_normalMode_wholeProper"
Both refutations are `decide` on the witness measurement, and the two derived theorems —
not extensive, not intensive — follow from the exhibited pair alone. The quantity-level
consequence is {uses "thm_assemble_ne_measured"}[assembling it anyway], in the object-type
chapter: with a license registered the sum still elaborates, and reports 20 rad/s for a mode
at 14.
:::


# Additivity to within a tolerance (§13.5.2)

The remaining branch of Bunge's four says the value for the total is "approximately equal" to
the sum over the parts. _Approximately_ is a claim about measurement, so the predicate is
stated where the uncertainty is, over $`\mathbb{R}` rather than over the numeral, and its
tolerance is a coverage factor rather than a number chosen to make the claim come out true.

:::definition "def_quasiExtensive" (parent := "extensivity") (lean := "PropertyKindCalculus.Uncertainty.QuasiExtensive")
A kind is _quasiextensive to within_ $`t` (§13.5.2) when composing two parts is additive up to
$`t` — at _each join_, not once for the whole. Naming the tolerance is what turns
"approximately" into a claim: two quasiextensive claims about one measurement are then
comparable, and the sharper is the one with the smaller $`t`. Refines
{uses "def_extensiveKind"}[extensivity].
:::

:::proof "def_quasiExtensive"
Realized as `Uncertainty.QuasiExtensive k m t`, the same two-field shape as
{uses "def_extensiveKind"}[`Extensive`] with the additivity equation replaced by
$`\lvert v(a \sqcup b) - (v(a) + v(b)) \rvert \le t`. Where the tolerance comes from is R18's
business: `join_within_tolerance` specializes the Chebyshev
{uses "thm_uq_coverage_chebyshev"}[coverage bound] to a mean-zero join discrepancy, so a
per-join tolerance of $`k` standard uncertainties carries probability at least $`1 - 1/k^2`.
:::

:::theorem "thm_quasiExtensive_leafSum" (parent := "extensivity") (lean := "PropertyKindCalculus.Uncertainty.quasiExtensive_leafSum") (tags := "capstone, proved") (effort := "medium")
*Quasiextensive aggregation.* For a kind quasiextensive to within $`t`, the value measured on
the whole differs from the sum over all atomic parts by at most the carving's join count times
the tolerance,
$$`\Bigl\lvert v\Bigl(\bigsqcup_i s_i\Bigr) - \sum_i v(s_i) \Bigr\rvert \le \mathrm{joins} \cdot t.`
That the bound grows with the carving is the content, not a weakness of the proof: a library
reporting one tolerance for a total however the total was assembled is reporting the wrong
number, and this says by how much. Builds on {uses "def_quasiExtensive"}[quasiextensive kinds].
:::

:::proof "thm_quasiExtensive_leafSum"
By induction on the decomposition, exactly as the §13.5.1 capstone: at a leaf the discrepancy
is zero over zero joins, and at a union the triangle inequality splits it into this join's
tolerance plus the two sub-carvings' accumulated bounds. The witness is a balance whose
composite readings carry one digit of rounding — quasiextensive to within 1, and not
extensive, so the branch is occupied by something §13.5.1 excludes.
:::

:::theorem "thm_extensive_iff_quasi_zero" (parent := "extensivity") (lean := "PropertyKindCalculus.Uncertainty.extensive_iff_quasiExtensive_zero") (tags := "proved") (effort := "small")
*§13.5.1 is §13.5.2 at zero tolerance.* A kind is extensive exactly when it is quasiextensive
to within nothing at all — so the branches are nested rather than parallel, and a tolerance is
not hiding a weaker law. Uses {uses "def_quasiExtensive"}[quasiextensive kinds] and
{uses "def_extensiveKind"}[extensive kinds].
:::

:::proof "thm_extensive_iff_quasi_zero"
Forward, the additivity equation makes the discrepancy zero; backward, $`\lvert x \rvert \le 0`
forces $`x = 0`. The tolerance is shown to be doing work by the other direction of the same
witness family: volume on mixing refutes _every_ tolerance below the 4 mL water and ethanol
actually contract by (`mixing_not_quasiExtensive`), so §13.5.3 reads as §13.5.2 with a
tolerance the conditions set.
:::

# Aggregating about a shared parameter

Some quantities add only relative to something the parts must share — a moment of inertia about
a common axis, an energy about a common datum. A `Measurement` reads a carving and nothing else,
so the parameter is made an explicit argument; what that buys is not a weaker law but a statable
one, about the case a library that forgets the axis actually hits.

The parameter is kind-specific — an axis for a moment of inertia, a *frame* for a momentum, a
*reference point* for an angular momentum — and the transports relating two parameter values
form a tower: each correction is priced in a summary that is itself extensive one rung down,
grounding out in mass. The worked witness is a rover (`RoverExtensivity`, examples): whether
its four wheels' spins, each read about its own axle, may be summed against the chassis is
decided by the priced correction — each assembly's momentum — which vanishes parked and does
not while driving.

:::definition "def_extensiveAbout" (parent := "extensivity") (lean := "PropertyKindCalculus.ExtensiveAbout")
A kind is _extensive about_ a parameter when fixing the parameter — an axis, an origin, a datum
— makes the ordinary additivity law hold. This is {uses "def_extensiveKind"}[extensivity] at
every parameter at once, not a weakening of it, which is what makes the mixed-parameter
statement a claim about the predicate rather than about one lucky choice.
:::

:::proof "def_extensiveAbout"
Realized as `ExtensiveAbout k m` over a `ParamMeasurement`, with `ExtensiveAbout.at` recovering
`Extensive k (m a)` at each parameter so both §13.5 capstones apply unchanged. Its companion
`Transports` carries the correction as an argument rather than defining it as the difference: a
transport law is useful only when the correction is computable from data the part already
carries.
:::

:::theorem "thm_parallel_axis" (parent := "extensivity") (lean := "PropertyKindCalculus.parallelAxis") (tags := "capstone, proved") (effort := "medium")
*The parallel-axis theorem, over any carving.* The moment of inertia about $`a` is the moment
about $`b` plus a correction built from the carving's own first moment and total mass,
$$`I_a = I_b + 2(b-a)\sum_i w_i x_i + (a^2 - b^2)\sum_i w_i.`
Both summaries are themselves extensive over the same carving, which is why this is a
metrological statement and not only an algebraic identity: transporting an aggregate costs
only quantities the parts already carry. Taking $`b` at the centre of mass kills the first
moment and leaves the textbook $`M d^2`. Builds on {uses "def_extensiveAbout"}[extensivity
about a parameter].
:::

:::proof "thm_parallel_axis"
By induction on the carving: at a leaf it is ring normalization of
$`w(x-a)^2 = w(x-b)^2 + 2(b-a)wx + (a^2-b^2)w`, and at a join the three folds distribute. The
`Int` ring arithmetic is why it lives in the Mathlib-backed `AggregationLaws` rather than the
core. What the core exhibits is the failure it corrects: two point masses read about axes
through themselves contribute nothing each, where the rod about its centre reads 2.
:::

:::theorem "thm_momentum_boost" (parent := "extensivity") (lean := "PropertyKindCalculus.momentumBoost") (tags := "proved") (effort := "small")
*A momentum transports between frames, priced in mass.* The momentum read in the frame at
$`u_1` is the momentum read at $`u_2` plus the carving's mass times the frame difference,
$$`p_{u_1} = p_{u_2} + \Bigl(\sum_i w_i\Bigr)(u_2 - u_1).`
The parameter of {uses "def_extensiveAbout"}[extensivity about a parameter] is a *frame* here
rather than an axis, and the failure it prices is reading each part in its own rest frame:
every reading is zero, so the untransported sum reports a system with no momentum at all.
:::

:::proof "thm_momentum_boost"
By induction on the carving: `ring` at a leaf on $`w(v-u_1) = w(v-u_2) + w(u_2-u_1)`, folds
distributing at a join. The core exhibits the failure (`drift_rest_frames_wrong`: two drifting
masses read 0 in their own rest frames where the laboratory reads the pair at 3) and
`drift_rest_frames_corrected` closes the gap from the general law, with the two corrections
being the parts' own laboratory momenta.
:::

:::theorem "thm_angular_momentum_transport" (parent := "extensivity") (lean := "PropertyKindCalculus.angularMomentumTransport") (tags := "proved") (effort := "small")
*An angular momentum transports between reference points, priced in momentum.* Componentwise
over any carving,
$$`L_a = L_b + (b - a) \times p,`
with the momentum components entering as the first moments of the velocities. This is the
middle rung of the transport tower: {uses "thm_parallel_axis"}[inertia's correction] is priced
in mass and first moment, this one in momentum, and {uses "thm_momentum_boost"}[momentum's] in
mass — each price itself extensive one rung down, so mixed-parameter aggregation is checkable
all the way to the ground.
:::

:::proof "thm_angular_momentum_transport"
By induction on the carving, `ring` at a leaf. Taking $`b` at a part's own mass centre and
$`a` at the system's shows the spin/orbital split of an angular momentum is this law and not
a new principle, and a part whose momentum vanishes reads the same about every point. The
rover instantiates both readings: each wheel's spin reads 2 about its own axle, parked or
driving; parked, every assembly's momentum vanishes and the four spins sum against the
chassis unchanged, while driving each transport costs −15 and the untransported sum misses
the whole by exactly the four prices.
:::

# The interface ledger — what parts exert across a cut

Every measurement above reads a *node* of a carving. A drive torque on a hub, a contact force
at a joint, the heat crossing a wall read no node at all: each is indexed by an ordered *pair*
of parts — an interface — and a `Measurement` has no slot for a pair. The ledger is that slot,
and its one law is the reason such quantities nonetheless aggregate.

:::definition "def_interfaceLedger" (parent := "extensivity") (lean := "PropertyKindCalculus.InterfaceLedger")
An _interface ledger_ over the parts of a {uses "def_decomposition"}[carving] is a pairwise
action carrying its cancellation law as a field: the two readings of one interface sum to
zero — for mechanical actions, Newton's third law. A pair of readings that does not cancel is
not two readings of one interface, so the obligation is a field for the reason a re-carving's
whole-preservation is.
:::

:::proof "def_interfaceLedger"
Realized as `InterfaceLedger` — `act` and `antisymm` — with `netOn` and `netTotal` reading
per-part nets against a carving and `mutualTotal` the flow across a cut. A ledger is entered
one direction at a time: `fun p q => raw p q - raw q p` antisymmetrizes any raw table, and
its law is `omega`. `act_self` is the law's own erasure clause: a carving that merges the two
ends of an interface hands both ends one name and the entry reads zero — which is why the
rover example's two drive trains (2/2 and 3/1 hub-to-rim splits) coarsen to the *same*
ledger, so internal-versus-external is the carving's fact rather than the machine's —
Dybkær's observer clause (§3.3 Note 5) with a proof attached.
:::

:::theorem "thm_net_total_union" (parent := "extensivity") (lean := "PropertyKindCalculus.netTotal_union") (tags := "proved") (effort := "small")
*The exact price of additivity.* For *any* pairwise action over a
{uses "def_decomposition"}[carving], lawful or not, rolling up per-part nets over a union
overshoots the two halves' own rollups by precisely the two cross-flows over the cut. A
ledger that drops a reaction does not fail additivity vaguely — it fails it by this number.
Stated with no law in scope, so it is the identity a violated law is measured against.
:::

:::proof "thm_net_total_union"
Six instances of the fold's linearity, assembled by `omega`. The rover example presents the
invoice: log the motor torques and forget the reactions, and the whole's rollup exceeds its
halves' by 16 — four motors' worth of uncancelled flow across the chassis–arms cut.
:::

:::theorem "thm_net_rollup" (parent := "extensivity") (lean := "PropertyKindCalculus.InterfaceLedger.netTotal_eq_extTotal") (tags := "proved") (effort := "small")
*The rollup.* Under the cancellation law the price at every cut is zero, so the sum over the
parts of the per-part nets is the exogenous total alone. The reaction a motor induces on the
body is real in the per-part net — it loads a bearing — and absent from the whole; both facts
are this theorem, read at a part and at the carving. Builds on
{uses "def_interfaceLedger"}[the ledger] and {uses "thm_net_total_union"}[the price identity].
:::

:::proof "thm_net_rollup"
The flows across any cut cancel (`mutualTotal_cancel`, by induction from the field), so the
interior of one carving cancels outright and only the exogenous column survives. In the
rover: the chassis's net reads −16 (four motors' reactions), each hub's balances to zero, and
the rover's total is the ground torque alone.
:::

:::theorem "thm_net_extensive" (parent := "extensivity") (lean := "PropertyKindCalculus.InterfaceLedger.netMeasurement_extensive") (tags := "capstone, proved") (effort := "medium")
*Additivity, purchased.* The net over a ledger satisfies {uses "def_extensiveKind"}[the
extensive law] — but where mass's `additive` field is the model's free choice, this one is a
theorem with a hypothesis: delete the cancellation field and
{uses "thm_net_total_union"}[the price identity] prices exactly what remains. One predicate,
two different licenses, which is the sense in which the *scope* of extensivity is
kind-specific: what varies between kinds is not whether a sum appears but which law licenses
it.
:::

:::proof "thm_net_extensive"
Both fields follow from {uses "thm_net_rollup"}[the rollup]: the kind is fixed by
construction, and additivity collapses to the fold's union case once each rollup is its
exogenous total. The rover example instantiates it at the torque kind, with the lawless
counter-witness beside it.
:::

# The weighted mean, and its license

A third aggregation mode, neither additive nor constant. Its side condition is the one a formula
written without it silently violates — where a centre of mass defined as a ratio of integrals
with no mass hypothesis returns the origin for a massless body.

:::definition "def_weightedCarving" (parent := "extensivity") (lean := "PropertyKindCalculus.WeightedCarving")
A _weighted carving_ is a carving, a weight per part, and the license the mean needs: the total
weight is not zero. Carrying the condition as a field is the point — a whole with no weight is
not a term of the type, so the degenerate case is unreachable rather than handled.
:::

:::proof "def_weightedCarving"
Realized as `WeightedCarving R P` in the Mathlib-free core (`Aggregation`), carried at whatever
numbers the task uses: `WeightedCarving.mean` is the ratio of the weighted fold to the weight
fold, and needs the carrier's `*` and `/` beside the `+` every mode needs. What cannot live
there is the mode's law — see below.
:::

:::definition "def_weightedCarving_mk" (parent := "extensivity") (lean := "PropertyKindCalculus.WeightedCarving.mk?")
The license _decided_ rather than assumed. A program does not hold a proof that its weights sum
to something nonzero; it holds the weights. The run-time constructor tests the total and either
produces the carving — license included — or refuses. The refusal is the value a formula written
without the hypothesis would have had to invent.
:::

:::proof "def_weightedCarving_mk"
`WeightedCarving.mk?` is a `dif` on the carrier's own equality test, and
`mk?_eq_none_iff` says it refuses exactly the carvings whose total is the carrier's zero.
Uses {uses "def_weightedCarving"}[weighted carvings].

What the test *rejects* is what the carrier calls zero, and that is where the ladder starts
mattering. At `Float` the license is satisfied by `NaN`: an all-`NaN` carving is accepted and its
mean of a constant is `NaN`, refuting at that carrier the law proved below. Nothing is wrong with
the field; what is absent is a carrier law to spend it on, which is why the executable rungs state
their own gate rather than inherit this one.
:::

:::theorem "thm_weighted_mean_const" (parent := "extensivity") (lean := "PropertyKindCalculus.WeightedCarving.mean_const") (tags := "proved") (effort := "small")
*The mean of a constant is that constant.* Put every part at the same place and the whole is at
that place, whatever the weights — the law that distinguishes this mode from a sum and from a
shared reading at once. Uses {uses "def_weightedCarving"}[weighted carvings].
:::

:::proof "thm_weighted_mean_const"
A constant factors out of the fold (`fold_mul_const`, by induction), and the license discharges
the cancellation. Cancellation is a field law, which is why this statement is in the
PhysLib-backed `AggregationLaws` over $`\mathbb{R}` while the mode it is about is in the core:
the structure travels down to every carrier and the law stops at the lawful ones.

That the weights are load-bearing is checked separately: a carving weighted 1 and 3 over values
3 and 1 has mean $`3/2` where the unweighted average of the same values is $`2`, so a `mean`
ignoring its weights would fail the probe.
:::

:::theorem "thm_mean_fp32_bound" (parent := "extensivity") (lean := "PropertyKindCalculus.Uncertainty.Adequacy.mean_fp32_within_errBound") (tags := "proved") (effort := "medium")
*The binary32 weighted mean is within the evaluation DAG's rounding budget of the exact one.* The
rung between the mode and its law: at genuine binary32 the mean is computed on a rounded grid, so
the constant law holds only up to an accumulated budget, and the theorem says what that budget is.
Uses {uses "def_weightedCarving"}[weighted carvings].
:::

:::proof "thm_mean_fp32_bound"
A mean is the first aggregation mode that is not a fold — it multiplies, sums, and finally
divides — so it is exactly the shape the adequacy layer's forward-error theorem
(`dag_fp32_error_bound`) was built for. `MeanBound` compiles a carving into that layer's `Expr`
(weights and values as exact binary32 constants, the folds as `add` nodes, the ratio as the one
`div` node) and reads the bound off it. Every rounding the mean incurs is a node of the budget,
and the quotient rule's magnitude factors are what a small total weight costs.

The load-bearing detail is that the *license does not cross the bridge*. `WeightedCarving`'s
field says the total is not the *carrier's* zero, which at binary32 is a statement about the
*rounded* fold; the theorem also needs one about the *exact* fold, and neither implies the
other. Both directions are ordinary floating-point behavior and both are exhibited: weights
$`2^{24}`, $`1`, $`-2^{24}` sum exactly to $`1` while their binary32 fold is exactly $`+0`,
because the first addition absorbs the $`1`; and weights $`2^{24}`, $`1`, $`1`, $`-(2^{24}+2)`
sum exactly to $`0` while their binary32 fold is exactly $`-2`, because two absorbed $`1`s leave
the running total short. So forgetting a binary32 carving to the real carving it specifies takes
the specification's license as an *argument*, and the signature is where that is recorded.
:::

:::theorem "thm_licenses_agree_exact" (parent := "extensivity") (lean := "PropertyKindCalculus.licenses_agree_of_exact") (tags := "proved") (effort := "small")
*A denominator that is never rounded has one license, not two.* Where the refinement's rounding
is the identity, forgetting a carving's total gives the total of the forgotten weights, so the
executable condition and the specification's are the same statement read through the forgetful
map — and a run-time test of the computed total is a test of the quantity being defined. Uses
{uses "def_weightedCarving"}[weighted carvings].
:::

:::proof "thm_licenses_agree_exact"
By induction on the carving: identity rounding makes the bridge law an additive homomorphism, so
the fold commutes with the forgetting. Stated in the core, over an arbitrary refinement, since
nothing about binary32 enters.

This is the strongest of the two remedies and the one to reach for first, because it removes the
question rather than answering it. It is available exactly when the weights are counts or
indicators — a validity mask, a sample tally, a pixel count — which is the ordinary shape of a
masked average: fold the denominator where addition is exact and convert to the numerator's
carrier once, rather than accumulating it in the same floating-point type as the numerator.
:::

:::theorem "thm_licenses_agree_nonneg" (parent := "extensivity") (lean := "PropertyKindCalculus.Uncertainty.Adequacy.licenses_agree_of_nonneg") (tags := "proved") (effort := "medium")
*Nonnegative weights make the two licenses equivalent.* Where the denominator genuinely is a
binary32 fold of real-valued weights, requiring them to be nonnegative and on the grid restores
the equivalence: the rounded total is zero exactly when the exact total is. Uses
{uses "def_weightedCarving"}[weighted carvings].
:::

:::proof "thm_licenses_agree_nonneg"
Both counterexamples are built from cancellation, so nonnegativity is exactly what excludes them.
The floating-point content is one lemma — a grid point does not shrink when a nonnegative is
added to it and the sum is rounded, which is monotonicity of rounding together with rounding
fixing the grid. Absorption may return the grid point unchanged; it cannot return anything
smaller. Induction then gives both halves: a positive exact total forces a positive rounded one,
and a zero exact total forces a zero rounded one.

Grid membership is a real hypothesis, not bookkeeping: the rounding-spec format is a bare record
over $`\mathbb{R}` with representability a separate predicate, so "this is a binary32 number" has
to be said, and without it a weight below half the smallest subnormal would round away and the
argument would fail at the leaf it starts from.

This covers the weights metrology actually uses — masses, areas, durations, coverage fractions,
validity indicators — but it is the second-best fix. Where the weights are counts, the theorem
above applies and no floating-point reasoning is needed at all.
:::

:::definition "def_weightedCarvingQ" (parent := "extensivity") (lean := "PropertyKindCalculus.WeightedCarvingQ")
*The mode with its kinds on.* A weighted carving over a bare carrier is silent about three things a
kind layer can say. The weight kind has to be one that sums, so `WeightedCarvingQ` carries its
{uses "def_weightedCarving"}[carving's] difference-kind proof as a field and a carving of a
non-summable kind cannot be built. The weight, value and product kinds have to be related, so the
mean asks for a product license and a quotient license that say so. And the quotient the mean
performs is a licensed kind change, not a bare division.
:::

:::theorem "thm_kinded_mean_erases" (parent := "extensivity") (lean := "PropertyKindCalculus.WeightedCarvingQ.mean_magnitude") (tags := "proved") (effort := "small")
*The kinded mean computes what the carrier mean computes.* Its magnitude is the carrier-level mean
of the same data. So the kind index gates which folds may be written and contributes nothing to the
value — which is what lets the {uses "thm_mean_fp32_bound"}[binary32 bound], stated about
magnitudes, apply unchanged to a mean a user wrote with kinds on.
:::

:::proof "thm_kinded_mean_erases"
Two inductions over the carving, one per fold, each with the same shape: a leaf is the erasure by
definition, and a join is `Carrier.add` on both sides once the operands have been rewritten.
Realized in the Mathlib-free core (`Aggregation.lean`), depending on `propext` alone.

The theorem is what makes the kinded layer honest about its cost. Nothing is recomputed and no
numerical claim is restated: the three obligations above are discharged once at construction, and
everything proved downstream about magnitudes continues to hold.
:::

:::theorem "thm_mean_div_refines" (parent := "extensivity") (lean := "PropertyKindCalculus.WeightedCarvingQ.mean_div_refines") (tags := "proved") (effort := "small")
*The mean's division is an R10 site.* Forgetting the executable kinded mean to the specification
carrier is the rounding of the specification quotient of the forgotten numerator and denominator —
the quotient bridge read at the mean's own division node.
:::

:::proof "thm_mean_div_refines"
Immediate from the quotient bridge, and that is the point: until the mean acquired kinds, the
bridge had no consumer that was not a test of itself. A weighted mean is the first model-level
construct in the library that divides across a licensed kind change, so it is the first place the
law does work.

What the theorem does *not* say is that the whole mean commutes with the forgetful map. The folds
above the division round at every join, and pushing the forgetful map through them is exactly what
{uses "thm_licenses_agree_exact"}[the exact-carrier hypothesis] supplies. The division is one step
of that argument, stated where it holds with no side condition. Instantiated at the binary32 rung on
an indicator-weighted carving whose license is discharged rather than assumed.
:::

# Re-carving, and what a count is keyed to

A carving is not a census, and the two halves of that claim are provable. What survives a
re-carving is every licensed aggregate; what does not is how many parts there are.

:::definition "def_recarving" (parent := "extensivity") (lean := "PropertyKindCalculus.Recarving")
A _re-carving_ is a map from one carving of a whole to another, carrying the obligation that the
measured whole is the same whole. It is the generalization of a pattern physics libraries prove
one functional at a time — merging indiscernible parts and checking that each additive
functional is unchanged.
:::

:::proof "def_recarving"
Realized as `Recarving m`, a map and its `preserves` field. The witness `coalesce` replaces any
carving by the single part whose mass is the total: fewer entities, same whole, with `preserves`
holding by `rfl`.
:::

:::theorem "thm_recarving_invariant" (parent := "extensivity") (lean := "PropertyKindCalculus.Recarving.leafSum_invariant") (tags := "capstone, proved") (effort := "medium")
*Every licensed aggregate is re-carving invariant.* For an extensive kind the total over the
parts is the value of the whole, so a map that preserves the whole preserves the total —
whatever it does to the parts. Builds on {uses "def_recarving"}[re-carvings] and
{uses "thm_extensive_additive"}[extensive aggregation].
:::

:::proof "thm_recarving_invariant"
Two rewrites by the extensive capstone reduce the claim to the `preserves` field. This is what
makes {uses "thm_extensive_additive"}[the $`\forall`-quantified form] the deliverable rather
than a convenience: a total that depended on how the whole was cut would fail exactly here.
:::

:::theorem "thm_count_not_invariant" (parent := "extensivity") (lean := "PropertyKindCalculus.coalesce_count_ne") (tags := "proved") (effort := "small")
*The count does not survive.* The same re-carving that preserves the mass takes a two-part
carving to a one-part one. So there is no function from the whole to how many parts it has,
and a count is licensed by a _sortal_ rather than by the whole — the SI's own reading of amount
of substance as a count of a specified elementary entity. Uses {uses "def_recarving"}[re-carvings].
:::

:::proof "thm_count_not_invariant"
`decide` on the exhibited pair, against `thm_recarving_invariant` on the same map: 2 kg before
and after, two parts before and one after. `countMeasurement` takes the sortal as an argument
and `count_sortal_ne` checks that the argument matters — one carving, two predicates, counts 2
and 0 — so a count is extensive over a fixed carving and yet not a property of the whole. This
is Marmodoro's "It is an open question how many entities a physical structure is"
{Manual.citep marmodoro_whole_but_not_one}[] as a refutation rather than a remark.
:::
