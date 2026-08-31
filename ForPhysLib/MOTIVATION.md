# Motivation

Ten reasons, strongest first, plus a coda on how to read the defects among them. Each has a
stable heading so it can be cited from elsewhere.

Everything asserted about PhysLib here was read from source. **None of it has been
compiled.** Turning each claim into a build artifact is the point of
[the plan](PLAN.md), not its premise.

---

### M1. PhysLib documents the gap in its own words

Three separate modules, by three separate authors, write down the thing this layer would fix.

1. `SpaceAndTime/Time/Basic.lean` — *"The choice of units or origin can be made on a
   case-by-case basis, as long as they are done consistently. However, **since the choice of
   units and origin is left implicit, Lean will not catch inconsistencies in the choice of
   units or origin when working with `Time`.**"* It then names the harmonic oscillator as the
   example, and `t` and `ω` as the pair the reader must keep consistent — which is
   [MR4](REQUIREMENTS.md#mr4-same-dimension-kinds-stay-apart) stated as a reader obligation,
   in the definition of time.

2. `SpaceAndTime/ReferenceFrame.lean` §C — *"`frame.Vector` … **intentionally records the
   coordinate frame but not the physical dimension**, so relative position, velocity,
   acceleration, force, momentum … can use the same componentwise calculations. **Their
   different physical roles, units, and transformation laws must be supplied by the
   surrounding definitions.**"*

3. `ReferenceFrame/API-map.yaml` — *"…so they share one carrier here; the physical dimension,
   units and transformation law belong to whatever definition supplies the quantity."*

The second and third defer three things: **physical role**, **units**, **transformation
law**. Those are `KindOfProperty`, `Dimension` and `Variance` — which together are
`InFrame f var k R`, item for item.

**PKC is not proposing an ontology to PhysLib. It is supplying the type PhysLib's own doc
comment is asking for.** And since `ReferenceFrame.Vector` has no parameter that could carry
them, "supplied by the surrounding definitions" can today only mean *supplied by the name of
the surrounding definition*.

### M2. PhysLib already applies this discipline, to space, and it works

`Space d` is an affine torsor over `EuclideanSpace ℝ (Fin d)`, and `ReferenceFrame`'s module
doc defends the choice at length:

> "Two points determine a displacement, but no point is automatically the zero point. The
> chosen origin therefore belongs to the frame, not to space itself."

That is the position/extent distinction — the interval/ratio scale split of
[MR5](REQUIREMENTS.md#mr5-scale-type-gates-the-operators) — done structurally, argued well,
and *already in the library*.

The proposal is not foreign to PhysLib. **It is the discipline PhysLib already applied to
space, applied also to time, to dimension, and to frame.** This is the most useful single
fact in the survey, and it is also why the transition is likely to be cheap where it matters:
the hard conceptual work has been done and accepted.

### M3. The metrology layer exists and is unused

PhysLib has 572 `.lean` files. Outside `PhysLib/Units/` itself, **two** use the metrological
layer:

| file | imports |
|---|---|
| `QFT/PerturbationTheory/FieldSpecification/Basic.lean` | `Physlib.Units.WithDim.Momentum` |
| `SpaceAndTime/Time/TimeTransMan.lean` | `Physlib.SpaceAndTime.Time.TimeUnit` |

Meanwhile roughly **140** files carry dimension and unit talk in prose. The metrology is
present throughout PhysLib; it lives outside the checker. This is jstoobysmith's own
observation in [#1579](https://github.com/leanprover-community/physlib/pull/1579), with a
number attached.

### M4. Four unit types, none connected to its quantity

| unit type | imported by |
|---|---|
| `SpaceAndTime/Time/TimeUnit` | `TimeTransMan.lean`, `Units/Basic.lean` |
| `SpaceAndTime/Space/LengthUnit` | `Units/Basic.lean` only — **not by `Space`** |
| `ClassicalMechanics/Mass/MassUnit` | `Units/Basic.lean` only |
| `Thermodynamics/Temperature/TemperatureUnits` | nothing at all |

Each is a well-built type — `LengthUnit` and `TimeUnit` carry scaling, ratios and concrete
units with their relations. None is reachable from the quantity it measures. The `Space`
API map records requirement 12 as `done: true` for `LengthUnit`, and it *is* done, exactly as
written. See [MR29](REQUIREMENTS.md#mr29-every-satisfied-requirement-has-a-machine-checkable-witness).

### M5. A correctness constraint enforced by not using an abbreviation

In `ClassicalMechanics/RigidBody`:

```lean
noncomputable def angularVelocity     (M : RigidBodyMotion 3) (t : Time) : Fin 3 → ℝ  -- lab,  Ω = Ṙ Rᵀ
noncomputable def bodyAngularVelocity (M : RigidBodyMotion 3) (t : Time) : Fin 3 → ℝ  -- body, Ω = Rᵀ Ṙ

noncomputable def rotationalKineticEnergy (R : RigidBody 3) (ω : Fin 3 → ℝ) : ℝ
noncomputable def angularMomentum         (R : RigidBody 3) (ω : Fin 3 → ℝ) : Fin 3 → ℝ
```

`M.toRigidBody.inertiaTensor` is the **body-frame** inertia tensor. So
`rotationalKineticEnergy` applied to `bodyAngularVelocity` is correct and applied to
`angularVelocity` is wrong — and both compile, because both are `Fin 3 → ℝ`.

**The library knows.** Compare the two König theorems in `KineticEnergy.lean`:

- `kineticEnergy_eq_translational_add_bodyAngularVelocity` (L181) calls
  `M.toRigidBody.rotationalKineticEnergy (M.bodyAngularVelocity t)`.
- `kineticEnergy_eq_translational_add_angularVelocity` (L157) does **not** call
  `rotationalKineticEnergy` at all. It writes `½ ∫ |ω × r|²` out longhand.

It writes it longhand *because* the abbreviation is not valid with the lab-frame `ω` and the
body-frame inertia tensor. The docstring even carries the justification in prose: *"The
rotational energy is a frame-independent scalar, so it is evaluated here from the body-frame
angular velocity."*

A correctness-critical constraint, correctly understood by the author, **enforced by
declining to use an abbreviation, and invisible to the checker.** This is
[MR18](REQUIREMENTS.md#mr18-frame-covariance-and-what-survives-it), and it is the cleanest
instance of it anywhere in the survey.

### M6. Names are load-bearing and unchecked

Four lines from `ClassicalMechanics/HarmonicOscillator/Basic.lean`:

```lean
lemma hamiltonian_eq :
    hamiltonian S = fun _ p x => (1 / (2 : ℝ)) * (1 / S.m) * ⟪p, p⟫_ℝ +
      (1 / (2 : ℝ)) * S.k * ⟪x, x⟫_ℝ := by
  funext t x p        -- binder names transposed w.r.t. the statement
```

The statement binds `(_, p, x)`; the proof introduces `(t, x, p)`. Inside the proof the
variable spelled `x` **is the momentum** and the one spelled `p` **is the position**.

The lemma is correct and the proof is valid — `funext` does not read names — so this is not a
soundness bug. It is something more useful: a demonstration, in PhysLib's flagship
classical-mechanics file, that the names are doing the metrological work and nothing checks
them.

The setting that makes it possible: in that file position, velocity, momentum and force are
all `EuclideanSpace ℝ (Fin 1)`, so

```lean
noncomputable def lagrangian  (t : Time) (x : E) (v : E) : ℝ
noncomputable def hamiltonian (t : Time) (p : E) (x : E) : ℝ
```

have the same type with the second and third arguments playing opposite roles, and
`S.hamiltonian t x p` is well-typed and wrong.

### M7. A stated API requirement that cannot be satisfied as written

`ReferenceFrame`'s API map lists five requirements as `done: false`. One of them:

> *"The API shall contain the relative motion of two inertial frames, expressed as the boost,
> rotation and translation carrying one to the other, **together with the induced
> transformation law for frame vectors**."*

**There is no single such law.** Under a Galilean boost `u` with rotation `R`, among the five
quantities the Overview names as sharing the carrier:

| quantity | law |
|---|---|
| relative position, acceleration, force | `R x` |
| velocity | `R v + u` |
| momentum | `R p + m u` |

Three distinct laws, one carrier. A single definition on `frame.Vector` cannot state the
requirement; the variance index is what makes it expressible at all.

Note also that `GalileanGroup` already exists, with `MulAction (GalileanGroup d)
(Time × Space d)`. It acts on **points**. Nothing acts on `frame.Vector`. The missing link is
exactly the induced action on quantities.

**This is the strongest argument in the proposal**, because here PKC would arrive as a
*design input* rather than a retrofit — the layer is what makes an unwritten, already-agreed
requirement writable.

### M8. The API maps are a ready-made adoption vehicle

Twelve `API-map.yaml` files in the two directories surveyed, with a stable schema and evident
maintenance. Adding one `checked_by:` field converts human attestation into CI, and upgrades
an artifact the project already invested in rather than asking it to adopt a new one.

Nothing else on offer has that leverage-to-intrusiveness ratio. See
[MR29](REQUIREMENTS.md#mr29-every-satisfied-requirement-has-a-machine-checkable-witness).

### M9. Reach — PhysLib as a component of built systems

The one reason here that is not about finding defects.

A rover has wheels, a chassis, motors, a mast, an IMU. Every equation it needs is classical
mechanics PhysLib has or nearly has: rigid-body kinematics, König's theorem, angular
momentum, reference frames, Galilean transformations between them. A soil-moisture retrieval
needs dielectric mixing, Debye relaxation, ionic conduction — physics that *ought* to be in
PhysLib eventually and mostly is not.

In both cases the same three things block use today:

1. **No systems vocabulary** — [MR20](REQUIREMENTS.md#mr20-a-quantity-belongs-to-a-named-part-of-a-named-system).
   `RigidBody.mass` cannot be told which wheel.
2. **No carrier but `ℝ`, and `noncomputable`** —
   [MR27](REQUIREMENTS.md#mr27-carrier-generic). The equation cannot be run.
3. **The metrology is in names** —
   [MR26](REQUIREMENTS.md#mr26-frame-generic). A rover's IMU reports body-frame angular
   velocity; the navigation filter wants lab-frame. The distinction that must not be got
   wrong is a substring.

The consequence is that applied users re-implement, and the formalisation and the shipped
code are related only by prose. Carrier parametricity closes that: the *same* authored
definition, proved over `ℝ` and executed at `Float32`, with agreement as a theorem.

This is the *user's* motivation, distinct from the defect-finding motivation above, and in
the long run the stronger of the two.

### M10. The first stage is free and already finds things

[Stage 1](PLAN.md#stage-1-the-metrology-annex) changes no existing definition, imposes no
authoring cost, and turns ~140 files' worth of prose dimension claims into statements a build
can fail on.

It finds `Temperature.β`, whose docstring reads "*This has dimensions equivalent to
`Energy`*" while `β = 1/(kB·T)` is inverse energy — the arithmetic right, the annotation
wrong, and nothing able to disagree.

It also *confirms* things, which matters for the proposal's credibility: the damped
oscillator's discriminant `γ² − 4mk` is dimensionally coherent, M²T⁻² on both sides, and a
coverage pass says so at zero authoring cost. Not every audit finds a defect, and an honest
proposal says so.

### M11. None of the defects is a soundness bug, and that is the argument

Not an eleventh independent reason — a lens on
[M5](#m5-a-correctness-constraint-enforced-by-not-using-an-abbreviation),
[M6](#m6-names-are-load-bearing-and-unchecked) and
[M10](#m10-the-first-stage-is-free-and-already-finds-things), stated separately because it is
the objection that will otherwise be raised first.

The frame mismatch in `RigidBody` produces no wrong theorem: the author saw it and routed
around it. The transposed binders in `hamiltonian_eq` produce no wrong theorem: `funext` does
not read names. `Temperature.β`'s docstring is wrong about a value that is right.

**That is the point, not a weakness in the evidence.** Every one of them sits in exactly the
register a kind layer checks and nothing else does — the register where a fact about a
quantity is true, is known to the author, is written down in prose or in a name, and is
invisible to the elaborator. A survey of a library this carefully built that turned up
soundness bugs would be finding *arithmetic* errors, which is not what is being proposed and
not what is missing.

So the claim is not "PhysLib is wrong". It is that PhysLib is **carrying correctness in
channels the compiler cannot read**, and that the three found here are the ones visible from
outside, in a survey of twelve API maps, without running a single audit.
