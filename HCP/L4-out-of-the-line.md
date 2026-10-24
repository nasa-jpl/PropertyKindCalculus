---
hcp: 5
id: l4-out-of-the-line
persona: "PhysLib contributor"
layer: PKC
pull: "The wobble throws body A's centre of mass off the line, and a second observer on a moving cart sees the pair differently. What must the model now say about where things are, and for whom?"
improvement: "Move the pair's centre-of-mass points into 3-D space, attach separation to its named pair, and make each observer's frame explicit."
concepts:
  - informal: "a pair state places body centres in 3-D"
    formal: "PairState3, BodyOf, and positionQ over the state's centre fields"
    where: "HCP.L4_OutOfTheLine#pair_state_and_bearers"
  - informal: "the A–B distance belongs to its pair and can change between states"
    formal: "separationOf, separationOf_magnitude, separationChange, and separationChange_magnitude"
    where: "HCP.L4_OutOfTheLine#whose_distance"
  - informal: "distance is the norm of displacement"
    formal: "distanceQ_eq_lengthOf_displacementQ and distanceQ_triangle over PairState3 points"
    where: "HCP.L4_OutOfTheLine#distance_is_length"
  - informal: "a vector's physical role and observer determine its transport"
    formal: "barePairDisplacement, kGeometricTransport, kBoostTransport, and origin_displacement_eq"
    where: "HCP.L4_OutOfTheLine#bare_frames; HCP.L4_OutOfTheLine#kinded_frames; HCP.L4_OutOfTheLine#observer_motion"
  - informal: "the Space adoption ladder reaches audited boundaries"
    formal: "pairSpanArea, pairSpanArea_magnitude, and the area-product refusal"
    where: "HCP.L4_OutOfTheLine#adoption_ladder"
artifacts: ['Lean lesson HCP.L4_OutOfTheLine', 'L4 system-context card']
tools: ['lake build HCP', 'python3 HCP/check-hcp.py']
exercises: 7
disclosure: ['distinguish points, vectors, and scalar distances', 'index pair separation by nominal identity', 'compare same-pair states', 'expose the role-blind bare frame API', 'kind frame transports by vector role', 'make observer motion part of frame context', 'recap Space stages 0–4']
owner: 'PKC methodology lead'
state:
  completed: []
---

# L4 — Out of the line

## 1. Persona

You are a PhysLib contributor: a physicist who writes Lean in PhysLib. You know Lean and
PhysLib and trust `Dimension` and `WithDim`; L0–L3 have established kinds, bearers,
composition, and body- and lab-frame angular velocity.

## 2. Pull

The wobble throws body A's centre of mass off the line, and a second observer on a
moving cart sees the pair differently. What must the model now say about where things
are, and for whom? The model moves the two centres of mass into `Space 3`, distinguishes
points from vectors and distances, and states the observer whose frame gives a vector its
context.

One name is one system; records under that name are its states at different times, its
configurations, or rival estimates of it—comparing them is the point; distinct names are
distinct systems. Pair P's separation therefore has one bearer across its states, while
pair Q has a different bearer. The lab frame F and cart frame G are explicit observers.

## Risks at this step

- **Bearer erased.** `distanceQ` cannot distinguish the A–B separation of pair P from that of pair Q; the typed cross-pair refusal is pinned at `HCP.L4_OutOfTheLine#whose_distance`.
- **Observer left implicit.** Bare vectors accept geometric, boost, and origin-shift transport even though only one law is right for each vector kind; `HCP.L4_OutOfTheLine#bare_frames` shows the wrong accepted forms and `HCP.L4_OutOfTheLine#kinded_frames` pins the role-specific refusals.

**Further reading**
- `Exhibits/ReferenceFrame`, MOTIVATION M7.

## 3. Small rigorous improvement

| Question | Context change | Attribute change | Risk shown | PhysLib stage |
|---|---|---|---|---|
| The wobble throws body A's centre of mass off the line, and a second observer on a moving cart sees the pair differently. What must the model now say about where things are, and for whom? | The pair's centres become points in `Space 3`; lab F and cart G are named frames. | Position vector, displacement, pair distance, and velocity per frame. | Pair P's distance can be confused with pair Q's, and bare frame vectors accept transport laws that are wrong for the vector's role. | Space Stages 0–4. |

The remaining one-dimensional, one-observer assumption is gone. The no-dissipation
assumption remains for L5.

## 4. Learning path

| # | Do | Checked by `HCP.L4_OutOfTheLine` anchor | Concept disclosed |
|---|---|---|---|
| 1 | Put the two centres in a `PairState3`; read position, displacement, and distance, then try the two kind collisions. | `points_vectors_and_distances` | Position and displacement are distinct vector kinds; distance and the length of displacement are distinct scalar kinds, even where magnitudes agree. HCP's body and separation bearers retain nominal identity. |
| 2 | Attach the distance to the named pair, compare two states, and mix P with Q. | `whose_distance` | `distance` admits `DifferenceKind.ofScale`; same-name states have a typed change whose magnitude reads their own centres, while Q's separation cannot be added to P's. |
| 3 | Relate distance to displacement length and apply the triangle inequality to state points. | `distance_is_length` | `distanceQ_eq_lengthOf_displacementQ` and `distanceQ_triangle` operate directly on the pair state's centres. |
| 4 | Feed one state-derived bare frame vector to all three upstream transports and add the cart's origin velocity. | `bare_frames` | Both terms compile, but are physically wrong when the vector's role is displacement: bare `F.Vector` cannot select a transport law or distinguish displacement from velocity. |
| 5 | Use `KVector` for displacement and velocity; try the wrong boost and velocity-plus-force. | `kinded_frames` | Frame components enter through each frame's own `dispEquiv`; the observer-independence theorem verifies geometric transport. Boost-on-displacement and velocity-plus-force are pinned refusals. Average velocity is computed from two same-pair states and an elapsed duration. |
| 6 | State the cart-origin displacement law and try adding its frame velocity to the pair displacement. | `observer_motion` | `origin_displacement_eq` makes observer motion an attribute of the cart frame; the kinded displacement-plus-velocity sum is refused. |
| 7 | Map Space Stages 0–4 and exercise Stage 3's operator table. | `adoption_ladder` | `spanArea` and its magnitude law are accepted on a displacement from the state and a probe point; area × area is refused. Stage 4's boundary and API-map audits are the final rung. |

## 5. AI assistance contract

- Keep L4 independent: define local `PairId | P | Q` and `Body | A | B`.
- Preserve nominal identity: one name is one system; records under it are states,
  configurations, or rival estimates; distinct names are distinct systems.
- Use the exact `PairState3.com` fields for all accepted position, displacement,
  distance, velocity, and area forms.
- Keep the `distance` bearer pair-indexed in HCP; do not alter ForPhysLib's `distanceQ`.
- Reuse the Space and ReferenceFrame APIs, and pin each requested kind refusal.
- Label the accepted unkinded frame examples wrong; they do not encode physical role.
- Recap, rather than rewrite, Space Stages 0–4 and point to Stage 4 audits.
- Leave the no-dissipation assumption for L5.

## 6. Questions to ask the model so far

| Question | Check | What the verdict means |
|---|---|---|
| Where is body A in this state? | `points_vectors_and_distances` | `positionQ` reads the state's `com .A` point from the conventional origin, and `BodyOf π` retains the body's nominal pair identity. |
| Can position be added to displacement? | `points_vectors_and_distances` | No; the Space kind layer refuses the distinct vector roles. |
| Is distance interchangeable with displacement length? | `points_vectors_and_distances`, `distance_is_length` | No; their scalar magnitudes are related by a theorem, not kind identity. |
| Whose separation is this? | `whose_distance` | `SeparationOf π` retains the pair name erased by the upstream `distanceQ`. |
| Can the separation change between P states? | `whose_distance` | Yes; distance is ratio-scale and the difference magnitude is the later distance minus the earlier one, computed from each state's centres. |
| Can Q's distance be mixed with P's? | `whose_distance` | No; distinct pair identities yield distinct separation bearers. |
| Which frame law applies to a displacement? | `bare_frames`, `kinded_frames` | Bare `F.Vector` accepts all three; `KVector` allows geometric transport, proves observer independence, and refuses the boost law. |
| Where does the observer's velocity live? | `observer_motion` | On the cart frame context, and not as a summand of the pair displacement. |
| What does the adoption ladder contribute? | `adoption_ladder` | Stage 3 curates operators; Stage 4 audits the Space boundary and API map. |

## 7. System-context card

| Scope | System or component | Sort / status | L4 assumptions and attributes |
|---|---|---|---|
| System | Coupled pair P or Q | Nominal `PairId` | One name denotes one system; records under it can be different states, configurations, or rival estimates. P and Q are distinct systems. |
| State | Pair state | `PairState3 π` | Stores the centre-of-mass point of each body in `Space 3`. |
| Part | Body A or B | `BodyOf π` | Its position vector is read from the point in this state. |
| Attribute | A–B separation | `SeparationOf π` | `distance` in ℝ; its change is comparable between states of one pair. |
| Attribute | Pair displacement | `SeparationOf π` bearer | A vector from body B's centre to body A's centre, kind `displacement`. |
| Observer | Lab F or cart G | `ReferenceFrame 3` | The frame is part of the context; the cart's origin velocity and motion law are explicit. |
| Deferred assumption | No dissipation | L5 | Not changed by this spatial and observer refinement. |

## 8. Space adoption ladder

| Stage | File | What it contributes |
|---|---|---|
| 0 | `ForPhysLib/Kinds/Space.lean` | Kind vocabulary for length, distance, position vector, displacement, and area. |
| 1 | `ForPhysLib/Metrology/Space.lean` | Dimension pairings and the kind algebra. |
| 2 | `ForPhysLib/Kinded/Space.lean` | `positionQ`, `displacementQ`, `distanceQ`, and `lengthOf`. |
| 3 | `ForPhysLib/Operators/Space.lean` | The curated operator table: `spanArea` is accepted, area × area is not. |
| 4 | `ForPhysLib/Audits/Space.lean` and `Space.checked_by.yaml` | Boundary and API-map audits under build checks. |

The Stage-3 accepted form is
`spanArea v w : Quantity area ℝ`, with magnitude
`‖v.magnitude‖ * ‖w.magnitude‖`; the product of two areas has no registration. Stage 4
audits the authored boundary and ties the API map to its Lean declarations.
