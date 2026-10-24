---
hcp: 4
id: l3-the-body-opens
persona: "PhysLib contributor"
layer: PKC
pull: "Body A wobbles instead of sliding along the line. Why, and what must the model now say about the body?"
improvement: "Open body A into mass-bearing halves and make centre-of-mass and rotational statements respect composition and reference frames."
concepts:
  - informal: "body A is a rigid composite with two halves"
    formal: "HalfOf .P .A, OpenBody .P .A, massOf, and bodyMass"
    where: "§7 System-context card; HCP.L3_TheBodyOpens#opened_body"
  - informal: "centre of mass is a weighted mean"
    formal: "centerOfMassCarving weights each half by OpenBody.mass; centerOfMass_eq and the 3/5-at-0/10 example"
    where: "HCP.L3_TheBodyOpens#center_of_mass_mean"
  - informal: "angular velocity is intensive and frame-specific"
    formal: "omegaOfHalf_intensive; bodyOmega versus labOmega in rotationalContraction"
    where: "HCP.L3_TheBodyOpens#angular_velocity_intensive; HCP.L3_TheBodyOpens#framed_rotational_energy"
  - informal: "homogeneity is a special case"
    formal: "solidSphere_inertiaTensor"
    where: "HCP.L3_TheBodyOpens#solid_sphere"
artifacts: ['Lean lesson HCP.L3_TheBodyOpens', 'L3 system-context card']
tools: ['lake build HCP', 'python3 HCP/check-hcp.py']
exercises: 7
disclosure: ['open body A into nominally indexed halves', 'use a weighted mean for centre of mass', 'expose the massless convention', 'treat angular velocity as intensive', 'show the accepted upstream frame mistake', 'enforce frames with PKC', 'recover the homogeneous solid sphere']
owner: 'PKC methodology lead'
state:
  completed: []
---

# L3 — The body opens up

## 1. Persona

You are a PhysLib contributor: a physicist who writes Lean in PhysLib. You know Lean and
PhysLib and trust `Dimension` and `WithDim`; L0–L2 have established kinds, bearers, and
sort-specific assembly licenses.

## 2. Pull

Body A wobbles instead of sliding along the line. Why, and what must the model now say
about the body? Its centre of mass is off the springs' line of action, so the force misses
the centre of mass, produces a torque, and rotates the body. Body A of pair P therefore
stops being a point mass. It opens into left and right halves, acquires a mass distribution
and inertia tensor, and needs a body-fixed frame beside the lab frame.

One name remains one system. Records under that name are its states at different times,
configurations, or rival estimates of it—comparing them is the point. Distinct names are
distinct systems. Thus `HalfOf .P .A` keeps body A's halves shared across descriptions of
pair P, while a half of pair Q has another bearer type.

## Risks at this step

- **Wrong carving.** For body A of pair P, counting a half twice or leaving one out changes the whole mass; the pinned decomposition gives one slot to each half and proves the total at `HCP.L3_TheBodyOpens#opened_body`.
- **Weighted mean, not sum.** The centre of mass uses each half's mass and position, while both halves share the same angular velocity; the pinned checks are `HCP.L3_TheBodyOpens#center_of_mass_mean` and `HCP.L3_TheBodyOpens#angular_velocity_intensive`.
- **Degenerate whole and frame.** A massless body has no physical centre of mass, and lab-frame angular velocity is not the body-frame input to rotational energy; the checks are `HCP.L3_TheBodyOpens#massless_center_of_mass`, `HCP.L3_TheBodyOpens#bare_frame_mismatch`, and `HCP.L3_TheBodyOpens#framed_rotational_energy`.

**Further reading**
- `Exhibits/Composition`, findings 2 and 5.

## 3. Small rigorous improvement

| Question | Context change | Attribute change | Risk shown | PhysLib stage |
|---|---|---|---|---|
| Body A wobbles instead of sliding along the line. Why, and what must the model now say about the body? | Body A of pair P becomes a rigid composite carved into left and right halves; a body-fixed frame appears beside the lab frame. | Per-half mass and position, centre of mass, inertia tensor, and body- versus lab-frame angular velocity. | Counting the wrong halves changes total mass; angular velocity is intensive; a massless body has no physical centre of mass; lab-frame angular velocity does not match the body-frame energy input. | Stages 2–3 on rigid bodies; proved solid-sphere inertia theorem. |

The L2 on-axis point-mass assumption has fallen. L4 revisits the remaining assumption of
motion along one line seen by one observer.

## 4. Learning path

| # | Do | Checked by `HCP.L3_TheBodyOpens` anchor | Concept disclosed |
|---|---|---|---|
| 1 | Open body A into left and right halves, index them by pair and body identity, and assemble their masses. | `opened_body` | `HalfOf .P .A` names the bearers; mass assembles to the rigid-body whole, while P and Q remain distinct systems. |
| 2 | Weight the half positions by this state's half masses, then try to assemble positions by addition. | `center_of_mass_mean` | `centerOfMass_eq` uses the `OpenBody.mass` and `.position` fields; masses 3 and 5 at positions 0 and 10 give 25/4, not the unit-weight midpoint 5. `rigidBodyS` has no displacement assembly license. |
| 3 | Inspect the massless whole and the nonzero-total condition on a weighted carving. | `massless_center_of_mass` | PhysLib reports the origin for zero mass; the license is hypothesis `h`, which a massless state cannot satisfy to build the carving. |
| 4 | Check angular velocity over halves and try to assemble it. | `angular_velocity_intensive` | The halves share ω; adding their angular velocities would double it, so no license exists. |
| 5 | Pass lab-frame angular velocity to upstream rotational kinetic energy. | `bare_frame_mismatch` | The bare expression type-checks even though the inertia tensor is body-fixed, so the accepted term is physically wrong. |
| 6 | Apply PKC's frame-indexed contraction to lab and body angular velocities. | `framed_rotational_energy` | The lab-frame term is refused, the body-frame term is accepted, and the accepted contraction agrees with PhysLib energy. |
| 7 | Specialize the old homogeneity assumption to a solid sphere. | `solid_sphere` | The proved inertia tensor is `(2/5) m R² · 1`; upstream records the target as `informal_lemma` `CM-RB-sphereI`. |

## 5. AI assistance contract

- Define L3-local `PairId` and `Body`: the preceding lesson modules are independent rather
  than importing one another.
- Reuse the ForPhysLib findings directly when their upstream bearers already express the
  claim; restate only the HCP-specific half bearers and the refused assembly probes.
- Preserve nominal identity: same-name records share bearers, while P and Q do not.
- Treat `Assembles` as an explicit physical license, not a generic arithmetic operation.
- Make the weighted-mean license the state's nonzero total mass; do not substitute unit weights.
- Keep the body- and lab-frame indices visible in rotational expressions.
- Label the accepted upstream lab-ω expression physically wrong even though Lean accepts it.
- Leave the one-dimensional, one-observer assumption for L4.

## 6. Questions to ask the model so far

| Question | Check | What the verdict means |
|---|---|---|
| What bears the mass of body A's left half? | `opened_body` | `Composite.part (HalfOf .P .A)` bears it; the body whole bears the assembled total. |
| Can another record of body A in pair P use the same bearer? | `opened_body` | Yes; it is another state, configuration, or estimate of the named system. |
| Can pair Q's left-half mass be mixed with pair P's? | `opened_body` | No; nominal pair identities produce distinct bearer types. |
| How does this state's centre of mass depend on its halves? | `center_of_mass_mean` | `centerOfMassCarving` uses the actual half masses; 3 at 0 and 5 at 10 yield 25/4 rather than 5. Position addition is unlicensed. |
| What happens when total mass is zero? | `massless_center_of_mass` | PhysLib returns the origin by convention, but hypothesis `h` fails, so the state cannot construct a weighted carving. |
| Does angular velocity add over a carving? | `angular_velocity_intensive` | No; it is intensive, and the attempted assembly is refused. |
| Can the body inertia tensor contract with lab-frame ω? | `bare_frame_mismatch`, `framed_rotational_energy` | The bare PhysLib API accepts it, but the PKC frame index refuses it. |
| Where does the homogeneous-body assumption survive? | `solid_sphere` | As the solid-sphere theorem `(2/5) m R² · 1`, ready to contribute upstream. |

## 7. System-context card

| Scope | System or component | Sort / status | L3 assumptions and attributes |
|---|---|---|---|
| System | Coupled pair P | Nominal `PairId.P` | The L2 coupled pair remains the named system; records under P may describe different states, configurations, or estimates. |
| Part | Body A | Rigid body in pair P | No longer point-like or homogeneous; carved into left and right halves with per-half mass and position. |
| Part | Left half of A | `HalfOf .P .A` | Mass-bearing rigid-body part, designated “left half.” |
| Part | Right half of A | `HalfOf .P .A` | Mass-bearing rigid-body part, designated “right half.” |
| Attribute | Centre of mass | Weighted mean | Uses each state's half masses and positions; defined only under nonzero-total hypothesis `h`. Masses 3 and 5 at positions 0 and 10 give 25/4. An off-axis value makes the spring force produce torque. |
| Attribute | Inertia tensor | Body-fixed tensor | The union theorem adds part tensors about a common origin; the solid sphere is the homogeneous special case. |
| Attribute | Angular velocity | Lab or body frame | Intensive over rigid halves; rotational contraction requires the body-frame value. |
| Outside / deferred | Observer and full 3-D motion | L4 | L3 introduces two frames but still defers the one-observer, one-line assumption to L4. |

The HCP bearer is narrower than the upstream `RigidBody` theorems: `HalfOf π b` adds
nominal pair-and-body identity. The mass total, state-dependent weighted mean, and refused
assembly probes are therefore stated over HCP bearers. The physical union, massless,
intensive-ω, frame-bridge, and solid-sphere results are reused directly from ForPhysLib.
