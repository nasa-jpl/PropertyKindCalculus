---
hcp: 2
id: l1-two-bodies
persona: 'PhysLib contributor'
layer: PKC
pull: 'Two bodies are now in view: whose mass is this, and can body B contaminate body A''s oscillator?'
improvement: 'Introduce one sort, two designated bodies, and indexed quantities so the bearer is checked by the type.'
concepts:
  - informal: 'two point-mass bodies with separate wall springs'
    formal: 'Body A and Body B share bodyS; Spring kA and kB are their wall springs'
    where: '§7 System-context card; HCP.L1_TwoBodies'
  - informal: 'the same kinded values with no bearer'
    formal: 'Quantity springConstantK ℝ / Quantity massK ℝ'
    where: 'HCP.L1_TwoBodies#kinded_bearer_free_cross_body'
  - informal: 'a quantity about one particular body'
    formal: 'IndividualQuantity b massK ℝ indexes b'
    where: 'HCP.L1_TwoBodies#bearer_indexed_quantities'
  - informal: 'a catalogue entry shared by a sort'
    formal: 'dedicatedFor uses Sorted.sortOf rather than the object index'
    where: 'HCP.L1_TwoBodies#bearer_indexed_quantities'
artifacts: ['Lean lesson HCP.L1_TwoBodies', 'L1 system-context card']
tools: ['lake build HCP', 'python3 HCP/check-hcp.py']
exercises: 7
disclosure: ['cross-body bare-real substitution', 'bearer-free kinded quotient', 'sort and designation', 'per-body quantities', 'shared dedicated kind', 'object-index refusals', 'nominal object has no sort']
owner: 'PKC methodology lead'
state:
  completed: []
---

# L1 — Two bodies

## 1. Persona

You are a PhysLib contributor: a physicist who writes Lean in PhysLib. You know Lean and
PhysLib and trust `Dimension` and `WithDim`; L0 has already shown what those dimensions
can and cannot distinguish.

## 2. Pull

There are two bodies now — whose mass is this? The bare-real oscillator lets body B's mass
enter body A's frequency. A kinded value still has no bearer, so the same cross-body
quotient remains expressible. L1 puts the object index and designation into the model.

## 3. Small rigorous improvement

| Question | Context change | Attribute change | Risk shown | PhysLib stage |
|---|---|---|---|---|
| There are two bodies now — whose mass is this? | Two particulars, A and B, of one sort (point mass), each on its own wall spring, kA or kB. They remain uncoupled; the coupling spring kC and the pair as a system belong to L2. | No new kinds: the same mass and spring-constant kinds, now per body or spring. | R1 cross-system contamination (B's mass in A's formula); R5 false identity (a constant designation). | Stage 2: the kinded form carries its bearer. |

L0's one-body, one-spring assumptions refine to two bodies and two separate wall springs.
The bodies do not interact in this lesson; L2 revisits that assumption when it introduces
the coupling spring and the pair as a system.

## 4. Learning path

| # | Do | Checked by `HCP.L1_TwoBodies` anchor | Concept disclosed |
|---|---|---|---|
| 1 | Put body B's mass in body A's bare-real frequency radicand. | `HCP.L1_TwoBodies#bare_real_cross_body` | The cross-body expression elaborates as `ℝ`. |
| 2 | Form the same spring-constant/mass quotient from kinded, bearer-free values. | `HCP.L1_TwoBodies#kinded_bearer_free_cross_body` | The registered `k/m` edge accepts values from different oscillators. |
| 3 | Declare Body A/B and spring kA/kB, give each one sort, and compare the bodies' sorts. | `HCP.L1_TwoBodies#context_and_sort` | Two particulars instantiate one sort. |
| 4 | Give bodies distinct designations and prove a constant designation is not injective. | `HCP.L1_TwoBodies#designation` | A valid `Designated` instance cannot collapse distinct bodies. |
| 5 | Index mass and stiffness by their bearers; compare the mass catalogue entries. | `HCP.L1_TwoBodies#bearer_indexed_quantities` | The dedicated mass kind is shared, while quantities keep the body index. |
| 6 | Try B's mass where A's is expected and try to add the two body-indexed masses. | `HCP.L1_TwoBodies#refused_cross_body_mass` | Both substitutions are refused by the object index. Total mass is meaningful, but whose total requires a whole; that is L2. |
| 7 | Ask for the mass kind dedicated to a nominal object with no sort. | `HCP.L1_TwoBodies#refused_unsorted_object` | A nominal `Object` cannot supply the `Sorted` instance required by `dedicatedFor`. |

## 5. AI assistance contract

- Keep the contributor's vocabulary: body, mass, spring, and bearer.
- Quote each Lean check from its anchored L1 region; do not redefine PhysLib or PKC declarations.
- Distinguish a bearer-free `Quantity` from an `IndividualQuantity` indexed by a body.
- Treat the guarded elaboration messages as evidence only for the refusals they actually show.

## 6. Questions to ask the model so far

| Question | Check | What the verdict means |
|---|---|---|
| Can B's mass enter A's bare-real frequency? | `bare_real_cross_body` | Yes; the expression has type `ℝ`. |
| Does kinding alone prevent the cross-body quotient? | `kinded_bearer_free_cross_body` | No; the registered `springConstantK / massK` edge accepts the two `Quantity` values. |
| Are A and B different sorts? | `context_and_sort` | No; both are point masses. |
| Can both bodies be given one constant designation? | `designation` | The function is not injective, so it cannot witness `Designated Body`. |
| Does the object index keep their masses apart? | `refused_cross_body_mass` | Yes; assignment and addition across A and B are refused. |
| Can a nominal name reach a dedicated kind? | `refused_unsorted_object` | Not without a sort; the nominal `Object` has no `Sorted` instance. |

## 7. System-context card

| Scope | System or component | Sort / status | L1 assumptions and attributes |
|---|---|---|---|
| System | Two separate oscillators | Two point-mass spring systems, not yet one pair system | Bodies do not interact; L2 revisits this assumption. No coupling spring kC yet. |
| Inside | Body A | Point mass | Homogeneous, rigid, and point-like as in L0; mass mA. |
| Inside | Body B | Point mass | Homogeneous, rigid, and point-like as in L0; mass mB. |
| Inside | Wall spring kA | Linear spring | One ideal, massless spring assigned to body A; stiffness kA. |
| Inside | Wall spring kB | Linear spring | One ideal, massless spring assigned to body B; stiffness kB. |
| Outside | Walls | Fixed, infinitely massive walls | Each spring has its own fixed-wall boundary. |
| Outside | Lines | One-dimensional lines of motion | Each body remains constrained to its oscillator's line. |

The Lean model has no coupling spring and does not model the two bodies as a whole. The
`wallSpring : Body → Spring` map pairs each body with its own spring; the inverse lookup
used by `stiffnessOf` makes that association explicit.
