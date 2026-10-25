---
hcp: 7
id: l6-requirements
persona: "PhysLib contributor"
layer: PKC
pull: "The pair now has bodies, a coupling spring, and multiple records. What must hold, for which systems or objects?"
improvement: "State requirements over named sorts and particulars, and discharge them with proofs, referents, gates, and audited scope."
concepts:
  - informal: "the pair mass requirement quantifies over pairs"
    formal: "pairS, pairMassOf, pairMass_assembled, and the 3 + 5 = 8 spot check"
    where: "HCP.L6_Requirements#r1_pair_mass"
  - informal: "a whole-only frequency has no body-assembly license"
    formal: "pairNormalModeLicense and the absent-instance requirement"
    where: "HCP.L6_Requirements#r2_no_aggregation"
  - informal: "the rated spring extension is an empirical requirement on P"
    formal: "the datasheet referent, Bool gate, and two P-record spot checks"
    where: "HCP.L6_Requirements#r3_empirical"
  - informal: "a scope must name a sort or nominal object"
    formal: "the rejected bare-real object and non-sort pins"
    where: "HCP.L6_Requirements#invalid_scopes"
  - informal: "every produced model port is governed"
    formal: "the requirement survey, coverage census, and clean gate"
    where: "HCP.L6_Requirements#requirement_census"
artifacts: ['Lean lesson HCP.L6_Requirements', 'L6 system-context card']
tools: ['lake build HCP', 'python3 HCP/check-hcp.py']
exercises: 5
disclosure: ['scope a pair-mass theorem over pairS', 'state the absence of pair-frequency aggregation', 'gate an empirical limit over P', 'pin invalid scope declarations', 'census and gate requirement coverage']
owner: 'PKC methodology lead'
state:
  completed: []
---

# L6 — What must hold

## Synopsis

### Purpose

State what must hold of the refined context as checked requirements: R1 and R2 over the sort "coupled pair", and R3 over every state of pair P. Each requirement names its boundary, port and scope; the census reports every output that no requirement governs.

### PKC vocabulary in scope

New at this step:
- `Provenance.Contract` — a declared model boundary with its members and ports.
- `Provenance.Requirement` (`statement`, `governs`, `port`, `scope`, `witness`, `absent`, `gate`, `referents`, `spotChecks`) — a requirement on a boundary.
- `RequirementKind.provable`, `RequirementKind.empirical` — discharged by a proof, or decided by a gate.
- `RequirementScope.sort`, `RequirementScope.objects` — what a requirement quantifies over.
- `NodeId.result`, `PortDir.output` — which port a requirement governs.
- `#kind_requirement_clean` — the gate that fails on any ungoverned or unchecked output.
- `@[kindReferent]`, `@[kindCounterexample]` — mark an empirical referent and a refuting witness.

Carried from earlier steps: `Composite`, `Decomposition`, `Assembles`, `assemble`, `IndividualQuantity`, `Quantity`, `KindOfProperty`, `SortOfSystem`, `Sorted` (`sortOf`), `Designated`, `massK`, `displacementK`, `angularFrequencyK`.

### Verifiable properties

- R1: every pair's mass is the assembly of its bodies' masses (theorem) `HCP.L6_Requirements#r1_pair_mass`.
- R2: no licence assembles a pair's normal-mode frequency from its bodies (theorem) `HCP.L6_Requirements#r2_no_aggregation`.
- R3: the coupling spring's extension is bounded in every state of pair P, decided by a gate (gate) `HCP.L6_Requirements#r3_empirical`.
- Scopes naming a bare number or a non-sort are rejected (refused) `HCP.L6_Requirements#invalid_scopes`.
- The requirement census is pinned and clean (census) `HCP.L6_Requirements#requirement_census`.
- A P-only requirement on a generic accessor reports Q as ungoverned (census) `HCP.L6_Requirements#scope_gap`.

### Errors prevented

- Unstatable scope: "every pair" or "pair P" with no named sort or particular to quantify over (`HCP.L6_Requirements#invalid_scopes`).
- Over-claimed coverage: a requirement about P counted as governing Q's output (`HCP.L6_Requirements#scope_gap`).
- Ungoverned output: a model output that no requirement covers passes unnoticed (`HCP.L6_Requirements#requirement_census`).

## 1. Persona

You are a PhysLib contributor: a physicist who writes Lean in PhysLib. You know Lean and
PhysLib and trust `Dimension` and `WithDim`; the earlier HCP levels have named the pair
sort, its particulars, and its parts.

## 2. Pull

The pair now has two bodies, a coupling spring, and multiple records. What must hold, for
which systems or objects? A requirement must state its quantification scope, and that scope
is writable only because the previous levels named sorts and nominal particulars.

One name is one system: records named P are states, configurations, or rival estimates of
that same pair and can be compared; Q is a distinct pair. An object-scoped requirement on P
governs every state or record of P, not just the two records used for a spot check.

## Risks at this step

- **Unstatable scope.** A requirement about every coupled pair needs the pair sort, and one about every state of P needs the nominal pair P; without those named systems, it has nowhere to range. `HCP.L6_Requirements#invalid_scopes` pins the rejection of a bare real and a name that is not a sort.

## 3. Small rigorous improvement

| Question | Context change | Attribute change | Risk shown | PhysLib stage |
|---|---|---|---|---|
| The pair now has bodies, a coupling spring, and multiple records. What must hold, for which systems or objects? | Give the nominal pair IDs P and Q a `Sorted` instance into `pairS`, and designate bodies and the coupling spring. | Pair mass, normal-mode frequency, coupling-spring extension, requirement scope, referent, and gate. | An unscoped claim cannot say whether it applies to every pair or to every state of P; a bare real and a non-sort are rejected as scopes. | Stage 4 requirements and audits. |

## 4. Learning path

| # | Do | Checked by `HCP.L6_Requirements` anchor | Concept disclosed |
|---|---|---|---|
| 1 | Assemble the two body masses into a pair mass and state R1 over `pairS`. | `r1_pair_mass` | The theorem reads the pair's own body quantities; the executable check evaluates 3 + 5 = 8. |
| 2 | State R2 as the absence of the pair-sort assembly license for normal-mode frequency. | `r2_no_aggregation` | A whole-only frequency does not inherit the body-mass aggregation license. |
| 3 | Scope the coupling-spring rating to P and compare two P records against a marked datasheet limit. | `r3_empirical` | The empirical requirement is gated by a Bool that names the referent and is spot-checked on two states of P. |
| 4 | Replace P with a bare real, then replace `pairS` with a declaration that is not a sort. | `invalid_scopes` | Object scope requires a `Sorted` instance; sort scope requires a `SortOfSystem`. |
| 5 | Survey requirements, census every produced model port, and run the clean gate. | `requirement_census` | Every produced port in these boundaries is governed; the invalid-scope twins are pinned counterexamples. |

Worksheet: `HCP/Worksheets/L6_Requirements.lean` · Solution: `HCP/L6_Requirements.lean`

## 5. AI assistance contract

- Keep L6 independent, with local nominal `PairId | P | Q`, `Body | A | B`, and the
  coupling spring.
- Preserve nominal identity: one pair name is one system; same-name records are comparable
  states or configurations; P and Q are distinct.
- Keep pair mass on the pair whole and body masses on their body-in-pair bearers.
- Use `.sort ``pairS` for R1 and `.objects [``PairId.P]` for the empirical R3.
- Mark the rated limit as an external referent; make the gate mention it and evaluate it on
  two states of P.
- Pin both invalid scopes and run the requirement survey, coverage census, and clean gate.
- Do not import the Tutorial worked example. The full worked example is
  `examples/Tutorial/HarmonicOscillatorRequirements.lean`.
- Leave optional `.decided` scope out of this lesson. If used, provide a `deciderProof`
  theorem proving that its decider returns `true` for every result of the governed member;
  without that proof the census reports the port unchecked.

## 6. Questions to ask the model so far

| Question | Check | What the verdict means |
|---|---|---|
| What does R1 quantify over? | `r1_pair_mass` | Every object of sort `pairS`; its theorem relates the assembled pair mass to the masses of the two bodies. |
| Does normal-mode frequency sum over the bodies? | `r2_no_aggregation` | No `Assembles pairS normalModeK` instance exists. |
| What does the spring rating govern? | `r3_empirical` | Every state or record of P; the gate checks two such records against the same datasheet limit. |
| Can a bare real or a non-sort name state the scope? | `invalid_scopes` | No; the object must have a `Sorted` instance and a sort must be a `SortOfSystem`. |
| Are all produced ports governed? | `requirement_census` | Yes; the census is clean and the command enforces that invariant. |

## 7. System-context card

| Scope | System or component | Sort / status | L6 requirements |
|---|---|---|---|
| System | Coupled pair P or Q | Nominal `PairId`, sorted into `pairS` | One name denotes one pair; same-name records are states or configurations, and Q differs from P. |
| Part | Body A or B | Designated body | Each body has its own mass bearer within the named pair. |
| Part | Coupling spring kC | Designated spring | Its extension is state-indexed and checked against an external rated limit. |
| Requirement | Pair mass R1 | `.sort ``pairS` | Provable from the pair's two body masses; spot check gives 8 from 3 and 5. |
| Requirement | Normal-mode frequency R2 | `.sort ``pairS` | Provable negative: no aggregation license for `normalModeK`. |
| Requirement | Spring range R3 | `.objects [``PairId.P]` | Empirical, gated by the datasheet referent; applies to every P state or record. |
| Audit | Requirement census | Stage 4 | The valid requirements govern every produced model port; invalid-scope twins are counterexamples. |

## 8. Requirement scope

The full worked requirements example is `examples/Tutorial/HarmonicOscillatorRequirements.lean`;
L6 mirrors its Provenance boundaries, witnesses, referents, gates, surveys, and coverage
commands without importing the Tutorial file. The census infers a result port's object
domain from its member's type: R3 covers a P-only result, but leaves Q ungoverned on a
generic pair boundary. An unresolved bearer is an unchecked violation unless exempted. A
`.sort` scope needs an indexed result whose object type has a `Sorted` instance: R1 and R2's
results are borne by the pair whole, and the instance above maps the whole to `pairS` and
each part to its own sort, so the census checks their scope. An object of another sort is
reported ungoverned. A `.decided` scope is checked against a `deciderProof` theorem proving
its decider returns `true` for every result of the governed member; without that proof the
census reports the port unchecked.
