# The RF/AC annex — the green-field member of the second campaign directory

The promotion of Exhibit E problem 5 to ladder form (see
[`PLAN.md`](../../PLAN.md)): **PhysLib has no AC or RF physics**, so unlike
`Kinematics/` there is no upstream module to mirror and no `checked_by` delta to
propose — the annex *is* the proposed capability, in the same Stage 0–4 discipline
the mirrored directories use: impedance at the complex carrier, the AC power lattice
with its refused join, and the dB link budget on `LevelKind`.

## The files

| file | ladder rung | what it holds |
|---|---|---|
| `Kinds.lean` | Stage 0 | 17 kinds — **all catalogue lookups, zero mints**; the densest collisions in the campaign (three kinds at the ohm's dimension counting the catalogue's own 6-46 = 6-51.3 identification, six at the watt, two at dimension one, each phasor at its base dimension), every separation a `decide`; the five-species power lattice with **no join** |
| `Metrology.lean` | Stage 1 | 17 pairings; Stage 0 proved to be the catalogue by `decide`, dimensions by `rfl`; ten edge laws — **five consumed from the catalogue's own `DefiningRelations`** (Ohm, the reciprocals, `P = U·I`, the power factor), five authored (the phasor spellings); coverage pinned clean |
| `Circuits.lean` | Stage 2/3 | four table registrations on Stage-1 laws; `Z = Û/Î` and `S̲ = Û·Î*` elaborating through the table at the complex carrier (MR14), conjugation as a kind-preserving crossing; the **refused join** (`P + Q` unwritable) beside the licensed quadrature `S = √(P² + Q²)` and the 6-61 residual |
| `Levels.lean` | the link budget | dBm/dBW rooted at the catalogue's 6-45, dBV at 6-11.3; the reference as kind identity (`decide`), gains shared across references (`rfl`) but not across roles (10 ≠ 20, by kind); the worked budget exact at `Int`; the level sum unwritable |
| `Audits.lean` | Stage 4 | the 5-site boundary audit pinned; silent clean/ratchet/dimensional gates over the annex |

## The cost line

| | count | artifact |
|---|---|---|
| kinds | 17 — all verbatim IEC 80000-6 lookups, **0 mints** (the Kinematics chain minted 8; the annex's vocabulary is the standard's home ground — that asymmetry is the finding) | `Kinds.lean`; the `decide` block in `Metrology.lean` |
| dimensional pairings | 17, with the campaign's densest collisions visible: 2 kinds at the ohm (+ the catalogue's own 6-46 = 6-51.3 identification, proved), 2 at the siemens, 6 at the watt, 2 at dimension one, 2 phasor/base pairs | `Metrology.lean` |
| kind edges | 10 — 5 consumed from `Part6.DefiningRelations` (the proof *is* the catalogue's theorem), 5 authored phasor laws; 4 table-registered in Stage 3 | the coverage pin; the `KindDiv`/`KindMul` instances |
| join entries | **0** — `P + Q` refused while `MutuallyComparable` holds; the licensed combination is the quadrature crossing. The pilot's energy family registers its join: same table, opposite verdict, both pinned | `Circuits.lean` |
| level kinds | 3 (dBm, dBW, dBV) + their gain kinds; the level sum structurally unavailable, the budget exact at `Int` | `Levels.lean` |
| boundary sites | 5 — 2 ingest, 3 crossings, 0 raw mints | the pinned `#kind_boundary_audit` in `Audits.lean` |
| lines | 650 total, of which 259 are code; **no upstream lines exist** to compare | `wc -l` |
| proof debt | 0 `sorry`; the layer is `decide`/`rfl`/construction throughout | `#print axioms` |

## The findings

1. **Zero mints.** Every kind the annex speaks — phasors included — is a verbatim
   IEC 80000-6 item, examination principles and all. The mirrored directories mint
   where the standard stops (frame-, gauge-, variational-relative readings); the
   annex shows the complement: where practice is the standard's home ground, Stage 0
   is pure lookup.
2. **The defining relations ship with the standard too.** Half the kind algebra is
   consumed from the catalogue's `DefiningRelations` rather than authored — the
   annex's Stage 1 is the first in the campaign where the *edges* are lookups.
3. **The catalogue identifies 6-46 with 6-51.3** — resistance and the real part of
   impedance are one kind by the standard's own id; the collision that is not one,
   proved beside eleven that are.
4. **The refused join is curation the domain dictates.** `P + Q` never elaborates
   (no `KindJoin` over the power lattice) while `S = √(P² + Q²)` is one attested
   crossing — and the pilot's `T + V` registers its join in the same calculus. The
   table says yes and no on the same page.
5. **The dB layer's invariants are kind identity.** dBm ≠ dBW because the reference
   is part of the kind; their gains are *one* kind because the reference cancels in
   differences; a power gain and a root-power gain stay two kinds because the 10/20
   factor is examination, not convention — and 30 dBm + 30 dBm is not writable at
   all.
