# The SysML v2 PKC DSL and the Lean ⇄ SysML interchange

`PKC.sysml` is the PropertyKindCalculus as a **SysML v2 language extension**: PKC's own
vocabulary — kinds of property with a scale type and an examination principle, explicit
specialization, the authored kind algebra, metrology modules with kind-typed ports and a
provenance hypergraph, relations, requirements, and the computational tape graph a module is
realized on — as SysML v2 semantic metadata (§7.27), so that a model is written with PKC
keywords and nothing of the Quantities and Units domain library.

```sysml
package Oscillator {
    private import PKC::*; private import PKC::Kinds::*;
    private import PKC::Modules::*; private import PKC::Tape::*;

    #principle transverseExtent { :>> id = "transverse-extent"; }
    #kind length { :>> id default = "length"; :>> scale default = ScaleType::ratio;
        attribute dimL :> dimension { :>> base default = "length"; :>> num default = 1; } }
    #kind width :> length { :>> id default = "width"; :>> principle default = transverseExtent;
        @Checked { decl = "PropertyKindCalculus.Iso80000.Part3.Edge.width_length"; } }
    #kind mass { :>> id default = "mass"; :>> scale default = ScaleType::ratio; }
    #kind stiffness { :>> id default = "mass × angular frequency²"; :>> scale default = ScaleType::ratio; }
    #kind omega2 { :>> id default = "angular frequency squared"; :>> scale default = ScaleType::ratio; }

    #quotient connection omegaSq : KindQuotient
        connect (numerator ::> stiffness, denominator ::> mass, result ::> omega2) { :>> table = true; }

    #module oscillator : Module {
        :>> name = "oscillator";
        port m : KindPort { :>> node = "m"; :>> kind = mass; :>> dir = PortDir::input; }
        port k : KindPort { :>> node = "k"; :>> kind = stiffness; :>> dir = PortDir::param; }
        port out : KindPort { :>> node = "result"; :>> kind = omega2; :>> dir = PortDir::output; }
        attribute occ0 :> occurrences { :>> family = EdgeFamily::quotient;
            attribute opK :> operands { :>> node = "k"; :>> kind = stiffness; }
            attribute opM :> operands { :>> node = "m"; :>> kind = mass; }
            :>> result = "result"; :>> resultKind = omega2; :>> site = "Attempt4Pkc.omegaSq"; }
        :>> exits = "result";
    }
    #tape oscillatorTape : TapeGraph {
        attribute v0 :> vertices { :>> name = "k"; }
        attribute v1 :> vertices { :>> name = "m"; }
        attribute v2 :> vertices { :>> name = "div"; :>> parents = (0, 1); }
    }
    #match connection realization : Match connect (module ::> oscillator, tape ::> oscillatorTape) {
        attribute cK :> components { :>> node = "k"; :>> vertices = 0; }
        attribute cM :> components { :>> node = "m"; :>> vertices = 1; }
        attribute cR :> components { :>> node = "result"; :>> vertices = 2; }
        attribute r0 :> realized { :>> occ = 0; }
        attribute :>> carrier { :>> rung = "tape"; :>> platform = "cuda"; }
    }
}
```

A complete model is in `examples/HarmonicOscillator.sysml`. Both files validate with
OpenSysML: `sysml -validate sysml/PKC.sysml sysml/examples/HarmonicOscillator.sysml`.

## The three packages

| Package | Keywords | Lean counterpart |
|---|---|---|
| `PKC::Kinds` | `#kind` (`:>` is specialization), `#principle`, `#dedicated`, `#unit`, and the kind-algebra connections `#product` `#quotient` `#reciprocal` `#power` `#transcendental` `#reference` `#difference` | `KindOfProperty`, `ScaleType`, `ExaminationPrinciple`, `Specializes`, `ProductKind`…/`KindMul`/`KindDiv`, `DedicatedKind`, `MetrologicalUnit`; the `Dimension` layer's vector and the ISO 80000 catalogue locators as metadata |
| `PKC::Modules` | `#module` with `port … : KindPort`, `intros`, `occurrences`, `aggregations`; `#relation`; `#req` | `Provenance.Contract`, `Provenance` (the hypergraph), `Provenance.Relation` with its `RelationLicense`s, `Provenance.Requirement` |
| `PKC::Tape` | `#tape`, `#match` with `components`, `realized`, `carrier` | `Paradigm.TapeGraph`, `Paradigm.Match`; the carrier rung and platform TorchLean compiles for |

Two annotations cite Lean: `@Source { decl = … }` names the declaration an element was
harvested from, `@Checked { decl = … }` a kernel-checked declaration backing it. A citation is
verified on import (the declaration must exist in the importing environment); it is never
turned into a proof. What SysML cannot express — carrier parametricity, the theorems, the
weak bisimulation between a module's hypergraph and its tape — stays in Lean and is *cited*.

## The interchange

The pivot is `PropertyKindCalculus.Interchange.PkcModel` (library `Interchange`,
`interchange/`): one plain record for the three layers, with a derived JSON form.

```
Lean environment ──Harvest──▶ PkcModel ──EmitSysml──▶ Model.sysml
                                  ▲                        │  sysml -convert api-json
                                  │                        ▼
                      ApiJson ◀── OMG API element list ◀───┘
                        │
                        └──EmitLean──▶ Generated/Model.lean ──lake──▶ kernel verdict
```

* **Lean → SysML.** `scripts/emit-sysml.lean` harvests the ISO 80000-3 catalogue and the
  harmonic-oscillator requirements tutorial into `.lake/build/sysml/*.sysml` (and `*.pkc.json`):
  `lake build Interchange Iso80000 Tutorial && lake env lean scripts/emit-sysml.lean`.
* **SysML → Lean.** `scripts/ingest-sysml.sh model.sysml …` converts with OpenSysML, reads the
  element list, writes `.lake/build/sysml/Generated/<Package>.lean` — `KindOfProperty`
  definitions, an `Edge` inductive, `KindMul`/`KindDiv` instances and `ProductKind`/`QuotientKind`
  theorems (discharged by the calculus's smart constructors, so the ratio-scale gate is checked),
  `Provenance.Contract`/`Relation`/`Requirement` values, tapes with their build order decided,
  and for a module that states its hypergraph the `Provenance` graph with `wellFormed` and
  `Contract.agrees` decided, plus `Match.accepts` for each match against it — and has the
  kernel check it. A citation the environment cannot honour (a missing declaration, or data
  cited as `@Checked`) fails the ingest.
* **Round trip.** `scripts/roundtrip-sysml.sh` checks, by content,
  `ApiJson.read (api-json (emit (harvest s))) = harvest s` for both scopes. A declaration
  the harvester skipped (a value it could not evaluate, a contract or hypergraph the assembly
  refused, a unit of an out-of-scope kind) is reported on stderr by both scripts, so a
  partial harvest that round-trips is still visible as partial.
  `lake build Tests` pins the JSON round trip, the citations and the reader's conventions
  (`tests/PropertyKindCalculus/Tests/Interchange.lean`).

Both scripts take `SYSML=/path/to/sysml` when OpenSysML's binary is not on `PATH`.

## Conventions the emitter follows (and the reader relies on)

* A kind's values are bound with `default =`: `#kind width :> length` *subsets* `length` and
  would otherwise inherit its fixed `id`. A species written without a `scale` or a dimension
  vector inherits its genus's through the subsetting.
* Nested records (dimension exponents, operands, occurrences, vertices, licenses, …) are
  subsetting usages — `attribute x :> operands { … }` — in order; the notation has no
  constructor expression for a data type.
* Keyworded connections carry the `connection` keyword: `#product connection e : KindProduct
  connect (left ::> a, right ::> b, result ::> c)`.
* Names that are reserved words of the notation are quoted (`'derived'`, `'port'`).
