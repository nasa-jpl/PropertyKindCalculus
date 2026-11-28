package PKC {
    doc
    /*
     * The SysML v2 PropertyKindCalculus DSL — PKC's own vocabulary as a SysML v2
     * language extension (SysML v2 §7.27 semantic metadata), deliberately not built on
     * the Quantities and Units domain library: a kind of property is a first-class
     * element with a scale type and an examination principle, specialization and the
     * kind algebra are explicit relationships, and theorems are cited, never restated.
     *
     * Three layers mirror the Lean libraries: `Kinds` (the ontological spine and the
     * ISO 80000 catalogues), `Modules` (metrology modules — kind-typed ports, the
     * provenance hypergraph, relations, requirements) and `Tape` (the computational
     * tape graph and its match against the hypergraph). Every element may carry a
     * `@Checked` citation naming the Lean declaration whose kernel-checked type backs
     * it; the interchange verifies the citation when it imports the model.
     */
    private import ScalarValues::*;
    private import Metaobjects::SemanticMetadata;

    metadata def Checked {
        doc /* A citation of a kernel-checked Lean declaration backing the annotated element. */
        attribute decl : String;
        attribute statement : String[0..1];
    }

    metadata def Source {
        doc /* The Lean declaration an element was harvested from, for the round trip. */
        attribute decl : String;
        attribute file : String[0..1];
    }

    package Kinds {
        doc /* Dybkær's kind of property, Flater's kind algebra, and the dimension layer. */

        enum def ScaleType {
            doc /* Operator-based scale stratification (Dybkær Ch. 12). */
            nominal; ordinal; interval; ratio;
        }

        attribute def ExaminationPrinciple {
            doc /* The principle individuating a species within a genus (width: transverse extent). */
            attribute id : String;
        }
        attribute principles : ExaminationPrinciple[*];
        metadata def <principle> Principle :> SemanticMetadata {
            :>> baseType = principles meta SysML::Usage;
        }

        attribute def DimensionExponent {
            doc /* One base-dimension exponent of a dimension vector, as a rational. */
            attribute base : String;
            attribute num : Integer;
            attribute den : Integer default 1;
        }

        attribute def KindOfProperty {
            doc
            /*
             * A kind of property: identity, scale type and optional examination principle
             * (the core structure), the dimension vector of the `Dimension` layer when the
             * kind is dimensioned, and the ISO 80000 catalogue locators when catalogued.
             * Specialization is subsetting between kinds: `#kind width :> length`.
             */
            attribute id : String;
            attribute scale : ScaleType;
            ref attribute principle : ExaminationPrinciple[0..1];
            attribute dimension : DimensionExponent[*] ordered;
            attribute standardRef : String[0..1];
            attribute catalogueItem : String[0..1];
            attribute symbol : String[0..1];
            attribute coherentUnit : String[0..1];
        }
        attribute kinds : KindOfProperty[*];
        metadata def <kind> Kind :> SemanticMetadata {
            :>> baseType = kinds meta SysML::Usage;
        }

        attribute def SortOfSystem { attribute id : String; }
        attribute sorts : SortOfSystem[*];
        metadata def <sort> Sort :> SemanticMetadata {
            :>> baseType = sorts meta SysML::Usage;
        }

        attribute def Component { attribute id : String; }
        attribute components : Component[*];
        metadata def <component> ComponentOf :> SemanticMetadata {
            :>> baseType = components meta SysML::Usage;
        }

        attribute def DedicatedKind {
            doc /* A kind dedicated to a component of a sort of system (soil — water ; volume fraction). */
            attribute sort : String;
            attribute component : String;
            ref attribute kind : KindOfProperty;
        }
        attribute dedicatedKinds : DedicatedKind[*];
        metadata def <dedicated> Dedicated :> SemanticMetadata {
            :>> baseType = dedicatedKinds meta SysML::Usage;
        }

        attribute def MetrologicalUnit {
            doc /* A measurement unit of a kind, by symbol. */
            ref attribute kind : KindOfProperty;
            attribute symbol : String;
        }
        attribute units : MetrologicalUnit[*];
        metadata def <unit> Unit :> SemanticMetadata {
            :>> baseType = units meta SysML::Usage;
        }

        /* The kind algebra: curated, partial, and authored — each edge a witness. */
        abstract connection def KindEdge {
            doc /* An authored kind-algebra witness; `table` marks a `KindMul`/`KindDiv` registration. */
            attribute table : Boolean default false;
        }
        connection def KindProduct :> KindEdge {
            end left : KindOfProperty;
            end right : KindOfProperty;
            end result : KindOfProperty;
        }
        connection def KindQuotient :> KindEdge {
            end numerator : KindOfProperty;
            end denominator : KindOfProperty;
            end result : KindOfProperty;
        }
        connection def KindReciprocal :> KindEdge {
            end base : KindOfProperty;
            end result : KindOfProperty;
        }
        connection def KindPower :> KindEdge {
            attribute num : Integer;
            attribute den : Integer default 1;
            end base : KindOfProperty;
            end result : KindOfProperty;
        }
        connection def KindRealPower :> KindEdge {
            end base : KindOfProperty;
            end exponent : KindOfProperty;
            end result : KindOfProperty;
        }
        connection def KindTranscendental :> KindEdge {
            end argument : KindOfProperty;
            end result : KindOfProperty;
        }
        connection def KindReference :> KindEdge {
            end base : KindOfProperty;
            end result : KindOfProperty;
        }
        connection def KindDifference :> KindEdge {
            end left : KindOfProperty;
            end right : KindOfProperty;
        }
        abstract connection products : KindProduct[*];
        abstract connection quotients : KindQuotient[*];
        abstract connection reciprocals : KindReciprocal[*];
        abstract connection powers : KindPower[*];
        abstract connection realPowers : KindRealPower[*];
        abstract connection transcendentals : KindTranscendental[*];
        abstract connection referenceEdges : KindReference[*];
        abstract connection differences : KindDifference[*];
        metadata def <product> Product :> SemanticMetadata {
            :>> baseType = products meta SysML::Usage;
        }
        metadata def <quotient> Quotient :> SemanticMetadata {
            :>> baseType = quotients meta SysML::Usage;
        }
        metadata def <reciprocal> Reciprocal :> SemanticMetadata {
            :>> baseType = reciprocals meta SysML::Usage;
        }
        metadata def <power> Power :> SemanticMetadata {
            :>> baseType = powers meta SysML::Usage;
        }
        metadata def <realPower> RealPower :> SemanticMetadata {
            :>> baseType = realPowers meta SysML::Usage;
        }
        metadata def <transcendental> Transcendental :> SemanticMetadata {
            :>> baseType = transcendentals meta SysML::Usage;
        }
        metadata def <reference> Reference :> SemanticMetadata {
            :>> baseType = referenceEdges meta SysML::Usage;
        }
        metadata def <difference> Difference :> SemanticMetadata {
            :>> baseType = differences meta SysML::Usage;
        }
    }

    package Modules {
        doc /* Metrology modules: kind-typed boundaries, the provenance hypergraph, relations, requirements. */
        private import Kinds::*;

        enum def PortDir { input; config; param; output; conditional; }
        enum def IntroTier { 'derived'; gated; attested; }
        enum def EdgeFamily {
            product; quotient; reciprocal; transcendental; power; realPower; reference;
            additive; tableMul; tableDiv; copy; step; select;
        }
        enum def BoundaryRole { model; specification; }
        enum def AggregationKind {
            extensive; quasiExtensive; conditionallyExtensive; intensive; wholeProper; countKeyed;
            extensiveAbout; interfaceLicensed;
        }
        enum def RelationKind { inverts; refines; equals; boundedBy; }
        enum def TransferKind { exact; nonneg; restated; }
        enum def RequirementKind { provable; empirical; }

        port def KindPort {
            doc /* A kind-typed port: the node, the kind the signature states, its role. */
            attribute node : String;
            ref attribute kind : KindOfProperty;
            attribute dir : PortDir;
        }

        attribute def Intro {
            doc /* A node introduced at a kind, with the evidence tier introducing it. */
            attribute node : String;
            ref attribute kind : KindOfProperty;
            attribute tier : IntroTier;
            attribute reason : String[0..1];
        }

        attribute def Operand {
            attribute node : String;
            ref attribute kind : KindOfProperty;
        }

        attribute def Occurrence {
            doc /* One hyperedge: an edge family relating ordered operands to a result, at a site. */
            attribute family : EdgeFamily;
            attribute operands : Operand[*] ordered;
            attribute result : String;
            ref attribute resultKind : KindOfProperty;
            attribute site : String;
            attribute op : String[0..1];
            attribute member : String[0..1];
            attribute instance : Integer[0..1];
            attribute arity : Integer[0..1];
            attribute powerNum : Integer[0..1];
            attribute powerDen : Integer[0..1];
        }

        attribute def Aggregation {
            attribute node : String;
            attribute class : AggregationKind;
            attribute witness : String[0..1];
        }

        part def Module {
            doc
            /*
             * A metrology module: the declared boundary (`Provenance.Contract`) with its
             * ports, members, exits, deciders, aggregations and suppliers, and the
             * provenance hypergraph the assembly computed for it.
             */
            attribute name : String;
            attribute members : String[*] ordered;
            port ports : KindPort[*] ordered;
            attribute exits : String[*] ordered;
            attribute deciders : String[*] ordered;
            attribute aggregations : Aggregation[*] ordered;
            attribute suppliers : String[*] ordered;
            attribute role : BoundaryRole default BoundaryRole::model;
            doc /* `hypergraph = true` states that `intros` and `occurrences` are this
                 * module's wiring and asks Lean for its wiring verdicts (`wellFormed`,
                 * `agrees`, `accepts` for a match); a module without it is a contract only. */
            attribute hypergraph : Boolean default false;
            attribute intros : Intro[*] ordered;
            attribute occurrences : Occurrence[*] ordered;
        }
        part modules : Module[*];
        metadata def <module> ModuleOf :> SemanticMetadata {
            :>> baseType = modules meta SysML::Usage;
        }

        attribute def RelationLicense {
            doc /* How the claim holds at one rung of the carrier ladder. */
            attribute rung : String;
            attribute transfer : TransferKind;
            attribute witness : String;
        }

        connection def Relation {
            doc /* The spec edge between two boundaries, with its theorem witness. */
            attribute kind : RelationKind;
            attribute witness : String;
            attribute claim : String[0..1];
            attribute tolerance : String[0..1];
            attribute hypotheses : String[*] ordered;
            attribute licenses : RelationLicense[*] ordered;
            attribute wellPosed : String[0..1];
            attribute domain : String[0..1];
            attribute ambiguity : String[0..1];
            end left : Module;
            end right : Module;
        }
        abstract connection relations : Relation[*];
        metadata def <relation> RelationOf :> SemanticMetadata {
            :>> baseType = relations meta SysML::Usage;
        }

        requirement def PkcRequirement {
            doc /* What a module's quantities must satisfy, with the evidence by which it is met. */
            attribute name : String;
            attribute statement : String;
            attribute kind : RequirementKind;
            attribute governs : String;
            attribute 'port' : String[0..1];
            attribute scope : String[0..1];
            attribute witness : String[0..1];
            attribute spotChecks : String[*] ordered;
            attribute absent : String[0..1];
            attribute referents : String[*] ordered;
        }
        requirement pkcRequirements : PkcRequirement[*];
        metadata def <req> Req :> SemanticMetadata {
            :>> baseType = pkcRequirements meta SysML::Usage;
        }
    }

    package Tape {
        doc /* The computational tape graph and its match against a provenance hypergraph. */
        private import Modules::*;

        attribute def TapeVertex {
            doc /* A tape node once its value and backward rule are forgotten: name and parents. */
            attribute name : String[0..1];
            attribute parents : Integer[*] ordered;
        }

        attribute def TapeGraph {
            attribute vertices : TapeVertex[*] ordered;
        }
        attribute tapes : TapeGraph[*];
        metadata def <tape> TapeOf :> SemanticMetadata {
            :>> baseType = tapes meta SysML::Usage;
        }

        attribute def NodeComponents {
            attribute node : String;
            attribute vertices : Integer[*] ordered;
        }

        attribute def Realized {
            attribute occ : Integer;
            attribute interior : Integer[*] ordered;
        }

        attribute def Carrier {
            doc /* A rung of the carrier ladder the module runs at, and the platform realizing it. */
            attribute rung : String;
            attribute platform : String[0..1];
        }

        connection def Match {
            doc /* The component table and realized occurrences relating a module's hypergraph to a tape. */
            attribute components : NodeComponents[*] ordered;
            attribute realized : Realized[*] ordered;
            attribute carrier : Carrier[0..1];
            end module : Module;
            end tape : TapeGraph;
        }
        abstract connection matches : Match[*];
        metadata def <match> MatchOf :> SemanticMetadata {
            :>> baseType = matches meta SysML::Usage;
        }
    }
}
