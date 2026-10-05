module

public import PropertyKindCalculus.Graph.Flow
public import PropertyKindCalculus.Derivation

/-!
# The seal of a module — no undeclared entry into an output's pedigree

The first capstone theorem of the calculus (blueprint, "Capstone theorems"). Once a module's
inputs, constants and attestations are declared, no other raw datum reaches its outputs:
for a well-formed provenance hypergraph, every node in the pedigree of an output — a
produced port or an exit — is either a *source* (a non-produced port, a gated ingest, an
attested mint carrying its reason) or the result of some occurrence all of whose operands
are themselves in that pedigree. Equivalently, the pedigree of an output has no leaf outside
the sources, and the assumption ledger the build prints for the output is the complete
list of what it rests on.

  * `Provenance.pedigree_seal` — the theorem, argued hop by hop through
    `Provenance.eq_or_operand_of_mem_ancestorsOf` and `Provenance.operand_mem_ancestorsOf`
    while its hypothesis is decided over lists;
  * `Provenance.sealed_of_wellFormed` — its executable form: `Provenance.sealed`, the
    check an instance pins with `decide`, follows from well-formedness;
  * `Provenance.seal_of_agrees` — the boundary reading: under agreement of the declared
    boundary, every produced port the boundary declares is sealed, and every source port in
    its ledger is one the boundary declares.

What the theorem does not claim: that the hypergraph is the code. That the harvest
attributed every mint, erasure and occurrence to the right node is what the boundary audit,
the mint ratchet and the unkinded sweep assert about the source; the seal of the
computation (`Graph.Bisimulation`, `Torch.Paradigm.TapeSeal`) is what turns that residual
trust into a cross-check.
-/

@[expose] public section Blanket

namespace PropertyKindCalculus

namespace Provenance

variable {ν κ : Type} [BEq ν] [LawfulBEq ν] [BEq κ]

/-! ### Declared nodes -/

omit [BEq κ] in
/-- A node with a declared kind is a port or an introduction. -/
lemma declared_of_kindOf?_eq_some {g : Provenance ν κ} {a : ν} {k : κ}
    (h : g.kindOf? a = some k) :
    (∃ p ∈ g.ports, p.node = a) ∨ ∃ i ∈ g.intros, i.node = a := by
  unfold kindOf? at h
  split at h
  · rename_i p hp
    exact Or.inl ⟨p, List.mem_of_find?_eq_some hp, by simpa using List.find?_some hp⟩
  · rename_i hnone
    simp only [Option.map_eq_some_iff] at h
    obtain ⟨i, hi, -⟩ := h
    exact Or.inr ⟨i, List.mem_of_find?_eq_some hi, by simpa using List.find?_some hi⟩

omit [LawfulBEq ν] in
/-- Every operand of an occurrence of a well-formed graph has a declared kind — the
`occurrencesTyped` clause, read as a membership. -/
lemma operand_kindOf?_isSome {g : Provenance ν κ} (hwf : g.WellFormed)
    {o : Occurrence ν κ} (ho : o ∈ g.occurrences) {oc : ν × κ} (hoc : oc ∈ o.operands) :
    ∃ k, g.kindOf? oc.1 = some k := by
  have ht := hwf.clauses.2.1
  simp only [occurrencesTyped, List.all_eq_true, Bool.and_eq_true] at ht
  have hk := (ht o ho).1.1.2 oc hoc
  cases h : g.kindOf? oc.1 with
  | none => rw [h, Option.none_beq_some] at hk; exact absurd hk Bool.false_ne_true
  | some k => exact ⟨k, rfl⟩

/-- A declared node is a source or known: a non-produced port and a gated or attested
introduction are sources; a produced port and a derived introduction are reached from the
sources. -/
lemma source_or_known_of_declared {g : Provenance ν κ} (hwf : g.WellFormed) {a : ν}
    (h : (∃ p ∈ g.ports, p.node = a) ∨ ∃ i ∈ g.intros, i.node = a) :
    a ∈ g.sources ∨ a ∈ g.known := by
  rcases h with ⟨p, hp, rfl⟩ | ⟨i, hi, rfl⟩
  · by_cases hprod : p.dir.produced = true
    · exact Or.inr (output_mem_known hwf (List.mem_append_left _
        (List.mem_map.mpr ⟨p, List.mem_filter.mpr ⟨hp, hprod⟩, rfl⟩)))
    · refine Or.inl (List.mem_append_left _ (List.mem_map.mpr ⟨p, List.mem_filter.mpr ⟨hp, ?_⟩, rfl⟩))
      simpa using hprod
  · cases hti : i.tier with
    | derived => exact Or.inr (derived_mem_known hwf hi hti)
    | gated =>
      exact Or.inl (List.mem_append_right _
        (List.mem_map.mpr ⟨i, List.mem_filter.mpr ⟨hi, by simp [IntroTier.isSource, hti]⟩, rfl⟩))
    | attested r =>
      exact Or.inl (List.mem_append_right _
        (List.mem_map.mpr ⟨i, List.mem_filter.mpr ⟨hi, by simp [IntroTier.isSource, hti]⟩, rfl⟩))

/-! ### The seal -/

/-- **The seal of a module.** In a well-formed provenance hypergraph, every node in the
pedigree of an output — a produced port or an exit — is a source, or the result of some
occurrence all of whose operands are themselves in that pedigree. Once the module's gates
are declared, no other raw datum reaches its outputs. -/
theorem pedigree_seal {g : Provenance ν κ} (hwf : g.WellFormed) {y : ν} (hy : y ∈ g.outputs)
    {a : ν} (ha : a ∈ g.ancestorsOf [y]) :
    a ∈ g.sources ∨
      ∃ o ∈ g.occurrences, o.result = a ∧ ∀ oc ∈ o.operands, oc.1 ∈ g.ancestorsOf [y] := by
  have hcase : a ∈ g.sources ∨ ∃ o ∈ g.occurrences, o.result = a := by
    rcases eq_or_operand_of_mem_ancestorsOf ha with hay | ⟨o, ho, oc, hoc, rfl⟩
    · obtain rfl := List.mem_singleton.mp hay
      exact mem_known (output_mem_known hwf hy)
    · obtain ⟨k, hk⟩ := operand_kindOf?_isSome hwf ho hoc
      rcases source_or_known_of_declared hwf (declared_of_kindOf?_eq_some hk) with hs | hkn
      · exact Or.inl hs
      · exact mem_known hkn
  rcases hcase with hsrc | ⟨o, ho, hres⟩
  · exact Or.inl hsrc
  · exact Or.inr ⟨o, ho, hres, fun oc hoc =>
      operand_mem_ancestorsOf ho (by rw [hres]; exact ha) hoc⟩

/-- **The seal, executable.** Well-formedness implies the decidable check: no output has an
undeclared leaf. -/
lemma sealed_of_wellFormed {g : Provenance ν κ} (hwf : g.WellFormed) : g.Sealed := by
  unfold Sealed sealed
  refine List.all_eq_true.mpr fun y hy => ?_
  rw [List.isEmpty_iff, undeclaredLeaves, List.filter_eq_nil_iff]
  intro a ha hbad
  rcases pedigree_seal hwf hy ha with hsrc | ⟨o, ho, hres, -⟩
  · have h1 : g.sources.contains a = true := List.contains_iff_mem.mpr hsrc
    rw [h1] at hbad
    simp at hbad
  · have h2 : g.occurrences.any (·.result == a) = true :=
      List.any_eq_true.mpr ⟨o, ho, by simp [hres]⟩
    rw [h2] at hbad
    simp at hbad

omit [BEq κ] in
/-- The sources in an output's pedigree are exactly its influencers, and — by the seal —
everything else in the pedigree is derived: the assumption ledger is the complete list of
what the output rests on. -/
lemma mem_influencers_iff {g : Provenance ν κ} {y a : ν} :
    a ∈ g.influencers y ↔ a ∈ g.sources ∧ a ∈ g.ancestorsOf [y] := by
  simp only [influencers, List.mem_filter, List.contains_iff_mem]

/-! ### The boundary reading -/

/-- A declared role that refines a produced computed role is itself produced, and the
computed role is then the declared one: `param` refines only `input`. -/
lemma PortDir.produced_of_refines (a b : PortDir) (h : a.refines b = true)
    (ha : a.produced = true) : b.produced = true := by
  cases a <;> cases b <;> simp_all [PortDir.refines, PortDir.produced]

/-- Under agreement of the declared boundary, every produced port it declares is an output
of the graph. -/
lemma output_of_agrees {g : Provenance ν κ} {c : Contract ν κ} (hc : c.Agrees g)
    {q : Port ν κ} (hq : q ∈ c.ports) (hprod : q.dir.produced = true) : q.node ∈ g.outputs := by
  have ha := hc
  simp only [Contract.Agrees, Contract.agrees, Bool.and_eq_true] at ha
  have hun := ha.1.1.2
  simp only [Contract.unrealized, List.isEmpty_iff, List.filter_eq_nil_iff] at hun
  have hany : (g.ports.any fun p => Contract.standsFor q p) = true := by
    have := hun q hq
    revert this
    cases g.ports.any fun p => Contract.standsFor q p <;> simp
  obtain ⟨p, hp, hst⟩ := List.any_eq_true.mp hany
  simp only [Contract.standsFor, Bool.and_eq_true, beq_iff_eq] at hst
  obtain ⟨⟨hnode, -⟩, href⟩ := hst
  exact List.mem_append_left _ (List.mem_map.mpr
    ⟨p, List.mem_filter.mpr ⟨hp, PortDir.produced_of_refines _ _ href hprod⟩, hnode.symm⟩)

/-- **The seal of a declared boundary.** Under well-formedness and agreement, every produced
port the boundary declares has no undeclared leaf, and every source port in its assumption
ledger is stood for by a port the boundary declares — the conclusion speaks of the declared
interface, not of whatever the harvest happened to port. -/
lemma seal_of_agrees {g : Provenance ν κ} {c : Contract ν κ} (hwf : g.WellFormed)
    (hc : c.Agrees g) {q : Port ν κ} (hq : q ∈ c.ports) (hprod : q.dir.produced = true) :
    g.undeclaredLeaves q.node = [] ∧
      ∀ p ∈ (g.assumptionLedger q.node).ports, ∃ q' ∈ c.ports, Contract.standsFor q' p = true := by
  constructor
  · have hs := sealed_of_wellFormed hwf
    simp only [Sealed, sealed, List.all_eq_true, List.isEmpty_iff] at hs
    exact hs _ (output_of_agrees hc hq hprod)
  · intro p hp
    have ha := hc
    simp only [Contract.Agrees, Contract.agrees, Bool.and_eq_true] at ha
    have hund := ha.1.1.1.2
    simp only [Contract.undeclared, List.isEmpty_iff, List.filter_eq_nil_iff] at hund
    have hpg : p ∈ g.ports := by
      simp only [assumptionLedger, List.mem_filter] at hp
      exact hp.1
    have hany : (c.ports.any fun q' => Contract.standsFor q' p) = true := by
      have := hund p hpg
      revert this
      cases c.ports.any fun q' => Contract.standsFor q' p <;> simp
    exact List.any_eq_true.mp hany

end Provenance

end PropertyKindCalculus

end Blanket
