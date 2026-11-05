import MCore.K9

namespace MCore

/-- The exact data needed by the K9 obstruction route to produce a separation
    witness. This structure does not assert that such data exists. -/
structure SeparationWitnessData (Language α Value : Type) where
  interface : ObstructionInterface Language α Value
  witness : Language
  witness_in_np : interface.classical.inNP witness
  obstruction_nonzero : interface.obstruction (interface.bridge.encode witness) ≠ interface.zero

/-- Any supplied K10 witness data yields an NP language outside P. -/
theorem separation_witness_not_in_P
    {Language α Value : Type}
    (W : SeparationWitnessData Language α Value) :
    ¬ W.interface.classical.inP W.witness :=
  obstruction_excludes_P W.interface W.witness W.obstruction_nonzero

/-- Any supplied K10 witness data separates the two class predicates. -/
theorem separation_witness_separates
    {Language α Value : Type}
    (W : SeparationWitnessData Language α Value) :
    ¬ (∀ L, W.interface.classical.inP L ↔ W.interface.classical.inNP L) :=
  witness_separates_classes W.interface.classical W.witness
    W.witness_in_np (separation_witness_not_in_P W)

/-- K10 exposes the genuine unresolved obligation: existence of witness data
    for a concrete classical complexity model. The proposition is recorded but
    not assumed, proved, or populated by a placeholder. -/
def k10_open_obligation : Prop :=
  ∃ (Language α Value : Type), Nonempty (SeparationWitnessData Language α Value)

/-- The obligation remains explicitly open in the certification graph. -/
def k10_obligation_node : CertNode :=
  { status := .openBridge
    statement := k10_open_obligation }

theorem k10_status_openBridge : k10_obligation_node.status = .openBridge := rfl

theorem k10_status_not_proved : k10_obligation_node.status ≠ .provedProperty := by
  intro h
  cases h

theorem k10_not_certified : ¬ Nonempty (ProofCertificate k10_obligation_node) := by
  intro h
  rcases h with ⟨hcert⟩
  exact k10_status_not_proved hcert.status_proved

/-- Even the formal statement of the K10 obligation cannot promote the
    pre-existing classical endpoint without actual witness data. -/
theorem k10_classical_endpoint_not_promoted :
    ¬ Nonempty (ProofCertificate k6_dependency.target) :=
  k6_target_not_certified

end MCore
