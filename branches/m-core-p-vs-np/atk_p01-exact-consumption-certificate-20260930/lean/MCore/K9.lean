import MCore.K8

namespace MCore

/-- Abstract language interface for the classical complexity layer.
    K9 deliberately does not claim that the experimental decomposition is NP. -/
structure ClassicalComplexityInterface (Language : Type) where
  inP : Language → Prop
  inNP : Language → Prop
  p_subset_np : ∀ L, inP L → inNP L

/-- A bridge maps a classical language into the experimental decomposition.
    Existence of a useful bridge is data, not an axiom and not assumed globally. -/
structure DecompositionBridge (Language α : Type) where
  encode : Language → ComplexityDecomposition α

/-- A bridge-compatible obstruction is stated only conditionally. -/
structure ObstructionInterface (Language α Value : Type) where
  classical : ClassicalComplexityInterface Language
  bridge : DecompositionBridge Language α
  obstruction : ComplexityDecomposition α → Value
  zero : Value
  p_vanishes : ∀ L, classical.inP L → obstruction (bridge.encode L) = zero

/-- If an NP language has a certified nonzero obstruction, it cannot be in P.
    This is pure logic from the explicit vanishing hypothesis; it does not assert
    that such a language or obstruction exists for classical SAT. -/
theorem obstruction_excludes_P
    {Language α Value : Type}
    (O : ObstructionInterface Language α Value)
    (L : Language)
    (hNonzero : O.obstruction (O.bridge.encode L) ≠ O.zero) :
    ¬ O.classical.inP L := by
  intro hP
  exact hNonzero (O.p_vanishes L hP)

/-- Conditional separation interface: an explicit NP witness outside P yields
    non-equality of the two predicates. No witness is manufactured here. -/
theorem witness_separates_classes
    {Language : Type}
    (C : ClassicalComplexityInterface Language)
    (L : Language)
    (hNP : C.inNP L)
    (hNotP : ¬ C.inP L) :
    ¬ (∀ X, C.inP X ↔ C.inNP X) := by
  intro hEq
  exact hNotP ((hEq L).mpr hNP)

/-- K9 records the classical-interface bridge as open. The proved statements
    above are conditional interface lemmas, not a proof of classical P != NP. -/
def k9_classical_interface_node : CertNode :=
  { status := .openBridge
    statement := ∀ {Language α Value : Type}
      (O : ObstructionInterface Language α Value) (L : Language),
      O.obstruction (O.bridge.encode L) ≠ O.zero → ¬ O.classical.inP L }

theorem k9_statement_valid : k9_classical_interface_node.statement := by
  intro Language α Value O L h
  exact obstruction_excludes_P O L h

theorem k9_status_openBridge : k9_classical_interface_node.status = .openBridge := rfl

theorem k9_status_not_proved : k9_classical_interface_node.status ≠ .provedProperty := by
  intro h
  cases h

theorem k9_not_certified : ¬ Nonempty (ProofCertificate k9_classical_interface_node) := by
  intro h
  rcases h with ⟨hcert⟩
  exact k9_status_not_proved hcert.status_proved

theorem k9_classical_endpoint_not_promoted :
    ¬ Nonempty (ProofCertificate k6_dependency.target) :=
  k6_target_not_certified

end MCore
