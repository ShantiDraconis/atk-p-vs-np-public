import MCore.Real.CanonicalSATNTMAttack

namespace MCore
namespace Real
namespace P01IntegrationFence

open CanonicalFinalProof

/-- A phase bridge that only states disjointness from reject carries no tape,
transition, halting, or semantic information.  This is the exact shape of the
historical IntegratedPhaseBridgeCertificate fields. -/
structure StateOnlyBridge where
  parser_to_witness :
    ∀ q : Fin 25, True → q.val < 47
  witness_to_verifier :
    (11 : Nat) < 47
  verifier_to_terminal :
    (7 : Nat) < 47

theorem stateOnlyBridge_trivially_inhabited :
    Nonempty StateOnlyBridge := by
  refine ⟨{
    parser_to_witness := ?_
    witness_to_verifier := by decide
    verifier_to_terminal := by decide
  }⟩
  intro q _
  exact Nat.lt_of_lt_of_le q.isLt (by decide)

/-- Therefore a state-only bridge cannot be accepted as evidence for the
canonical SAT machine closure.  Promotion still requires the actual machine
realization. -/
def MaterialIntegrationTarget : Prop :=
  CanonicalSATNTMAttack.CanonicalSATMachineClosure

#print axioms MCore.Real.P01IntegrationFence.stateOnlyBridge_trivially_inhabited

end P01IntegrationFence
end Real
end MCore
