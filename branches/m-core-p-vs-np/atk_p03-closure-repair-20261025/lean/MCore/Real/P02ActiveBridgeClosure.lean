import MCore.Real.P01PostMinCutClosure
import MCore.Real.P02RejectionImageEscape
import MCore.Attack.CanonicalTerminalProducer

namespace MCore
namespace Real
namespace P02ActiveBridgeClosure

open CanonicalFinalProof
open CanonicalSATBoundary
open CanonicalCircuitBits
open P01PostMinCutClosure
open P02RejectionImageEscape

/-- The active canonical route has no remaining model/signature bridge:
canonicalInterface matches the official repository InP/InNP predicates. -/
theorem active_signature_adapter_closed :
    ∀ L : BitLanguage,
      (CanonicalComplexityBridge.canonicalInterface.inP L ↔ InP L) ∧
      (CanonicalComplexityBridge.canonicalInterface.inNP L ↔ InNP L) :=
  Attack.canonicalModelMatch

/-- The only active mathematical residue is RejectImageEscape. Once supplied,
the already-frozen SAT-in-NP certificate and canonical endpoint close P != NP. -/
theorem rejectImageEscape_closes_pneqnp
    (hEscape : RejectImageEscape) :
    PneqNP := by
  exact remaining_material_gap_implies_p_ne_np
    (rejectImageEscape_implies_universalFailure hEscape)

/-- Same closure stated directly at the canonical fixed witness layer. -/
def canonicalWitnessOfRejectImageEscape
    (hEscape : RejectImageEscape) :
    Attack.CanonicalNotInPWitness :=
  { language := SATBits circuitBitEncoding
    in_np := canonical_sat_in_np_closed
    not_in_p :=
      universal_failure_implies_not_in_p
        (rejectImageEscape_implies_universalFailure hEscape) }

theorem rejectImageEscape_closes_canonical_separation
    (hEscape : RejectImageEscape) :
    ClosedDiscriminant.SeparationFinal
      CanonicalComplexityBridge.canonicalInterface.inP
      CanonicalComplexityBridge.canonicalInterface.inNP :=
  Attack.canonicalWitness_closes_separation
    (canonicalWitnessOfRejectImageEscape hEscape)

#print axioms MCore.Real.P02ActiveBridgeClosure.active_signature_adapter_closed
#print axioms MCore.Real.P02ActiveBridgeClosure.rejectImageEscape_closes_pneqnp
#print axioms MCore.Real.P02ActiveBridgeClosure.rejectImageEscape_closes_canonical_separation

end P02ActiveBridgeClosure
end Real
end MCore
