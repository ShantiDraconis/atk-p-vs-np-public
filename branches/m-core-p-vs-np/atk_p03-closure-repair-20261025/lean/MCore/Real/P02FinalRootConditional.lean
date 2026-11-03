import MCore.Real.P02DiagonalNoShortcut
import MCore.Real.P02ActiveBridgeClosure

namespace MCore
namespace Real
namespace P02FinalRootConditional

open CanonicalFinalProof
open P02DiagonalNoShortcut
open P02ActiveBridgeClosure

/-- Active FINAL_ROOT: all engineering/bridge obligations are discharged.
The only remaining producer is CandidateCodeSemanticFixedPoint. -/
theorem FINAL_ROOT
    (hFixed : CandidateCodeSemanticFixedPoint) :
    PneqNP := by
  exact rejectImageEscape_closes_pneqnp
    (candidateCodeSemanticFixedPoint_implies_escape hFixed)

/-- Publication-facing form of the same root. -/
def FINAL_GLOBAL_EXTERNAL : Prop :=
  CandidateCodeSemanticFixedPoint

theorem FINAL_GLOBAL_EXTERNAL_implies_FINAL_ROOT :
    FINAL_GLOBAL_EXTERNAL → PneqNP := by
  intro h
  exact FINAL_ROOT h

#print axioms MCore.Real.P02FinalRootConditional.FINAL_ROOT
#print axioms MCore.Real.P02FinalRootConditional.FINAL_GLOBAL_EXTERNAL_implies_FINAL_ROOT

end P02FinalRootConditional
end Real
end MCore
