import MCore.Real.P03OpenMathFrontier
import MCore.Real.P03RangeFailureFrontier

namespace MCore.Real.P03.ClosedBridge.Transport

open CanonicalFinalProof
open P03OpenMathFrontier
open P03TerminalSemanticBridge
open P03RangeFailureFrontier

theorem closed_fullRun_to_internal_endpoint
    (H : FullRunAcceptanceLaw) :
    PneqNP :=
  full_run_acceptance_law_closes_internal_endpoint H

theorem closed_rangeFailure_to_internal_endpoint
    (H : RangeFailureLaw) :
    PneqNP := by
  apply closed_fullRun_to_internal_endpoint
  exact rangeFailureLaw_iff_fullRunAcceptanceLaw.mp H

#print axioms MCore.Real.P03.ClosedBridge.Transport.closed_fullRun_to_internal_endpoint
#print axioms MCore.Real.P03.ClosedBridge.Transport.closed_rangeFailure_to_internal_endpoint

end MCore.Real.P03.ClosedBridge.Transport
