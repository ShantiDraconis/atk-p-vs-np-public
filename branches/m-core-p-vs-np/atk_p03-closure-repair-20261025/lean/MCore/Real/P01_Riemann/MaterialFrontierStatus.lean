import MCore.Real.P01_Riemann.OpenBridge.BoundedZeroCandidate
import MCore.Real.P01_Riemann.ClosedBridge.FiniteSpanToDNLimit

namespace MCore.Real.P01_Riemann.MaterialFrontierStatus

def frontierName : String := "FiniteSpanApproximatesChi concreteGeneratorFamily / DNLimit = 0"
def material_frontier_closed : Bool := false

theorem material_frontier_not_closed :
    material_frontier_closed = false := rfl

#print axioms MCore.Real.P01_Riemann.MaterialFrontierStatus.material_frontier_not_closed

end MCore.Real.P01_Riemann.MaterialFrontierStatus
