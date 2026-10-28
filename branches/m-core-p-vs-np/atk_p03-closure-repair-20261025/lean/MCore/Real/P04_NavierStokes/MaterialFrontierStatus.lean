import MCore.Real.P04_NavierStokes.OpenBridge.ActualNSToSignedGainCoreTarget
import MCore.Real.P04_NavierStokes.ClosedBridge.CoreToCertificate
import MCore.Real.P04_NavierStokes.ClosedBridge.SignedGainToDifferential

namespace MCore.Real.P04_NavierStokes.MaterialFrontierStatus

def frontierName : String := "ActualNSToSignedGainCore"
def material_frontier_closed : Bool := false

theorem material_frontier_not_closed :
    material_frontier_closed = false := rfl

#print axioms MCore.Real.P04_NavierStokes.MaterialFrontierStatus.material_frontier_not_closed

end MCore.Real.P04_NavierStokes.MaterialFrontierStatus
