import MCore.Real.P05_Hodge.OpenBridge.ConcreteAlgebraicityPayloadTarget
import MCore.Real.P05_Hodge.ClosedBridge.H01ToPointwise
import MCore.Real.P05_Hodge.ClosedBridge.PointwiseToHodge

namespace MCore.Real.P05_Hodge.MaterialFrontierStatus

def frontierName : String := "ConcreteAlgebraicityPayload"
def material_frontier_closed : Bool := false

theorem material_frontier_not_closed :
    material_frontier_closed = false := rfl

#print axioms MCore.Real.P05_Hodge.MaterialFrontierStatus.material_frontier_not_closed

end MCore.Real.P05_Hodge.MaterialFrontierStatus
