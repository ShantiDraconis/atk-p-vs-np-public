import MCore.Real.P02_YangMills.OpenBridge.B60Target
import MCore.Real.P02_YangMills.ClosedBridge.B60ToMassGap

namespace MCore.Real.P02_YangMills.MaterialFrontierStatus

def frontierName : String := "B60ConcretePhysicalAdapter"
def material_frontier_closed : Bool := false

theorem material_frontier_not_closed :
    material_frontier_closed = false := rfl

#print axioms MCore.Real.P02_YangMills.MaterialFrontierStatus.material_frontier_not_closed

end MCore.Real.P02_YangMills.MaterialFrontierStatus
