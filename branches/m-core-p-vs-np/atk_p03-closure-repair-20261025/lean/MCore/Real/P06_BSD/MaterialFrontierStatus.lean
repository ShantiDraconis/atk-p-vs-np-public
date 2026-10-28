import MCore.Real.P06_BSD.OpenBridge.RealizableBSDProducerTarget
import MCore.Real.P06_BSD.ClosedBridge.RankWitnessToOpenCore
import MCore.Real.P06_BSD.ClosedBridge.RankPartToEquality

namespace MCore.Real.P06_BSD.MaterialFrontierStatus

def frontierName : String := "RealizableBSDProducer"
def material_frontier_closed : Bool := false

theorem material_frontier_not_closed :
    material_frontier_closed = false := rfl

#print axioms MCore.Real.P06_BSD.MaterialFrontierStatus.material_frontier_not_closed

end MCore.Real.P06_BSD.MaterialFrontierStatus
