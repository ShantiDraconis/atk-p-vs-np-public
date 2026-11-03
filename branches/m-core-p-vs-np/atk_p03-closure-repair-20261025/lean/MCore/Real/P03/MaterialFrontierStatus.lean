import MCore.Real.P03.OpenBridge.CompleteRouteB

namespace MCore.Real.P03.MaterialFrontierStatus

open OpenBridge.CompleteRouteB
open P03RangeFailureFrontier

def frontierName : String := "Nonempty CompleteRouteBInhabitant"
def material_frontier_closed : Bool := false

theorem material_frontier_not_closed :
    material_frontier_closed = false := rfl

/-- Downstream consumption is closed: a genuine material inhabitant refutes RangeFailureLaw. -/
theorem terminal_from_material
    (C : CompleteRouteBInhabitant) :
    ¬ RangeFailureLaw :=
  completeRouteB_refutes_rangeFailureLaw C

#print axioms MCore.Real.P03.MaterialFrontierStatus.material_frontier_not_closed
#print axioms MCore.Real.P03.MaterialFrontierStatus.terminal_from_material

end MCore.Real.P03.MaterialFrontierStatus
