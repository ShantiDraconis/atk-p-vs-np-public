import MCore.Real.P03PerfectFlipDichotomy

namespace MCore.Real.P03.ClosedBridge.Dichotomy

open P03RangeFailureFrontier
open P03PerfectFlipDichotomy

theorem closed_existsPerfectFlip_iff_not_rangeFailureLaw :
    ExistsPerfectFlip ↔ ¬ RangeFailureLaw :=
  existsPerfectFlip_iff_not_rangeFailureLaw

theorem closed_global_dichotomy :
    RangeFailureLaw ∨ ExistsPerfectFlip :=
  rangeFailureLaw_or_existsPerfectFlip

#print axioms MCore.Real.P03.ClosedBridge.Dichotomy.closed_existsPerfectFlip_iff_not_rangeFailureLaw
#print axioms MCore.Real.P03.ClosedBridge.Dichotomy.closed_global_dichotomy

end MCore.Real.P03.ClosedBridge.Dichotomy
