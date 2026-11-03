import MCore.Real.P03CriticalHalfSymmetry

namespace MCore.Real.P03.ClosedBase.R2I

open P03CriticalHalfSymmetry

/-- CLOSED reflection involution. This is CriticalReflection, not the Cook--Levin R_M. -/
theorem closed_r2i (s : ℝ) :
    CriticalReflection (CriticalReflection s) = s :=
  criticalReflection_involutive s

#print axioms MCore.Real.P03.ClosedBase.R2I.closed_r2i

end MCore.Real.P03.ClosedBase.R2I
