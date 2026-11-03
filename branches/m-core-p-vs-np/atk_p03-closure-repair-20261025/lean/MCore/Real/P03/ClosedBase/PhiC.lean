import MCore.Real.P03CriticalHalfSymmetry

namespace MCore.Real.P03.ClosedBase.PhiC

open P03CriticalHalfSymmetry

theorem closed_phi_equivariance (α : ℝ) (p : ℝ × ℝ) :
    CriticalHalfMap α (ComplementSymmetry p) =
      CriticalReflection (CriticalHalfMap α p) :=
  criticalHalfMap_intertwines α p

#print axioms MCore.Real.P03.ClosedBase.PhiC.closed_phi_equivariance

end MCore.Real.P03.ClosedBase.PhiC
