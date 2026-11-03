import MCore.Real.P03CriticalHalfSymmetry

namespace MCore.Real.P03.ClosedBase.C2I

open P03CriticalHalfSymmetry

theorem closed_c2i (p : ℝ × ℝ) :
    ComplementSymmetry (ComplementSymmetry p) = p :=
  complementSymmetry_involutive p

#print axioms MCore.Real.P03.ClosedBase.C2I.closed_c2i

end MCore.Real.P03.ClosedBase.C2I
