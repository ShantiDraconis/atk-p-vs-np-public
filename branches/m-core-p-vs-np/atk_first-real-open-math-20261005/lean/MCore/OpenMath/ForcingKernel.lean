import MCore.BackwardAudit.OrientedWitnessBoundary

namespace MCore.OpenMath.PNP

open MCore.BackwardAudit

def FirstRealOpenMath
    {Language : Type}
    (P NP : Language → Prop) : Prop :=
  Nonempty (LowerBoundWitness P NP)

theorem close_separation_from_first_real_open_math
    {Language : Type}
    {P NP : Language → Prop}
    (h : FirstRealOpenMath P NP) :
    ClosedDiscriminant.SeparationFinal P NP := by
  rcases h with ⟨w⟩
  exact typeB_closes_separation w

#print axioms MCore.OpenMath.PNP.close_separation_from_first_real_open_math

end MCore.OpenMath.PNP
