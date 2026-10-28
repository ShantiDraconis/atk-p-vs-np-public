import MCore.BackwardAudit.ClosedDiscriminant

namespace MCore
namespace PvsNPOpenMath

open ClosedDiscriminant

/--
Logical P-vs-NP dichotomy over a supplied pair of language classes.

This claim deliberately does not select either branch. It states only that
either the supplied classes are extensionally equal or they are not.
The proof below is classical excluded middle and therefore is not a proof
of the separation branch.
-/
def PvsNP_OpenMath {Language : Type}
    (P NP : Language → Prop) : Prop :=
  EqualityFinal P NP ∨ SeparationFinal P NP

theorem pvsnp_open_math
    {Language : Type}
    (P NP : Language → Prop) :
    PvsNP_OpenMath P NP := by
  exact final_closed P NP

theorem pvsnp_open_math_eq_or_neq
    {Language : Type}
    (P NP : Language → Prop) :
    PvsNP_OpenMath P NP ↔
      (EqualityFinal P NP ∨ ¬ EqualityFinal P NP) := by
  rfl

#print axioms MCore.PvsNPOpenMath.pvsnp_open_math
#print axioms MCore.PvsNPOpenMath.pvsnp_open_math_eq_or_neq

end PvsNPOpenMath
end MCore
