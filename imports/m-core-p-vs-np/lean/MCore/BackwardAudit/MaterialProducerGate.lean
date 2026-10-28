import MCore.BackwardAudit.OrientedWitnessBoundary

namespace MCore.BackwardAudit

/-
Material audit:
LowerBoundWitness stores the endpoint `¬ P language` as a field.
Therefore extracting `not_in_p` is transport/projection, not a lower-bound producer.
-/
theorem lowerBoundWitness_notInP_is_projection
    {Language : Type}
    {P NP : Language → Prop}
    (w : LowerBoundWitness P NP) :
    ¬ P w.language :=
  w.not_in_p

#print axioms lowerBoundWitness_notInP_is_projection

end MCore.BackwardAudit
