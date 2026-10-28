import MCore.BackwardAudit.OrientedWitnessBoundary

namespace MCore
namespace BackwardAudit

open ClosedDiscriminant

/-- Constructive/material orientation of the P-vs-NP discriminant.
    Unlike bare `D ∨ ¬D`, this requires an explicit algorithmic or lower-bound
    payload and therefore cannot be manufactured by excluded middle alone. -/
inductive MaterialOrientation
    {Language : Type}
    (P NP : Language → Prop) where
  | equality
      {SATInstance : Type}
      {SAT : SATInstance → Prop}
      (alg : PolySATCertificate SATInstance SAT)
      (transfer : SATCompletenessTransfer P NP SAT) :
      MaterialOrientation P NP
  | separation
      (w : LowerBoundWitness P NP) :
      MaterialOrientation P NP

theorem material_orientation_closes_terminal
    {Language : Type}
    {P NP : Language → Prop}
    (hStart : StartClosed P NP)
    (m : MaterialOrientation P NP) :
    EqualityFinal P NP ∨ SeparationFinal P NP := by
  cases m with
  | equality alg transfer =>
      exact Or.inl (typeA_closes_equality hStart alg transfer)
  | separation w =>
      exact Or.inr (typeB_closes_separation w)

def materialOrientationBuilt : Bool := false

theorem material_orientation_still_open :
    materialOrientationBuilt = false := by rfl

#print axioms material_orientation_closes_terminal
#print axioms material_orientation_still_open

end BackwardAudit
end MCore
