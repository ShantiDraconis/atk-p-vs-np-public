import MCore.BackwardAudit.OrientedWitnessBoundary

namespace MCore.BackwardAudit

/-- Counter-audit for the abstract parameterized boundary.
With an artificial one-point language, P=False and NP=True, the generic
LowerBoundWitness is trivially inhabited. This does not concern the official
complexity model; it proves that official-model binding is indispensable. -/
def toyLowerBoundWitness :
    LowerBoundWitness
      (fun _ : Unit => False)
      (fun _ : Unit => True) where
  language := ()
  in_np := trivial
  not_in_p := by
    intro h
    exact h

theorem abstract_lowerBoundWitness_is_inhabited :
    Nonempty
      (LowerBoundWitness
        (fun _ : Unit => False)
        (fun _ : Unit => True)) :=
  ⟨toyLowerBoundWitness⟩

end MCore.BackwardAudit
