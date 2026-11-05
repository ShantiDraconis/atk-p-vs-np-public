import MCore.Real.CNFStructure

namespace MCore.Research

structure ExactResidual (Parent Child : Prop) where
  forward : Parent → Child
  backward : Child → Parent

structure ParallelAttack (Goal : Prop) where
  Residual : Prop
  exact : ExactResidual Goal Residual

theorem return_to_primary {Goal : Prop} (a : ParallelAttack Goal)
    (h : a.Residual) : Goal := a.exact.backward h

/-- Current parser residual.  This names the exact primary target without
    postulating a proof of it. -/
def ParserRoundtripGoal : Prop :=
  ∀ φ : CircuitK1.Circuit, Real.parseCNF (Real.renderCNF φ) = some φ

end MCore.Research
