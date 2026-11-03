import MCore.Real.P02OpenClosedDuality

namespace MCore
namespace Real
namespace P02OpenClosedIrreflexiveCollapse

open CanonicalFinalProof
open P02DiagonalNoShortcut
open P02TerminalHabitantCycle
open P02OpenClosedDuality

/-- The user's final two clauses, interpreted literally as disequality
of propositions. -/
def OpenSelfDifferent : Prop := OpenMath ≠ OpenMath
def ClosedSelfDifferent : Prop := ClosedMath ≠ ClosedMath

/-- No proposition is unequal to itself. -/
theorem not_open_self_different :
    ¬ OpenSelfDifferent := by
  intro h
  exact h rfl

theorem not_closed_self_different :
    ¬ ClosedSelfDifferent := by
  intro h
  exact h rfl

/-- Requiring either self-disequality collapses immediately. -/
theorem open_self_difference_implies_false
    (h : OpenSelfDifferent) :
    False := by
  exact h rfl

theorem closed_self_difference_implies_false
    (h : ClosedSelfDifferent) :
    False := by
  exact h rfl

/-- Full terminal conjunction with the previously proposed dualities plus
self-disequality is inconsistent. -/
def FullTerminalConjuncture : Prop :=
  (OpenMath ↔ ¬ ClosedMath) ∧
  (OpenMath ↔ ClosedMath) ∧
  (ClosedMath ↔ ¬ OpenMath) ∧
  OpenSelfDifferent ∧
  ClosedSelfDifferent

theorem full_terminal_conjuncture_impossible :
    ¬ FullTerminalConjuncture := by
  intro H
  exact H.2.2.2.1 rfl

/-- Consistent core retained after removing the contradictory clauses. -/
theorem consistent_terminal_duality :
    (OpenMath ↔ ¬ ClosedMath) ∧
    (ClosedMath ↔ ¬ OpenMath) :=
  terminal_duality_consistent_shape

#print axioms MCore.Real.P02OpenClosedIrreflexiveCollapse.not_open_self_different
#print axioms MCore.Real.P02OpenClosedIrreflexiveCollapse.not_closed_self_different
#print axioms MCore.Real.P02OpenClosedIrreflexiveCollapse.full_terminal_conjuncture_impossible
#print axioms MCore.Real.P02OpenClosedIrreflexiveCollapse.consistent_terminal_duality

end P02OpenClosedIrreflexiveCollapse
end Real
end MCore
