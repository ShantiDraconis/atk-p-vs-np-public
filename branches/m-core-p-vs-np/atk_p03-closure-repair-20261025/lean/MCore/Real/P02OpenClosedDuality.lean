import MCore.Real.P02TerminalFractionConvergence

namespace MCore
namespace Real
namespace P02OpenClosedDuality

open CanonicalFinalProof
open P02DiagonalNoShortcut
open P02TerminalHabitantCycle

abbrev OpenMath : Prop := Endpoint
abbrev ClosedMath : Prop := ¬ OpenMath

/-- "open math = - closed math" interpreted as logical negation. -/
theorem open_eq_neg_closed :
    OpenMath ↔ ¬ ClosedMath := by
  unfold ClosedMath
  classical
  exact not_not

/-- "closed math = - open math" is definitionally the chosen dual. -/
theorem closed_eq_neg_open :
    ClosedMath ↔ ¬ OpenMath := by
  rfl

/-- If one additionally identifies open and closed as equivalent propositions,
the system collapses: P ↔ ¬P is impossible. -/
theorem open_closed_identification_is_inconsistent
    (h : OpenMath ↔ ClosedMath) :
    False := by
  by_cases hp : OpenMath
  · have hc : ClosedMath := h.mp hp
    exact hc hp
  · have hc : ClosedMath := hp
    have hp' : OpenMath := h.mpr hc
    exact hp hp'

/-- Therefore the three claims
    Open = -Closed, Open = Closed, Closed = -Open
cannot simultaneously serve as a consistent proof rule. -/
def FullOpenClosedIdentification : Prop :=
  (OpenMath ↔ ¬ ClosedMath) ∧
  (OpenMath ↔ ClosedMath) ∧
  (ClosedMath ↔ ¬ OpenMath)

theorem full_open_closed_identification_impossible :
    ¬ FullOpenClosedIdentification := by
  intro H
  exact open_closed_identification_is_inconsistent H.2.1

/-- A consistent terminal classification keeps the duality but does not
identify a proposition with its negation. -/
theorem terminal_duality_consistent_shape :
    (OpenMath ↔ ¬ ClosedMath) ∧
    (ClosedMath ↔ ¬ OpenMath) := by
  exact ⟨open_eq_neg_closed, closed_eq_neg_open⟩

#print axioms MCore.Real.P02OpenClosedDuality.open_eq_neg_closed
#print axioms MCore.Real.P02OpenClosedDuality.closed_eq_neg_open
#print axioms MCore.Real.P02OpenClosedDuality.open_closed_identification_is_inconsistent
#print axioms MCore.Real.P02OpenClosedDuality.full_open_closed_identification_impossible
#print axioms MCore.Real.P02OpenClosedDuality.terminal_duality_consistent_shape

end P02OpenClosedDuality
end Real
end MCore
