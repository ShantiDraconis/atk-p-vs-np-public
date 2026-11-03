import MCore.Real.P02TerminalRecurrenceTheorem

namespace MCore
namespace Real
namespace P02TerminalHabitantCycle

open CanonicalFinalProof
open P02DiagonalNoShortcut
open P02TerminalRecurrenceTheorem

abbrev Endpoint : Prop := CandidateCodeSemanticFixedPoint
abbrev Gap : Prop := Endpoint
abbrev Habitant : Prop := Gap
abbrev Inhabitant : Prop := Habitant

theorem endpoint_to_gap : Endpoint → Gap := id
theorem gap_to_habitant : Gap → Habitant := id
theorem habitant_to_inhabitant : Habitant → Inhabitant := id
theorem inhabitant_to_endpoint : Inhabitant → Endpoint := id

theorem endpoint_iff_gap : Endpoint ↔ Gap := Iff.rfl
theorem gap_iff_habitant : Gap ↔ Habitant := Iff.rfl
theorem habitant_iff_inhabitant : Habitant ↔ Inhabitant := Iff.rfl
theorem inhabitant_iff_endpoint : Inhabitant ↔ Endpoint := Iff.rfl

/-- The complete terminal wheel is definitionally closed. -/
theorem terminal_cycle :
    (Endpoint ↔ Gap) ∧
    (Gap ↔ Habitant) ∧
    (Habitant ↔ Inhabitant) ∧
    (Inhabitant ↔ Endpoint) := by
  exact ⟨Iff.rfl, Iff.rfl, Iff.rfl, Iff.rfl⟩

/-- Generic recurrence does not manufacture an inhabitant.
This kernel theorem is the negative control for the proposed truncation rule. -/
def RecurrenceCreatesInhabitant : Prop :=
  ∀ P : Prop, (P ↔ P) → P

theorem recurrence_does_not_create_inhabitant :
    ¬ RecurrenceCreatesInhabitant := by
  intro H
  have hFalse : False := H False Iff.rfl
  exact hFalse

/-- Therefore the terminal cycle is a valid identity-of-signature certificate,
but a proof of Endpoint still requires a term whose type is Endpoint. -/
theorem terminal_cycle_preserves_any_existing_inhabitant
    (h : Endpoint) :
    Gap ∧ Habitant ∧ Inhabitant ∧ Endpoint := by
  exact ⟨h, h, h, h⟩

#print axioms MCore.Real.P02TerminalHabitantCycle.terminal_cycle
#print axioms MCore.Real.P02TerminalHabitantCycle.recurrence_does_not_create_inhabitant
#print axioms MCore.Real.P02TerminalHabitantCycle.terminal_cycle_preserves_any_existing_inhabitant

end P02TerminalHabitantCycle
end Real
end MCore
