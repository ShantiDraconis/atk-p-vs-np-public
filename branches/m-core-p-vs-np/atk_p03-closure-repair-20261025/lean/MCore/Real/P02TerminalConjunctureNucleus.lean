import MCore.Real.P02TerminalHabitantCycle

namespace MCore
namespace Real
namespace P02TerminalConjunctureNucleus

open CanonicalFinalProof
open P02DiagonalNoShortcut
open P02TerminalHabitantCycle

/-- User's closed-start / closed-middle / closed-end presentation of the
same terminal signature. -/
abbrev ClosedStart : Prop := Endpoint
abbrev ClosedMiddle : Prop := Endpoint
abbrev ClosedEnd : Prop := Endpoint

/-- Both orientations collapse definitionally onto the same middle. -/
theorem start_to_middle : ClosedStart → ClosedMiddle := id
theorem end_to_middle : ClosedEnd → ClosedMiddle := id
theorem middle_to_start : ClosedMiddle → ClosedStart := id
theorem middle_to_end : ClosedMiddle → ClosedEnd := id

theorem two_sided_terminal_nucleus :
    (ClosedStart ↔ ClosedMiddle) ∧
    (ClosedEnd ↔ ClosedMiddle) := by
  exact ⟨Iff.rfl, Iff.rfl⟩

/-- The conjunction of both closed sides is equivalent to the terminal
endpoint itself; no extra parameter survives the collapse. -/
theorem closed_sides_iff_endpoint :
    (ClosedStart ∧ ClosedEnd) ↔ Endpoint := by
  constructor
  · intro h
    exact h.1
  · intro h
    exact ⟨h, h⟩

/-- A three-valued label can record position in the recurrence without
changing the proposition carried by the nucleus. -/
inductive TerminalPhase
  | zero
  | one
  | two
  deriving DecidableEq, Repr

def phasePayload : TerminalPhase → Prop
  | .zero => ClosedStart
  | .one => ClosedMiddle
  | .two => ClosedEnd

theorem phase_payload_same
    (p : TerminalPhase) :
    phasePayload p ↔ Endpoint := by
  cases p <;> rfl

/-- "Tension/repulsion/torsion" interpreted purely as moving among the three
labels preserves the same terminal payload. -/
def rotatePhase : TerminalPhase → TerminalPhase
  | .zero => .one
  | .one => .two
  | .two => .zero

theorem rotation_preserves_terminal_signature
    (p : TerminalPhase) :
    phasePayload (rotatePhase p) ↔ phasePayload p := by
  cases p <;> rfl

theorem rotation_three_returns
    (p : TerminalPhase) :
    rotatePhase (rotatePhase (rotatePhase p)) = p := by
  cases p <;> rfl

/-- Negative control: even simultaneous closure from both sides cannot create
an inhabitant for an arbitrary proposition without already having one. -/
def TwoSidedClosureCreatesInhabitant : Prop :=
  ∀ P : Prop, ((P ↔ P) ∧ (P ↔ P)) → P

theorem two_sided_closure_does_not_create_inhabitant :
    ¬ TwoSidedClosureCreatesInhabitant := by
  intro H
  exact H False ⟨Iff.rfl, Iff.rfl⟩

/-- If the endpoint is inhabited, every phase of the 0/1/2 recurrence is. -/
theorem endpoint_inhabits_all_phases
    (h : Endpoint) :
    ∀ p : TerminalPhase, phasePayload p := by
  intro p
  exact (phase_payload_same p).2 h

#print axioms MCore.Real.P02TerminalConjunctureNucleus.two_sided_terminal_nucleus
#print axioms MCore.Real.P02TerminalConjunctureNucleus.closed_sides_iff_endpoint
#print axioms MCore.Real.P02TerminalConjunctureNucleus.rotation_preserves_terminal_signature
#print axioms MCore.Real.P02TerminalConjunctureNucleus.rotation_three_returns
#print axioms MCore.Real.P02TerminalConjunctureNucleus.two_sided_closure_does_not_create_inhabitant
#print axioms MCore.Real.P02TerminalConjunctureNucleus.endpoint_inhabits_all_phases

end P02TerminalConjunctureNucleus
end Real
end MCore
