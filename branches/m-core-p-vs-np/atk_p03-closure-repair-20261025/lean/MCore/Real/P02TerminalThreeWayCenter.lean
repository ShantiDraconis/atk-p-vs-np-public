import MCore.Real.P02TerminalConjunctureNucleus

namespace MCore
namespace Real
namespace P02TerminalThreeWayCenter

open CanonicalFinalProof
open P02DiagonalNoShortcut
open P02TerminalHabitantCycle
open P02TerminalConjunctureNucleus

/-- The unique center hit by all three terminal phases. -/
abbrev TerminalCenter : Prop := Endpoint

def phaseToCenter (p : TerminalPhase) : phasePayload p → TerminalCenter := by
  intro h
  exact (phase_payload_same p).1 h

def centerToPhase (p : TerminalPhase) : TerminalCenter → phasePayload p := by
  intro h
  exact (phase_payload_same p).2 h

theorem three_ways_hit_same_center :
    (phasePayload .zero ↔ TerminalCenter) ∧
    (phasePayload .one ↔ TerminalCenter) ∧
    (phasePayload .two ↔ TerminalCenter) := by
  exact ⟨phase_payload_same .zero,
    phase_payload_same .one,
    phase_payload_same .two⟩

/-- A Boolean orientation may label the center as true/false observation,
but does not alter the proposition carried by the center. -/
inductive CenterOrientation
  | falseSide
  | trueSide
  deriving DecidableEq, Repr

def orientedPayload : CenterOrientation → Prop
  | .falseSide => TerminalCenter
  | .trueSide => TerminalCenter

theorem orientation_preserves_center
    (o : CenterOrientation) :
    orientedPayload o ↔ TerminalCenter := by
  cases o <;> rfl

/-- The 0/1/2 phase and the Boolean orientation are independent labels on
the same terminal payload. -/
def conjuncturePayload
    (p : TerminalPhase)
    (o : CenterOrientation) : Prop :=
  phasePayload p ∧ orientedPayload o

theorem conjuncture_collapses_to_center
    (p : TerminalPhase)
    (o : CenterOrientation) :
    conjuncturePayload p o ↔ TerminalCenter := by
  constructor
  · intro h
    exact (phase_payload_same p).1 h.1
  · intro h
    exact ⟨(phase_payload_same p).2 h,
      (orientation_preserves_center o).2 h⟩

/-- Negative control: merely having three convergent labels and a Boolean
orientation cannot produce an arbitrary proposition without an inhabitant. -/
def ThreeWayCenterCreatesInhabitant : Prop :=
  ∀ P : Prop,
    ((P ↔ P) ∧ (P ↔ P) ∧ (P ↔ P)) →
    Bool →
    P

theorem three_way_center_does_not_create_inhabitant :
    ¬ ThreeWayCenterCreatesInhabitant := by
  intro H
  exact H False ⟨Iff.rfl, Iff.rfl, Iff.rfl⟩ false

#print axioms MCore.Real.P02TerminalThreeWayCenter.three_ways_hit_same_center
#print axioms MCore.Real.P02TerminalThreeWayCenter.orientation_preserves_center
#print axioms MCore.Real.P02TerminalThreeWayCenter.conjuncture_collapses_to_center
#print axioms MCore.Real.P02TerminalThreeWayCenter.three_way_center_does_not_create_inhabitant

end P02TerminalThreeWayCenter
end Real
end MCore
