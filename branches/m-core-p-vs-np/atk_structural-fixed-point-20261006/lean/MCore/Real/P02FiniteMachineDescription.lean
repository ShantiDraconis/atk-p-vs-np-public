import MCore.Real.P02ClockBridgeMaterial

namespace MCore
namespace Real
namespace P02FiniteMachineDescription

open CanonicalFinalProof

/--
Finite operational description of the hardened deterministic candidate.
The clock is deliberately excluded: it is handled separately by
P02ClockBridgeMaterial.
-/
structure EncodedMachine where
  stateCount : Nat
  initial : Fin (stateCount + 1)
  transition :
    Fin (stateCount + 1) →
      Option Bool →
        Fin (stateCount + 1) × Option Bool × Direction
  halting : Fin (stateCount + 1) → Bool
  accepting : Fin (stateCount + 1) → Bool

def EncodedMachine.toTM (enc : EncodedMachine) :
    TM (Fin (enc.stateCount + 1)) (Option Bool) :=
  { initial := enc.initial
    blank := none
    transition := enc.transition
    halting := enc.halting }

def projectFiniteMachine (M : PolyDTMCandidate) : EncodedMachine :=
  { stateCount := M.stateCount
    initial := M.machine.initial
    transition := M.machine.transition
    halting := M.machine.halting
    accepting := M.accepting }

theorem projectFiniteMachine_stateCount
    (M : PolyDTMCandidate) :
    (projectFiniteMachine M).stateCount = M.stateCount := by
  rfl

theorem projectFiniteMachine_accepting
    (M : PolyDTMCandidate) :
    (projectFiniteMachine M).accepting = M.accepting := by
  rfl

theorem projectFiniteMachine_toTM
    (M : PolyDTMCandidate) :
    (projectFiniteMachine M).toTM = M.machine := by
  cases M with
  | mk stateCount machine blank_none accepting timeBound time_poly =>
      cases machine with
      | mk initial blank transition halting =>
          simp only [projectFiniteMachine, EncodedMachine.toTM] at *
          cases blank_none
          rfl

theorem projectFiniteMachine_step
    (M : PolyDTMCandidate)
    (cfg : Configuration (Fin (M.stateCount + 1)) (Option Bool)) :
    (projectFiniteMachine M).toTM.step cfg =
      M.machine.step cfg := by
  rw [projectFiniteMachine_toTM]

theorem projectFiniteMachine_run
    (M : PolyDTMCandidate)
    (k : Nat)
    (cfg : Configuration (Fin (M.stateCount + 1)) (Option Bool)) :
    (projectFiniteMachine M).toTM.run k cfg =
      M.machine.run k cfg := by
  rw [projectFiniteMachine_toTM]

theorem projectFiniteMachine_haltsWithin
    (M : PolyDTMCandidate)
    (k : Nat)
    (cfg : Configuration (Fin (M.stateCount + 1)) (Option Bool)) :
    (projectFiniteMachine M).toTM.HaltsWithin k cfg ↔
      M.machine.HaltsWithin k cfg := by
  rw [projectFiniteMachine_toTM]

#print axioms MCore.Real.P02FiniteMachineDescription.projectFiniteMachine_toTM
#print axioms MCore.Real.P02FiniteMachineDescription.projectFiniteMachine_run
#print axioms MCore.Real.P02FiniteMachineDescription.projectFiniteMachine_haltsWithin

end P02FiniteMachineDescription
end Real
end MCore
