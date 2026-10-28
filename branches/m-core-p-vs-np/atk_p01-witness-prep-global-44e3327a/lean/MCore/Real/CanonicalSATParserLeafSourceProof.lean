import MCore.Real.CanonicalSATParserLeafReturnProof
import MCore.Real.CanonicalSATParserRewindProof
import MCore.Real.MachineRunLemmas

namespace MCore
namespace Real
namespace CanonicalSATParserLeafSourceProof

open CanonicalFinalProof
open CanonicalSATParserMachine
open CanonicalSATParserLeafReturnProof
open CanonicalSATParserRewindProof
open CanonicalSATParserHeadProof
open CanonicalSATSlotLog
open MachineRunLemmas

/-- Canonical accepting configuration reached when a leaf consumes the last
active slot and no unread source bit remains. -/
def leafAcceptConfig
    (pad : Nat)
    (right : List (Option Bool)) :
    Configuration (Fin 25) (Option Bool) :=
  { state := 23
    tape :=
      Tape.move none .left
        { left := List.replicate pad none
          head := none
          right := right } }

/-- Canonical rejecting configuration for an exhausted source with outstanding
work still present. -/
def leafRejectConfig
    (pad : Nat)
    (right : List (Option Bool)) :
    Configuration (Fin 25) (Option Bool) :=
  { state := 24
    tape :=
      Tape.move none .left
        { left := List.replicate pad none
          head := none
          right := right } }

theorem leaf16_exhausted_accepts
    (pad : Nat)
    (hpad : 0 < pad)
    (right : List (Option Bool)) :
    parserMachine.step
        (leafSourceCheckConfig 16 (List.replicate pad none) right) =
      leafAcceptConfig pad right := by
  cases pad with
  | zero => omega
  | succ p =>
      simp [leafSourceCheckConfig, leafAcceptConfig, parserMachine,
        TM.step, Tape.write, Tape.move, List.replicate_succ]

theorem leaf17_exhausted_rejects
    (pad : Nat)
    (hpad : 0 < pad)
    (right : List (Option Bool)) :
    parserMachine.step
        (leafSourceCheckConfig 17 (List.replicate pad none) right) =
      leafRejectConfig pad right := by
  cases pad with
  | zero => omega
  | succ p =>
      simp [leafSourceCheckConfig, leafRejectConfig, parserMachine,
        TM.step, Tape.write, Tape.move, List.replicate_succ]

/-- If unread source remains and an older active slot still exists, state 17
enters the already-certified source rewind invariant in one machine step. -/
theorem leaf17_step_to_rewind
    (pad : Nat)
    (hpad : 0 < pad)
    (last : Bool)
    (rest : BitString)
    (log : SlotLog) :
    parserMachine.step
        (leafSourceCheckConfig 17
          (some last ::
            (rest.map some ++ List.replicate pad (none : Option Bool)))
          (log.map some)) =
      rewindUnreadConfig rest [last] pad log := by
  cases rest with
  | nil =>
      cases pad with
      | zero => omega
      | succ p =>
          simp [leafSourceCheckConfig, rewindUnreadConfig, parserMachine,
            TM.step, Tape.write, Tape.move, List.replicate_succ]
  | cons b bs =>
      simp [leafSourceCheckConfig, rewindUnreadConfig, parserMachine,
        TM.step, Tape.write, Tape.move, List.append_assoc]

/-- Full source-return macro after a successful leaf pop when both unread input
and at least one older active slot remain. -/
theorem leaf17_roundtrip_to_phase
    (pad : Nat)
    (hpad : 0 < pad)
    (last : Bool)
    (rest : BitString)
    (log : SlotLog) :
    parserMachine.run (rest.length + 2)
        (leafSourceCheckConfig 17
          (some last ::
            (rest.map some ++ List.replicate pad (none : Option Bool)))
          (log.map some)) =
      phaseConfig 4 pad (rest.reverse ++ [last]) log := by
  rw [show rest.length + 2 = 1 + (rest.length + 1) by omega]
  rw [MachineRunLemmas.run_add]
  have hhalt :
      parserMachine.halting
        (leafSourceCheckConfig 17
          (some last ::
            (rest.map some ++ List.replicate pad (none : Option Bool)))
          (log.map some)).state = false := by
    change parserMachine.halting (17 : Fin 25) = false
    decide
  have hrun1 :
      parserMachine.run 1
        (leafSourceCheckConfig 17
          (some last ::
            (rest.map some ++ List.replicate pad (none : Option Bool)))
          (log.map some)) =
      parserMachine.step
        (leafSourceCheckConfig 17
          (some last ::
            (rest.map some ++ List.replicate pad (none : Option Bool)))
          (log.map some)) := by
    rw [TM.run]
    rw [hhalt]
    rfl
  rw [hrun1]
  rw [leaf17_step_to_rewind pad hpad last rest log]
  exact rewindUnread_run rest [last] pad hpad log

@[simp] theorem leafAcceptConfig_halted
    (pad : Nat)
    (right : List (Option Bool)) :
    parserMachine.halting (leafAcceptConfig pad right).state = true := by
  simp [leafAcceptConfig, parserMachine]

@[simp] theorem leafRejectConfig_halted
    (pad : Nat)
    (right : List (Option Bool)) :
    parserMachine.halting (leafRejectConfig pad right).state = true := by
  simp [leafRejectConfig, parserMachine]

#print axioms MCore.Real.CanonicalSATParserLeafSourceProof.leaf16_exhausted_accepts
#print axioms MCore.Real.CanonicalSATParserLeafSourceProof.leaf17_exhausted_rejects
#print axioms MCore.Real.CanonicalSATParserLeafSourceProof.leaf17_step_to_rewind
#print axioms MCore.Real.CanonicalSATParserLeafSourceProof.leaf17_roundtrip_to_phase

end CanonicalSATParserLeafSourceProof
end Real
end MCore
