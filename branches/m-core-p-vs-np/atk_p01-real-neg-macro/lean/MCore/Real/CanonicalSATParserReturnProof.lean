import MCore.Real.CanonicalSATParserMacroProof
import MCore.Real.CanonicalSATParserRewindProof

namespace MCore
namespace Real
namespace CanonicalSATParserReturnProof

open CanonicalFinalProof
open CanonicalSATParserMachine
open CanonicalSATParserHeadProof
open CanonicalSATParserWorkScanProof
open CanonicalSATParserMacroProof
open CanonicalSATParserRewindProof
open CanonicalSATSlotLog
open CanonicalSATSlotLogMachine

/-- State-20 configuration while returning left across the old work log.
remaining is ordered from the current head toward the source delimiter. -/
def binaryReturnConfig
    (remaining : SlotLog)
    (sourceLeft right : List (Option Bool)) :
    Configuration (Fin 25) (Option Bool) :=
  match remaining with
  | [] =>
      { state := 20
        tape := { left := sourceLeft, head := none, right := right } }
  | b :: bs =>
      { state := 20
        tape :=
          { left := bs.map some ++ none :: sourceLeft
            head := some b
            right := right } }

@[simp] theorem binaryReturnConfig_state
    (remaining : SlotLog)
    (sourceLeft right : List (Option Bool)) :
    (binaryReturnConfig remaining sourceLeft right).state = (20 : Fin 25) := by
  cases remaining <;> rfl

@[simp] theorem parser_not_halted_20 :
    parserMachine.halting (20 : Fin 25) = false := by decide

theorem binaryReturn_step_cons
    (b : Bool)
    (bs : SlotLog)
    (sourceLeft right : List (Option Bool)) :
    parserMachine.step
        (binaryReturnConfig (b :: bs) sourceLeft right) =
      binaryReturnConfig bs sourceLeft (some b :: right) := by
  cases bs <;>
    simp [binaryReturnConfig, parserMachine, TM.step, Tape.write, Tape.move,
      List.append_assoc]

/-- Scan exactly the remaining old-log cells back to the source delimiter. -/
theorem binaryReturn_run
    (remaining : SlotLog)
    (sourceLeft right : List (Option Bool)) :
    parserMachine.run remaining.length
        (binaryReturnConfig remaining sourceLeft right) =
      binaryReturnConfig []
        sourceLeft
        (remaining.reverse.map some ++ right) := by
  induction remaining generalizing right with
  | nil =>
      rfl
  | cons b bs ih =>
      rw [List.length_cons, TM.run]
      rw [binaryReturnConfig_state, parser_not_halted_20]
      rw [binaryReturn_step_cons]
      rw [ih (some b :: right)]
      simp [List.reverse_cons, List.map_append, List.append_assoc]

/-- The state-20 configuration produced by the binary append macro is exactly
the return-scan configuration for the reversed old log. -/
theorem afterEndMoveLeft_binary_eq_return
    (sourceLeft : List (Option Bool))
    (log : SlotLog) :
    afterEndMoveLeft 20 (none :: sourceLeft) log (some true) =
      binaryReturnConfig log.reverse sourceLeft [some true] := by
  cases hlog : log.reverse with
  | nil =>
      have hnil : log = [] := by
        simpa using congrArg List.reverse hlog
      subst log
      simp [afterEndMoveLeft, binaryReturnConfig, Tape.move]
  | cons b bs =>
      have hrev := congrArg List.reverse hlog
      have hshape : log = bs.reverse ++ [b] := by
        simpa using hrev
      subst log
      simp [afterEndMoveLeft, binaryReturnConfig, Tape.move,
        List.map_reverse, List.map_append, List.append_assoc]

/-- Complete the binary work-log return scan up to the source delimiter.
The right side now contains exactly pushSlot log. -/
theorem binary_afterEnd_to_delimiter
    (sourceLeft : List (Option Bool))
    (log : SlotLog) :
    parserMachine.run log.length
        (afterEndMoveLeft 20 (none :: sourceLeft) log (some true)) =
      binaryReturnConfig []
        sourceLeft
        ((pushSlot log).map some) := by
  rw [afterEndMoveLeft_binary_eq_return]
  have h := binaryReturn_run log.reverse sourceLeft [some true]
  simpa [pushSlot, List.map_append, List.append_assoc] using h

#print axioms MCore.Real.CanonicalSATParserReturnProof.binaryReturn_step_cons
#print axioms MCore.Real.CanonicalSATParserReturnProof.binaryReturn_run
#print axioms MCore.Real.CanonicalSATParserReturnProof.afterEndMoveLeft_binary_eq_return
#print axioms MCore.Real.CanonicalSATParserReturnProof.binary_afterEnd_to_delimiter

/-- State-21 configuration immediately after crossing the source/work
delimiter from the work-log side. -/
def binaryCheckConfig
    (last : Bool)
    (sourceTail right : List (Option Bool)) :
    Configuration (Fin 25) (Option Bool) :=
  { state := 21
    tape :=
      { left := sourceTail
        head := some last
        right := none :: right } }

@[simp] theorem binaryCheckConfig_state
    (last : Bool)
    (sourceTail right : List (Option Bool)) :
    (binaryCheckConfig last sourceTail right).state = (21 : Fin 25) := rfl

@[simp] theorem parser_not_halted_21 :
    parserMachine.halting (21 : Fin 25) = false := by decide

theorem binaryReturn_step_delimiter_nonempty
    (last : Bool)
    (sourceTail right : List (Option Bool)) :
    parserMachine.step
        (binaryReturnConfig [] (some last :: sourceTail) right) =
      binaryCheckConfig last sourceTail right := by
  simp [binaryReturnConfig, binaryCheckConfig, parserMachine,
    TM.step, Tape.write, Tape.move]

theorem binaryCheck_step_to_rewind
    (pad : Nat)
    (hpad : 0 < pad)
    (last : Bool)
    (rest : BitString)
    (log : SlotLog) :
    parserMachine.step
        (binaryCheckConfig last
          (rest.map some ++ List.replicate pad (none : Option Bool))
          ((pushSlot log).map some)) =
      rewindUnreadConfig rest [last] pad (pushSlot log) := by
  cases rest with
  | nil =>
      cases pad with
      | zero => omega
      | succ p =>
          simp [binaryCheckConfig, parserMachine, rewindUnreadConfig,
            TM.step, Tape.write, Tape.move, List.replicate_succ, pushSlot]
  | cons b bs =>
      simp [binaryCheckConfig, parserMachine, rewindUnreadConfig,
        TM.step, Tape.write, Tape.move, List.append_assoc, pushSlot]

/-- After the old log has been scanned back to its delimiter, two parser steps
cross that delimiter and enter state 22 with the unread suffix represented by
the existing rewind invariant. -/
theorem binary_delimiter_enters_rewind
    (pad : Nat)
    (hpad : 0 < pad)
    (last : Bool)
    (rest : BitString)
    (log : SlotLog) :
    parserMachine.run 2
        (binaryReturnConfig []
          (some last :: (rest.map some ++
            List.replicate pad (none : Option Bool)))
          ((pushSlot log).map some)) =
      rewindUnreadConfig rest [last] pad (pushSlot log) := by
  rw [TM.run]
  simp only [binaryReturnConfig_state, parser_not_halted_20,
    Bool.false_eq_true, if_false]
  rw [binaryReturn_step_delimiter_nonempty]
  rw [TM.run]
  simp only [binaryCheckConfig_state, parser_not_halted_21,
    Bool.false_eq_true, if_false]
  rw [binaryCheck_step_to_rewind pad hpad last rest log]
  rfl

/-- Complete the binary post-head macro: append one active slot, return across
the work log, cross the source delimiter, rewind the unread source, and re-enter
TAG_0 with the unread bitstring restored. -/
theorem binary_afterEnd_roundtrip
    (pad : Nat)
    (hpad : 0 < pad)
    (last : Bool)
    (rest : BitString)
    (log : SlotLog) :
    parserMachine.run
        (log.length + 2 + (rest.length + 1))
        (afterEndMoveLeft 20
          (none :: some last :: (rest.map some ++
            List.replicate pad (none : Option Bool)))
          log (some true)) =
      phaseConfig 4 pad
        (rest.reverse ++ [last])
        (pushSlot log) := by
  rw [show log.length + 2 + (rest.length + 1) =
      log.length + (2 + (rest.length + 1)) by omega]
  rw [MachineRunLemmas.run_add]
  rw [binary_afterEnd_to_delimiter
    (some last :: (rest.map some ++
      List.replicate pad (none : Option Bool))) log]
  rw [MachineRunLemmas.run_add]
  rw [binary_delimiter_enters_rewind pad hpad last rest log]
  exact rewindUnread_run rest [last] pad hpad (pushSlot log)

#print axioms MCore.Real.CanonicalSATParserReturnProof.binary_delimiter_enters_rewind
#print axioms MCore.Real.CanonicalSATParserReturnProof.binary_afterEnd_roundtrip

end CanonicalSATParserReturnProof
end Real
end MCore
