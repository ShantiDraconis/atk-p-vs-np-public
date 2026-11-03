import MCore.Real.CanonicalSATParserMachine
import MCore.Real.CanonicalSATSlotLog
import MCore.Real.MachineRunLemmas

namespace MCore
namespace Real
namespace CanonicalSATParserInitProof

open CanonicalFinalProof
open CanonicalSATParserMachine
open CanonicalSATSlotLog

def forwardConfig
    (left : List (Option Bool))
    (bits : BitString) :
    Configuration (Fin 25) (Option Bool) :=
  match bits with
  | [] =>
      { state := 0
        tape := { left := left, head := none, right := [] } }
  | b :: bs =>
      { state := 0
        tape := { left := left, head := some b, right := bs.map some } }

@[simp] theorem forwardConfig_state
    (left : List (Option Bool))
    (bits : BitString) :
    (forwardConfig left bits).state = (0 : Fin 25) := by
  cases bits <;> rfl

@[simp] theorem parserMachine_not_halted_0 :
    parserMachine.halting (0 : Fin 25) = false := by decide

theorem forward_step_cons
    (left : List (Option Bool))
    (b : Bool)
    (bs : BitString) :
    parserMachine.step (forwardConfig left (b :: bs)) =
      forwardConfig (some b :: left) bs := by
  cases bs <;>
    simp [parserMachine, forwardConfig, TM.step, Tape.write, Tape.move]

theorem forward_scan_run
    (left : List (Option Bool))
    (bits : BitString) :
    parserMachine.run bits.length (forwardConfig left bits) =
      { state := (0 : Fin 25)
        tape :=
          { left := (bits.map some).reverse ++ left
            head := none
            right := [] } } := by
  induction bits generalizing left with
  | nil =>
      rfl
  | cons b bs ih =>
      rw [List.length_cons, TM.run]
      rw [forwardConfig_state, parserMachine_not_halted_0]
      rw [forward_step_cons]
      rw [ih (some b :: left)]
      simp [List.reverse_cons, List.append_assoc]

/-- State-3 rewind configuration. remaining is ordered from the current head
toward the left boundary: head first, then successive cells to the left. -/
def rewindConfig
    (remaining : List Bool)
    (right : List (Option Bool)) :
    Configuration (Fin 25) (Option Bool) :=
  match remaining with
  | [] =>
      { state := 3
        tape := { left := [], head := none, right := right } }
  | b :: bs =>
      { state := 3
        tape := { left := bs.map some, head := some b, right := right } }

@[simp] theorem rewindConfig_state
    (remaining : List Bool)
    (right : List (Option Bool)) :
    (rewindConfig remaining right).state = (3 : Fin 25) := by
  cases remaining <;> rfl

@[simp] theorem parserMachine_not_halted_3 :
    parserMachine.halting (3 : Fin 25) = false := by decide

theorem rewind_step_cons
    (b : Bool)
    (bs : List Bool)
    (right : List (Option Bool)) :
    parserMachine.step (rewindConfig (b :: bs) right) =
      rewindConfig bs (some b :: right) := by
  cases bs <;>
    simp [parserMachine, rewindConfig, TM.step, Tape.write, Tape.move]

theorem rewind_run
    (remaining : List Bool)
    (right : List (Option Bool)) :
    parserMachine.run remaining.length (rewindConfig remaining right) =
      rewindConfig []
        ((remaining.reverse.map some) ++ right) := by
  induction remaining generalizing right with
  | nil =>
      rfl
  | cons b bs ih =>
      rw [List.length_cons, TM.run]
      rw [rewindConfig_state, parserMachine_not_halted_3]
      rw [rewind_step_cons]
      rw [ih (some b :: right)]
      simp [List.reverse_cons, List.map_append, List.append_assoc]

def boundaryConfig
    (leftBlankCount : Nat)
    (unread : BitString)
    (log : SlotLog) :
    Configuration (Fin 25) (Option Bool) :=
  match unread with
  | [] =>
      { state := 4
        tape :=
          { left := List.replicate leftBlankCount none
            head := none
            right := log.map some } }
  | b :: bs =>
      { state := 4
        tape :=
          { left := List.replicate leftBlankCount none
            head := some b
            right := bs.map some ++ none :: log.map some } }

@[simp] theorem boundaryConfig_state
    (leftBlankCount : Nat)
    (unread : BitString)
    (log : SlotLog) :
    (boundaryConfig leftBlankCount unread log).state = (4 : Fin 25) := by
  cases unread <;> rfl

/-- Three fixed transitions after the right scan create the initial slot,
cross back over the delimiter, and enter the rewind state. -/
theorem setup_to_rewind
    (revBits : BitString) :
    parserMachine.run 3
      { state := (0 : Fin 25)
        tape := { left := revBits.map some, head := none, right := [] } } =
    rewindConfig revBits [none, some true] := by
  cases revBits <;>
    simp [parserMachine, rewindConfig, TM.run, TM.step, Tape.write, Tape.move]

/-- Rewind the reversed input and cross the left boundary into TAG_0. -/
theorem rewind_to_boundary
    (revBits : BitString) :
    parserMachine.run (revBits.length + 1)
      (rewindConfig revBits [none, some true]) =
    boundaryConfig 1 revBits.reverse initialSlotLog := by
  rw [MachineRunLemmas.run_add]
  rw [rewind_run]
  cases hrev : revBits.reverse with
  | nil =>
      simp [rewindConfig, boundaryConfig, initialSlotLog, parserMachine,
        TM.run, TM.step, Tape.write, Tape.move, hrev]
  | cons b bs =>
      simp [rewindConfig, boundaryConfig, initialSlotLog, parserMachine,
        TM.run, TM.step, Tape.write, Tape.move, hrev]

/-- The first 2*|bits|+4 steps deterministically create exactly one active
slot, rewind to the beginning, and enter TAG_0. -/
theorem parser_initializes
    (bits : BitString) :
    parserMachine.run (2 * bits.length + 4)
      (initialTMConfig parserMachine bits) =
    boundaryConfig 1 bits initialSlotLog := by
  have hInitial :
      initialTMConfig parserMachine bits = forwardConfig [] bits := by
    cases bits <;> rfl
  rw [hInitial]
  rw [show 2 * bits.length + 4 =
      bits.length + (3 + (bits.reverse.length + 1)) by
        simp
        omega]
  rw [MachineRunLemmas.run_add]
  rw [forward_scan_run]
  rw [MachineRunLemmas.run_add]
  simp only [List.append_nil]
  have hScanCfg :
      ({ state := (0 : Fin 25)
         tape :=
           { left := (bits.map some).reverse
             head := none
             right := [] } } :
        Configuration (Fin 25) (Option Bool)) =
      { state := (0 : Fin 25)
        tape :=
          { left := bits.reverse.map some
            head := none
            right := [] } } := by
    simp
  rw [hScanCfg]
  rw [setup_to_rewind (bits.reverse)]
  rw [rewind_to_boundary]
  simp

#print axioms MCore.Real.CanonicalSATParserInitProof.forward_scan_run
#print axioms MCore.Real.CanonicalSATParserInitProof.rewind_run
#print axioms MCore.Real.CanonicalSATParserInitProof.setup_to_rewind
#print axioms MCore.Real.CanonicalSATParserInitProof.rewind_to_boundary
#print axioms MCore.Real.CanonicalSATParserInitProof.parser_initializes

end CanonicalSATParserInitProof
end Real
end MCore
