import MCore.Real.CanonicalSATParserMachine
import MCore.Real.CanonicalSATSlotLog
import MCore.Real.MachineRunLemmas

namespace MCore
namespace Real
namespace CanonicalSATRecursiveParserInitProof

open CanonicalFinalProof
open CanonicalSATParserMachine
open CanonicalSATSlotLog

theorem nat_pow_two_init_local (x : Nat) : x ^ 2 = x * x := by
  rw [show (2 : Nat) = Nat.succ 1 by rfl]
  rw [Nat.pow_succ, Nat.pow_one]

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
@[simp] theorem parserMachine_not_halted_3 :
    parserMachine.halting (3 : Fin 25) = false := by decide

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
  | nil => rfl
  | cons b bs ih =>
      rw [List.length_cons, TM.run]
      rw [forwardConfig_state, parserMachine_not_halted_0]
      rw [forward_step_cons]
      rw [ih (some b :: left)]
      simp [List.reverse_cons, List.append_assoc]

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
      rewindConfig [] ((remaining.reverse.map some) ++ right) := by
  induction remaining generalizing right with
  | nil => rfl
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

def endConfig (bits : BitString) :
    Configuration (Fin 25) (Option Bool) :=
  { state := 0
    tape :=
      { left := bits.reverse.map some
        head := none
        right := [] } }

theorem setup_to_rewind
    (bits : BitString) :
    parserMachine.run 3 (endConfig bits) =
      rewindConfig bits.reverse [none, some true] := by
  cases h : bits.reverse with
  | nil =>
      simp [endConfig, h, parserMachine, rewindConfig, TM.run,
        TM.step, Tape.write, Tape.move]
  | cons b bs =>
      simp [endConfig, h, parserMachine, rewindConfig, TM.run,
        TM.step, Tape.write, Tape.move]

theorem rewind_finish
    (bits : BitString) :
    parserMachine.run (bits.length + 1)
      (rewindConfig bits.reverse [none, some true]) =
      boundaryConfig 1 bits initialSlotLog := by
  rw [show bits.length + 1 = bits.reverse.length + 1 by simp]
  rw [MachineRunLemmas.run_add parserMachine bits.reverse.length 1]
  rw [rewind_run]
  have hrr : bits.reverse.reverse = bits := List.reverse_reverse bits
  simp [hrr, boundaryConfig, initialSlotLog, rewindConfig, parserMachine,
    TM.run, TM.step, Tape.write, Tape.move]
  cases bits <;> simp [boundaryConfig, initialSlotLog]

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
      bits.length + (3 + (bits.length + 1)) by omega]
  rw [MachineRunLemmas.run_add parserMachine bits.length
      (3 + (bits.length + 1))]
  rw [forward_scan_run]
  have hEnd :
      { state := (0 : Fin 25)
        tape :=
          { left := (bits.map some).reverse ++ []
            head := none
            right := [] } } = endConfig bits := by
    simp [endConfig]
  rw [hEnd]
  rw [MachineRunLemmas.run_add parserMachine 3 (bits.length + 1)]
  rw [setup_to_rewind]
  exact rewind_finish bits

theorem parser_initialization_within_global_bound
    (bits : BitString) :
    2 * bits.length + 4 ≤ parserTimeBound bits.length := by
  let n := bits.length
  have h1 : 2 * n + 4 ≤ 4 * (n + 1) := by omega
  have h2 : 4 * (n + 1) ≤ 256 * (n + 1) := by
    exact Nat.mul_le_mul_right (n + 1) (by decide)
  have hpos : 1 ≤ n + 1 := by omega
  have hsq : n + 1 ≤ (n + 1) ^ 2 := by
    calc
      n + 1 = 1 * (n + 1) := by simp
      _ ≤ (n + 1) * (n + 1) :=
        Nat.mul_le_mul_right (n + 1) hpos
      _ = (n + 1) ^ 2 := by
        rw [nat_pow_two_init_local]
  have h3 : 256 * (n + 1) ≤ 256 * (n + 1) ^ 2 :=
    Nat.mul_le_mul_left 256 hsq
  exact Nat.le_trans h1 (Nat.le_trans h2 h3)

#print axioms MCore.Real.CanonicalSATRecursiveParserInitProof.forward_scan_run
#print axioms MCore.Real.CanonicalSATRecursiveParserInitProof.rewind_run
#print axioms MCore.Real.CanonicalSATRecursiveParserInitProof.parser_initializes
#print axioms MCore.Real.CanonicalSATRecursiveParserInitProof.parser_initialization_within_global_bound

end CanonicalSATRecursiveParserInitProof
end Real
end MCore
