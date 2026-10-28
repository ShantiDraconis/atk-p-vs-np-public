import MCore.Real.P01EvalCursorMachine
import MCore.Real.MachineRunLemmas

namespace MCore
namespace Real
namespace P01EvalCursorRoundTrip

open CanonicalFinalProof
open P01EvalCursorMachine
open MachineRunLemmas

inductive CursorReturnState where
  | erase
  | scanUnread
  | scanFrames
  | halt
  | reject
  deriving DecidableEq, Repr

/-- Fixed-control return machine.  Starting on the currently unread source bit,
it erases that bit, scans right across the remaining unread source, crosses the
source/frame separator, scans across the physically reversed frame stack, and
halts on the stack-end blank. -/
def cursorReturnMachine : TM CursorReturnState (Option Bool) :=
  { initial := .erase
    blank := none
    transition := fun q symbol =>
      match q with
      | .erase =>
          match symbol with
          | some _ => (.scanUnread, none, .right)
          | none => (.reject, none, .stay)
      | .scanUnread =>
          match symbol with
          | some b => (.scanUnread, some b, .right)
          | none => (.scanFrames, none, .right)
      | .scanFrames =>
          match symbol with
          | some b => (.scanFrames, some b, .right)
          | none => (.halt, none, .stay)
      | .halt => (.halt, symbol, .stay)
      | .reject => (.reject, symbol, .stay)
    halting := fun q =>
      match q with
      | .halt => true
      | .reject => true
      | _ => false }

@[simp] theorem erase_not_halting :
    cursorReturnMachine.halting .erase = false := rfl

@[simp] theorem scanUnread_not_halting :
    cursorReturnMachine.halting .scanUnread = false := rfl

@[simp] theorem scanFrames_not_halting :
    cursorReturnMachine.halting .scanFrames = false := rfl

/-- Configuration while scanning the unread source to the right. -/
def unreadReturnConfig
    (left : List (Option Bool))
    (remaining frameStack : BitString)
    (padding : Nat) :
    Configuration CursorReturnState (Option Bool) :=
  match remaining with
  | [] =>
      { state := .scanUnread
        tape :=
          { left := left
            head := none
            right :=
              frameStack.reverse.map some ++
                none :: List.replicate padding none } }
  | b :: bs =>
      { state := .scanUnread
        tape :=
          { left := left
            head := some b
            right :=
              bs.map some ++
                none :: frameStack.reverse.map some ++
                none :: List.replicate padding none } }

@[simp] theorem unreadReturnConfig_state
    (left : List (Option Bool))
    (remaining frameStack : BitString)
    (padding : Nat) :
    (unreadReturnConfig left remaining frameStack padding).state =
      .scanUnread := by
  cases remaining <;> rfl

/-- Erasing the consumed source bit enters the unread-tail scan with one more
blank recorded in the consumed region. -/
theorem erase_to_unread
    (witness : BitString)
    (consumed : Nat)
    (b : Bool) (bs frameStack : BitString)
    (padding : Nat) :
    cursorReturnMachine.run 1
      { state := .erase
        tape :=
          evalCursorReadTape
            witness consumed (b :: bs) frameStack padding } =
      unreadReturnConfig
        (List.replicate (consumed + 1) none ++ none :: witness.map some)
        bs frameStack padding := by
  cases bs <;>
    simp [cursorReturnMachine, evalCursorReadTape, unreadReturnConfig,
      TM.run, TM.step, Tape.write, Tape.move, List.replicate_succ,
      List.append_assoc]

theorem unreadReturn_step_cons
    (left : List (Option Bool))
    (b : Bool) (bs frameStack : BitString)
    (padding : Nat) :
    cursorReturnMachine.step
      (unreadReturnConfig left (b :: bs) frameStack padding) =
      unreadReturnConfig (some b :: left) bs frameStack padding := by
  cases bs <;>
    simp [unreadReturnConfig, cursorReturnMachine, TM.step,
      Tape.write, Tape.move, List.append_assoc]

/-- Scanning the entire unread tail moves it, in reverse tape order, to the
left side while preserving all symbols. -/
theorem unreadReturn_run
    (left : List (Option Bool))
    (remaining frameStack : BitString)
    (padding : Nat) :
    cursorReturnMachine.run remaining.length
      (unreadReturnConfig left remaining frameStack padding) =
      unreadReturnConfig
        (remaining.reverse.map some ++ left)
        [] frameStack padding := by
  induction remaining generalizing left with
  | nil =>
      rfl
  | cons b bs ih =>
      rw [List.length_cons]
      rw [TM.run]
      rw [unreadReturnConfig_state]
      rw [scanUnread_not_halting]
      rw [unreadReturn_step_cons]
      rw [ih]
      simp [List.reverse_cons, List.map_append, List.append_assoc]

/-- Configuration while scanning the physical reversed frame stack to the
stack-end blank. -/
def frameReturnConfig
    (left : List (Option Bool))
    (remainingRev : BitString)
    (padding : Nat) :
    Configuration CursorReturnState (Option Bool) :=
  match remainingRev with
  | [] =>
      { state := .scanFrames
        tape :=
          { left := left
            head := none
            right := List.replicate padding none } }
  | b :: bs =>
      { state := .scanFrames
        tape :=
          { left := left
            head := some b
            right := bs.map some ++ none :: List.replicate padding none } }

@[simp] theorem frameReturnConfig_state
    (left : List (Option Bool))
    (remainingRev : BitString)
    (padding : Nat) :
    (frameReturnConfig left remainingRev padding).state = .scanFrames := by
  cases remainingRev <;> rfl

/-- Crossing the source/frame separator enters the frame scan. -/
theorem sourceSeparator_to_frames
    (left : List (Option Bool))
    (frameStack : BitString)
    (padding : Nat) :
    cursorReturnMachine.run 1
      (unreadReturnConfig left [] frameStack padding) =
      frameReturnConfig (none :: left) frameStack.reverse padding := by
  cases h : frameStack.reverse <;>
    simp [unreadReturnConfig, frameReturnConfig, cursorReturnMachine,
      TM.run, TM.step, Tape.write, Tape.move, h, List.append_assoc]

theorem frameReturn_step_cons
    (left : List (Option Bool))
    (b : Bool) (bs : BitString)
    (padding : Nat) :
    cursorReturnMachine.step
      (frameReturnConfig left (b :: bs) padding) =
      frameReturnConfig (some b :: left) bs padding := by
  cases bs <;>
    simp [frameReturnConfig, cursorReturnMachine, TM.step,
      Tape.write, Tape.move, List.append_assoc]

theorem frameReturn_run
    (left : List (Option Bool))
    (remainingRev : BitString)
    (padding : Nat) :
    cursorReturnMachine.run remainingRev.length
      (frameReturnConfig left remainingRev padding) =
      frameReturnConfig
        (remainingRev.reverse.map some ++ left)
        [] padding := by
  induction remainingRev generalizing left with
  | nil =>
      rfl
  | cons b bs ih =>
      rw [List.length_cons]
      rw [TM.run]
      rw [frameReturnConfig_state]
      rw [scanFrames_not_halting]
      rw [frameReturn_step_cons]
      rw [ih]
      simp [List.reverse_cons, List.map_append, List.append_assoc]

theorem frameReturn_halt
    (left : List (Option Bool))
    (padding : Nat) :
    cursorReturnMachine.run 1
      (frameReturnConfig left [] padding) =
      { state := .halt
        tape :=
          { left := left
            head := none
            right := List.replicate padding none } } := by
  simp [frameReturnConfig, cursorReturnMachine, TM.run, TM.step,
    Tape.write, Tape.move]

/-- Main return theorem.  Together with `cursorSeek_run`, this gives the
physical round-trip needed by the streaming evaluator: after consuming exactly
one source bit, the fixed return machine restores the stack-end representation
with the consumed counter incremented by one and all frame/witness data
preserved. -/
theorem cursorReturn_run
    (witness : BitString)
    (consumed : Nat)
    (b : Bool) (bs frameStack : BitString)
    (padding : Nat) :
    cursorReturnMachine.run
      (bs.length + frameStack.length + 3)
      { state := .erase
        tape :=
          evalCursorReadTape
            witness consumed (b :: bs) frameStack padding } =
      { state := .halt
        tape :=
          evalCursorStackEndTape
            witness (consumed + 1) bs frameStack padding } := by
  rw [show bs.length + frameStack.length + 3 =
      1 + (bs.length + (1 + (frameStack.length + 1))) by omega]
  rw [MachineRunLemmas.run_add]
  rw [erase_to_unread]
  rw [MachineRunLemmas.run_add]
  rw [unreadReturn_run]
  rw [MachineRunLemmas.run_add]
  rw [sourceSeparator_to_frames]
  rw [show frameStack.length + 1 = frameStack.reverse.length + 1 by simp]
  rw [MachineRunLemmas.run_add]
  rw [frameReturn_run]
  rw [frameReturn_halt]
  simp [evalCursorStackEndTape, List.reverse_reverse, List.map_append,
    List.replicate_succ, List.append_assoc]

#print axioms MCore.Real.P01EvalCursorRoundTrip.cursorReturn_run

end P01EvalCursorRoundTrip
end Real
end MCore
