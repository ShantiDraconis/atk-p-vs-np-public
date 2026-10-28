import MCore.Real.P01EvalCursorMachine
import MCore.Real.P01EvalCursorRoundTrip
import MCore.Real.MachineRunLemmas

namespace MCore
namespace Real
namespace P01PhysicalConsumeOneMachine

open CanonicalFinalProof
open P01EvalCursorMachine
open MachineRunLemmas

abbrev ConsumeState := Fin 8

def seekStart : ConsumeState := 0
def seekStack : ConsumeState := 1
def seekUnread : ConsumeState := 2
def eraseBit : ConsumeState := 3
def returnUnread : ConsumeState := 4
def returnFrames : ConsumeState := 5
def halt : ConsumeState := 6
def reject : ConsumeState := 7

/-- One fixed finite-control TM that performs the complete source-cursor
round trip and consumes exactly one source bit.  It starts and ends at the
canonical stack-end blank. -/
def consumeOneMachine : TM ConsumeState (Option Bool) :=
  { initial := seekStart
    blank := none
    transition := fun q symbol =>
      if q = seekStart then
        match symbol with
        | none => (seekStack, none, .left)
        | some b => (reject, some b, .stay)
      else if q = seekStack then
        match symbol with
        | some b => (seekStack, some b, .left)
        | none => (seekUnread, none, .left)
      else if q = seekUnread then
        match symbol with
        | some b => (seekUnread, some b, .left)
        | none => (eraseBit, none, .right)
      else if q = eraseBit then
        match symbol with
        | some _ => (returnUnread, none, .right)
        | none => (reject, none, .stay)
      else if q = returnUnread then
        match symbol with
        | some b => (returnUnread, some b, .right)
        | none => (returnFrames, none, .right)
      else if q = returnFrames then
        match symbol with
        | some b => (returnFrames, some b, .right)
        | none => (halt, none, .stay)
      else
        (q, symbol, .stay)
    halting := fun q => (q == halt) || (q == reject) }

@[simp] theorem consumeOneMachine_blank :
    consumeOneMachine.blank = none := rfl

@[simp] theorem seekStart_not_halting :
    consumeOneMachine.halting seekStart = false := by decide

@[simp] theorem seekStack_not_halting :
    consumeOneMachine.halting seekStack = false := by decide

@[simp] theorem seekUnread_not_halting :
    consumeOneMachine.halting seekUnread = false := by decide

@[simp] theorem eraseBit_not_halting :
    consumeOneMachine.halting eraseBit = false := by decide

@[simp] theorem returnUnread_not_halting :
    consumeOneMachine.halting returnUnread = false := by decide

@[simp] theorem returnFrames_not_halting :
    consumeOneMachine.halting returnFrames = false := by decide

@[simp] theorem halt_halting :
    consumeOneMachine.halting halt = true := by decide

def seekStackConfig
    (witness : BitString) (consumed : Nat) (unread : BitString)
    (remaining : BitString) (right : List (Option Bool)) :
    Configuration ConsumeState (Option Bool) :=
  match remaining with
  | [] =>
      { state := seekStack
        tape :=
          { left := unread.reverse.map some ++
              List.replicate consumed none ++ none :: witness.map some
            head := none
            right := right } }
  | b :: bs =>
      { state := seekStack
        tape :=
          { left := bs.map some ++ none :: unread.reverse.map some ++
              List.replicate consumed none ++ none :: witness.map some
            head := some b
            right := right } }

@[simp] theorem seekStackConfig_state
    (witness : BitString) (consumed : Nat) (unread remaining : BitString)
    (right : List (Option Bool)) :
    (seekStackConfig witness consumed unread remaining right).state = seekStack := by
  cases remaining <;> rfl

theorem start_to_seekStack
    (witness : BitString) (consumed : Nat) (unread frames : BitString)
    (padding : Nat) :
    consumeOneMachine.run 1
      { state := seekStart
        tape := evalCursorStackEndTape witness consumed unread frames padding } =
      seekStackConfig witness consumed unread frames
        (none :: List.replicate padding none) := by
  cases frames <;>
    simp [consumeOneMachine, seekStart, seekStack, seekUnread, eraseBit, returnUnread, returnFrames, halt, reject,
      evalCursorStackEndTape, seekStackConfig, TM.run, TM.step,
      Tape.write, Tape.move, List.append_assoc]

theorem seekStack_step_cons
    (witness : BitString) (consumed : Nat) (unread : BitString)
    (b : Bool) (bs : BitString) (right : List (Option Bool)) :
    consumeOneMachine.step
      (seekStackConfig witness consumed unread (b :: bs) right) =
      seekStackConfig witness consumed unread bs (some b :: right) := by
  cases bs <;>
    simp [seekStackConfig, consumeOneMachine, seekStart, seekStack,
      TM.step, Tape.write, Tape.move, List.append_assoc]

theorem seekStack_run
    (witness : BitString) (consumed : Nat) (unread remaining : BitString)
    (right : List (Option Bool)) :
    consumeOneMachine.run remaining.length
      (seekStackConfig witness consumed unread remaining right) =
      seekStackConfig witness consumed unread []
        (remaining.reverse.map some ++ right) := by
  induction remaining generalizing right with
  | nil => rfl
  | cons b bs ih =>
      rw [List.length_cons]
      rw [TM.run]
      rw [seekStackConfig_state]
      rw [seekStack_not_halting]
      rw [seekStack_step_cons]
      rw [ih]
      simp [List.reverse_cons, List.map_append, List.append_assoc]

def seekUnreadConfig
    (witness : BitString) (consumed : Nat)
    (remainingRev : BitString) (right : List (Option Bool)) :
    Configuration ConsumeState (Option Bool) :=
  match remainingRev with
  | [] =>
      match consumed with
      | 0 =>
          { state := seekUnread
            tape := { left := witness.map some, head := none, right := right } }
      | n + 1 =>
          { state := seekUnread
            tape :=
              { left := List.replicate n none ++ none :: witness.map some
                head := none
                right := right } }
  | b :: bs =>
      { state := seekUnread
        tape :=
          { left := bs.map some ++ List.replicate consumed none ++
              none :: witness.map some
            head := some b
            right := right } }

@[simp] theorem seekUnreadConfig_state
    (witness : BitString) (consumed : Nat)
    (remaining : BitString) (right : List (Option Bool)) :
    (seekUnreadConfig witness consumed remaining right).state = seekUnread := by
  cases remaining with
  | nil => cases consumed <;> rfl
  | cons b bs => rfl

theorem stackSeparator_to_seekUnread
    (witness : BitString) (consumed : Nat) (unread : BitString)
    (right : List (Option Bool)) :
    consumeOneMachine.run 1
      (seekStackConfig witness consumed unread [] right) =
      seekUnreadConfig witness consumed unread.reverse (none :: right) := by
  cases h : unread.reverse with
  | nil =>
      have hu : unread = [] := by
        simpa using congrArg List.reverse h
      subst unread
      cases consumed <;>
        simp [seekStackConfig, seekUnreadConfig, consumeOneMachine,
          seekStart, seekStack, seekUnread, eraseBit, returnUnread, returnFrames, halt, reject, TM.run, TM.step,
          Tape.write, Tape.move, List.replicate_succ, List.append_assoc]
  | cons b bs =>
      simp [seekStackConfig, seekUnreadConfig, consumeOneMachine,
        seekStart, seekStack, seekUnread, eraseBit, returnUnread, returnFrames, halt, reject, TM.run, TM.step,
        Tape.write, Tape.move, h, List.append_assoc]

theorem seekUnread_step_cons
    (witness : BitString) (consumed : Nat)
    (b : Bool) (bs : BitString) (right : List (Option Bool)) :
    consumeOneMachine.step
      (seekUnreadConfig witness consumed (b :: bs) right) =
      seekUnreadConfig witness consumed bs (some b :: right) := by
  cases bs with
  | nil =>
      cases consumed <;>
        simp [seekUnreadConfig, consumeOneMachine, seekStart, seekStack,
          seekUnread, TM.step, Tape.write, Tape.move,
          List.replicate_succ, List.append_assoc]
  | cons c cs =>
      simp [seekUnreadConfig, consumeOneMachine, seekStart, seekStack,
        seekUnread, TM.step, Tape.write, Tape.move, List.append_assoc]

theorem seekUnread_run
    (witness : BitString) (consumed : Nat)
    (remaining : BitString) (right : List (Option Bool)) :
    consumeOneMachine.run remaining.length
      (seekUnreadConfig witness consumed remaining right) =
      seekUnreadConfig witness consumed []
        (remaining.reverse.map some ++ right) := by
  induction remaining generalizing right with
  | nil => rfl
  | cons b bs ih =>
      rw [List.length_cons]
      rw [TM.run]
      rw [seekUnreadConfig_state]
      rw [seekUnread_not_halting]
      rw [seekUnread_step_cons]
      rw [ih]
      simp [List.reverse_cons, List.map_append, List.append_assoc]

theorem cursor_boundary_to_erase
    (witness : BitString) (consumed : Nat)
    (b : Bool) (bs frames : BitString) (padding : Nat) :
    consumeOneMachine.run 1
      (seekUnreadConfig witness consumed []
        ((b :: bs).map some ++ none :: frames.reverse.map some ++
          none :: List.replicate padding none)) =
      { state := eraseBit
        tape := evalCursorReadTape witness consumed (b :: bs) frames padding } := by
  cases consumed <;>
    simp [seekUnreadConfig, evalCursorReadTape, consumeOneMachine,
      seekStart, seekStack, seekUnread, eraseBit, returnUnread, returnFrames, halt, reject, TM.run, TM.step,
      Tape.write, Tape.move, List.replicate_succ, List.append_assoc]

def returnUnreadConfig
    (left : List (Option Bool)) (remaining frames : BitString)
    (padding : Nat) : Configuration ConsumeState (Option Bool) :=
  match remaining with
  | [] =>
      { state := returnUnread
        tape :=
          { left := left
            head := none
            right := frames.reverse.map some ++
              none :: List.replicate padding none } }
  | b :: bs =>
      { state := returnUnread
        tape :=
          { left := left
            head := some b
            right := bs.map some ++ none :: frames.reverse.map some ++
              none :: List.replicate padding none } }

@[simp] theorem returnUnreadConfig_state
    (left : List (Option Bool)) (remaining frames : BitString)
    (padding : Nat) :
    (returnUnreadConfig left remaining frames padding).state = returnUnread := by
  cases remaining <;> rfl

theorem erase_to_returnUnread
    (witness : BitString) (consumed : Nat)
    (b : Bool) (bs frames : BitString) (padding : Nat) :
    consumeOneMachine.run 1
      { state := eraseBit
        tape := evalCursorReadTape witness consumed (b :: bs) frames padding } =
      returnUnreadConfig
        (List.replicate (consumed + 1) none ++ none :: witness.map some)
        bs frames padding := by
  cases bs <;>
    simp [consumeOneMachine, seekStart, seekStack, seekUnread, eraseBit, returnUnread, returnFrames, halt, reject,
      evalCursorReadTape, returnUnreadConfig, TM.run, TM.step,
      Tape.write, Tape.move, List.replicate_succ, List.append_assoc]

theorem returnUnread_step_cons
    (left : List (Option Bool)) (b : Bool) (bs frames : BitString)
    (padding : Nat) :
    consumeOneMachine.step
      (returnUnreadConfig left (b :: bs) frames padding) =
      returnUnreadConfig (some b :: left) bs frames padding := by
  cases bs <;>
    simp [returnUnreadConfig, consumeOneMachine, seekStart, seekStack, seekUnread, eraseBit, returnUnread, returnFrames, halt, reject,
      TM.step, Tape.write, Tape.move, List.append_assoc]

theorem returnUnread_run
    (left : List (Option Bool)) (remaining frames : BitString)
    (padding : Nat) :
    consumeOneMachine.run remaining.length
      (returnUnreadConfig left remaining frames padding) =
      returnUnreadConfig (remaining.reverse.map some ++ left) []
        frames padding := by
  induction remaining generalizing left with
  | nil => rfl
  | cons b bs ih =>
      rw [List.length_cons]
      rw [TM.run]
      rw [returnUnreadConfig_state]
      rw [returnUnread_not_halting]
      rw [returnUnread_step_cons]
      rw [ih]
      simp [List.reverse_cons, List.map_append, List.append_assoc]

def returnFrameConfig
    (left : List (Option Bool)) (remainingRev : BitString) (padding : Nat) :
    Configuration ConsumeState (Option Bool) :=
  match remainingRev with
  | [] =>
      { state := returnFrames
        tape :=
          { left := left
            head := none
            right := List.replicate padding none } }
  | b :: bs =>
      { state := returnFrames
        tape :=
          { left := left
            head := some b
            right := bs.map some ++ none :: List.replicate padding none } }

@[simp] theorem returnFrameConfig_state
    (left : List (Option Bool)) (remainingRev : BitString) (padding : Nat) :
    (returnFrameConfig left remainingRev padding).state = returnFrames := by
  cases remainingRev <;> rfl

theorem sourceSeparator_to_returnFrames
    (left : List (Option Bool)) (frames : BitString) (padding : Nat) :
    consumeOneMachine.run 1
      (returnUnreadConfig left [] frames padding) =
      returnFrameConfig (none :: left) frames.reverse padding := by
  cases h : frames.reverse <;>
    simp [returnUnreadConfig, returnFrameConfig, consumeOneMachine,
      seekStart, seekStack, seekUnread, eraseBit, returnUnread, returnFrames, halt, reject, TM.run, TM.step, Tape.write, Tape.move,
      h, List.append_assoc]

theorem returnFrames_step_cons
    (left : List (Option Bool)) (b : Bool) (bs : BitString) (padding : Nat) :
    consumeOneMachine.step
      (returnFrameConfig left (b :: bs) padding) =
      returnFrameConfig (some b :: left) bs padding := by
  cases bs <;>
    simp [returnFrameConfig, consumeOneMachine, seekStart, seekStack, seekUnread, eraseBit, returnUnread, returnFrames, halt, reject,
      TM.step, Tape.write, Tape.move, List.append_assoc]

theorem returnFrames_run
    (left : List (Option Bool)) (remainingRev : BitString) (padding : Nat) :
    consumeOneMachine.run remainingRev.length
      (returnFrameConfig left remainingRev padding) =
      returnFrameConfig (remainingRev.reverse.map some ++ left) [] padding := by
  induction remainingRev generalizing left with
  | nil => rfl
  | cons b bs ih =>
      rw [List.length_cons]
      rw [TM.run]
      rw [returnFrameConfig_state]
      rw [returnFrames_not_halting]
      rw [returnFrames_step_cons]
      rw [ih]
      simp [List.reverse_cons, List.map_append, List.append_assoc]

theorem returnFrames_halt
    (left : List (Option Bool)) (padding : Nat) :
    consumeOneMachine.run 1 (returnFrameConfig left [] padding) =
      { state := halt
        tape :=
          { left := left
            head := none
            right := List.replicate padding none } } := by
  simp [returnFrameConfig, consumeOneMachine, seekStart, seekStack, seekUnread, eraseBit, returnUnread, returnFrames, halt, reject, halt,
    TM.run, TM.step, Tape.write, Tape.move]

/-- Exact machine-level result: one single fixed TM consumes one source bit,
preserves witness and frame stack, and restores the stack-end cursor. -/
theorem consumeOne_run
    (witness : BitString) (consumed : Nat)
    (b : Bool) (bs frames : BitString) (padding : Nat) :
    consumeOneMachine.run
      (2 * frames.length + 2 * bs.length + 7)
      { state := seekStart
        tape := evalCursorStackEndTape witness consumed (b :: bs) frames padding } =
      { state := halt
        tape := evalCursorStackEndTape witness (consumed + 1) bs frames padding } := by
  rw [show 2 * frames.length + 2 * bs.length + 7 =
      1 + (frames.length + (1 + ((b :: bs).length +
        (1 + (1 + (bs.length + (1 + (frames.length + 1)))))))) by
      simp
      omega]
  rw [run_add]
  rw [start_to_seekStack]
  rw [run_add]
  rw [seekStack_run]
  rw [run_add]
  rw [stackSeparator_to_seekUnread]
  rw [show (b :: bs).length = (b :: bs).reverse.length by simp]
  rw [run_add]
  rw [seekUnread_run]
  simp only [List.reverse_reverse]
  rw [run_add]
  have hErase :
      consumeOneMachine.run 1
        (seekUnreadConfig witness consumed []
          ((b :: bs).map some ++
            none :: (frames.reverse.map some ++
              none :: List.replicate padding none))) =
        { state := eraseBit
          tape := evalCursorReadTape witness consumed (b :: bs) frames padding } := by
    simpa [List.append_assoc] using
      cursor_boundary_to_erase witness consumed b bs frames padding
  rw [hErase]
  rw [run_add]
  rw [erase_to_returnUnread]
  rw [run_add]
  rw [returnUnread_run]
  rw [run_add]
  rw [sourceSeparator_to_returnFrames]
  rw [show frames.length = frames.reverse.length by simp]
  rw [run_add]
  rw [returnFrames_run]
  rw [returnFrames_halt]
  simp [evalCursorStackEndTape, List.reverse_reverse, List.map_append,
    List.replicate_succ, List.append_assoc]

theorem consumeOne_halts
    (witness : BitString) (consumed : Nat)
    (b : Bool) (bs frames : BitString) (padding : Nat) :
    consumeOneMachine.HaltsWithin
      (2 * frames.length + 2 * bs.length + 7)
      { state := seekStart
        tape := evalCursorStackEndTape witness consumed (b :: bs) frames padding } := by
  unfold TM.HaltsWithin
  rw [consumeOne_run]
  exact halt_halting

#print axioms MCore.Real.P01PhysicalConsumeOneMachine.consumeOne_run
#print axioms MCore.Real.P01PhysicalConsumeOneMachine.consumeOne_halts

end P01PhysicalConsumeOneMachine
end Real
end MCore
