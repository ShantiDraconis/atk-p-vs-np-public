import MCore.Real.P01EncodedFrameTape
import MCore.Real.P01FullVerifierPhysicalStackV2
import MCore.Real.MachineRunLemmas

namespace MCore
namespace Real
namespace P01EvalCursorMachine

open CanonicalFinalProof
open P01EncodedFrameTape
open P01FullVerifierPhysicalStackV2
open MachineRunLemmas

/-- Stack-end representation for the streaming evaluator.

The current continuation frames occupy the ordinary V2 stack prefix.  The
unread source remains physically present, while already-consumed source cells
have been erased to blanks.  The source/witness separator is retained.

This gives a physical cursor without storing an unbounded source index in
finite control. -/
def evalCursorStackEndTape
    (witness : BitString)
    (consumed : Nat)
    (unread : BitString)
    (frameStack : BitString)
    (padding : Nat := 0) : Tape (Option Bool) :=
  { left :=
      frameStack.map some ++
        none ::
        unread.reverse.map some ++
        List.replicate consumed none ++
        none :: witness.map some
    head := none
    right := List.replicate padding none }

/-- At consumed=0 this is the ordinary V2 stack/source/witness layout. -/
theorem evalCursorStackEndTape_zero
    (witness unread frameStack : BitString)
    (padding : Nat) :
    evalCursorStackEndTape witness 0 unread frameStack padding =
      physicalStackV2Tape witness unread frameStack padding := by
  simp [evalCursorStackEndTape, physicalStackV2Tape, List.append_assoc]

/-- Physical tape after seeking from the stack end to the logical first unread
source bit.  The frame stack is now to the right of the source, in reverse
physical traversal order. -/
def evalCursorReadTape
    (witness : BitString)
    (consumed : Nat)
    (unread : BitString)
    (frameStack : BitString)
    (padding : Nat := 0) : Tape (Option Bool) :=
  match unread with
  | [] =>
      { left := List.replicate consumed none ++ none :: witness.map some
        head := none
        right :=
          frameStack.reverse.map some ++
            none :: List.replicate padding none }
  | b :: bs =>
      { left := List.replicate consumed none ++ none :: witness.map some
        head := some b
        right :=
          bs.map some ++
            none :: frameStack.reverse.map some ++
            none :: List.replicate padding none }

/-- Fixed finite-control cursor seeker.  It requires no source index:
1. enter the frame stack;
2. scan left to the stack/source separator;
3. scan left across the unread source (stored reversed from the stack end);
4. stop after one right move on the first unread source bit.

Already-consumed source cells are blanks, so the second encountered blank is
exactly the source cursor boundary. -/
inductive CursorSeekState where
  | start
  | scanStack
  | scanUnread
  | halt
  | reject
  deriving DecidableEq, Repr

def cursorSeekMachine : TM CursorSeekState (Option Bool) :=
  { initial := .start
    blank := none
    transition := fun q symbol =>
      match q with
      | .start =>
          match symbol with
          | none => (.scanStack, none, .left)
          | some b => (.reject, some b, .stay)
      | .scanStack =>
          match symbol with
          | some b => (.scanStack, some b, .left)
          | none => (.scanUnread, none, .left)
      | .scanUnread =>
          match symbol with
          | some b => (.scanUnread, some b, .left)
          | none => (.halt, none, .right)
      | .halt => (.halt, symbol, .stay)
      | .reject => (.reject, symbol, .stay)
    halting := fun q =>
      match q with
      | .halt => true
      | .reject => true
      | _ => false }

@[simp] theorem cursorSeekMachine_blank :
    cursorSeekMachine.blank = none := rfl

@[simp] theorem start_not_halting :
    cursorSeekMachine.halting .start = false := rfl

@[simp] theorem scanStack_not_halting :
    cursorSeekMachine.halting .scanStack = false := rfl

@[simp] theorem scanUnread_not_halting :
    cursorSeekMachine.halting .scanUnread = false := rfl

/-- Scan configuration while frame-stack bits remain under/left of the head. -/
def stackScanConfig
    (witness : BitString)
    (consumed : Nat)
    (unread : BitString)
    (remainingStack : BitString)
    (right : List (Option Bool)) :
    Configuration CursorSeekState (Option Bool) :=
  match remainingStack with
  | [] =>
      { state := .scanStack
        tape :=
          { left :=
              unread.reverse.map some ++
                List.replicate consumed none ++
                none :: witness.map some
            head := none
            right := right } }
  | b :: bs =>
      { state := .scanStack
        tape :=
          { left :=
              bs.map some ++
                none ::
                unread.reverse.map some ++
                List.replicate consumed none ++
                none :: witness.map some
            head := some b
            right := right } }

@[simp] theorem stackScanConfig_state
    (witness : BitString) (consumed : Nat) (unread remaining : BitString)
    (right : List (Option Bool)) :
    (stackScanConfig witness consumed unread remaining right).state =
      .scanStack := by
  cases remaining <;> rfl

theorem start_to_stackScan
    (witness : BitString)
    (consumed : Nat)
    (unread frameStack : BitString)
    (padding : Nat) :
    cursorSeekMachine.run 1
      { state := .start,
        tape :=
          evalCursorStackEndTape
            witness consumed unread frameStack padding } =
      stackScanConfig witness consumed unread frameStack
        (none :: List.replicate padding none) := by
  cases frameStack <;>
    simp [cursorSeekMachine, evalCursorStackEndTape, stackScanConfig,
      TM.run, TM.step, Tape.write, Tape.move, List.append_assoc]

theorem stackScan_step_cons
    (witness : BitString)
    (consumed : Nat)
    (unread : BitString)
    (b : Bool) (bs : BitString)
    (right : List (Option Bool)) :
    cursorSeekMachine.step
      (stackScanConfig witness consumed unread (b :: bs) right) =
      stackScanConfig witness consumed unread bs (some b :: right) := by
  cases bs <;>
    simp [stackScanConfig, cursorSeekMachine, TM.step, Tape.write, Tape.move,
      List.append_assoc]

theorem stackScan_run
    (witness : BitString)
    (consumed : Nat)
    (unread remaining : BitString)
    (right : List (Option Bool)) :
    cursorSeekMachine.run remaining.length
      (stackScanConfig witness consumed unread remaining right) =
      stackScanConfig witness consumed unread []
        (remaining.reverse.map some ++ right) := by
  induction remaining generalizing right with
  | nil => rfl
  | cons b bs ih =>
      rw [List.length_cons]
      simp only [TM.run, stackScanConfig_state, scanStack_not_halting,
        Bool.false_eq_true, if_false]
      rw [stackScan_step_cons]
      rw [ih]
      simp [List.reverse_cons, List.map_append, List.append_assoc]

/-- Source-scan configuration.  When no unread bit remains, the current head is
the cursor boundary blank.  Its left tail depends on whether that boundary is a
consumed cell or the original source/witness separator. -/
def unreadScanConfig
    (witness : BitString)
    (consumed : Nat)
    (remainingRev : BitString)
    (right : List (Option Bool)) :
    Configuration CursorSeekState (Option Bool) :=
  match remainingRev with
  | [] =>
      match consumed with
      | 0 =>
          { state := .scanUnread
            tape := { left := witness.map some, head := none, right := right } }
      | n + 1 =>
          { state := .scanUnread
            tape :=
              { left :=
                  List.replicate n none ++ none :: witness.map some
                head := none
                right := right } }
  | b :: bs =>
      { state := .scanUnread
        tape :=
          { left :=
              bs.map some ++
                List.replicate consumed none ++
                none :: witness.map some
            head := some b
            right := right } }

@[simp] theorem unreadScanConfig_state
    (witness : BitString) (consumed : Nat)
    (remaining : BitString) (right : List (Option Bool)) :
    (unreadScanConfig witness consumed remaining right).state =
      .scanUnread := by
  cases remaining with
  | nil => cases consumed <;> rfl
  | cons b bs => rfl

theorem stackSeparator_to_unreadScan
    (witness : BitString)
    (consumed : Nat)
    (unread : BitString)
    (right : List (Option Bool)) :
    cursorSeekMachine.run 1
      (stackScanConfig witness consumed unread [] right) =
      unreadScanConfig witness consumed unread.reverse (none :: right) := by
  cases h : unread.reverse with
  | nil =>
      have hu : unread = [] := by
        simpa using congrArg List.reverse h
      subst unread
      cases consumed <;>
        simp [stackScanConfig, unreadScanConfig, cursorSeekMachine,
          TM.run, TM.step, Tape.write, Tape.move, List.replicate_succ,
          List.append_assoc]
  | cons b bs =>
      simp [stackScanConfig, unreadScanConfig, cursorSeekMachine,
        TM.run, TM.step, Tape.write, Tape.move, h, List.append_assoc]

theorem unreadScan_step_cons
    (witness : BitString)
    (consumed : Nat)
    (b : Bool) (bs : BitString)
    (right : List (Option Bool)) :
    cursorSeekMachine.step
      (unreadScanConfig witness consumed (b :: bs) right) =
      unreadScanConfig witness consumed bs (some b :: right) := by
  cases bs with
  | nil =>
      cases consumed <;>
        simp [unreadScanConfig, cursorSeekMachine, TM.step, Tape.write,
          Tape.move, List.replicate_succ, List.append_assoc]
  | cons c cs =>
      simp [unreadScanConfig, cursorSeekMachine, TM.step, Tape.write,
        Tape.move, List.append_assoc]

theorem unreadScan_run
    (witness : BitString)
    (consumed : Nat)
    (remaining : BitString)
    (right : List (Option Bool)) :
    cursorSeekMachine.run remaining.length
      (unreadScanConfig witness consumed remaining right) =
      unreadScanConfig witness consumed []
        (remaining.reverse.map some ++ right) := by
  induction remaining generalizing right with
  | nil => rfl
  | cons b bs ih =>
      rw [List.length_cons]
      simp only [TM.run, unreadScanConfig_state, scanUnread_not_halting,
        Bool.false_eq_true, if_false]
      rw [unreadScan_step_cons]
      rw [ih]
      simp [List.reverse_cons, List.map_append, List.append_assoc]

theorem unreadBoundary_to_cursor
    (witness : BitString)
    (consumed : Nat)
    (unread frameStack : BitString)
    (padding : Nat) :
    cursorSeekMachine.run 1
      (unreadScanConfig witness consumed []
        (unread.map some ++
          none :: frameStack.reverse.map some ++
          none :: List.replicate padding none)) =
      { state := .halt,
        tape :=
          evalCursorReadTape
            witness consumed unread frameStack padding } := by
  cases unread with
  | nil =>
      cases consumed <;>
        simp [unreadScanConfig, evalCursorReadTape, cursorSeekMachine,
          TM.run, TM.step, Tape.write, Tape.move, List.replicate_succ,
          List.append_assoc]
  | cons b bs =>
      cases consumed <;>
        simp [unreadScanConfig, evalCursorReadTape, cursorSeekMachine,
          TM.run, TM.step, Tape.write, Tape.move, List.replicate_succ,
          List.append_assoc]

/-- Main cursor theorem: a fixed five-state machine reaches the logical first
unread source cell with no numeric cursor stored in finite control. -/
theorem cursorSeek_run
    (witness : BitString)
    (consumed : Nat)
    (unread frameStack : BitString)
    (padding : Nat) :
    cursorSeekMachine.run
      (frameStack.length + unread.length + 3)
      { state := .start,
        tape :=
          evalCursorStackEndTape
            witness consumed unread frameStack padding } =
      { state := .halt,
        tape :=
          evalCursorReadTape
            witness consumed unread frameStack padding } := by
  rw [show frameStack.length + unread.length + 3 =
      1 + (frameStack.length + (1 + (unread.length + 1))) by omega]
  rw [MachineRunLemmas.run_add]
  rw [start_to_stackScan]
  rw [MachineRunLemmas.run_add]
  rw [stackScan_run]
  rw [MachineRunLemmas.run_add]
  rw [stackSeparator_to_unreadScan]
  rw [show unread.length + 1 = unread.reverse.length + 1 by simp]
  rw [MachineRunLemmas.run_add]
  rw [unreadScan_run]
  simpa [List.reverse_reverse, List.append_assoc] using
    unreadBoundary_to_cursor witness consumed unread frameStack padding

#print axioms MCore.Real.P01EvalCursorMachine.cursorSeek_run

end P01EvalCursorMachine
end Real
end MCore
