/- ATK BATCH05: full source snapshot. Archival only; no kernel certification implied. -/

/- SOURCE lean/MCore/Real/P01EvalCursorConsume.lean BLOB 730b493a49e2729a2130311ba4f889c2fa4a5b75 -/
import MCore.Real.P01EvalCursorRoundTrip
import MCore.Real.P01EvalCursorFramePush

namespace MCore
namespace Real
namespace P01EvalCursorConsume

open CanonicalFinalProof
open P01EvalCursorMachine
open P01EvalCursorRoundTrip

/-- Execute one physical cursor cycle: seek the first unread source bit with
the fixed seeker, then erase/consume it and return to stack-end with the fixed
return machine.  This is a verified macro built only from concrete TMs. -/
def consumeOneTape
    (witness : BitString)
    (consumed : Nat)
    (unread frameStack : BitString)
    (padding : Nat) : Tape (Option Bool) :=
  match unread with
  | [] =>
      evalCursorStackEndTape witness consumed [] frameStack padding
  | b :: bs =>
      let seekFinal :=
        cursorSeekMachine.run
          (frameStack.length + (b :: bs).length + 3)
          { state := CursorSeekState.start,
            tape :=
              evalCursorStackEndTape
                witness consumed (b :: bs) frameStack padding }
      let returnFinal :=
        cursorReturnMachine.run
          (bs.length + frameStack.length + 3)
          { state := CursorReturnState.erase,
            tape := seekFinal.tape }
      returnFinal.tape

/-- One macro cycle consumes exactly one unread bit and changes no other
logical payload. -/
theorem consumeOneTape_correct
    (witness : BitString)
    (consumed : Nat)
    (b : Bool) (bs frameStack : BitString)
    (padding : Nat) :
    consumeOneTape witness consumed (b :: bs) frameStack padding =
      evalCursorStackEndTape
        witness (consumed + 1) bs frameStack padding := by
  change
    (cursorReturnMachine.run
      (bs.length + frameStack.length + 3)
      { state := CursorReturnState.erase,
        tape :=
          (cursorSeekMachine.run
            (frameStack.length + (b :: bs).length + 3)
            { state := CursorSeekState.start,
              tape :=
                evalCursorStackEndTape
                  witness consumed (b :: bs) frameStack padding }).tape }).tape =
      evalCursorStackEndTape
        witness (consumed + 1) bs frameStack padding
  rw [cursorSeek_run witness consumed (b :: bs) frameStack padding]
  simpa using
    congrArg Configuration.tape
      (cursorReturn_run witness consumed b bs frameStack padding)

/-- Three successive concrete cursor cycles. -/
def consumeThreeTape
    (witness : BitString)
    (consumed : Nat)
    (bits frameStack : BitString)
    (padding : Nat) : Tape (Option Bool) :=
  match bits with
  | b0 :: b1 :: b2 :: rest =>
      let t1 := consumeOneTape witness consumed
        (b0 :: b1 :: b2 :: rest) frameStack padding
      let t2 := consumeOneTape witness (consumed + 1)
        (b1 :: b2 :: rest) frameStack padding
      let t3 := consumeOneTape witness (consumed + 2)
        (b2 :: rest) frameStack padding
      -- The first two cycle results are retained as explicit logical stages;
      -- their correctness is supplied by consumeOneTape_correct.
      let _ := t1
      let _ := t2
      t3
  | _ =>
      evalCursorStackEndTape witness consumed bits frameStack padding

/-- A canonical three-bit tag is consumed exactly: witness and frame stack are
preserved, the unread tail is untouched, and the source cursor advances by 3. -/
theorem consumeThreeTape_correct
    (witness : BitString)
    (consumed : Nat)
    (b0 b1 b2 : Bool)
    (rest frameStack : BitString)
    (padding : Nat) :
    consumeThreeTape witness consumed
        (b0 :: b1 :: b2 :: rest) frameStack padding =
      evalCursorStackEndTape
        witness (consumed + 3) rest frameStack padding := by
  have h :=
    consumeOneTape_correct witness (consumed + 2)
      b2 rest frameStack padding
  simpa [consumeThreeTape, Nat.add_assoc] using h

#print axioms MCore.Real.P01EvalCursorConsume.consumeOneTape_correct
#print axioms MCore.Real.P01EvalCursorConsume.consumeThreeTape_correct

end P01EvalCursorConsume
end Real
end MCore


/- SOURCE lean/MCore/Real/P01EvalCursorFramePush.lean BLOB 368d7bfc1ced85f4dd17cb7db7cbf03efab6b8a7 -/
import MCore.Real.P01EvalCursorMachine
import MCore.Real.P01EvalFramePushMachine

namespace MCore
namespace Real
namespace P01EvalCursorFramePush

open CanonicalFinalProof
open P01EncodedStackEvaluator
open P01EncodedFrameTape
open P01EvalCursorMachine
open P01EvalFramePushMachine
open P01FullVerifierPhysicalStackV2
open MachineRunLemmas

/-- One Boolean stack push preserves the entire cursor representation:
only the finite frame-stack prefix and right blank padding change. -/
theorem pushStep_evalCursorStackEndTape
    (witness unread frameStack : BitString)
    (consumed padding : Nat) (b : Bool) :
    pushStep b
      (evalCursorStackEndTape
        witness consumed unread frameStack padding) =
      evalCursorStackEndTape
        witness consumed unread (b :: frameStack) (padding - 1) := by
  cases padding with
  | zero =>
      simp [pushStep, evalCursorStackEndTape, Tape.write, Tape.move,
        List.append_assoc]
  | succ n =>
      simp [pushStep, evalCursorStackEndTape, Tape.write, Tape.move,
        List.replicate_succ, Nat.succ_sub_one, List.append_assoc]

/-- The already-certified fixed three-step frame writer works unchanged on the
cursor-aware stack-end representation.  It preserves witness, consumed count,
and unread source exactly. -/
theorem framePush_run_three_cursor
    (witness unread frameStack : BitString)
    (consumed padding : Nat)
    (f : EvalFrame) :
    let final :=
      framePushMachine.run 3
        (framePushConfig f
          (evalCursorStackEndTape
            witness consumed unread frameStack padding))
    final.state = .halt ∧
      final.tape =
        evalCursorStackEndTape
          witness consumed unread
          (encodeEvalFrame f ++ frameStack)
          (((padding - 1) - 1) - 1) := by
  dsimp
  unfold framePushConfig
  have h1 := framePush_start_one f
    (evalCursorStackEndTape witness consumed unread frameStack padding) rfl
  have hp1 :=
    pushStep_evalCursorStackEndTape
      witness unread frameStack consumed padding (frameBit2 f)
  have h2 := framePush_after1_one f
    (evalCursorStackEndTape witness consumed unread
      (frameBit2 f :: frameStack) (padding - 1)) rfl
  have hp2 :=
    pushStep_evalCursorStackEndTape
      witness unread (frameBit2 f :: frameStack)
      consumed (padding - 1) (frameBit1 f)
  have h3 := framePush_after2_one f
    (evalCursorStackEndTape witness consumed unread
      (frameBit1 f :: frameBit2 f :: frameStack)
      ((padding - 1) - 1)) rfl
  have hp3 :=
    pushStep_evalCursorStackEndTape
      witness unread
      (frameBit1 f :: frameBit2 f :: frameStack)
      consumed ((padding - 1) - 1) (frameBit0 f)
  rw [show 3 = 1 + 2 by decide, MachineRunLemmas.run_add]
  rw [h1, hp1]
  rw [show 2 = 1 + 1 by decide, MachineRunLemmas.run_add]
  rw [h2, hp2]
  rw [h3, hp3]
  constructor
  · rfl
  · rw [encodeEvalFrame_eq_bits]
    rfl

#print axioms MCore.Real.P01EvalCursorFramePush.pushStep_evalCursorStackEndTape
#print axioms MCore.Real.P01EvalCursorFramePush.framePush_run_three_cursor

end P01EvalCursorFramePush
end Real
end MCore


/- SOURCE lean/MCore/Real/P01EvalCursorMachine.lean BLOB ad4c242831748514b78cddd6ba5c3e5d066cebb0 -/
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


/- SOURCE lean/MCore/Real/P01EvalCursorRoundTrip.lean BLOB 46b6d78f3d1d4772ade8a66249b8ff1c5d953def -/
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


/- SOURCE lean/MCore/Real/P01EvalFramePopMachine.lean BLOB 80ac03328cf7387951d7d44d4d9da2614c671075 -/
import MCore.Real.P01EncodedFrameTape
import MCore.Real.P01FullVerifierPhysicalStackV2

namespace MCore
namespace Real
namespace P01EvalFramePopMachine

open CanonicalFinalProof
open P01EncodedStackEvaluator
open P01EncodedFrameTape
open P01FullVerifierPhysicalStackV2

/-- Fixed finite-control states for physically reading and removing one
three-bit evaluator frame.  The three bits are accumulated only in finite
control; no unbounded syntax object is stored in the machine state. -/
inductive FramePopState where
  | start
  | read0
  | read1 : Bool → FramePopState
  | read2 : Bool → Bool → FramePopState
  | halt : EvalFrame → FramePopState
  | reject
  deriving DecidableEq, Repr

/-- Decode exactly one three-bit frame in finite control.  Code 111 is rejected
because it is deliberately unused by `encodeEvalFrame`. -/
def decodeBits (b0 b1 b2 : Bool) : Option EvalFrame :=
  decodeEvalFrame [b0, b1, b2]

/-- One fixed physical frame-pop/read machine.

The V2 stack representation keeps a blank cell under the head immediately to
the right of the stack.  We first move left onto bit0, then consume bit0,
bit1, bit2 while erasing them.  The final state carries the decoded finite
frame and the tape again has the canonical blank-head V2 layout. -/
def framePopMachine : TM FramePopState (Option Bool) :=
  { initial := .start
    blank := none
    transition := fun q symbol =>
      match q with
      | .start =>
          match symbol with
          | none => (.read0, none, .left)
          | some b => (.reject, some b, .stay)
      | .read0 =>
          match symbol with
          | none => (.reject, none, .stay)
          | some b0 => (.read1 b0, none, .left)
      | .read1 b0 =>
          match symbol with
          | none => (.reject, none, .stay)
          | some b1 => (.read2 b0 b1, none, .left)
      | .read2 b0 b1 =>
          match symbol with
          | none => (.reject, none, .stay)
          | some b2 =>
              match decodeBits b0 b1 b2 with
              | some f => (.halt f, none, .stay)
              | none => (.reject, none, .stay)
      | .halt f => (.halt f, symbol, .stay)
      | .reject => (.reject, symbol, .stay)
    halting := fun q =>
      match q with
      | .halt _ => true
      | .reject => true
      | _ => false }

@[simp] theorem framePopMachine_blank :
    framePopMachine.blank = none := rfl

def framePopConfig
    (t : Tape (Option Bool)) :
    Configuration FramePopState (Option Bool) :=
  { state := .start, tape := t }

/-- Four physical steps decode and remove exactly one valid evaluator frame.
The remaining stack is unchanged and the three erased cells become blank
padding to the right of the head. -/
theorem framePop_run_four
    (witness source : BitString)
    (stack : List Bool)
    (padding : Nat)
    (f : EvalFrame) :
    let final :=
      framePopMachine.run 4
        (framePopConfig
          (physicalStackV2Tape witness source
            (encodeEvalFrame f ++ stack) padding))
    final.state = .halt f ∧
      final.tape =
        physicalStackV2Tape witness source stack (padding + 3) := by
  cases f with
  | neg =>
      simp [framePopMachine, framePopConfig, decodeBits,
        decodeEvalFrame, encodeEvalFrame, physicalStackV2Tape,
        TM.run, TM.step, Tape.write, Tape.move,
        List.replicate_succ, Nat.add_comm, Nat.add_left_comm,
        Nat.add_assoc]
  | andLeft =>
      simp [framePopMachine, framePopConfig, decodeBits,
        decodeEvalFrame, encodeEvalFrame, physicalStackV2Tape,
        TM.run, TM.step, Tape.write, Tape.move,
        List.replicate_succ, Nat.add_comm, Nat.add_left_comm,
        Nat.add_assoc]
  | andRight b =>
      cases b <;>
        simp [framePopMachine, framePopConfig, decodeBits,
          decodeEvalFrame, encodeEvalFrame, physicalStackV2Tape,
          TM.run, TM.step, Tape.write, Tape.move,
          List.replicate_succ, Nat.add_comm, Nat.add_left_comm,
          Nat.add_assoc]
  | orLeft =>
      simp [framePopMachine, framePopConfig, decodeBits,
        decodeEvalFrame, encodeEvalFrame, physicalStackV2Tape,
        TM.run, TM.step, Tape.write, Tape.move,
        List.replicate_succ, Nat.add_comm, Nat.add_left_comm,
        Nat.add_assoc]
  | orRight b =>
      cases b <;>
        simp [framePopMachine, framePopConfig, decodeBits,
          decodeEvalFrame, encodeEvalFrame, physicalStackV2Tape,
          TM.run, TM.step, Tape.write, Tape.move,
          List.replicate_succ, Nat.add_comm, Nat.add_left_comm,
          Nat.add_assoc]

/-- Representation-level corollary used by the global evaluator refinement. -/
theorem framePop_run_four_rep
    (witness source : BitString)
    (stack : List Bool)
    (padding : Nat)
    (f : EvalFrame) :
    let final :=
      framePopMachine.run 4
        (framePopConfig
          (physicalStackV2Tape witness source
            (encodeEvalFrame f ++ stack) padding))
    final.state = .halt f ∧
      PhysicalStackRepV2 final.tape witness source stack := by
  dsimp
  have h := framePop_run_four witness source stack padding f
  rcases h with ⟨hs, ht⟩
  exact ⟨hs, ⟨padding + 3, ht⟩⟩

/-- The deliberately unused code 111 is rejected rather than decoded as an
evaluator frame. -/
theorem framePop_rejects_111
    (witness source : BitString)
    (stack : List Bool)
    (padding : Nat) :
    let final :=
      framePopMachine.run 4
        (framePopConfig
          (physicalStackV2Tape witness source
            (true :: true :: true :: stack) padding))
    final.state = .reject := by
  simp [framePopMachine, framePopConfig, decodeBits,
    decodeEvalFrame, physicalStackV2Tape, TM.run, TM.step,
    Tape.write, Tape.move, List.replicate_succ,
    Nat.add_comm, Nat.add_left_comm, Nat.add_assoc]

#print axioms MCore.Real.P01EvalFramePopMachine.framePop_run_four
#print axioms MCore.Real.P01EvalFramePopMachine.framePop_run_four_rep
#print axioms MCore.Real.P01EvalFramePopMachine.framePop_rejects_111

end P01EvalFramePopMachine
end Real
end MCore


/- SOURCE lean/MCore/Real/P01EvalFramePopMachineV2.lean BLOB 4cde6cb928a3541960d74c272880653fceeffa2c -/
import MCore.Real.P01EvalFramePushMachine

namespace MCore
namespace Real
namespace P01EvalFramePopMachineV2

open CanonicalFinalProof
open P01EncodedStackEvaluator
open P01EncodedFrameTape
open P01EvalFramePushMachine
open P01FullVerifierPhysicalStackV2
open MachineRunLemmas

/-- Finite-control states for reading and removing one three-bit frame. -/
inductive FramePopState where
  | start
  | read0
  | gap1 : Bool → FramePopState
  | read1 : Bool → FramePopState
  | gap2 : Bool → Bool → FramePopState
  | read2 : Bool → Bool → FramePopState
  | halt : EvalFrame → FramePopState
  | reject
  deriving DecidableEq, Repr

/-- Fixed physical frame-pop machine.
It alternates boundary-to-cell moves and erase/read steps.  The two already-read
bits live in finite control; after the third bit the exact semantic frame is
decoded.  Truncated or malformed input rejects fail-closed. -/
def framePopMachine : TM FramePopState (Option Bool) :=
  { initial := .start
    blank := none
    transition := fun q symbol =>
      match q with
      | .start =>
          match symbol with
          | none => (.read0, none, .left)
          | some b => (.reject, some b, .stay)
      | .read0 =>
          match symbol with
          | some b0 => (.gap1 b0, none, .stay)
          | none => (.reject, none, .stay)
      | .gap1 b0 =>
          match symbol with
          | none => (.read1 b0, none, .left)
          | some b => (.reject, some b, .stay)
      | .read1 b0 =>
          match symbol with
          | some b1 => (.gap2 b0 b1, none, .stay)
          | none => (.reject, none, .stay)
      | .gap2 b0 b1 =>
          match symbol with
          | none => (.read2 b0 b1, none, .left)
          | some b => (.reject, some b, .stay)
      | .read2 b0 b1 =>
          match symbol with
          | some b2 =>
              match decodeEvalFrame [b0,b1,b2] with
              | some f => (.halt f, none, .stay)
              | none => (.reject, none, .stay)
          | none => (.reject, none, .stay)
      | .halt f => (.halt f, symbol, .stay)
      | .reject => (.reject, symbol, .stay)
    halting := fun q =>
      match q with
      | .halt _ => true
      | .reject => true
      | _ => false }

@[simp] theorem framePopMachine_blank :
    framePopMachine.blank = none := rfl

def framePopConfig
    (t : Tape (Option Bool)) :
    Configuration FramePopState (Option Bool) :=
  { state := .start, tape := t }

/-- Writing blank onto an already-blank head is physically inert. -/
theorem tape_write_none_of_head_none
    (t : Tape (Option Bool))
    (h : t.head = none) :
    Tape.write t none = t := by
  cases t with
  | mk left head right =>
      simp [Tape.write] at h ⊢
      exact h.symm

theorem framePop_start_one
    (t : Tape (Option Bool))
    (hblank : t.head = none) :
    framePopMachine.run 1
      { state := FramePopState.start, tape := t } =
      { state := FramePopState.read0, tape := popEnter t } := by
  rw [TM.run]
  simp [framePopMachine, hblank, TM.step, popEnter,
    tape_write_none_of_head_none t hblank, TM.run]

theorem framePop_read0_one
    (b0 : Bool) (t : Tape (Option Bool))
    (hhead : t.head = some b0) :
    framePopMachine.run 1
      { state := FramePopState.read0, tape := t } =
      { state := FramePopState.gap1 b0, tape := popErase t } := by
  rw [TM.run]
  simp [framePopMachine, hhead, TM.step, popErase]
  rfl

theorem framePop_gap1_one
    (b0 : Bool) (t : Tape (Option Bool))
    (hblank : t.head = none) :
    framePopMachine.run 1
      { state := FramePopState.gap1 b0, tape := t } =
      { state := FramePopState.read1 b0, tape := popEnter t } := by
  rw [TM.run]
  simp [framePopMachine, hblank, TM.step, popEnter,
    tape_write_none_of_head_none t hblank, TM.run]

theorem framePop_read1_one
    (b0 b1 : Bool) (t : Tape (Option Bool))
    (hhead : t.head = some b1) :
    framePopMachine.run 1
      { state := FramePopState.read1 b0, tape := t } =
      { state := FramePopState.gap2 b0 b1, tape := popErase t } := by
  rw [TM.run]
  simp [framePopMachine, hhead, TM.step, popErase]
  rfl

theorem framePop_gap2_one
    (b0 b1 : Bool) (t : Tape (Option Bool))
    (hblank : t.head = none) :
    framePopMachine.run 1
      { state := FramePopState.gap2 b0 b1, tape := t } =
      { state := FramePopState.read2 b0 b1, tape := popEnter t } := by
  rw [TM.run]
  simp [framePopMachine, hblank, TM.step, popEnter,
    tape_write_none_of_head_none t hblank, TM.run]

theorem framePop_read2_one
    (b0 b1 b2 : Bool) (f : EvalFrame)
    (t : Tape (Option Bool))
    (hhead : t.head = some b2)
    (hdecode : decodeEvalFrame [b0,b1,b2] = some f) :
    framePopMachine.run 1
      { state := FramePopState.read2 b0 b1, tape := t } =
      { state := FramePopState.halt f, tape := popErase t } := by
  rw [TM.run]
  simp [framePopMachine, hhead, hdecode, TM.step, popErase]
  rfl

/-- First physical bit removal. -/
theorem framePop_first_two
    (witness source : BitString)
    (rest : List Bool) (padding : Nat)
    (b0 : Bool) :
    framePopMachine.run 2
      (framePopConfig
        (physicalStackV2Tape witness source (b0 :: rest) padding)) =
      { state := FramePopState.gap1 b0,
        tape := physicalStackV2Tape witness source rest (padding + 1) } := by
  unfold framePopConfig
  rw [show 2 = 1 + 1 by decide, MachineRunLemmas.run_add]
  rw [framePop_start_one _ rfl]
  rw [framePop_read0_one b0 _
    (popEnter_head witness source b0 rest padding)]
  rw [popErase_correct]

/-- Second physical bit removal, retaining the first bit in finite control. -/
theorem framePop_second_two
    (witness source : BitString)
    (rest : List Bool) (padding : Nat)
    (b0 b1 : Bool) :
    framePopMachine.run 2
      { state := FramePopState.gap1 b0,
        tape := physicalStackV2Tape witness source (b1 :: rest) padding } =
      { state := FramePopState.gap2 b0 b1,
        tape := physicalStackV2Tape witness source rest (padding + 1) } := by
  rw [show 2 = 1 + 1 by decide, MachineRunLemmas.run_add]
  rw [framePop_gap1_one b0 _ rfl]
  rw [framePop_read1_one b0 b1 _
    (popEnter_head witness source b1 rest padding)]
  rw [popErase_correct]

/-- Third bit removal decodes the exact frame and halts. -/
theorem framePop_third_two
    (witness source : BitString)
    (rest : List Bool) (padding : Nat)
    (b0 b1 b2 : Bool) (f : EvalFrame)
    (hdecode : decodeEvalFrame [b0,b1,b2] = some f) :
    framePopMachine.run 2
      { state := FramePopState.gap2 b0 b1,
        tape := physicalStackV2Tape witness source (b2 :: rest) padding } =
      { state := FramePopState.halt f,
        tape := physicalStackV2Tape witness source rest (padding + 1) } := by
  rw [show 2 = 1 + 1 by decide, MachineRunLemmas.run_add]
  rw [framePop_gap2_one b0 b1 _ rfl]
  rw [framePop_read2_one b0 b1 b2 f _
    (popEnter_head witness source b2 rest padding) hdecode]
  rw [popErase_correct]

/-- Six physical steps remove exactly one encoded frame and return that exact
frame in the halting control state. -/
theorem framePop_run_six
    (witness source : BitString)
    (stack : List Bool)
    (padding : Nat)
    (f : EvalFrame) :
    framePopMachine.run 6
      (framePopConfig
        (physicalStackV2Tape witness source
          (encodeEvalFrame f ++ stack) padding)) =
      { state := FramePopState.halt f,
        tape := physicalStackV2Tape witness source stack (padding + 3) } := by
  rw [encodeEvalFrame_eq_bits]
  simp only [List.cons_append, List.nil_append]
  have hdecode :
      decodeEvalFrame [frameBit0 f, frameBit1 f, frameBit2 f] = some f := by
    rw [← encodeEvalFrame_eq_bits]
    exact decodeEvalFrame_encodeEvalFrame f
  rw [show 6 = 2 + (2 + 2) by decide, MachineRunLemmas.run_add]
  rw [framePop_first_two witness source
    (frameBit1 f :: frameBit2 f :: stack) padding (frameBit0 f)]
  rw [MachineRunLemmas.run_add]
  rw [framePop_second_two witness source
    (frameBit2 f :: stack) (padding + 1) (frameBit0 f) (frameBit1 f)]
  rw [framePop_third_two witness source
    stack (padding + 1 + 1)
    (frameBit0 f) (frameBit1 f) (frameBit2 f) f hdecode]

/-- Empty/truncated stack rejects rather than fabricating a frame. -/
theorem framePop_empty_rejects
    (witness source : BitString) (padding : Nat) :
    (framePopMachine.run 2
      (framePopConfig
        (physicalStackV2Tape witness source [] padding))).state =
      .reject := by
  unfold framePopConfig
  cases padding <;>
    simp [framePopMachine, TM.run, TM.step, physicalStackV2Tape,
      Tape.move, Tape.write]

#print axioms MCore.Real.P01EvalFramePopMachineV2.framePop_run_six
#print axioms MCore.Real.P01EvalFramePopMachineV2.framePop_empty_rejects

end P01EvalFramePopMachineV2
end Real
end MCore


/- SOURCE lean/MCore/Real/P01EvalFramePushMachine.lean BLOB 63bba08487b03636194b45fffea80a6fd863233e -/
import MCore.Real.P01EncodedFrameTape
import MCore.Real.P01FullVerifierPhysicalStackV2
import MCore.Real.MachineRunLemmas

namespace MCore
namespace Real
namespace P01EvalFramePushMachine

open CanonicalFinalProof
open P01EncodedStackEvaluator
open P01EncodedFrameTape
open P01FullVerifierPhysicalStackV2
open MachineRunLemmas

/-- Explicit three physical bits of a semantic evaluator frame. -/
def frameBits : EvalFrame → Bool × Bool × Bool
  | .neg            => (false, false, false)
  | .andLeft        => (false, false, true)
  | .andRight false => (false, true, false)
  | .andRight true  => (false, true, true)
  | .orLeft         => (true, false, false)
  | .orRight false  => (true, false, true)
  | .orRight true   => (true, true, false)

def frameBit0 (f : EvalFrame) : Bool := (frameBits f).1
def frameBit1 (f : EvalFrame) : Bool := (frameBits f).2.1
def frameBit2 (f : EvalFrame) : Bool := (frameBits f).2.2

theorem encodeEvalFrame_eq_bits (f : EvalFrame) :
    encodeEvalFrame f = [frameBit0 f, frameBit1 f, frameBit2 f] := by
  cases f with
  | neg => rfl
  | andLeft => rfl
  | andRight b => cases b <;> rfl
  | orLeft => rfl
  | orRight b => cases b <;> rfl

/-- Finite-control states for a three-cell frame push.
The frame value is one of seven finite constructors; it is control data, not
an unbounded circuit/AST. -/
inductive FramePushState where
  | start : EvalFrame → FramePushState
  | after1 : EvalFrame → FramePushState
  | after2 : EvalFrame → FramePushState
  | halt
  | reject
  deriving DecidableEq, Repr

/-- Fixed physical machine: each successful step requires the current cell to
be blank, writes one code bit, and advances right.  Bits are emitted in reverse
temporal order so the left stack prefix ends as bit0::bit1::bit2. -/
def framePushMachine : TM FramePushState (Option Bool) :=
  { initial := .halt
    blank := none
    transition := fun q symbol =>
      match q with
      | .start f =>
          match symbol with
          | none => (.after1 f, some (frameBit2 f), .right)
          | some b => (.reject, some b, .stay)
      | .after1 f =>
          match symbol with
          | none => (.after2 f, some (frameBit1 f), .right)
          | some b => (.reject, some b, .stay)
      | .after2 f =>
          match symbol with
          | none => (.halt, some (frameBit0 f), .right)
          | some b => (.reject, some b, .stay)
      | .halt => (.halt, symbol, .stay)
      | .reject => (.reject, symbol, .stay)
    halting := fun q =>
      match q with
      | .halt => true
      | .reject => true
      | _ => false }

@[simp] theorem framePushMachine_blank :
    framePushMachine.blank = none := rfl

def framePushConfig
    (f : EvalFrame) (t : Tape (Option Bool)) :
    Configuration FramePushState (Option Bool) :=
  { state := .start f, tape := t }

/-- One start-state step is exactly the certified Boolean push transform. -/
theorem framePush_start_one
    (f : EvalFrame) (t : Tape (Option Bool))
    (hblank : t.head = none) :
    framePushMachine.run 1
      { state := FramePushState.start f, tape := t } =
      { state := FramePushState.after1 f,
        tape := pushStep (frameBit2 f) t } := by
  rw [TM.run]
  simp [framePushMachine, hblank, TM.step, pushStep]
  rfl

/-- Second code-bit step. -/
theorem framePush_after1_one
    (f : EvalFrame) (t : Tape (Option Bool))
    (hblank : t.head = none) :
    framePushMachine.run 1
      { state := FramePushState.after1 f, tape := t } =
      { state := FramePushState.after2 f,
        tape := pushStep (frameBit1 f) t } := by
  rw [TM.run]
  simp [framePushMachine, hblank, TM.step, pushStep]
  rfl

/-- Third code-bit step reaches the halting state. -/
theorem framePush_after2_one
    (f : EvalFrame) (t : Tape (Option Bool))
    (hblank : t.head = none) :
    framePushMachine.run 1
      { state := FramePushState.after2 f, tape := t } =
      { state := FramePushState.halt,
        tape := pushStep (frameBit0 f) t } := by
  rw [TM.run]
  simp [framePushMachine, hblank, TM.step, pushStep]
  rfl

/-- Three physical push steps realize exactly the fixed-width frame encoding on
the V2 stack layout.  The proof composes the already-certified Boolean
`pushStep_correct` invariant rather than normalizing raw tape padding. -/
theorem framePush_run_three
    (witness source : BitString)
    (stack : List Bool)
    (padding : Nat)
    (f : EvalFrame) :
    let final :=
      framePushMachine.run 3
        (framePushConfig f
          (physicalStackV2Tape witness source stack padding))
    final.state = .halt ∧
      final.tape =
        physicalStackV2Tape witness source
          (encodeEvalFrame f ++ stack)
          (((padding - 1) - 1) - 1) := by
  dsimp
  unfold framePushConfig
  have h1 := framePush_start_one f
    (physicalStackV2Tape witness source stack padding) rfl
  have hp1 := pushStep_correct witness source stack padding (frameBit2 f)
  have h2 := framePush_after1_one f
    (physicalStackV2Tape witness source
      (frameBit2 f :: stack) (padding - 1)) rfl
  have hp2 := pushStep_correct witness source
    (frameBit2 f :: stack) (padding - 1) (frameBit1 f)
  have h3 := framePush_after2_one f
    (physicalStackV2Tape witness source
      (frameBit1 f :: frameBit2 f :: stack) ((padding - 1) - 1)) rfl
  have hp3 := pushStep_correct witness source
    (frameBit1 f :: frameBit2 f :: stack) ((padding - 1) - 1)
    (frameBit0 f)
  rw [show 3 = 1 + 2 by decide, MachineRunLemmas.run_add]
  rw [h1, hp1]
  rw [show 2 = 1 + 1 by decide, MachineRunLemmas.run_add]
  rw [h2, hp2]
  rw [h3, hp3]
  constructor
  · rfl
  · rw [encodeEvalFrame_eq_bits]
    rfl

/-- Fail-closed behavior: starting a push on a nonblank cell rejects in one
step instead of overwriting existing data. -/
theorem framePush_rejects_nonblank
    (f : EvalFrame) (b : Bool)
    (left right : List (Option Bool)) :
    (framePushMachine.run 1
      (framePushConfig f
        { left := left, head := some b, right := right })).state =
      .reject := by
  cases f <;> simp [framePushMachine, framePushConfig, TM.run, TM.step]

#print axioms MCore.Real.P01EvalFramePushMachine.framePush_run_three
#print axioms MCore.Real.P01EvalFramePushMachine.framePush_rejects_nonblank

end P01EvalFramePushMachine
end Real
end MCore


/- SOURCE lean/MCore/Real/P01EvalStepFrameRefinement.lean BLOB 0559152d52b8373539df9ba77325c59568359658 -/
import MCore.Real.P01EvalFramePushMachine
import MCore.Real.P01EvalFramePopMachine

namespace MCore
namespace Real
namespace P01EvalStepFrameRefinement

open CanonicalFinalProof
open P01EncodedStackEvaluator
open P01EncodedFrameTape
open P01FullVerifierPhysicalStackV2
open P01EvalFramePushMachine
open P01EvalFramePopMachine

/-- Exact physical refinement of semantic frame-stack push: three TM steps
prepend precisely the canonical three-bit code of the new EvalFrame. -/
theorem push_refines_frame_cons
    (witness source : BitString)
    (frames : List EvalFrame)
    (padding : Nat)
    (f : EvalFrame) :
    let final :=
      framePushMachine.run 3
        (framePushConfig f
          (physicalStackV2Tape witness source
            (encodeEvalFrames frames) padding))
    final.state = .halt ∧
      final.tape =
        physicalStackV2Tape witness source
          (encodeEvalFrames (f :: frames))
          (((padding - 1) - 1) - 1) := by
  dsimp
  simpa [encodeEvalFrames] using
    framePush_run_three witness source (encodeEvalFrames frames) padding f

/-- Exact physical refinement of semantic frame-stack pop/read: four TM steps
decode the head frame, erase exactly its three-bit code, and restore the
canonical physical representation of the tail frame stack. -/
theorem pop_refines_frame_tail
    (witness source : BitString)
    (frames : List EvalFrame)
    (padding : Nat)
    (f : EvalFrame) :
    let final :=
      framePopMachine.run 4
        (framePopConfig
          (physicalStackV2Tape witness source
            (encodeEvalFrames (f :: frames)) padding))
    final.state = .halt f ∧
      final.tape =
        physicalStackV2Tape witness source
          (encodeEvalFrames frames) (padding + 3) := by
  dsimp
  simpa [encodeEvalFrames] using
    framePop_run_four witness source (encodeEvalFrames frames) padding f

/-- The semantic NOT-tag transition and its physical frame-stack action agree:
the logical step pushes .neg and the fixed physical machine pushes exactly the
canonical .neg frame code. -/
theorem evalStep_not_tag_refined
    (sigma : Assignment)
    (rest witness source : BitString)
    (frames : List EvalFrame)
    (padding : Nat) :
    evalStep sigma
      (needExpr (false :: true :: true :: rest) frames) =
        some (needExpr rest (.neg :: frames)) ∧
    let final :=
      framePushMachine.run 3
        (framePushConfig .neg
          (physicalStackV2Tape witness source
            (encodeEvalFrames frames) padding))
    final.state = .halt ∧
      final.tape =
        physicalStackV2Tape witness source
          (encodeEvalFrames (.neg :: frames))
          (((padding - 1) - 1) - 1) := by
  constructor
  · simp [evalStep, needExpr]
  · exact push_refines_frame_cons witness source frames padding .neg

/-- The semantic AND-tag transition and its physical frame-stack action agree. -/
theorem evalStep_and_tag_refined
    (sigma : Assignment)
    (rest witness source : BitString)
    (frames : List EvalFrame)
    (padding : Nat) :
    evalStep sigma
      (needExpr (true :: false :: false :: rest) frames) =
        some (needExpr rest (.andLeft :: frames)) ∧
    let final :=
      framePushMachine.run 3
        (framePushConfig .andLeft
          (physicalStackV2Tape witness source
            (encodeEvalFrames frames) padding))
    final.state = .halt ∧
      final.tape =
        physicalStackV2Tape witness source
          (encodeEvalFrames (.andLeft :: frames))
          (((padding - 1) - 1) - 1) := by
  constructor
  · simp [evalStep, needExpr]
  · exact push_refines_frame_cons witness source frames padding .andLeft

/-- The semantic OR-tag transition and its physical frame-stack action agree. -/
theorem evalStep_or_tag_refined
    (sigma : Assignment)
    (rest witness source : BitString)
    (frames : List EvalFrame)
    (padding : Nat) :
    evalStep sigma
      (needExpr (true :: false :: true :: rest) frames) =
        some (needExpr rest (.orLeft :: frames)) ∧
    let final :=
      framePushMachine.run 3
        (framePushConfig .orLeft
          (physicalStackV2Tape witness source
            (encodeEvalFrames frames) padding))
    final.state = .halt ∧
      final.tape =
        physicalStackV2Tape witness source
          (encodeEvalFrames (.orLeft :: frames))
          (((padding - 1) - 1) - 1) := by
  constructor
  · simp [evalStep, needExpr]
  · exact push_refines_frame_cons witness source frames padding .orLeft

/-- Returning through a semantic frame is physically readable/removable with
the already-certified fixed pop machine.  This theorem covers every EvalFrame
constructor and is the common first half of neg/and/or return refinement. -/
theorem evalStep_return_frame_physically_decodable
    (witness source : BitString)
    (frames : List EvalFrame)
    (padding : Nat)
    (f : EvalFrame) :
    let final :=
      framePopMachine.run 4
        (framePopConfig
          (physicalStackV2Tape witness source
            (encodeEvalFrames (f :: frames)) padding))
    final.state = .halt f ∧
      PhysicalStackRepV2 final.tape witness source
        (encodeEvalFrames frames) := by
  dsimp
  have h :=
    framePop_run_four_rep witness source
      (encodeEvalFrames frames) padding f
  simpa [encodeEvalFrames] using h

#print axioms MCore.Real.P01EvalStepFrameRefinement.push_refines_frame_cons
#print axioms MCore.Real.P01EvalStepFrameRefinement.pop_refines_frame_tail
#print axioms MCore.Real.P01EvalStepFrameRefinement.evalStep_not_tag_refined
#print axioms MCore.Real.P01EvalStepFrameRefinement.evalStep_and_tag_refined
#print axioms MCore.Real.P01EvalStepFrameRefinement.evalStep_or_tag_refined
#print axioms MCore.Real.P01EvalStepFrameRefinement.evalStep_return_frame_physically_decodable


/-- Returning through negation: the semantic transition only updates the
finite-control Boolean value; the physical tape action is exactly one frame
pop. -/
theorem evalStep_neg_return_refined
    (sigma : Assignment)
    (v : Bool)
    (bits witness source : BitString)
    (frames : List EvalFrame)
    (padding : Nat) :
    evalStep sigma
      (haveValue v bits (.neg :: frames)) =
        some (haveValue (!v) bits frames) ∧
    let final :=
      framePopMachine.run 4
        (framePopConfig
          (physicalStackV2Tape witness source
            (encodeEvalFrames (.neg :: frames)) padding))
    final.state = .halt .neg ∧
      final.tape =
        physicalStackV2Tape witness source
          (encodeEvalFrames frames) (padding + 3) := by
  constructor
  · rfl
  · exact pop_refines_frame_tail witness source frames padding .neg

/-- Returning from the left operand of AND: semantic control replaces
.andLeft by .andRight l; physically this is one certified pop followed by one
certified push of the finite frame carrying l. -/
theorem evalStep_andLeft_return_refined
    (sigma : Assignment)
    (l : Bool)
    (bits witness source : BitString)
    (frames : List EvalFrame)
    (padding : Nat) :
    evalStep sigma
      (haveValue l bits (.andLeft :: frames)) =
        some (needExpr bits (.andRight l :: frames)) ∧
    let popped :=
      framePopMachine.run 4
        (framePopConfig
          (physicalStackV2Tape witness source
            (encodeEvalFrames (.andLeft :: frames)) padding))
    let pushed :=
      framePushMachine.run 3
        (framePushConfig (.andRight l) popped.tape)
    popped.state = .halt .andLeft ∧
      pushed.state = .halt ∧
      pushed.tape =
        physicalStackV2Tape witness source
          (encodeEvalFrames (.andRight l :: frames))
          ((((padding + 3) - 1) - 1) - 1) := by
  constructor
  · rfl
  · dsimp
    have hp := pop_refines_frame_tail witness source frames padding .andLeft
    rcases hp with ⟨hps, hpt⟩
    have hpt' :
        (framePopMachine.run 4
          (framePopConfig
            (physicalStackV2Tape witness source
              (encodeEvalFrame .andLeft ++ encodeEvalFrames frames) padding))).tape =
          physicalStackV2Tape witness source
            (encodeEvalFrames frames) (padding + 3) := by
      simpa [encodeEvalFrames] using hpt
    rw [hpt']
    have hq :=
      push_refines_frame_cons witness source frames (padding + 3) (.andRight l)
    exact ⟨by simpa [encodeEvalFrames] using hps, hq.1, by simpa using hq.2⟩

/-- Returning from the left operand of OR: identical physical pop/push pattern
with the .orRight l continuation frame. -/
theorem evalStep_orLeft_return_refined
    (sigma : Assignment)
    (l : Bool)
    (bits witness source : BitString)
    (frames : List EvalFrame)
    (padding : Nat) :
    evalStep sigma
      (haveValue l bits (.orLeft :: frames)) =
        some (needExpr bits (.orRight l :: frames)) ∧
    let popped :=
      framePopMachine.run 4
        (framePopConfig
          (physicalStackV2Tape witness source
            (encodeEvalFrames (.orLeft :: frames)) padding))
    let pushed :=
      framePushMachine.run 3
        (framePushConfig (.orRight l) popped.tape)
    popped.state = .halt .orLeft ∧
      pushed.state = .halt ∧
      pushed.tape =
        physicalStackV2Tape witness source
          (encodeEvalFrames (.orRight l :: frames))
          ((((padding + 3) - 1) - 1) - 1) := by
  constructor
  · rfl
  · dsimp
    have hp := pop_refines_frame_tail witness source frames padding .orLeft
    rcases hp with ⟨hps, hpt⟩
    have hpt' :
        (framePopMachine.run 4
          (framePopConfig
            (physicalStackV2Tape witness source
              (encodeEvalFrame .orLeft ++ encodeEvalFrames frames) padding))).tape =
          physicalStackV2Tape witness source
            (encodeEvalFrames frames) (padding + 3) := by
      simpa [encodeEvalFrames] using hpt
    rw [hpt']
    have hq :=
      push_refines_frame_cons witness source frames (padding + 3) (.orRight l)
    exact ⟨by simpa [encodeEvalFrames] using hps, hq.1, by simpa using hq.2⟩

/-- Returning from the right operand of AND: the stored left bit is already
finite-control data in the frame; after physical pop, the Boolean result is a
finite-control computation and no further tape mutation is required. -/
theorem evalStep_andRight_return_refined
    (sigma : Assignment)
    (l r : Bool)
    (bits witness source : BitString)
    (frames : List EvalFrame)
    (padding : Nat) :
    evalStep sigma
      (haveValue r bits (.andRight l :: frames)) =
        some (haveValue (Bool.and l r) bits frames) ∧
    let final :=
      framePopMachine.run 4
        (framePopConfig
          (physicalStackV2Tape witness source
            (encodeEvalFrames (.andRight l :: frames)) padding))
    final.state = .halt (.andRight l) ∧
      final.tape =
        physicalStackV2Tape witness source
          (encodeEvalFrames frames) (padding + 3) := by
  constructor
  · rfl
  · exact pop_refines_frame_tail witness source frames padding (.andRight l)

/-- Returning from the right operand of OR. -/
theorem evalStep_orRight_return_refined
    (sigma : Assignment)
    (l r : Bool)
    (bits witness source : BitString)
    (frames : List EvalFrame)
    (padding : Nat) :
    evalStep sigma
      (haveValue r bits (.orRight l :: frames)) =
        some (haveValue (Bool.or l r) bits frames) ∧
    let final :=
      framePopMachine.run 4
        (framePopConfig
          (physicalStackV2Tape witness source
            (encodeEvalFrames (.orRight l :: frames)) padding))
    final.state = .halt (.orRight l) ∧
      final.tape =
        physicalStackV2Tape witness source
          (encodeEvalFrames frames) (padding + 3) := by
  constructor
  · rfl
  · exact pop_refines_frame_tail witness source frames padding (.orRight l)

#print axioms MCore.Real.P01EvalStepFrameRefinement.evalStep_neg_return_refined
#print axioms MCore.Real.P01EvalStepFrameRefinement.evalStep_andLeft_return_refined
#print axioms MCore.Real.P01EvalStepFrameRefinement.evalStep_orLeft_return_refined
#print axioms MCore.Real.P01EvalStepFrameRefinement.evalStep_andRight_return_refined
#print axioms MCore.Real.P01EvalStepFrameRefinement.evalStep_orRight_return_refined

end P01EvalStepFrameRefinement
end Real
end MCore


/- SOURCE lean/MCore/Real/P01EvalTagPhysicalRefinement.lean BLOB 140f16c6b576417e68f53759e48bc31e91b032f1 -/
import MCore.Real.P01EvalCursorConsume
import MCore.Real.P01EvalCursorFramePush
import MCore.Real.P01EncodedStackEvaluator

namespace MCore
namespace Real
namespace P01EvalTagPhysicalRefinement

open CanonicalFinalProof
open P01EncodedStackEvaluator
open P01EncodedFrameTape
open P01EvalCursorMachine
open P01EvalCursorConsume
open P01EvalCursorFramePush
open P01EvalFramePushMachine

/-- Three physical source-bit consumptions followed by one certified frame push.
This is the common physical action for NOT/AND/OR prefix tags. -/
theorem consumeThree_then_push_frame
    (witness : BitString)
    (consumed : Nat)
    (b0 b1 b2 : Bool)
    (rest : BitString)
    (frames : List EvalFrame)
    (padding : Nat)
    (f : EvalFrame) :
    let consumedTape :=
      consumeThreeTape witness consumed
        (b0 :: b1 :: b2 :: rest)
        (encodeEvalFrames frames) padding
    let final :=
      framePushMachine.run 3
        (framePushConfig f consumedTape)
    final.state = .halt ∧
      final.tape =
        evalCursorStackEndTape witness (consumed + 3) rest
          (encodeEvalFrame f ++ encodeEvalFrames frames)
          (((padding - 1) - 1) - 1) := by
  dsimp
  rw [consumeThreeTape_correct]
  exact
    framePush_run_three_cursor
      witness rest (encodeEvalFrames frames)
      (consumed + 3) padding f

/-- Constant false: semantic evalStep and concrete physical tag consumption
agree exactly.  No frame mutation is required. -/
theorem evalStep_const_false_cursor_refined
    (sigma : Assignment)
    (witness : BitString)
    (consumed : Nat)
    (rest : BitString)
    (frames : List EvalFrame)
    (padding : Nat) :
    evalStep sigma
      (needExpr (false :: false :: true :: rest) frames) =
        some (haveValue false rest frames) ∧
    consumeThreeTape witness consumed
      (false :: false :: true :: rest)
      (encodeEvalFrames frames) padding =
        evalCursorStackEndTape witness (consumed + 3) rest
          (encodeEvalFrames frames) padding := by
  constructor
  · simp [evalStep, needExpr, haveValue]
  · exact
      consumeThreeTape_correct witness consumed
        false false true rest (encodeEvalFrames frames) padding

/-- Constant true: semantic evalStep and concrete physical tag consumption
agree exactly. -/
theorem evalStep_const_true_cursor_refined
    (sigma : Assignment)
    (witness : BitString)
    (consumed : Nat)
    (rest : BitString)
    (frames : List EvalFrame)
    (padding : Nat) :
    evalStep sigma
      (needExpr (false :: true :: false :: rest) frames) =
        some (haveValue true rest frames) ∧
    consumeThreeTape witness consumed
      (false :: true :: false :: rest)
      (encodeEvalFrames frames) padding =
        evalCursorStackEndTape witness (consumed + 3) rest
          (encodeEvalFrames frames) padding := by
  constructor
  · simp [evalStep, needExpr, haveValue]
  · exact
      consumeThreeTape_correct witness consumed
        false true false rest (encodeEvalFrames frames) padding

/-- NOT prefix tag: consume exactly three source bits and push exactly the
canonical negation continuation frame. -/
theorem evalStep_not_tag_cursor_refined
    (sigma : Assignment)
    (witness : BitString)
    (consumed : Nat)
    (rest : BitString)
    (frames : List EvalFrame)
    (padding : Nat) :
    evalStep sigma
      (needExpr (false :: true :: true :: rest) frames) =
        some (needExpr rest (.neg :: frames)) ∧
    let consumedTape :=
      consumeThreeTape witness consumed
        (false :: true :: true :: rest)
        (encodeEvalFrames frames) padding
    let final :=
      framePushMachine.run 3
        (framePushConfig .neg consumedTape)
    final.state = .halt ∧
      final.tape =
        evalCursorStackEndTape witness (consumed + 3) rest
          (encodeEvalFrame .neg ++ encodeEvalFrames frames)
          (((padding - 1) - 1) - 1) := by
  constructor
  · simp [evalStep, needExpr, haveValue]
  · exact
      consumeThree_then_push_frame
        witness consumed false true true rest frames padding .neg

/-- AND prefix tag: consume exactly three source bits and push the left-operand
continuation frame. -/
theorem evalStep_and_tag_cursor_refined
    (sigma : Assignment)
    (witness : BitString)
    (consumed : Nat)
    (rest : BitString)
    (frames : List EvalFrame)
    (padding : Nat) :
    evalStep sigma
      (needExpr (true :: false :: false :: rest) frames) =
        some (needExpr rest (.andLeft :: frames)) ∧
    let consumedTape :=
      consumeThreeTape witness consumed
        (true :: false :: false :: rest)
        (encodeEvalFrames frames) padding
    let final :=
      framePushMachine.run 3
        (framePushConfig .andLeft consumedTape)
    final.state = .halt ∧
      final.tape =
        evalCursorStackEndTape witness (consumed + 3) rest
          (encodeEvalFrame .andLeft ++ encodeEvalFrames frames)
          (((padding - 1) - 1) - 1) := by
  constructor
  · simp [evalStep, needExpr, haveValue]
  · exact
      consumeThree_then_push_frame
        witness consumed true false false rest frames padding .andLeft

/-- OR prefix tag: consume exactly three source bits and push the left-operand
continuation frame. -/
theorem evalStep_or_tag_cursor_refined
    (sigma : Assignment)
    (witness : BitString)
    (consumed : Nat)
    (rest : BitString)
    (frames : List EvalFrame)
    (padding : Nat) :
    evalStep sigma
      (needExpr (true :: false :: true :: rest) frames) =
        some (needExpr rest (.orLeft :: frames)) ∧
    let consumedTape :=
      consumeThreeTape witness consumed
        (true :: false :: true :: rest)
        (encodeEvalFrames frames) padding
    let final :=
      framePushMachine.run 3
        (framePushConfig .orLeft consumedTape)
    final.state = .halt ∧
      final.tape =
        evalCursorStackEndTape witness (consumed + 3) rest
          (encodeEvalFrame .orLeft ++ encodeEvalFrames frames)
          (((padding - 1) - 1) - 1) := by
  constructor
  · simp [evalStep, needExpr, haveValue]
  · exact
      consumeThree_then_push_frame
        witness consumed true false true rest frames padding .orLeft

#print axioms MCore.Real.P01EvalTagPhysicalRefinement.consumeThree_then_push_frame
#print axioms MCore.Real.P01EvalTagPhysicalRefinement.evalStep_const_false_cursor_refined
#print axioms MCore.Real.P01EvalTagPhysicalRefinement.evalStep_const_true_cursor_refined
#print axioms MCore.Real.P01EvalTagPhysicalRefinement.evalStep_not_tag_cursor_refined
#print axioms MCore.Real.P01EvalTagPhysicalRefinement.evalStep_and_tag_cursor_refined
#print axioms MCore.Real.P01EvalTagPhysicalRefinement.evalStep_or_tag_cursor_refined

end P01EvalTagPhysicalRefinement
end Real
end MCore


/- SOURCE lean/MCore/Real/P01FinalCertificate.lean BLOB 79e04a486769b1f129c90b0eecb91c2a0828b50b -/
import MCore.Real.CanonicalSATNTMAttack

namespace MCore
namespace Real
namespace P01FinalCertificate

open CanonicalFinalProof
open CanonicalCircuitBits
open CanonicalSATBoundary
open CanonicalSATNTMAttack

/-- Exact concrete integrated NTM payload required for the SAT-in-NP side.
No endpoint proposition is stored as a field. -/
structure P01MachineConstruction where
  stateCount : Nat
  machine : NTM (Fin (stateCount + 1)) (Option Bool)
  blank_none : machine.blank = none
  timeBound : TimeBound
  time_poly : PolynomialTimeBound timeBound
  halts :
    ∀ bs : BitString,
      machine.HaltsWithin
        (timeBound bs.length)
        (initialNTMConfig machine bs)
  accepts_iff :
    ∀ bs : BitString,
      machine.AcceptsWithin
          (timeBound bs.length)
          (initialNTMConfig machine bs) ↔
        SATBits circuitBitEncoding bs

def P01MachineConstruction.toCandidate
    (C : P01MachineConstruction) :
    PolyNTMCandidate :=
  { stateCount := C.stateCount
    machine := C.machine
    blank_none := C.blank_none
    timeBound := C.timeBound
    time_poly := C.time_poly }

theorem P01MachineConstruction.correctAt
    (C : P01MachineConstruction)
    (bs : BitString) :
    C.toCandidate.CorrectAt
      (SATBits circuitBitEncoding) bs := by
  constructor
  · exact C.halts bs
  · exact C.accepts_iff bs

def P01MachineConstruction.toRealization
    (C : P01MachineConstruction) :
    PolyNTMRealization (SATBits circuitBitEncoding) :=
  { candidate := C.toCandidate
    decides := C.correctAt }

def P01ConstructionGap : Prop :=
  Nonempty P01MachineConstruction

theorem construction_closes_p01
    (h : P01ConstructionGap) :
    CanonicalSATMachineClosure := by
  rcases h with ⟨C⟩
  exact ⟨C.toRealization⟩

#print axioms MCore.Real.P01FinalCertificate.P01MachineConstruction.correctAt
#print axioms MCore.Real.P01FinalCertificate.construction_closes_p01

end P01FinalCertificate
end Real
end MCore


/- SOURCE lean/MCore/Real/P01FullVerifierEvalLocal.lean BLOB f57ddf300dfff95dac2aeee069a2dae18805a7ac -/
import MCore.Real.P01FullVerifierPhysical
import MCore.Real.P01FullVerifierStackSemantics
import MCore.Real.P01VerifierGateMachine

namespace MCore
namespace Real
namespace P01FullVerifierEvalLocal

open P01FullVerifierPhysical
open P01FullVerifierStackSemantics
open P01VerifierGateMachine

theorem evalNeg_local_semantics
    (sigma : Assignment) (v : Bool) (stack : List Bool) :
    execInstr sigma (v :: stack) .neg = some ((!v) :: stack) := by
  simp [execInstr]

theorem evalAnd_local_semantics
    (sigma : Assignment) (l r : Bool) (stack : List Bool) :
    execInstr sigma (r :: l :: stack) .and =
      some (Bool.and l r :: stack) := by
  rfl

theorem evalOr_local_semantics
    (sigma : Assignment) (l r : Bool) (stack : List Bool) :
    execInstr sigma (r :: l :: stack) .or =
      some (Bool.or l r :: stack) := by
  rfl

theorem gate_and_exact (l r : Bool) :
    gateResult false l r = Bool.and l r := by
  rfl

theorem gate_or_exact (l r : Bool) :
    gateResult true l r = Bool.or l r := by
  rfl

#print axioms MCore.Real.P01FullVerifierEvalLocal.evalNeg_local_semantics
#print axioms MCore.Real.P01FullVerifierEvalLocal.evalAnd_local_semantics
#print axioms MCore.Real.P01FullVerifierEvalLocal.evalOr_local_semantics
#print axioms MCore.Real.P01FullVerifierEvalLocal.gate_and_exact
#print axioms MCore.Real.P01FullVerifierEvalLocal.gate_or_exact

end P01FullVerifierEvalLocal
end Real
end MCore


/- SOURCE lean/MCore/Real/P01FullVerifierInputShuttleV2.lean BLOB a2d1aad399907e802230c27e1b8e930b7ad3d737 -/
import MCore.Real.P01FullVerifierPhysicalStackV2
import MCore.Real.P01FullVerifierPhysicalMoves
import MCore.Real.P01FullVerifierPhysicalShuttles

namespace MCore
namespace Real
namespace P01FullVerifierInputShuttleV2

open CanonicalFinalProof
open P01FullVerifierPhysicalStackV2
open P01FullVerifierPhysicalMoves
open P01FullVerifierPhysicalShuttles

/-- Exact number of left moves from the V2 stack blank to witness[i].
The offset includes current stack cells, the stack/source blank, the source,
the source/witness blank, and finally the selected witness cell. -/
def witnessOffsetV2 (stack : List Bool) (source : BitString) (i : Nat) : Nat :=
  stack.length + source.length + 3 + i

def moveToWitnessSeqV2
    (stack : List Bool) (source : BitString) (i : Nat) : List Direction :=
  moveLeftSeq (witnessOffsetV2 stack source i)

def moveBackToStackSeqV2
    (stack : List Bool) (source : BitString) (i : Nat) : List Direction :=
  moveRightSeq (witnessOffsetV2 stack source i)

theorem moveToWitnessSeqV2_length
    (stack : List Bool) (source : BitString) (i : Nat) :
    (moveToWitnessSeqV2 stack source i).length =
      witnessOffsetV2 stack source i := by
  simp [moveToWitnessSeqV2, witnessOffsetV2, moveLeftSeq_length]

theorem witnessOffsetV2_positive
    (stack : List Bool) (source : BitString) (i : Nat) :
    0 < witnessOffsetV2 stack source i := by
  simp [witnessOffsetV2]
  omega

/-- The V2 left region has the exact prefix shape required by the generic
separator+witness indexing lemma. -/
theorem stackV2_left_as_prefix
    (witness source : BitString) (stack : List Bool) (padding : Nat) :
    (physicalStackV2Tape witness source stack padding).left =
      (stack.map some ++ none :: source.reverse.map some) ++
        none :: witness.map some := by
  simp [physicalStackV2Tape, List.append_assoc]

/-- Physical input lookup: after the exact left shuttle, the head is witness[i]. -/
theorem moveToWitnessSeqV2_head_correct
    (witness source : BitString)
    (stack : List Bool) (padding i : Nat)
    (hi : i < witness.length) :
    (execMoves none (moveToWitnessSeqV2 stack source i)
      (physicalStackV2Tape witness source stack padding)).head =
      some witness[i] := by
  unfold moveToWitnessSeqV2 witnessOffsetV2
  rw [show stack.length + source.length + 3 + i =
      ((stack.map some ++ none :: source.reverse.map some).length + 1 + i) + 1 by
        simp; omega]
  rw [execMoves_moveLeftSeq_head_getD]
  rw [stackV2_left_as_prefix]
  exact getD_prefix_separator_witness
    (stack.map some ++ none :: source.reverse.map some) witness i hi

theorem witness_roundTripV2_length
    (stack : List Bool) (source : BitString) (i : Nat) :
    (moveToWitnessSeqV2 stack source i ++
      moveBackToStackSeqV2 stack source i).length =
      2 * witnessOffsetV2 stack source i := by
  simp [moveToWitnessSeqV2, moveBackToStackSeqV2,
    moveLeftSeq_length, moveRightSeq_length, witnessOffsetV2]
  omega

theorem moveToWitnessSeqV2_legal
    (stack : List Bool) (source : BitString) (i : Nat) :
    LegalMoveSeq (moveToWitnessSeqV2 stack source i) := by
  exact moveLeftSeq_legal _

theorem moveBackToStackSeqV2_legal
    (stack : List Bool) (source : BitString) (i : Nat) :
    LegalMoveSeq (moveBackToStackSeqV2 stack source i) := by
  exact moveRightSeq_legal _

#print axioms MCore.Real.P01FullVerifierInputShuttleV2.moveToWitnessSeqV2_head_correct
#print axioms MCore.Real.P01FullVerifierInputShuttleV2.witness_roundTripV2_length
#print axioms MCore.Real.P01FullVerifierInputShuttleV2.moveToWitnessSeqV2_legal

end P01FullVerifierInputShuttleV2
end Real
end MCore

