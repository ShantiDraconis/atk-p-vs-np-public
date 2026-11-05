import MCore.Real.P01EvalCursorMachine
import MCore.Real.MachineRunLemmas

namespace MCore
namespace Real
namespace P01InputReturnMode

open CanonicalFinalProof
open P01EvalCursorMachine
open MachineRunLemmas

/-- What lies immediately after the unary input index in the physical source
stream.  This finite datum is sufficient to remove the otherwise ambiguous
all-blank return case after an indexed witness read. -/
inductive InputReturnMode where
  | sourceTail
  | frameStack
  | done
  deriving DecidableEq, Repr

inductive InputReturnClassifyState where
  | start
  | peekTail
  | peekFrame
  | backSeparator : InputReturnMode → InputReturnClassifyState
  | halt : InputReturnMode → InputReturnClassifyState
  | reject
  deriving DecidableEq, Repr

/-- Fixed finite-control lookahead executed while the head is on the false
terminator of `encodeNat i`.

It inspects at most two cells to the right and returns to the same terminator:
* a source bit means the unread source tail is nonempty;
* a blank followed by a frame bit means the source tail is empty but frames
  remain;
* two blanks mean both the source tail and frame stack are empty.

No tape symbol is changed. -/
def inputReturnClassifyMachine :
    TM InputReturnClassifyState (Option Bool) where
  initial := .start
  blank := none
  transition := fun q symbol =>
    match q with
    | .start =>
        match symbol with
        | some false => (.peekTail, some false, .right)
        | some true => (.reject, some true, .stay)
        | none => (.reject, none, .stay)
    | .peekTail =>
        match symbol with
        | some b => (.halt .sourceTail, some b, .left)
        | none => (.peekFrame, none, .right)
    | .peekFrame =>
        match symbol with
        | some b => (.backSeparator .frameStack, some b, .left)
        | none => (.backSeparator .done, none, .left)
    | .backSeparator mode =>
        match symbol with
        | none => (.halt mode, none, .left)
        | some b => (.reject, some b, .stay)
    | .halt mode => (.halt mode, symbol, .stay)
    | .reject => (.reject, symbol, .stay)
  halting := fun q =>
    match q with
    | .halt _ => true
    | .reject => true
    | _ => false

@[simp] theorem inputReturnClassifyMachine_halt (mode : InputReturnMode) :
    inputReturnClassifyMachine.halting (.halt mode) = true := rfl

/-- Physical tape view with the head on the unary false terminator.  The left
side is intentionally arbitrary: it contains the true unary prefix and the
already-consumed source/witness region. -/
def inputTerminatorTape
    (left : List (Option Bool))
    (tail frameStack : BitString)
    (padding : Nat) : Tape (Option Bool) :=
  { left := left
    head := some false
    right :=
      tail.map some ++
        none :: frameStack.reverse.map some ++
        none :: List.replicate padding none }

/-- Nonempty source tail classification.  Extra fuel is inert after the
two-step classification halts. -/
theorem classify_sourceTail
    (left : List (Option Bool))
    (b : Bool) (tail frameStack : BitString)
    (padding : Nat) :
    inputReturnClassifyMachine.run 4
      { state := inputReturnClassifyMachine.initial,
        tape := inputTerminatorTape left (b :: tail) frameStack padding } =
      { state := .halt .sourceTail,
        tape := inputTerminatorTape left (b :: tail) frameStack padding } := by
  cases b <;>
    simp [inputReturnClassifyMachine, inputTerminatorTape,
      TM.run, TM.step, Tape.write, Tape.move, run_halted,
      List.append_assoc]

/-- Empty source tail with a nonempty encoded frame stack. -/
theorem classify_frameStack
    (left : List (Option Bool))
    (b : Bool) (frameTail : BitString)
    (padding : Nat) :
    inputReturnClassifyMachine.run 4
      { state := inputReturnClassifyMachine.initial,
        tape := inputTerminatorTape left [] (b :: frameTail) padding } =
      { state := .halt .frameStack,
        tape := inputTerminatorTape left [] (b :: frameTail) padding } := by
  have hne : (b :: frameTail).reverse ≠ [] := by
    simp
  cases hrev : (b :: frameTail).reverse with
  | nil =>
      exact False.elim (hne hrev)
  | cons x xs =>
      have hmap :
          (b :: frameTail).reverse.map some =
            some x :: xs.map some := by
        rw [hrev]
        rfl
      have htape :
          inputTerminatorTape left [] (b :: frameTail) padding =
            { left := left,
              head := some false,
              right :=
                none :: some x :: xs.map some ++
                  none :: List.replicate padding none } := by
        unfold inputTerminatorTape
        rw [hmap]
        rfl
      rw [htape]
      cases x <;>
        simp [inputReturnClassifyMachine,
          TM.run, TM.step, Tape.write, Tape.move,
          List.append_assoc]

/-- Empty source tail and empty frame stack: the semantic input value is already
a final evaluator value. -/
theorem classify_done
    (left : List (Option Bool))
    (padding : Nat) :
    inputReturnClassifyMachine.run 4
      { state := inputReturnClassifyMachine.initial,
        tape := inputTerminatorTape left [] [] padding } =
      { state := .halt .done,
        tape := inputTerminatorTape left [] [] padding } := by
  simp [inputReturnClassifyMachine, inputTerminatorTape,
    TM.run, TM.step, Tape.write, Tape.move, List.append_assoc]

/-- Canonical finite return mode determined by the unread source tail and
encoded frame stack. -/
def inputReturnModeOf
    (tail frameStack : BitString) : InputReturnMode :=
  match tail with
  | _ :: _ => .sourceTail
  | [] =>
      match frameStack with
      | _ :: _ => .frameStack
      | [] => .done

/-- The classifier computes exactly `inputReturnModeOf` and restores the
terminator tape unchanged. -/
theorem classify_inputReturnMode
    (left : List (Option Bool))
    (tail frameStack : BitString)
    (padding : Nat) :
    inputReturnClassifyMachine.run 4
      { state := inputReturnClassifyMachine.initial,
        tape := inputTerminatorTape left tail frameStack padding } =
      { state := .halt (inputReturnModeOf tail frameStack),
        tape := inputTerminatorTape left tail frameStack padding } := by
  cases tail with
  | cons b bs =>
      simpa [inputReturnModeOf] using
        classify_sourceTail left b bs frameStack padding
  | nil =>
      cases frameStack with
      | cons b bs =>
          simpa [inputReturnModeOf] using
            classify_frameStack left b bs padding
      | nil =>
          simpa [inputReturnModeOf] using
            classify_done left padding

#print axioms MCore.Real.P01InputReturnMode.classify_inputReturnMode

#print axioms MCore.Real.P01InputReturnMode.classify_sourceTail
#print axioms MCore.Real.P01InputReturnMode.classify_frameStack
#print axioms MCore.Real.P01InputReturnMode.classify_done

end P01InputReturnMode
end Real
end MCore
