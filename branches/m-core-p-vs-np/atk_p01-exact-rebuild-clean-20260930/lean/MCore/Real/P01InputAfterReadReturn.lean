import MCore.Real.P01InputReturnMode
import MCore.Real.P01EvalCursorMachine
import MCore.Real.MachineRunLemmas

namespace MCore
namespace Real
namespace P01InputAfterReadReturn

open CanonicalFinalProof
open P01EvalCursorMachine
open P01InputReturnMode
open MachineRunLemmas

inductive InputAfterReadReturnState where
  | start : InputReturnMode → InputAfterReadReturnState
  | seekSource
  | scanSource
  | seekFrames
  | scanFrames
  | halt : InputReturnMode → InputAfterReadReturnState
  | reject
  deriving DecidableEq, Repr

/-- Return machine used after the indexed witness reader has restored the
witness and left the head on the witness/source separator.

The finite return mode removes the only ambiguity caused by an all-blank
source tail. -/
def inputAfterReadReturnMachine :
    TM InputAfterReadReturnState (Option Bool) where
  initial := .start .done
  blank := none
  transition := fun q symbol =>
    match q with
    | .start .sourceTail =>
        match symbol with
        | none => (.seekSource, none, .right)
        | some b => (.reject, some b, .stay)
    | .start .frameStack =>
        match symbol with
        | none => (.seekFrames, none, .right)
        | some b => (.reject, some b, .stay)
    | .start .done =>
        (.halt .done, symbol, .stay)
    | .seekSource =>
        match symbol with
        | none => (.seekSource, none, .right)
        | some b => (.scanSource, some b, .right)
    | .scanSource =>
        match symbol with
        | some b => (.scanSource, some b, .right)
        | none => (.scanFrames, none, .right)
    | .seekFrames =>
        match symbol with
        | none => (.seekFrames, none, .right)
        | some b => (.scanFrames, some b, .right)
    | .scanFrames =>
        match symbol with
        | some b => (.scanFrames, some b, .right)
        | none => (.halt .frameStack, none, .stay)
    | .halt mode => (.halt mode, symbol, .stay)
    | .reject => (.reject, symbol, .stay)
  halting := fun q =>
    match q with
    | .halt _ => true
    | .reject => true
    | _ => false

@[simp] theorem inputAfterReadReturnMachine_halt (mode : InputReturnMode) :
    inputAfterReadReturnMachine.halting (.halt mode) = true := rfl

/-- Exact reader-final tape before the mode-aware return phase. -/
def afterIndexedReadTape
    (witness : BitString)
    (consumed : Nat)
    (tail frameStack : BitString)
    (padding : Nat) : Tape (Option Bool) :=
  { left := witness.map some
    head := none
    right :=
      List.replicate consumed none ++
        tail.map some ++
        none :: frameStack.reverse.map some ++
        none :: List.replicate padding none }

/-- Canonical source-scan view for the return machine. -/
def sourceReturnConfig
    (left : List (Option Bool))
    (remaining frameStack : BitString)
    (padding : Nat) :
    Configuration InputAfterReadReturnState (Option Bool) :=
  match remaining with
  | [] =>
      { state := .scanSource
        tape :=
          { left := left
            head := none
            right :=
              frameStack.reverse.map some ++
                none :: List.replicate padding none } }
  | b :: bs =>
      { state := .scanSource
        tape :=
          { left := left
            head := some b
            right :=
              bs.map some ++
                none :: frameStack.reverse.map some ++
                none :: List.replicate padding none } }

@[simp] theorem sourceReturnConfig_state
    (left : List (Option Bool))
    (remaining frameStack : BitString)
    (padding : Nat) :
    (sourceReturnConfig left remaining frameStack padding).state =
      .scanSource := by
  cases remaining <;> rfl

theorem sourceReturn_step_cons
    (left : List (Option Bool))
    (b : Bool) (bs frameStack : BitString)
    (padding : Nat) :
    inputAfterReadReturnMachine.step
      (sourceReturnConfig left (b :: bs) frameStack padding) =
      sourceReturnConfig (some b :: left) bs frameStack padding := by
  cases bs <;>
    simp [sourceReturnConfig, inputAfterReadReturnMachine,
      TM.step, Tape.write, Tape.move, List.append_assoc]

theorem sourceReturn_run
    (left : List (Option Bool))
    (remaining frameStack : BitString)
    (padding : Nat) :
    inputAfterReadReturnMachine.run remaining.length
      (sourceReturnConfig left remaining frameStack padding) =
      sourceReturnConfig
        (remaining.reverse.map some ++ left)
        [] frameStack padding := by
  induction remaining generalizing left with
  | nil =>
      rfl
  | cons b bs ih =>
      rw [List.length_cons]
      rw [TM.run]
      rw [sourceReturnConfig_state]
      simp only [show inputAfterReadReturnMachine.halting (.scanSource) = false by rfl,
        Bool.false_eq_true, if_false]
      rw [sourceReturn_step_cons]
      rw [ih]
      simp [List.reverse_cons, List.map_append, List.append_assoc]

/-- Frame-stack scan view. -/
def frameReturnConfig
    (left : List (Option Bool))
    (remainingRev : BitString)
    (padding : Nat) :
    Configuration InputAfterReadReturnState (Option Bool) :=
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

theorem frameReturn_step_cons
    (left : List (Option Bool))
    (b : Bool) (bs : BitString)
    (padding : Nat) :
    inputAfterReadReturnMachine.step
      (frameReturnConfig left (b :: bs) padding) =
      frameReturnConfig (some b :: left) bs padding := by
  cases bs <;>
    simp [frameReturnConfig, inputAfterReadReturnMachine,
      TM.step, Tape.write, Tape.move, List.append_assoc]

theorem frameReturn_run
    (left : List (Option Bool))
    (remainingRev : BitString)
    (padding : Nat) :
    inputAfterReadReturnMachine.run remainingRev.length
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
      simp only [show inputAfterReadReturnMachine.halting (.scanFrames) = false by rfl,
        Bool.false_eq_true, if_false]
      rw [frameReturn_step_cons]
      rw [ih]
      simp [List.reverse_cons, List.map_append, List.append_assoc]

theorem frameReturn_halt
    (left : List (Option Bool))
    (padding : Nat) :
    inputAfterReadReturnMachine.run 1
      (frameReturnConfig left [] padding) =
      { state := .halt .frameStack
        tape :=
          { left := left
            head := none
            right := List.replicate padding none } } := by
  simp [frameReturnConfig, inputAfterReadReturnMachine,
    TM.run, TM.step, Tape.write, Tape.move]

/-- Normalization used whenever one more physical blank has been crossed. -/
theorem replicate_none_succ_right
    (k : Nat) (tail : List (Option Bool)) :
    List.replicate k none ++ (none :: tail) =
      List.replicate (k + 1) none ++ tail := by
  induction k with
  | zero =>
      rfl
  | succ k ih =>
      simp only [List.replicate_succ, List.cons_append]
      congr 1

/-- Crossing the source/frame separator enters the frame scan. -/
theorem sourceSeparator_to_frames
    (left : List (Option Bool))
    (frameStack : BitString)
    (padding : Nat) :
    inputAfterReadReturnMachine.run 1
      (sourceReturnConfig left [] frameStack padding) =
      frameReturnConfig (none :: left) frameStack.reverse padding := by
  cases h : frameStack.reverse <;>
    simp [sourceReturnConfig, frameReturnConfig,
      inputAfterReadReturnMachine, TM.run, TM.step,
      Tape.write, Tape.move, h, List.append_assoc]

/-- Canonical seek-source configuration with exactly `k` blanks before the
first unread source bit. -/
def seekSourceConfig
    (k : Nat) (b : Bool)
    (left : List (Option Bool))
    (tail frameStack : BitString)
    (padding : Nat) :
    Configuration InputAfterReadReturnState (Option Bool) :=
  match k with
  | 0 =>
      { state := .seekSource
        tape :=
          { left := left
            head := some b
            right :=
              tail.map some ++ none :: frameStack.reverse.map some ++
                none :: List.replicate padding none } }
  | n + 1 =>
      { state := .seekSource
        tape :=
          { left := left
            head := none
            right :=
              List.replicate n none ++ some b ::
                (tail.map some ++ none :: frameStack.reverse.map some ++
                  none :: List.replicate padding none) } }

/-- Seeking across the reader-created blank block consumes the first source bit
and enters the canonical source scan. -/
theorem seekSourceConfig_run
    (k : Nat) (b : Bool)
    (left : List (Option Bool))
    (tail frameStack : BitString)
    (padding : Nat) :
    inputAfterReadReturnMachine.run (k + 1)
      (seekSourceConfig k b left tail frameStack padding) =
      sourceReturnConfig
        (some b :: List.replicate k none ++ left)
        tail frameStack padding := by
  induction k generalizing left with
  | zero =>
      cases tail <;>
        simp [seekSourceConfig, sourceReturnConfig,
          inputAfterReadReturnMachine, TM.run, TM.step,
          Tape.write, Tape.move, List.map_reverse, List.append_assoc]
  | succ k ih =>
      rw [show Nat.succ k + 1 = 1 + (k + 1) by omega]
      rw [run_add]
      have hstep :
          inputAfterReadReturnMachine.run 1
            (seekSourceConfig (Nat.succ k) b left tail frameStack padding) =
          seekSourceConfig k b (none :: left) tail frameStack padding := by
        cases k <;>
          simp [seekSourceConfig, inputAfterReadReturnMachine,
            TM.run, TM.step, Tape.write, Tape.move,
            List.replicate_succ, List.append_assoc]
      rw [hstep]
      rw [ih (none :: left)]
      have hr := replicate_none_succ_right k left
      exact congrArg
        (fun l : List (Option Bool) =>
          sourceReturnConfig (some b :: l) tail frameStack padding)
        hr

/-- Canonical seek-frame configuration with exactly `k` blanks before the
first physical frame bit. -/
def seekFramesConfig
    (k : Nat) (b : Bool) (bs : BitString)
    (left : List (Option Bool))
    (padding : Nat) :
    Configuration InputAfterReadReturnState (Option Bool) :=
  match k with
  | 0 =>
      { state := .seekFrames
        tape :=
          { left := left
            head := some b
            right := bs.map some ++ none :: List.replicate padding none } }
  | n + 1 =>
      { state := .seekFrames
        tape :=
          { left := left
            head := none
            right :=
              List.replicate n none ++
                some b :: bs.map some ++ none :: List.replicate padding none } }

/-- Seeking across a known blank prefix consumes the first physical frame bit
and enters the canonical frame scan. -/
theorem seekFramesConfig_run
    (k : Nat) (b : Bool) (bs : BitString)
    (left : List (Option Bool))
    (padding : Nat) :
    inputAfterReadReturnMachine.run (k + 1)
      (seekFramesConfig k b bs left padding) =
      frameReturnConfig
        (some b :: List.replicate k none ++ left)
        bs padding := by
  induction k generalizing left with
  | zero =>
      cases bs <;>
        simp [seekFramesConfig, frameReturnConfig,
          inputAfterReadReturnMachine, TM.run, TM.step,
          Tape.write, Tape.move, List.map_reverse, List.append_assoc]
  | succ k ih =>
      rw [show Nat.succ k + 1 = 1 + (k + 1) by omega]
      rw [run_add]
      have hstep :
          inputAfterReadReturnMachine.run 1
            (seekFramesConfig (Nat.succ k) b bs left padding) =
          seekFramesConfig k b bs (none :: left) padding := by
        cases k <;>
          simp [seekFramesConfig, inputAfterReadReturnMachine,
            TM.run, TM.step, Tape.write, Tape.move,
            List.replicate_succ, List.append_assoc]
      rw [hstep]
      rw [ih (none :: left)]
      have hr := replicate_none_succ_right k left
      exact congrArg
        (fun l : List (Option Bool) =>
          frameReturnConfig (some b :: l) bs padding)
        hr

/-- Main nonempty-source return theorem. -/
theorem return_sourceTail
    (witness : BitString)
    (consumed : Nat)
    (b : Bool) (tail frameStack : BitString)
    (padding : Nat) :
    inputAfterReadReturnMachine.run
      (consumed + (b :: tail).length + frameStack.length + 3)
      { state := .start .sourceTail,
        tape :=
          afterIndexedReadTape witness consumed
            (b :: tail) frameStack padding } =
      { state := .halt .frameStack,
        tape :=
          evalCursorStackEndTape witness consumed
            (b :: tail) frameStack padding } := by
  let left0 : List (Option Bool) := none :: witness.map some
  let left1 : List (Option Bool) :=
    some b :: List.replicate consumed none ++ left0

  have hstart :
      inputAfterReadReturnMachine.run 1
        { state := .start .sourceTail,
          tape := afterIndexedReadTape witness consumed
            (b :: tail) frameStack padding } =
        seekSourceConfig consumed b left0 tail frameStack padding := by
    cases consumed <;>
      simp [afterIndexedReadTape, seekSourceConfig,
        inputAfterReadReturnMachine, left0,
        TM.run, TM.step, Tape.write, Tape.move,
        List.replicate_succ, List.append_assoc]

  rw [show consumed + (b :: tail).length + frameStack.length + 3 =
      1 + ((consumed + 1) +
        (tail.length + (1 + (frameStack.reverse.length + 1)))) by
      simp
      omega]
  rw [run_add, hstart]
  rw [run_add]
  rw [seekSourceConfig_run consumed b left0 tail frameStack padding]
  change inputAfterReadReturnMachine.run
      (tail.length + (1 + (frameStack.reverse.length + 1)))
      (sourceReturnConfig left1 tail frameStack padding) = _
  rw [run_add]
  rw [sourceReturn_run]
  rw [run_add]
  rw [sourceSeparator_to_frames]
  rw [run_add]
  rw [frameReturn_run]
  rw [frameReturn_halt]
  simp [evalCursorStackEndTape, left0, left1,
    List.reverse_reverse, List.map_append, List.append_assoc,
    Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]

/-- Empty source tail with frames remaining. -/
theorem return_frameStack
    (witness : BitString)
    (consumed : Nat)
    (b : Bool) (frameTail : BitString)
    (padding : Nat) :
    inputAfterReadReturnMachine.run
      (consumed + (b :: frameTail).length + 3)
      { state := .start .frameStack,
        tape :=
          afterIndexedReadTape witness consumed
            [] (b :: frameTail) padding } =
      { state := .halt .frameStack,
        tape :=
          evalCursorStackEndTape witness consumed
            [] (b :: frameTail) padding } := by
  let left0 : List (Option Bool) := none :: witness.map some
  have hne : (b :: frameTail).reverse ≠ [] := by simp
  cases hrev : (b :: frameTail).reverse with
  | nil =>
      exact False.elim (hne hrev)
  | cons f fs =>
      have hlen : (b :: frameTail).length = fs.length + 1 := by
        simpa using congrArg List.length hrev

      have hstart :
          inputAfterReadReturnMachine.run 1
            { state := .start .frameStack,
              tape :=
                afterIndexedReadTape witness consumed
                  [] (b :: frameTail) padding } =
            seekFramesConfig (consumed + 1) f fs left0 padding := by
        cases consumed with
        | zero =>
            simp [afterIndexedReadTape, seekFramesConfig,
              inputAfterReadReturnMachine, left0, hrev,
              TM.run, TM.step, Tape.write, Tape.move,
              List.map_reverse, List.replicate_succ, List.append_assoc]
        | succ n =>
            simp [afterIndexedReadTape, seekFramesConfig,
              inputAfterReadReturnMachine, left0, hrev,
              TM.run, TM.step, Tape.write, Tape.move,
              List.map_reverse, List.replicate_succ, List.append_assoc]
            exact replicate_none_succ_right n
              (some f :: (fs.map some ++ none :: List.replicate padding none))

      rw [show consumed + (b :: frameTail).length + 3 =
          1 + ((consumed + 2) + (fs.length + 1)) by
          rw [hlen]
          omega]
      rw [run_add, hstart]
      rw [run_add]
      rw [seekFramesConfig_run (consumed + 1) f fs left0 padding]
      rw [run_add]
      rw [frameReturn_run]
      rw [frameReturn_halt]
      have horig : b :: frameTail = fs.reverse ++ [f] := by
        have hr := congrArg List.reverse hrev
        simpa [List.reverse_cons, List.reverse_reverse] using hr
      simp [evalCursorStackEndTape, left0, horig,
        List.reverse_reverse, List.map_reverse, List.map_append,
        List.append_assoc, List.replicate_succ]

/-- Final-value mode needs no cursor normalization. -/
theorem return_done
    (witness : BitString)
    (consumed padding : Nat) :
    inputAfterReadReturnMachine.run 1
      { state := .start .done,
        tape := afterIndexedReadTape witness consumed [] [] padding } =
      { state := .halt .done,
        tape := afterIndexedReadTape witness consumed [] [] padding } := by
  rfl

#print axioms MCore.Real.P01InputAfterReadReturn.return_sourceTail
#print axioms MCore.Real.P01InputAfterReadReturn.return_frameStack
#print axioms MCore.Real.P01InputAfterReadReturn.return_done

end P01InputAfterReadReturn
end Real
end MCore
