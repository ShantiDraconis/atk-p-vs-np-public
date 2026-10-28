import MCore.Real.P01InputReturnMode
import MCore.Real.P01EvalCursorMachine
import MCore.Real.P01WitnessIndexedReadPreserving
import MCore.Real.MachineRunLemmas

namespace MCore
namespace Real
namespace P01InputIndexLookahead

open CanonicalFinalProof
open CanonicalCircuitBits
open P01EvalCursorMachine
open P01WitnessIndexedReadPreserving
open P01InputReturnMode
open MachineRunLemmas

inductive InputIndexLookaheadState where
  | scanIndex
  | peekTail
  | peekFrame
  | backSeparator : InputReturnMode → InputIndexLookaheadState
  | rewind : InputReturnMode → InputIndexLookaheadState
  | halt : InputReturnMode → InputIndexLookaheadState
  | reject
  deriving DecidableEq, Repr

/-- Fixed finite control that inspects the finite structural mode following an
input-node unary index and then returns to the first index bit without changing
the tape. -/
def inputIndexLookaheadMachine :
    TM InputIndexLookaheadState (Option Bool) where
  initial := .scanIndex
  blank := none
  transition := fun q symbol =>
    match q with
    | .scanIndex =>
        match symbol with
        | some true => (.scanIndex, some true, .right)
        | some false => (.peekTail, some false, .right)
        | none => (.reject, none, .stay)
    | .peekTail =>
        match symbol with
        | some b => (.rewind .sourceTail, some b, .left)
        | none => (.peekFrame, none, .right)
    | .peekFrame =>
        match symbol with
        | some b => (.backSeparator .frameStack, some b, .left)
        | none => (.backSeparator .done, none, .left)
    | .backSeparator mode =>
        match symbol with
        | none => (.rewind mode, none, .left)
        | some b => (.reject, some b, .stay)
    | .rewind mode =>
        match symbol with
        | some b => (.rewind mode, some b, .left)
        | none => (.halt mode, none, .right)
    | .halt mode => (.halt mode, symbol, .stay)
    | .reject => (.reject, symbol, .stay)
  halting := fun q =>
    match q with
    | .halt _ => true
    | .reject => true
    | _ => false

@[simp] theorem inputIndexLookaheadMachine_halt (mode : InputReturnMode) :
    inputIndexLookaheadMachine.halting (.halt mode) = true := rfl

@[simp] theorem inputIndexLookaheadMachine_initial :
    inputIndexLookaheadMachine.initial = .scanIndex := rfl

/-- Unary encoding as an explicit block of true markers followed by false. -/
theorem encodeNat_eq_replicate_true (i : Nat) :
    encodeNat i = List.replicate i true ++ [false] := by
  induction i with
  | zero =>
      rfl
  | succ i ih =>
      simp [encodeNat, ih, List.replicate_succ]

/-- The actual evaluator cursor with an input index under the head is a simple
right stream consisting of the unary index followed by the untouched physical
suffix. -/
theorem evalCursorReadTape_index_stream
    (witness tail frameStack : BitString)
    (consumed padding i : Nat) :
    evalCursorReadTape witness consumed
        (encodeNat i ++ tail) frameStack padding =
      rightStreamTape
        (List.replicate consumed none ++ none :: witness.map some)
        ((encodeNat i).map some ++
          tail.map some ++ none :: frameStack.reverse.map some ++
            none :: List.replicate padding none) := by
  cases i <;>
    simp [evalCursorReadTape, rightStreamTape, encodeNat,
      List.map_append, List.append_assoc]

/-- A replicated block commutes with one more identical symbol. -/
theorem replicate_same_cons
    {α : Type} (a : α) (k : Nat) (tail : List α) :
    List.replicate k a ++ (a :: tail) =
      List.replicate (k + 1) a ++ tail := by
  induction k with
  | zero =>
      rfl
  | succ k ih =>
      simp only [List.replicate_succ, List.cons_append]
      congr 1

/-- Normalized cursor view: the witness/source separator is the first physical
blank on the left, while the already-consumed blanks are retained behind it. -/
theorem evalCursorReadTape_index_stream_normalized
    (witness tail frameStack : BitString)
    (consumed padding i : Nat) :
    evalCursorReadTape witness consumed
        (encodeNat i ++ tail) frameStack padding =
      rightStreamTape
        (none :: (List.replicate consumed none ++ witness.map some))
        ((encodeNat i).map some ++
          tail.map some ++ none :: frameStack.reverse.map some ++
            none :: List.replicate padding none) := by
  rw [evalCursorReadTape_index_stream]
  congr 2
  exact P01WitnessIndexedReadPreserving.replicate_none_cons
    consumed (witness.map some)

/-- Empty-tail specialization of the normalized cursor view. -/
theorem evalCursorReadTape_index_stream_nil
    (witness frameStack : BitString)
    (consumed padding i : Nat) :
    evalCursorReadTape witness consumed
        (encodeNat i) frameStack padding =
      rightStreamTape
        (none :: (List.replicate consumed none ++ witness.map some))
        ((encodeNat i).map some ++
          none :: frameStack.reverse.map some ++
            none :: List.replicate padding none) := by
  simpa using
    evalCursorReadTape_index_stream_normalized
      witness ([] : BitString) frameStack consumed padding i

/-- Scan a homogeneous block of true unary markers without modifying it. -/
theorem scanIndex_over_true
    (k : Nat)
    (left stream : List (Option Bool)) :
    inputIndexLookaheadMachine.run k
      { state := .scanIndex,
        tape :=
          rightStreamTape left
            (List.replicate k (some true) ++ stream) } =
      { state := .scanIndex,
        tape :=
          rightStreamTape
            (List.replicate k (some true) ++ left)
            stream } := by
  induction k generalizing left with
  | zero =>
      rfl
  | succ k ih =>
      rw [show k + 1 = 1 + k by omega]
      rw [run_add]
      have hstep :
          inputIndexLookaheadMachine.run 1
            { state := .scanIndex,
              tape :=
                rightStreamTape left
                  (List.replicate (1 + k) (some true) ++ stream) } =
            { state := .scanIndex,
              tape :=
                rightStreamTape (some true :: left)
                  (List.replicate k (some true) ++ stream) } := by
        simp only [Nat.one_add, List.replicate_succ]
        cases hrest : List.replicate k (some true) ++ stream <;>
          simp [rightStreamTape, inputIndexLookaheadMachine,
            TM.run, TM.step, Tape.write, Tape.move, hrest]
      rw [hstep]
      rw [ih (some true :: left)]
      apply congrArg
        (fun l : List (Option Bool) =>
          ({ state := .scanIndex,
             tape := rightStreamTape l stream } :
            Configuration InputIndexLookaheadState (Option Bool)))
      simpa [Nat.one_add] using
        replicate_same_cons (some true) k left


/-- A unary payload containing only true markers has no mandatory false
terminator.  The physical lookahead scans all markers and rejects on the first
blank immediately after them. -/
theorem unterminated_true_index_rejects
    (witness frameStack : BitString)
    (consumed padding n : Nat) :
    (inputIndexLookaheadMachine.run (n + 1)
      { state := inputIndexLookaheadMachine.initial,
        tape :=
          evalCursorReadTape witness consumed
            (List.replicate n true) frameStack padding }).state = .reject := by
  let base : List (Option Bool) :=
    List.replicate consumed none ++ none :: witness.map some
  let suffix : List (Option Bool) :=
    none :: frameStack.reverse.map some ++
      none :: List.replicate padding none
  have hview :
      evalCursorReadTape witness consumed
          (List.replicate n true) frameStack padding =
        rightStreamTape base
          (List.replicate n (some true) ++ suffix) := by
    cases n with
    | zero =>
        simp [base, suffix, evalCursorReadTape, rightStreamTape]
    | succ n =>
        simp [base, suffix, evalCursorReadTape, rightStreamTape,
          List.replicate_succ, List.map_replicate, List.append_assoc]
  rw [inputIndexLookaheadMachine_initial, hview]
  rw [show n + 1 = n + 1 by rfl, MachineRunLemmas.run_add]
  rw [scanIndex_over_true n base suffix]
  simp [suffix, rightStreamTape, inputIndexLookaheadMachine,
    TM.run, TM.step, Tape.write, Tape.move]

#print axioms MCore.Real.P01InputIndexLookahead.unterminated_true_index_rejects

/-- One false terminator step enters the finite structural classifier. -/
theorem scanIndex_false
    (left stream : List (Option Bool)) :
    inputIndexLookaheadMachine.run 1
      { state := .scanIndex,
        tape := rightStreamTape left (some false :: stream) } =
      { state := .peekTail,
        tape := rightStreamTape (some false :: left) stream } := by
  cases stream <;>
    simp [rightStreamTape, inputIndexLookaheadMachine,
      TM.run, TM.step, Tape.write, Tape.move]

/-- Generic rewind: starting on the false terminator with a finite Boolean
prefix physically to its left, return to the first symbol of that prefix and
leave the complete segment unchanged. -/
theorem rewind_segment
    (mode : InputReturnMode)
    (bits : BitString) (current : Bool)
    (base right : List (Option Bool)) :
    inputIndexLookaheadMachine.run (bits.length + 2)
      { state := .rewind mode,
        tape :=
          { left := bits.map some ++ (none :: base),
            head := some current,
            right := right } } =
      { state := .halt mode,
        tape :=
          rightStreamTape (none :: base)
            (bits.reverse.map some ++ (some current :: right)) } := by
  induction bits generalizing current right with
  | nil =>
      simp [inputIndexLookaheadMachine, rightStreamTape,
        TM.run, TM.step, Tape.write, Tape.move]
  | cons b bs ih =>
      rw [show (b :: bs).length + 2 =
          1 + (bs.length + 2) by
            simp [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]]
      rw [run_add]
      have hstep :
          inputIndexLookaheadMachine.run 1
            { state := .rewind mode,
              tape :=
                { left := (b :: bs).map some ++ (none :: base),
                  head := some current,
                  right := right } } =
            { state := .rewind mode,
              tape :=
                { left := bs.map some ++ (none :: base),
                  head := some b,
                  right := some current :: right } } := by
        simp [inputIndexLookaheadMachine, TM.run, TM.step,
          Tape.write, Tape.move]
      rw [hstep]
      rw [ih b (some current :: right)]
      apply congrArg
        (fun stream : List (Option Bool) =>
          ({ state := .halt mode,
             tape := rightStreamTape (none :: base) stream } :
            Configuration InputIndexLookaheadState (Option Bool)))
      simp [List.reverse_cons, List.map_append, List.append_assoc]

theorem rewind_index_segment
    (mode : InputReturnMode)
    (bits : BitString)
    (base right : List (Option Bool)) :
    inputIndexLookaheadMachine.run (bits.length + 2)
      { state := .rewind mode,
        tape :=
          { left := bits.map some ++ (none :: base),
            head := some false,
            right := right } } =
      { state := .halt mode,
        tape :=
          rightStreamTape (none :: base)
            (bits.reverse.map some ++ (some false :: right)) } := by
  exact rewind_segment mode bits false base right

/-- Exact source-tail classifier path after the unary false terminator. -/
theorem classify_sourceTail_after_false
    (indexLeft : List (Option Bool))
    (b : Bool) (tail frameStack : BitString)
    (padding : Nat) :
    inputIndexLookaheadMachine.run 1
      { state := .peekTail,
        tape :=
          rightStreamTape (some false :: indexLeft)
            (some b :: tail.map some ++ none ::
              frameStack.reverse.map some ++ none ::
                List.replicate padding none) } =
      { state := .rewind .sourceTail,
        tape :=
          { left := indexLeft,
            head := some false,
            right :=
              some b :: tail.map some ++ none ::
                frameStack.reverse.map some ++ none ::
                  List.replicate padding none } } := by
  simp [rightStreamTape, inputIndexLookaheadMachine,
    TM.run, TM.step, Tape.write, Tape.move, List.append_assoc]

/-- Exact three-step path for an empty source tail and nonempty frame stack. -/
theorem classify_frameStack_after_false
    (indexLeft : List (Option Bool))
    (b : Bool) (frameTail : BitString)
    (padding : Nat) :
    inputIndexLookaheadMachine.run 3
      { state := .peekTail,
        tape :=
          rightStreamTape (some false :: indexLeft)
            (none :: (b :: frameTail).reverse.map some ++
              none :: List.replicate padding none) } =
      { state := .rewind .frameStack,
        tape :=
          { left := indexLeft,
            head := some false,
            right :=
              none :: (b :: frameTail).reverse.map some ++
                none :: List.replicate padding none } } := by
  have hne : (b :: frameTail).reverse ≠ [] := by simp
  cases hrev : (b :: frameTail).reverse with
  | nil =>
      exact False.elim (hne hrev)
  | cons f fs =>
      cases f <;>
        simp [rightStreamTape, inputIndexLookaheadMachine,
          TM.run, TM.step, Tape.write, Tape.move, hrev,
          List.append_assoc]

/-- Exact three-step path when both source tail and frame stack are empty. -/
theorem classify_done_after_false
    (indexLeft : List (Option Bool))
    (padding : Nat) :
    inputIndexLookaheadMachine.run 3
      { state := .peekTail,
        tape :=
          rightStreamTape (some false :: indexLeft)
            (none :: none :: List.replicate padding none) } =
      { state := .rewind .done,
        tape :=
          { left := indexLeft,
            head := some false,
            right := none :: none :: List.replicate padding none } } := by
  simp [rightStreamTape, inputIndexLookaheadMachine,
    TM.run, TM.step, Tape.write, Tape.move]

/-- Full lookahead for a nonempty source tail. -/
theorem lookahead_sourceTail
    (witness : BitString) (consumed i : Nat)
    (b : Bool) (tail frameStack : BitString) (padding : Nat) :
    inputIndexLookaheadMachine.run (2 * i + 4)
      { state := inputIndexLookaheadMachine.initial,
        tape :=
          evalCursorReadTape witness consumed
            (encodeNat i ++ (b :: tail)) frameStack padding } =
      { state := .halt .sourceTail,
        tape :=
          evalCursorReadTape witness consumed
            (encodeNat i ++ (b :: tail)) frameStack padding } := by
  let base : List (Option Bool) :=
    List.replicate consumed none ++ witness.map some
  let suffix : List (Option Bool) :=
    some b :: tail.map some ++ none :: frameStack.reverse.map some ++
      none :: List.replicate padding none

  have hview :
      evalCursorReadTape witness consumed
          (encodeNat i ++ (b :: tail)) frameStack padding =
        rightStreamTape (none :: base)
          (List.replicate i (some true) ++ some false :: suffix) := by
    rw [evalCursorReadTape_index_stream_normalized]
    rw [encodeNat_eq_replicate_true]
    simp [base, suffix, List.map_append, List.map_replicate,
      List.append_assoc]

  rw [inputIndexLookaheadMachine_initial, hview]
  rw [show 2 * i + 4 = i + (1 + (1 + (i + 2))) by omega]

  let C0 : Configuration InputIndexLookaheadState (Option Bool) :=
    { state := .scanIndex,
      tape :=
        rightStreamTape (none :: base)
          (List.replicate i (some true) ++ some false :: suffix) }
  let C1 : Configuration InputIndexLookaheadState (Option Bool) :=
    { state := .scanIndex,
      tape :=
        rightStreamTape
          (List.replicate i (some true) ++ (none :: base))
          (some false :: suffix) }
  let C2 : Configuration InputIndexLookaheadState (Option Bool) :=
    { state := .peekTail,
      tape :=
        rightStreamTape
          (some false ::
            (List.replicate i (some true) ++ (none :: base)))
          suffix }
  let C3 : Configuration InputIndexLookaheadState (Option Bool) :=
    { state := .rewind .sourceTail,
      tape :=
        { left := List.replicate i (some true) ++ (none :: base),
          head := some false,
          right := suffix } }
  let C4 : Configuration InputIndexLookaheadState (Option Bool) :=
    { state := .halt .sourceTail,
      tape :=
        rightStreamTape (none :: base)
          (List.replicate i (some true) ++ some false :: suffix) }

  change inputIndexLookaheadMachine.run
      (i + (1 + (1 + (i + 2)))) C0 = C4

  have hscan : inputIndexLookaheadMachine.run i C0 = C1 := by
    simpa [C0, C1] using
      scanIndex_over_true i (none :: base) (some false :: suffix)

  have hfalse : inputIndexLookaheadMachine.run 1 C1 = C2 := by
    simpa [C1, C2] using
      scanIndex_false
        (List.replicate i (some true) ++ (none :: base)) suffix

  have hclass : inputIndexLookaheadMachine.run 1 C2 = C3 := by
    simpa [C2, C3, suffix] using
      classify_sourceTail_after_false
        (List.replicate i (some true) ++ (none :: base))
        b tail frameStack padding

  have hrew : inputIndexLookaheadMachine.run (i + 2) C3 = C4 := by
    simpa [C3, C4, List.map_replicate] using
      rewind_index_segment .sourceTail
        (List.replicate i true) base suffix

  calc
    inputIndexLookaheadMachine.run
        (i + (1 + (1 + (i + 2)))) C0 =
      inputIndexLookaheadMachine.run
        (1 + (1 + (i + 2)))
        (inputIndexLookaheadMachine.run i C0) :=
      run_add inputIndexLookaheadMachine i
        (1 + (1 + (i + 2))) C0
    _ = inputIndexLookaheadMachine.run
        (1 + (1 + (i + 2))) C1 := by rw [hscan]
    _ = inputIndexLookaheadMachine.run
        (1 + (i + 2))
        (inputIndexLookaheadMachine.run 1 C1) :=
      run_add inputIndexLookaheadMachine 1 (1 + (i + 2)) C1
    _ = inputIndexLookaheadMachine.run
        (1 + (i + 2)) C2 := by rw [hfalse]
    _ = inputIndexLookaheadMachine.run
        (i + 2)
        (inputIndexLookaheadMachine.run 1 C2) :=
      run_add inputIndexLookaheadMachine 1 (i + 2) C2
    _ = inputIndexLookaheadMachine.run (i + 2) C3 := by rw [hclass]
    _ = C4 := hrew

/-- Full lookahead for an empty source tail with frames remaining. -/
theorem lookahead_frameStack
    (witness : BitString) (consumed i : Nat)
    (b : Bool) (frameTail : BitString) (padding : Nat) :
    inputIndexLookaheadMachine.run (2 * i + 6)
      { state := inputIndexLookaheadMachine.initial,
        tape :=
          evalCursorReadTape witness consumed
            (encodeNat i) (b :: frameTail) padding } =
      { state := .halt .frameStack,
        tape :=
          evalCursorReadTape witness consumed
            (encodeNat i) (b :: frameTail) padding } := by
  let base : List (Option Bool) :=
    List.replicate consumed none ++ witness.map some
  let suffix : List (Option Bool) :=
    none :: (b :: frameTail).reverse.map some ++
      none :: List.replicate padding none

  have hview :
      evalCursorReadTape witness consumed
          (encodeNat i) (b :: frameTail) padding =
        rightStreamTape (none :: base)
          (List.replicate i (some true) ++ some false :: suffix) := by
    rw [evalCursorReadTape_index_stream_nil]
    rw [encodeNat_eq_replicate_true]
    simp [base, suffix, List.map_append, List.map_replicate,
      List.append_assoc]

  rw [inputIndexLookaheadMachine_initial, hview]
  rw [show 2 * i + 6 = i + (1 + (3 + (i + 2))) by omega]

  let C0 : Configuration InputIndexLookaheadState (Option Bool) :=
    { state := .scanIndex,
      tape := rightStreamTape (none :: base)
        (List.replicate i (some true) ++ some false :: suffix) }
  let C1 : Configuration InputIndexLookaheadState (Option Bool) :=
    { state := .scanIndex,
      tape := rightStreamTape
        (List.replicate i (some true) ++ (none :: base))
        (some false :: suffix) }
  let C2 : Configuration InputIndexLookaheadState (Option Bool) :=
    { state := .peekTail,
      tape := rightStreamTape
        (some false ::
          (List.replicate i (some true) ++ (none :: base)))
        suffix }
  let C3 : Configuration InputIndexLookaheadState (Option Bool) :=
    { state := .rewind .frameStack,
      tape :=
        { left := List.replicate i (some true) ++ (none :: base),
          head := some false,
          right := suffix } }
  let C4 : Configuration InputIndexLookaheadState (Option Bool) :=
    { state := .halt .frameStack,
      tape := rightStreamTape (none :: base)
        (List.replicate i (some true) ++ some false :: suffix) }

  change inputIndexLookaheadMachine.run
      (i + (1 + (3 + (i + 2)))) C0 = C4

  have hscan : inputIndexLookaheadMachine.run i C0 = C1 := by
    simpa [C0, C1] using
      scanIndex_over_true i (none :: base) (some false :: suffix)

  have hfalse : inputIndexLookaheadMachine.run 1 C1 = C2 := by
    simpa [C1, C2] using
      scanIndex_false
        (List.replicate i (some true) ++ (none :: base)) suffix

  have hclass : inputIndexLookaheadMachine.run 3 C2 = C3 := by
    simpa [C2, C3, suffix] using
      classify_frameStack_after_false
        (List.replicate i (some true) ++ (none :: base))
        b frameTail padding

  have hrew : inputIndexLookaheadMachine.run (i + 2) C3 = C4 := by
    simpa [C3, C4, List.map_replicate] using
      rewind_index_segment .frameStack
        (List.replicate i true) base suffix

  calc
    inputIndexLookaheadMachine.run
        (i + (1 + (3 + (i + 2)))) C0 =
      inputIndexLookaheadMachine.run
        (1 + (3 + (i + 2)))
        (inputIndexLookaheadMachine.run i C0) :=
      run_add inputIndexLookaheadMachine i
        (1 + (3 + (i + 2))) C0
    _ = inputIndexLookaheadMachine.run
        (1 + (3 + (i + 2))) C1 := by rw [hscan]
    _ = inputIndexLookaheadMachine.run
        (3 + (i + 2))
        (inputIndexLookaheadMachine.run 1 C1) :=
      run_add inputIndexLookaheadMachine 1 (3 + (i + 2)) C1
    _ = inputIndexLookaheadMachine.run
        (3 + (i + 2)) C2 := by rw [hfalse]
    _ = inputIndexLookaheadMachine.run
        (i + 2)
        (inputIndexLookaheadMachine.run 3 C2) :=
      run_add inputIndexLookaheadMachine 3 (i + 2) C2
    _ = inputIndexLookaheadMachine.run (i + 2) C3 := by rw [hclass]
    _ = C4 := hrew

/-- Full lookahead when the input value will be the final evaluator value. -/
theorem lookahead_done
    (witness : BitString) (consumed i padding : Nat) :
    inputIndexLookaheadMachine.run (2 * i + 6)
      { state := inputIndexLookaheadMachine.initial,
        tape :=
          evalCursorReadTape witness consumed (encodeNat i) [] padding } =
      { state := .halt .done,
        tape :=
          evalCursorReadTape witness consumed (encodeNat i) [] padding } := by
  let base : List (Option Bool) :=
    List.replicate consumed none ++ witness.map some
  let suffix : List (Option Bool) :=
    none :: none :: List.replicate padding none

  have hview :
      evalCursorReadTape witness consumed (encodeNat i) [] padding =
        rightStreamTape (none :: base)
          (List.replicate i (some true) ++ some false :: suffix) := by
    rw [evalCursorReadTape_index_stream_nil]
    rw [encodeNat_eq_replicate_true]
    simp [base, suffix, List.map_append, List.map_replicate,
      List.append_assoc]

  rw [inputIndexLookaheadMachine_initial, hview]
  rw [show 2 * i + 6 = i + (1 + (3 + (i + 2))) by omega]

  let C0 : Configuration InputIndexLookaheadState (Option Bool) :=
    { state := .scanIndex,
      tape := rightStreamTape (none :: base)
        (List.replicate i (some true) ++ some false :: suffix) }
  let C1 : Configuration InputIndexLookaheadState (Option Bool) :=
    { state := .scanIndex,
      tape := rightStreamTape
        (List.replicate i (some true) ++ (none :: base))
        (some false :: suffix) }
  let C2 : Configuration InputIndexLookaheadState (Option Bool) :=
    { state := .peekTail,
      tape := rightStreamTape
        (some false ::
          (List.replicate i (some true) ++ (none :: base)))
        suffix }
  let C3 : Configuration InputIndexLookaheadState (Option Bool) :=
    { state := .rewind .done,
      tape :=
        { left := List.replicate i (some true) ++ (none :: base),
          head := some false,
          right := suffix } }
  let C4 : Configuration InputIndexLookaheadState (Option Bool) :=
    { state := .halt .done,
      tape := rightStreamTape (none :: base)
        (List.replicate i (some true) ++ some false :: suffix) }

  change inputIndexLookaheadMachine.run
      (i + (1 + (3 + (i + 2)))) C0 = C4

  have hscan : inputIndexLookaheadMachine.run i C0 = C1 := by
    simpa [C0, C1] using
      scanIndex_over_true i (none :: base) (some false :: suffix)

  have hfalse : inputIndexLookaheadMachine.run 1 C1 = C2 := by
    simpa [C1, C2] using
      scanIndex_false
        (List.replicate i (some true) ++ (none :: base)) suffix

  have hclass : inputIndexLookaheadMachine.run 3 C2 = C3 := by
    simpa [C2, C3, suffix] using
      classify_done_after_false
        (List.replicate i (some true) ++ (none :: base)) padding

  have hrew : inputIndexLookaheadMachine.run (i + 2) C3 = C4 := by
    simpa [C3, C4, List.map_replicate] using
      rewind_index_segment .done
        (List.replicate i true) base suffix

  calc
    inputIndexLookaheadMachine.run
        (i + (1 + (3 + (i + 2)))) C0 =
      inputIndexLookaheadMachine.run
        (1 + (3 + (i + 2)))
        (inputIndexLookaheadMachine.run i C0) :=
      run_add inputIndexLookaheadMachine i
        (1 + (3 + (i + 2))) C0
    _ = inputIndexLookaheadMachine.run
        (1 + (3 + (i + 2))) C1 := by rw [hscan]
    _ = inputIndexLookaheadMachine.run
        (3 + (i + 2))
        (inputIndexLookaheadMachine.run 1 C1) :=
      run_add inputIndexLookaheadMachine 1 (3 + (i + 2)) C1
    _ = inputIndexLookaheadMachine.run
        (3 + (i + 2)) C2 := by rw [hfalse]
    _ = inputIndexLookaheadMachine.run
        (i + 2)
        (inputIndexLookaheadMachine.run 3 C2) :=
      run_add inputIndexLookaheadMachine 3 (i + 2) C2
    _ = inputIndexLookaheadMachine.run (i + 2) C3 := by rw [hclass]
    _ = C4 := hrew

/-- Uniform lookahead fuel.  The source-tail case halts two steps earlier and
therefore remains stable under the extra fuel. -/
theorem lookahead_inputReturnMode
    (witness tail frameStack : BitString)
    (consumed padding i : Nat) :
    inputIndexLookaheadMachine.run (2 * i + 6)
      { state := inputIndexLookaheadMachine.initial,
        tape :=
          evalCursorReadTape witness consumed
            (encodeNat i ++ tail) frameStack padding } =
      { state := .halt (inputReturnModeOf tail frameStack),
        tape :=
          evalCursorReadTape witness consumed
            (encodeNat i ++ tail) frameStack padding } := by
  cases tail with
  | cons b bs =>
      have h := lookahead_sourceTail
        witness consumed i b bs frameStack padding
      have hle : 2 * i + 4 ≤ 2 * i + 6 := by omega
      have hh :
          inputIndexLookaheadMachine.halting
            (.halt .sourceTail) = true := rfl
      have hlong :=
        run_to_larger_fuel_of_halt
          inputIndexLookaheadMachine
          { state := inputIndexLookaheadMachine.initial,
            tape :=
              evalCursorReadTape witness consumed
                (encodeNat i ++ (b :: bs)) frameStack padding }
          { state := .halt .sourceTail,
            tape :=
              evalCursorReadTape witness consumed
                (encodeNat i ++ (b :: bs)) frameStack padding }
          hle h hh
      simpa [inputReturnModeOf] using hlong
  | nil =>
      cases frameStack with
      | cons b bs =>
          simpa [inputReturnModeOf] using
            lookahead_frameStack witness consumed i b bs padding
      | nil =>
          simpa [inputReturnModeOf] using
            lookahead_done witness consumed i padding

#print axioms MCore.Real.P01InputIndexLookahead.lookahead_sourceTail
#print axioms MCore.Real.P01InputIndexLookahead.lookahead_frameStack
#print axioms MCore.Real.P01InputIndexLookahead.lookahead_done
#print axioms MCore.Real.P01InputIndexLookahead.lookahead_inputReturnMode

end P01InputIndexLookahead
end Real
end MCore
