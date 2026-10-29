import MCore.Real.P01WitnessIndexedRead
import MCore.Real.MachineRunLemmas

namespace MCore
namespace Real
namespace P01WitnessIndexedReadPreserving

open CanonicalFinalProof
open CanonicalCircuitBits
open CanonicalSATWitness
open P01WitnessIndexedRead
open MachineRunLemmas

/-- Fixed finite control for a preserving unary-index witness read.

The machine never stores the unbounded index in control.  Each consumed unary
true marker advances a blank separator one witness cell to the left.  The
already-crossed witness prefix is moved, not erased.  At the false terminator
the selected witness bit is read, then the separator is moved back to its
original position, restoring the witness exactly. -/
inductive PreservingReadState where
  | indexNoMoved
  | indexMoved
  | advanceSep
  | seekMoved
  | scanMoved
  | capture
  | writeMoved : Bool → PreservingReadState
  | returnMoved
  | returnBlanks
  | finalSepNoMoved
  | finalReadNoMoved
  | finalSeekMoved
  | finalScanMoved
  | finalReadMoved
  | restoreStart : Bool → PreservingReadState
  | restoreInspect : Bool → PreservingReadState
  | restoreWrite : Bool → Bool → PreservingReadState
  | restoreHalt : Bool → PreservingReadState
  | halt : Bool → PreservingReadState
  | reject
  deriving DecidableEq, Repr

/-- The preserving reader.  It uses only the canonical tape alphabet
`Option Bool`: no extra marker symbol is introduced. -/
def preservingReadMachine : TM PreservingReadState (Option Bool) where
  initial := .indexNoMoved
  blank := none
  transition := fun q symbol =>
    match q with
    | .indexNoMoved =>
        match symbol with
        | some true => (.advanceSep, none, .left)
        | some false => (.finalSepNoMoved, none, .left)
        | none => (.reject, none, .stay)
    | .indexMoved =>
        match symbol with
        | some true => (.seekMoved, none, .left)
        | some false => (.finalSeekMoved, none, .left)
        | none => (.reject, none, .stay)
    | .advanceSep =>
        match symbol with
        | none => (.advanceSep, none, .left)
        | some b => (.writeMoved b, none, .right)
    | .seekMoved =>
        match symbol with
        | none => (.seekMoved, none, .left)
        | some b => (.scanMoved, some b, .left)
    | .scanMoved =>
        match symbol with
        | some b => (.scanMoved, some b, .left)
        | none => (.capture, none, .left)
    | .capture =>
        match symbol with
        | some b => (.writeMoved b, none, .right)
        | none => (.reject, none, .stay)
    | .writeMoved b =>
        match symbol with
        | none => (.returnMoved, some b, .right)
        | some c => (.reject, some c, .stay)
    | .returnMoved =>
        match symbol with
        | some b => (.returnMoved, some b, .right)
        | none => (.returnBlanks, none, .right)
    | .returnBlanks =>
        match symbol with
        | none => (.returnBlanks, none, .right)
        | some b => (.indexMoved, some b, .stay)
    | .finalSepNoMoved =>
        match symbol with
        | none => (.finalSepNoMoved, none, .left)
        | some b => (.restoreHalt b, some b, .right)
    | .finalReadNoMoved =>
        match symbol with
        | some b => (.restoreHalt b, some b, .right)
        | none => (.reject, none, .stay)
    | .finalSeekMoved =>
        match symbol with
        | none => (.finalSeekMoved, none, .left)
        | some b => (.finalScanMoved, some b, .left)
    | .finalScanMoved =>
        match symbol with
        | some b => (.finalScanMoved, some b, .left)
        | none => (.finalReadMoved, none, .left)
    | .finalReadMoved =>
        match symbol with
        | some b => (.restoreStart b, some b, .right)
        | none => (.reject, none, .stay)
    | .restoreStart result =>
        match symbol with
        | none => (.restoreInspect result, none, .right)
        | some b => (.reject, some b, .stay)
    | .restoreInspect result =>
        match symbol with
        | some b => (.restoreWrite result b, none, .left)
        | none => (.restoreHalt result, none, .left)
    | .restoreWrite result b =>
        match symbol with
        | none => (.restoreStart result, some b, .right)
        | some c => (.reject, some c, .stay)
    | .restoreHalt result =>
        match symbol with
        | none => (.halt result, none, .stay)
        | some b => (.reject, some b, .stay)
    | .halt result => (.halt result, symbol, .stay)
    | .reject => (.reject, symbol, .stay)
  halting := fun q =>
    match q with
    | .halt _ => true
    | .reject => true
    | _ => false

@[simp] theorem preservingReadMachine_blank :
    preservingReadMachine.blank = none := rfl

@[simp] theorem preservingReadMachine_halt (b : Bool) :
    preservingReadMachine.halting (.halt b) = true := rfl

@[simp] theorem preservingReadMachine_reject :
    preservingReadMachine.halting .reject = true := rfl

/-- Canonical input layout for the preserving reader.  The unary index remains
the physical counter; `tail` is arbitrary unread source data and is never part
of finite control. -/
def preservingReadTape
    (witness : BitString) (i : Nat) (tail : BitString) :
    Tape (Option Bool) :=
  match encodeNat i ++ tail with
  | [] =>
      { left := none :: witness.map some, head := none, right := [] }
  | b :: bs =>
      { left := none :: witness.map some,
        head := some b,
        right := bs.map some }

/-- Canonical intermediate layout after at least one unary true marker has
been consumed.  `moved` is the witness prefix temporarily shifted across the
separator; `rest` is the untouched witness suffix. -/
def preservingMovedTape
    (moved rest : BitString) (remaining : Nat) (tail : BitString) :
    Tape (Option Bool) :=
  match encodeNat remaining ++ tail with
  | [] =>
      { left := List.replicate moved.length none ++ moved.map some ++
          (none :: rest.map some),
        head := none,
        right := [] }
  | b :: bs =>
      { left := List.replicate moved.length none ++ moved.map some ++
          (none :: rest.map some),
        head := some b,
        right := bs.map some }

/-- Intermediate machine configuration used by the successor induction. -/
def preservingMovedConfig
    (moved rest : BitString) (remaining : Nat) (tail : BitString) :
    Configuration PreservingReadState (Option Bool) :=
  { state := .indexMoved,
    tape := preservingMovedTape moved rest remaining tail }

/-- Enter the moved-prefix invariant after the first unary true marker. -/
theorem preservingRead_start_successor
    (b : Bool) (witnessTail tail : BitString) (n : Nat) :
    preservingReadMachine.run 6
      { state := preservingReadMachine.initial,
        tape := preservingReadTape (b :: witnessTail) (n + 1) tail } =
      preservingMovedConfig [b] witnessTail n tail := by
  cases b <;> cases n <;>
    simp [preservingReadMachine, preservingReadTape,
      preservingMovedConfig, preservingMovedTape, encodeNat,
      TM.run, TM.step, Tape.write, Tape.move]

/-- Appending one more blank after a replicated blank block is the same as
increasing the replication count. -/
theorem replicate_none_extend
    (k : Nat) (right : List (Option Bool)) :
    List.replicate (k + 1) none ++ (none :: right) =
      List.replicate (k + 2) none ++ right := by
  induction k with
  | zero => rfl
  | succ k ih =>
      simp only [Nat.succ_add, List.replicate_succ, List.cons_append]
      congr 1

/-- `seekMoved` crosses a finite block of blanks and stops on the first
moved witness bit.  This is the first generic traversal lemma needed by the
successor cycle. -/
theorem seekMoved_over_blanks
    (k : Nat) (b : Bool)
    (left right : List (Option Bool)) :
    preservingReadMachine.run (k + 1)
      { state := .seekMoved,
        tape :=
          { left := List.replicate k none ++ (some b :: left),
            head := none,
            right := right } } =
      { state := .seekMoved,
        tape :=
          { left := left,
            head := some b,
            right := List.replicate (k + 1) none ++ right } } := by
  induction k generalizing right with
  | zero =>
      simp [preservingReadMachine, TM.run, TM.step, Tape.write, Tape.move]
  | succ k ih =>
      rw [show Nat.succ k + 1 = (k + 1) + 1 by omega]
      rw [TM.run]
      simp only [show preservingReadMachine.halting (.seekMoved) = false by rfl,
        Bool.false_eq_true, if_false]
      change preservingReadMachine.run (k + 1)
        { state := .seekMoved,
          tape :=
            { left := List.replicate k none ++ (some b :: left),
              head := none,
              right := none :: right } } =
        { state := .seekMoved,
          tape :=
            { left := left,
              head := some b,
              right := List.replicate (Nat.succ k + 1) none ++ right } }
      rw [ih (none :: right)]
      apply congrArg
        (fun r : List (Option Bool) =>
          ({ state := .seekMoved,
             tape := { left := left, head := some b, right := r } } :
            Configuration PreservingReadState (Option Bool)))
      simpa [Nat.succ_eq_add_one, Nat.add_assoc] using
        replicate_none_extend k right

/-- Tape view used while `scanMoved` walks left across the already-moved
witness prefix.  The blank separator and selected witness bit are immediately
after `bits` in the leftward direction. -/
def scanMovedTape
    (bits : BitString) (b : Bool)
    (left right : List (Option Bool)) :
    Tape (Option Bool) :=
  match bits with
  | [] =>
      { left := some b :: left,
        head := none,
        right := right }
  | x :: xs =>
      { left := xs.map some ++ (none :: some b :: left),
        head := some x,
        right := right }

/-- One physical `scanMoved` step peels the current moved witness bit
and pushes it onto the right side of the tape. -/
theorem scanMoved_step_cons
    (x b : Bool) (xs : BitString)
    (left right : List (Option Bool)) :
    preservingReadMachine.step
      { state := .scanMoved,
        tape := scanMovedTape (x :: xs) b left right } =
      { state := .scanMoved,
        tape := scanMovedTape xs b left (some x :: right) } := by
  cases xs <;>
    simp [scanMovedTape, preservingReadMachine,
      TM.step, Tape.write, Tape.move]

/-- `scanMoved` crosses every moved witness bit and then the separator,
arriving at `capture` with the selected witness bit under the head. -/
theorem scanMoved_over_bits
    (bits : BitString) (b : Bool)
    (left right : List (Option Bool)) :
    preservingReadMachine.run (bits.length + 1)
      { state := .scanMoved,
        tape := scanMovedTape bits b left right } =
      { state := .capture,
        tape :=
          { left := left,
            head := some b,
            right := none :: (bits.reverse.map some ++ right) } } := by
  induction bits generalizing right with
  | nil =>
      simp [scanMovedTape, preservingReadMachine,
        TM.run, TM.step, Tape.write, Tape.move]
  | cons x xs ih =>
      rw [show (x :: xs).length + 1 = (xs.length + 1) + 1 by simp]
      rw [TM.run]
      simp only [show preservingReadMachine.halting (.scanMoved) = false by rfl,
        Bool.false_eq_true, if_false]
      rw [scanMoved_step_cons]
      rw [ih (some x :: right)]
      apply congrArg
        (fun r : List (Option Bool) =>
          ({ state := .capture,
             tape := { left := left, head := some b, right := r } } :
            Configuration PreservingReadState (Option Bool)))
      simp [List.reverse_cons, List.map_append, List.append_assoc]

/-- Canonical view of a rightward stream under a fixed left tape. -/
def rightStreamTape
    (left stream : List (Option Bool)) :
    Tape (Option Bool) :=
  match stream with
  | [] =>
      { left := left, head := none, right := [] }
  | x :: xs =>
      { left := left, head := x, right := xs }

/-- Tape view while `returnMoved` walks right across the reversed moved
prefix and then crosses its separator blank. -/
def returnMovedTape
    (bits : BitString)
    (left after : List (Option Bool)) :
    Tape (Option Bool) :=
  match bits with
  | [] =>
      rightStreamTape left (none :: after)
  | x :: xs =>
      { left := left,
        head := some x,
        right := xs.map some ++ (none :: after) }

/-- One `returnMoved` step consumes the current moved-prefix bit. -/
theorem returnMoved_step_cons
    (x : Bool) (xs : BitString)
    (left after : List (Option Bool)) :
    preservingReadMachine.step
      { state := .returnMoved,
        tape := returnMovedTape (x :: xs) left after } =
      { state := .returnMoved,
        tape := returnMovedTape xs (some x :: left) after } := by
  cases xs <;>
    simp [returnMovedTape, rightStreamTape, preservingReadMachine,
      TM.step, Tape.write, Tape.move]

/-- `returnMoved` restores all moved-prefix bits on the left and crosses the
separator, entering `returnBlanks` at the first symbol of `after`. -/
theorem returnMoved_over_bits
    (bits : BitString)
    (left after : List (Option Bool)) :
    preservingReadMachine.run (bits.length + 1)
      { state := .returnMoved,
        tape := returnMovedTape bits left after } =
      { state := .returnBlanks,
        tape :=
          rightStreamTape
            (none :: (bits.reverse.map some ++ left))
            after } := by
  induction bits generalizing left with
  | nil =>
      cases after <;>
        simp [returnMovedTape, rightStreamTape, preservingReadMachine,
          TM.run, TM.step, Tape.write, Tape.move]
  | cons x xs ih =>
      rw [show (x :: xs).length + 1 = (xs.length + 1) + 1 by simp]
      rw [TM.run]
      simp only [show preservingReadMachine.halting (.returnMoved) = false by rfl,
        Bool.false_eq_true, if_false]
      rw [returnMoved_step_cons]
      rw [ih (some x :: left)]
      apply congrArg
        (fun l : List (Option Bool) =>
          ({ state := .returnBlanks,
             tape := rightStreamTape l after } :
            Configuration PreservingReadState (Option Bool)))
      simp [List.reverse_cons, List.map_append, List.append_assoc]

/-- `returnBlanks` crosses a finite blank block and changes back to
`indexMoved` on the first nonblank source bit. -/
theorem returnBlanks_over_blanks
    (k : Nat) (b : Bool)
    (left right : List (Option Bool)) :
    preservingReadMachine.run (k + 2)
      { state := .returnBlanks,
        tape :=
          { left := left,
            head := none,
            right := List.replicate k none ++ (some b :: right) } } =
      { state := .indexMoved,
        tape :=
          { left := List.replicate (k + 1) none ++ left,
            head := some b,
            right := right } } := by
  induction k generalizing left with
  | zero =>
      simp [preservingReadMachine, TM.run, TM.step, Tape.write, Tape.move]
  | succ k ih =>
      rw [show Nat.succ k + 2 = (k + 2) + 1 by omega]
      rw [TM.run]
      simp only [show preservingReadMachine.halting (.returnBlanks) = false by rfl,
        Bool.false_eq_true, if_false]
      change preservingReadMachine.run (k + 2)
        { state := .returnBlanks,
          tape :=
            { left := none :: left,
              head := none,
              right := List.replicate k none ++ (some b :: right) } } =
        { state := .indexMoved,
          tape :=
            { left := List.replicate (Nat.succ k + 1) none ++ left,
              head := some b,
              right := right } }
      rw [ih (none :: left)]
      apply congrArg
        (fun l : List (Option Bool) =>
          ({ state := .indexMoved,
             tape := { left := l, head := some b, right := right } } :
            Configuration PreservingReadState (Option Bool)))
      simpa [Nat.succ_eq_add_one, Nat.add_assoc] using
        replicate_none_extend k left

/-- Same moved-prefix layout as `preservingMovedTape`, but with the unread
source supplied directly.  This removes unary-encoding case splits from the
physical successor cycle. -/
def movedBitsTape
    (moved rest source : BitString) :
    Tape (Option Bool) :=
  match source with
  | [] =>
      { left := List.replicate moved.length none ++ moved.map some ++
          (none :: rest.map some),
        head := none,
        right := [] }
  | x :: xs =>
      { left := List.replicate moved.length none ++ moved.map some ++
          (none :: rest.map some),
        head := some x,
        right := xs.map some }

def movedBitsConfig
    (moved rest source : BitString) :
    Configuration PreservingReadState (Option Bool) :=
  { state := .indexMoved,
    tape := movedBitsTape moved rest source }

theorem preservingMovedConfig_eq_bits
    (moved rest : BitString) (n : Nat) (tail : BitString) :
    preservingMovedConfig moved rest n tail =
      movedBitsConfig moved rest (encodeNat n ++ tail) := by
  cases n <;>
    rfl

/-- Once `seekMoved` is sitting on the first moved witness bit, one physical
step enters the generic `scanMovedTape` view. -/
theorem seekMoved_step_bit
    (first b : Bool) (movedTail : BitString)
    (left right : List (Option Bool)) :
    preservingReadMachine.step
      { state := .seekMoved,
        tape :=
          { left := movedTail.map some ++ (none :: some b :: left),
            head := some first,
            right := right } } =
      { state := .scanMoved,
        tape := scanMovedTape movedTail b left (some first :: right) } := by
  cases movedTail <;>
    simp [scanMovedTape, preservingReadMachine,
      TM.step, Tape.write, Tape.move]

/-- The fixed capture/write pair shifts the selected witness bit into the
temporary separator and starts the rightward return on an arbitrary stream. -/
theorem capture_write_to_stream
    (b : Bool) (left stream : List (Option Bool)) :
    preservingReadMachine.run 2
      { state := .capture,
        tape := { left := left, head := some b, right := none :: stream } } =
      { state := .returnMoved,
        tape := rightStreamTape (some b :: none :: left) stream } := by
  cases stream <;>
    simp [rightStreamTape, preservingReadMachine,
      TM.run, TM.step, Tape.write, Tape.move]

theorem returnMovedTape_eq_stream
    (bits : BitString)
    (left after : List (Option Bool)) :
    returnMovedTape bits left after =
      rightStreamTape left (bits.map some ++ (none :: after)) := by
  cases bits <;>
    rfl

/-- A blank commutes through a replicated blank block because every element
of the block is the same canonical blank symbol. -/
theorem replicate_none_cons
    (k : Nat) (source : List (Option Bool)) :
    List.replicate k none ++ (none :: source) =
      none :: (List.replicate k none ++ source) := by
  induction k with
  | zero => rfl
  | succ k ih =>
      simpa [List.replicate_succ] using
        congrArg (fun xs : List (Option Bool) => none :: xs) ih

/-- A right stream containing one current blank plus `k` further blanks is
exactly the canonical input expected by `returnBlanks_over_blanks`. -/
theorem rightStreamTape_blank_block
    (k : Nat)
    (left source : List (Option Bool)) :
    rightStreamTape left
        (List.replicate k none ++ (none :: source)) =
      { left := left,
        head := none,
        right := List.replicate k none ++ source } := by
  rw [replicate_none_cons]
  rfl

/-- One complete symbolic successor cycle.  With a nonempty moved prefix,
one remaining unary `true` marker moves exactly the next witness bit across the
temporary separator and returns to `indexMoved` on the next source symbol. -/
theorem preservingMoved_cycle
    (first b next : Bool)
    (movedTail witnessTail sourceTail : BitString) :
    preservingReadMachine.run (4 * movedTail.length + 10)
      (movedBitsConfig
        (first :: movedTail) (b :: witnessTail)
        (true :: next :: sourceTail)) =
      movedBitsConfig
        ((first :: movedTail) ++ [b]) witnessTail
        (next :: sourceTail) := by
  let m : Nat := movedTail.length
  let moved : BitString := first :: movedTail
  let witnessSuffix : List (Option Bool) := witnessTail.map some
  let src : List (Option Bool) := some next :: sourceTail.map some
  let after : List (Option Bool) :=
    List.replicate m none ++ (none :: src)
  let stream : List (Option Bool) :=
    moved.reverse.map some ++ (none :: after)
  let restoredLeft : List (Option Bool) :=
    none :: (moved.map some ++ (some b :: none :: witnessSuffix))

  let C0 : Configuration PreservingReadState (Option Bool) :=
    movedBitsConfig moved (b :: witnessTail) (true :: next :: sourceTail)
  let C1 : Configuration PreservingReadState (Option Bool) :=
    { state := .seekMoved,
      tape :=
        { left :=
            List.replicate m none ++
              (some first ::
                (movedTail.map some ++
                  (none :: some b :: witnessSuffix))),
          head := none,
          right := none :: src } }
  let C2 : Configuration PreservingReadState (Option Bool) :=
    { state := .seekMoved,
      tape :=
        { left :=
            movedTail.map some ++ (none :: some b :: witnessSuffix),
          head := some first,
          right := List.replicate (m + 1) none ++ (none :: src) } }
  let C3 : Configuration PreservingReadState (Option Bool) :=
    { state := .scanMoved,
      tape :=
        scanMovedTape movedTail b witnessSuffix
          (some first ::
            (List.replicate (m + 1) none ++ (none :: src))) }
  let C4 : Configuration PreservingReadState (Option Bool) :=
    { state := .capture,
      tape :=
        { left := witnessSuffix,
          head := some b,
          right := none :: stream } }
  let C5 : Configuration PreservingReadState (Option Bool) :=
    { state := .returnMoved,
      tape :=
        returnMovedTape moved.reverse
          (some b :: none :: witnessSuffix) after }
  let C6 : Configuration PreservingReadState (Option Bool) :=
    { state := .returnBlanks,
      tape := rightStreamTape restoredLeft after }
  let C6e : Configuration PreservingReadState (Option Bool) :=
    { state := .returnBlanks,
      tape :=
        { left := restoredLeft,
          head := none,
          right := List.replicate m none ++ src } }
  let C7e : Configuration PreservingReadState (Option Bool) :=
    { state := .indexMoved,
      tape :=
        { left := List.replicate (m + 1) none ++ restoredLeft,
          head := some next,
          right := sourceTail.map some } }
  let C7 : Configuration PreservingReadState (Option Bool) :=
    movedBitsConfig (moved ++ [b]) witnessTail (next :: sourceTail)

  have h01 : preservingReadMachine.run 1 C0 = C1 := by
    dsimp [C0, C1, moved, m, witnessSuffix, src,
      movedBitsConfig, movedBitsTape]
    simp [preservingReadMachine, TM.run, TM.step,
      Tape.write, Tape.move, List.replicate_succ, List.append_assoc]

  have h12 : preservingReadMachine.run (m + 1) C1 = C2 := by
    dsimp [C1, C2]
    simpa using
      seekMoved_over_blanks m first
        (movedTail.map some ++ (none :: some b :: witnessSuffix))
        (none :: src)

  have h23 : preservingReadMachine.run 1 C2 = C3 := by
    dsimp [C2, C3]
    simpa [TM.run] using
      seekMoved_step_bit first b movedTail witnessSuffix
        (List.replicate (m + 1) none ++ (none :: src))

  have h34 : preservingReadMachine.run (m + 1) C3 = C4 := by
    dsimp [C3, C4, stream, moved, after, src, m]
    simpa [List.reverse_cons, List.map_append,
      List.replicate_succ, List.append_assoc] using
      scanMoved_over_bits movedTail b witnessSuffix
        (some first ::
          (List.replicate (movedTail.length + 1) none ++
            (none :: (some next :: sourceTail.map some))))

  have h45 : preservingReadMachine.run 2 C4 = C5 := by
    dsimp [C4, C5, stream]
    simpa [returnMovedTape_eq_stream] using
      capture_write_to_stream b witnessSuffix
        (moved.reverse.map some ++ (none :: after))

  have h56 : preservingReadMachine.run (m + 2) C5 = C6 := by
    dsimp [C5, C6, restoredLeft, moved]
    simpa [moved, m] using
      returnMoved_over_bits moved.reverse
        (some b :: none :: witnessSuffix) after

  have h6eq : C6 = C6e := by
    dsimp [C6, C6e, after]
    exact congrArg
      (fun t : Tape (Option Bool) =>
        ({ state := .returnBlanks, tape := t } :
          Configuration PreservingReadState (Option Bool)))
      (rightStreamTape_blank_block m restoredLeft src)

  have h67 : preservingReadMachine.run (m + 2) C6e = C7e := by
    dsimp [C6e, C7e, src]
    simpa using
      returnBlanks_over_blanks m next restoredLeft (sourceTail.map some)

  have hleft :
      List.replicate (m + 1) none ++ restoredLeft =
        List.replicate ((moved ++ [b]).length) none ++
          (moved ++ [b]).map some ++ (none :: witnessSuffix) := by
    have h :=
      replicate_none_extend m
        (moved.map some ++ (some b :: none :: witnessSuffix))
    dsimp [restoredLeft, moved, m] at h ⊢
    simpa [List.map_append, List.append_assoc] using h

  have h7eq : C7e = C7 := by
    dsimp [C7e, C7, movedBitsConfig, movedBitsTape, src]
    rw [hleft]

  have h56e : preservingReadMachine.run (m + 2) C5 = C6e := by
    rw [h56, h6eq]

  have h67t : preservingReadMachine.run (m + 2) C6e = C7 := by
    rw [h67, h7eq]

  have h02 :
      preservingReadMachine.run (1 + (m + 1)) C0 = C2 := by
    rw [run_add, h01, h12]
  have h03 :
      preservingReadMachine.run ((1 + (m + 1)) + 1) C0 = C3 := by
    rw [run_add, h02, h23]
  have h04 :
      preservingReadMachine.run (((1 + (m + 1)) + 1) + (m + 1)) C0 = C4 := by
    rw [run_add, h03, h34]
  have h05 :
      preservingReadMachine.run
        ((((1 + (m + 1)) + 1) + (m + 1)) + 2) C0 = C5 := by
    rw [run_add, h04, h45]
  have h06 :
      preservingReadMachine.run
        (((((1 + (m + 1)) + 1) + (m + 1)) + 2) + (m + 2)) C0 = C6e := by
    rw [run_add, h05, h56e]
  have h07 :
      preservingReadMachine.run
        ((((((1 + (m + 1)) + 1) + (m + 1)) + 2) + (m + 2)) + (m + 2)) C0 =
        C7 := by
    rw [run_add, h06, h67t]

  have hFuel :
      4 * movedTail.length + 10 =
        ((((((1 + (m + 1)) + 1) + (m + 1)) + 2) + (m + 2)) + (m + 2)) := by
    dsimp [m]
    omega
  rw [hFuel]
  simpa [C0, C7, moved] using h07



/-- Final-read analogue of \`seekMoved_over_blanks\`: cross the temporary
blank block and stop on the first moved witness bit. -/
theorem finalSeekMoved_over_blanks
    (k : Nat) (b : Bool)
    (left right : List (Option Bool)) :
    preservingReadMachine.run (k + 1)
      { state := .finalSeekMoved,
        tape :=
          { left := List.replicate k none ++ (some b :: left),
            head := none,
            right := right } } =
      { state := .finalSeekMoved,
        tape :=
          { left := left,
            head := some b,
            right := List.replicate (k + 1) none ++ right } } := by
  induction k generalizing right with
  | zero =>
      simp [preservingReadMachine, TM.run, TM.step, Tape.write, Tape.move]
  | succ k ih =>
      rw [show Nat.succ k + 1 = (k + 1) + 1 by omega]
      rw [TM.run]
      simp only [show preservingReadMachine.halting (.finalSeekMoved) = false by rfl,
        Bool.false_eq_true, if_false]
      change preservingReadMachine.run (k + 1)
        { state := .finalSeekMoved,
          tape :=
            { left := List.replicate k none ++ (some b :: left),
              head := none,
              right := none :: right } } =
        { state := .finalSeekMoved,
          tape :=
            { left := left,
              head := some b,
              right := List.replicate (Nat.succ k + 1) none ++ right } }
      rw [ih (none :: right)]
      apply congrArg
        (fun r : List (Option Bool) =>
          ({ state := .finalSeekMoved,
             tape := { left := left, head := some b, right := r } } :
            Configuration PreservingReadState (Option Bool)))
      simpa [Nat.succ_eq_add_one, Nat.add_assoc] using
        replicate_none_extend k right

/-- Once the final seek reaches the first moved witness bit, one step enters
the final moved-prefix scan. -/
theorem finalSeekMoved_step_bit
    (first b : Bool) (movedTail : BitString)
    (left right : List (Option Bool)) :
    preservingReadMachine.step
      { state := .finalSeekMoved,
        tape :=
          { left := movedTail.map some ++ (none :: some b :: left),
            head := some first,
            right := right } } =
      { state := .finalScanMoved,
        tape := scanMovedTape movedTail b left (some first :: right) } := by
  cases movedTail <;>
    simp [scanMovedTape, preservingReadMachine,
      TM.step, Tape.write, Tape.move]

theorem finalScanMoved_step_cons
    (x b : Bool) (xs : BitString)
    (left right : List (Option Bool)) :
    preservingReadMachine.step
      { state := .finalScanMoved,
        tape := scanMovedTape (x :: xs) b left right } =
      { state := .finalScanMoved,
        tape := scanMovedTape xs b left (some x :: right) } := by
  cases xs <;>
    simp [scanMovedTape, preservingReadMachine,
      TM.step, Tape.write, Tape.move]

/-- Final scan crosses the remaining moved prefix and separator, landing on the
selected witness bit without changing it. -/
theorem finalScanMoved_over_bits
    (bits : BitString) (b : Bool)
    (left right : List (Option Bool)) :
    preservingReadMachine.run (bits.length + 1)
      { state := .finalScanMoved,
        tape := scanMovedTape bits b left right } =
      { state := .finalReadMoved,
        tape :=
          { left := left,
            head := some b,
            right := none :: (bits.reverse.map some ++ right) } } := by
  induction bits generalizing right with
  | nil =>
      simp [scanMovedTape, preservingReadMachine,
        TM.run, TM.step, Tape.write, Tape.move]
  | cons x xs ih =>
      rw [show (x :: xs).length + 1 = (xs.length + 1) + 1 by simp]
      rw [TM.run]
      simp only [show preservingReadMachine.halting (.finalScanMoved) = false by rfl,
        Bool.false_eq_true, if_false]
      rw [finalScanMoved_step_cons]
      rw [ih (some x :: right)]
      apply congrArg
        (fun r : List (Option Bool) =>
          ({ state := .finalReadMoved,
             tape := { left := left, head := some b, right := r } } :
            Configuration PreservingReadState (Option Bool)))
      simp [List.reverse_cons, List.map_append, List.append_assoc]

/-- Canonical restore-loop configuration.  The current separator blank is under
the head; \`bits\` are restored one-by-one from right to left. -/
def restoreMovedConfig
    (result : Bool) (left : List (Option Bool))
    (bits : BitString) (after : List (Option Bool)) :
    Configuration PreservingReadState (Option Bool) :=
  { state := .restoreStart result,
    tape :=
      { left := left,
        head := none,
        right := bits.map some ++ after } }

theorem restoreMoved_step_cons
    (result x : Bool) (xs : BitString)
    (left after : List (Option Bool)) :
    preservingReadMachine.run 3
      (restoreMovedConfig result left (x :: xs) after) =
      restoreMovedConfig result (some x :: left) xs after := by
  simp [restoreMovedConfig, preservingReadMachine,
    TM.run, TM.step, Tape.write, Tape.move, List.append_assoc]

/-- Restore every moved-prefix bit exactly. -/
theorem restoreMoved_over_bits
    (result : Bool) (bits : BitString)
    (left after : List (Option Bool)) :
    preservingReadMachine.run (3 * bits.length)
      (restoreMovedConfig result left bits after) =
      restoreMovedConfig result (bits.reverse.map some ++ left) [] after := by
  induction bits generalizing left with
  | nil =>
      rfl
  | cons x xs ih =>
      rw [show 3 * (x :: xs).length = 3 + 3 * xs.length by
        simp
        omega]
      rw [run_add]
      rw [restoreMoved_step_cons]
      rw [ih (some x :: left)]
      apply congrArg
        (fun l : List (Option Bool) =>
          restoreMovedConfig result l [] after)
      simp [List.reverse_cons, List.map_append, List.append_assoc]

def preservingMovedFinalizeFuel (moved : BitString) : Nat :=
  5 * moved.length + 6

/-- Generic terminal \`false\` case for a nonempty moved prefix.  The selected
witness bit is returned in the halt state, the entire witness is restored
exactly, the unary index is consumed into blanks, and the unread source tail is
preserved byte-for-byte. -/
theorem movedBits_false_finalize
    (first selected : Bool)
    (movedTail rest sourceTail : BitString) :
    preservingReadMachine.run
      (preservingMovedFinalizeFuel (first :: movedTail))
      (movedBitsConfig (first :: movedTail) (selected :: rest)
        (false :: sourceTail)) =
      { state := .halt selected,
        tape :=
          { left := ((first :: movedTail) ++ (selected :: rest)).map some,
            head := none,
            right :=
              List.replicate ((first :: movedTail).length + 1) none ++
                sourceTail.map some } } := by
  let m : Nat := movedTail.length
  let moved : BitString := first :: movedTail
  let witnessSuffix : List (Option Bool) := rest.map some
  let src : List (Option Bool) := sourceTail.map some
  let after : List (Option Bool) :=
    List.replicate (m + 1) none ++ (none :: src)

  let C0 : Configuration PreservingReadState (Option Bool) :=
    movedBitsConfig moved (selected :: rest) (false :: sourceTail)
  let C1 : Configuration PreservingReadState (Option Bool) :=
    { state := .finalSeekMoved,
      tape :=
        { left :=
            List.replicate m none ++
              (some first ::
                (movedTail.map some ++
                  (none :: some selected :: witnessSuffix))),
          head := none,
          right := none :: src } }
  let C2 : Configuration PreservingReadState (Option Bool) :=
    { state := .finalSeekMoved,
      tape :=
        { left :=
            movedTail.map some ++ (none :: some selected :: witnessSuffix),
          head := some first,
          right := List.replicate (m + 1) none ++ (none :: src) } }
  let C3 : Configuration PreservingReadState (Option Bool) :=
    { state := .finalScanMoved,
      tape :=
        scanMovedTape movedTail selected witnessSuffix
          (some first ::
            (List.replicate (m + 1) none ++ (none :: src))) }
  let C4 : Configuration PreservingReadState (Option Bool) :=
    { state := .finalReadMoved,
      tape :=
        { left := witnessSuffix,
          head := some selected,
          right :=
            none :: (moved.reverse.map some ++ after) } }
  let C5 : Configuration PreservingReadState (Option Bool) :=
    restoreMovedConfig selected (some selected :: witnessSuffix)
      moved.reverse after
  let restoredWitness : List (Option Bool) :=
    moved.map some ++ (some selected :: witnessSuffix)
  let C6 : Configuration PreservingReadState (Option Bool) :=
    restoreMovedConfig selected restoredWitness [] after
  let C7 : Configuration PreservingReadState (Option Bool) :=
    { state := .halt selected,
      tape :=
        { left := restoredWitness,
          head := none,
          right := List.replicate (m + 2) none ++ src } }

  have h01 : preservingReadMachine.run 1 C0 = C1 := by
    dsimp [C0, C1, moved, m, witnessSuffix, src,
      movedBitsConfig, movedBitsTape]
    simp [preservingReadMachine, TM.run, TM.step,
      Tape.write, Tape.move, List.replicate_succ, List.append_assoc]

  have h12 : preservingReadMachine.run (m + 1) C1 = C2 := by
    dsimp [C1, C2]
    simpa using
      finalSeekMoved_over_blanks m first
        (movedTail.map some ++ (none :: some selected :: witnessSuffix))
        (none :: src)

  have h23 : preservingReadMachine.run 1 C2 = C3 := by
    dsimp [C2, C3]
    simpa [TM.run] using
      finalSeekMoved_step_bit first selected movedTail witnessSuffix
        (List.replicate (m + 1) none ++ (none :: src))

  have h34 : preservingReadMachine.run (m + 1) C3 = C4 := by
    dsimp [C3, C4, moved, after]
    simpa [List.reverse_cons, List.map_append, List.append_assoc] using
      finalScanMoved_over_bits movedTail selected witnessSuffix
        (some first ::
          (List.replicate (movedTail.length + 1) none ++
            (none :: sourceTail.map some)))

  have h45 : preservingReadMachine.run 1 C4 = C5 := by
    dsimp [C4, C5, moved, after, src, witnessSuffix, restoreMovedConfig]
    simp [preservingReadMachine, TM.run, TM.step,
      Tape.write, Tape.move, List.reverse_cons, List.map_append,
      List.append_assoc]

  have h56 :
      preservingReadMachine.run (3 * moved.length) C5 = C6 := by
    dsimp [C5, C6, restoredWitness]
    simpa [moved] using
      restoreMoved_over_bits selected moved.reverse
        (some selected :: witnessSuffix) after

  have h67 : preservingReadMachine.run 3 C6 = C7 := by
    dsimp [C6, C7, restoreMovedConfig, restoredWitness, after, src, moved, m]
    simp [preservingReadMachine, TM.run, TM.step,
      Tape.write, Tape.move, List.replicate_succ,
      List.map_append, List.append_assoc]
    simpa using
      replicate_none_cons movedTail.length (sourceTail.map some)

  have h02 :
      preservingReadMachine.run (1 + (m + 1)) C0 = C2 := by
    rw [run_add, h01, h12]
  have h03 :
      preservingReadMachine.run ((1 + (m + 1)) + 1) C0 = C3 := by
    rw [run_add, h02, h23]
  have h04 :
      preservingReadMachine.run (((1 + (m + 1)) + 1) + (m + 1)) C0 = C4 := by
    rw [run_add, h03, h34]
  have h05 :
      preservingReadMachine.run
        ((((1 + (m + 1)) + 1) + (m + 1)) + 1) C0 = C5 := by
    rw [run_add, h04, h45]
  have h06 :
      preservingReadMachine.run
        (((((1 + (m + 1)) + 1) + (m + 1)) + 1) +
          (3 * moved.length)) C0 = C6 := by
    rw [run_add, h05, h56]
  have h07 :
      preservingReadMachine.run
        ((((((1 + (m + 1)) + 1) + (m + 1)) + 1) +
          (3 * moved.length)) + 3) C0 = C7 := by
    rw [run_add, h06, h67]

  have hFuel :
      preservingMovedFinalizeFuel moved =
        ((((((1 + (m + 1)) + 1) + (m + 1)) + 1) +
          (3 * moved.length)) + 3) := by
    dsimp [preservingMovedFinalizeFuel, moved, m]
    omega
  rw [show preservingMovedFinalizeFuel (first :: movedTail) =
      preservingMovedFinalizeFuel moved by rfl]
  rw [hFuel]
  simpa [C0, C7, moved, restoredWitness, src, m,
    List.map_append, List.append_assoc] using h07


/-- Canonical unary-index form of one successor cycle. -/
theorem preservingMoved_cycle_index
    (first next : Bool) (movedTail rest tail : BitString) (n : Nat) :
    preservingReadMachine.run (4 * movedTail.length + 10)
      (preservingMovedConfig
        (first :: movedTail) (next :: rest) (n + 1) tail) =
      preservingMovedConfig
        ((first :: movedTail) ++ [next]) rest n tail := by
  rw [preservingMovedConfig_eq_bits]
  rw [preservingMovedConfig_eq_bits]
  cases n with
  | zero =>
      simpa [encodeNat, List.append_assoc] using
        preservingMoved_cycle first next false movedTail rest tail
  | succ n =>
      simpa [encodeNat, List.append_assoc] using
        preservingMoved_cycle first next true movedTail rest
          (encodeNat n ++ tail)

/-- Exact remaining-run fuel after a nonempty prefix has already been moved.
The recursion mirrors the machine: a terminal false uses the restore cost;
a successor true uses one preserving cycle and continues with a prefix one
cell longer. -/
def preservingMovedFuel (movedLen : Nat) : Nat → Nat
  | 0 => 5 * movedLen + 6
  | n + 1 =>
      (4 * movedLen + 6) + preservingMovedFuel (movedLen + 1) n

/-- Complete preserving read from the moved-prefix invariant. -/
theorem preservingMoved_forall
    (first : Bool) (movedTail rest tail : BitString) (n : Nat)
    (h : n < rest.length) :
    preservingReadMachine.run
      (preservingMovedFuel (first :: movedTail).length n)
      (preservingMovedConfig (first :: movedTail) rest n tail) =
      { state := .halt (rest.getD n false),
        tape :=
          { left := ((first :: movedTail) ++ rest).map some,
            head := none,
            right :=
              List.replicate
                ((first :: movedTail).length + n + 1) none ++
                tail.map some } } := by
  induction n generalizing movedTail rest with
  | zero =>
      cases rest with
      | nil =>
          simp at h
      | cons selected restTail =>
          rw [preservingMovedConfig_eq_bits]
          simpa [preservingMovedFuel, preservingMovedFinalizeFuel,
            encodeNat, List.map_append, List.append_assoc] using
            movedBits_false_finalize first selected movedTail restTail tail
  | succ n ih =>
      cases rest with
      | nil =>
          simp at h
      | cons selected restTail =>
          have htail : n < restTail.length := by
            simpa using h
          rw [show
            preservingMovedFuel (first :: movedTail).length (n + 1) =
              (4 * movedTail.length + 10) +
                preservingMovedFuel
                  (first :: (movedTail ++ [selected])).length n by
              simp [preservingMovedFuel]
              omega]
          rw [run_add]
          rw [preservingMoved_cycle_index
            first selected movedTail restTail tail n]
          change preservingReadMachine.run
            (preservingMovedFuel
              (first :: (movedTail ++ [selected])).length n)
            (preservingMovedConfig
              (first :: (movedTail ++ [selected])) restTail n tail) = _
          rw [ih (movedTail := movedTail ++ [selected])
            (rest := restTail) htail]
          simp [List.getD_cons_succ, List.map_append,
            List.append_assoc]
          omega

/-- Compatibility name for the already-kernelized generic preserving cycle.
No second proof is maintained here. -/
theorem preservingMoved_true_cycle
    (first b next : Bool)
    (movedTail restTail sourceTail : BitString) :
    preservingReadMachine.run (4 * movedTail.length + 10)
      (movedBitsConfig (first :: movedTail) (b :: restTail)
        (true :: next :: sourceTail)) =
      movedBitsConfig ((first :: movedTail) ++ [b]) restTail
        (next :: sourceTail) := by
  exact preservingMoved_cycle first b next movedTail restTail sourceTail

#print axioms MCore.Real.P01WitnessIndexedReadPreserving.preservingMoved_true_cycle

/-- Zero-index read is already completely non-destructive: the false unary
terminator is consumed, while the witness cell itself is only inspected. -/
theorem preservingRead_zero
    (b : Bool) (witnessTail tail : BitString) :
    preservingReadMachine.run 4
      { state := preservingReadMachine.initial,
        tape := preservingReadTape (b :: witnessTail) 0 tail } =
      { state := .halt b,
        tape :=
          { left := (b :: witnessTail).map some,
            head := none,
            right := none :: tail.map some } } := by
  cases b <;>
    simp [preservingReadMachine, preservingReadTape, encodeNat,
      TM.run, TM.step, Tape.write, Tape.move]

/-- The zero-index theorem already shows the key preservation property: the
selected bit and the untouched witness tail remain physically present. -/
theorem preservingRead_zero_value
    (b : Bool) (witnessTail tail : BitString) :
    (preservingReadMachine.run 4
      { state := preservingReadMachine.initial,
        tape := preservingReadTape (b :: witnessTail) 0 tail }).state =
      .halt b := by
  rw [preservingRead_zero]


/-- Exact successor checkpoint.  Unary index 1 consumes its true marker
and false terminator, reads the second witness bit, and restores the entire
witness exactly.  The two consumed source symbols remain as blanks immediately
to the right of the canonical witness/source separator. -/
theorem preservingRead_one
    (b0 b1 : Bool) (witnessTail tail : BitString) :
    preservingReadMachine.run 17
      { state := preservingReadMachine.initial,
        tape := preservingReadTape (b0 :: b1 :: witnessTail) 1 tail } =
      { state := .halt b1,
        tape :=
          { left := (b0 :: b1 :: witnessTail).map some,
            head := none,
            right := none :: none :: tail.map some } } := by
  set_option maxHeartbeats 2000000 in
    cases b0 <;> cases b1 <;>
      simp [preservingReadMachine, preservingReadTape, encodeNat,
        TM.run, TM.step, Tape.write, Tape.move]

/-- First successor checkpoint.  For unary index 1 the machine must move one
witness cell across the temporary separator, read the second witness bit, then
restore the moved cell before halting.  Extra fuel is inert after halting. -/
theorem preservingRead_one_value
    (b0 b1 : Bool) (witnessTail tail : BitString) :
    (preservingReadMachine.run 32
      { state := preservingReadMachine.initial,
        tape := preservingReadTape (b0 :: b1 :: witnessTail) 1 tail }).state =
      .halt b1 := by
  set_option maxHeartbeats 2000000 in
    cases b0 <;> cases b1 <;>
      simp [preservingReadMachine, preservingReadTape, encodeNat,
        TM.run, TM.step, Tape.write, Tape.move]


/-- Exact fuel for a complete preserving unary-index read from the canonical
initial layout. -/
def preservingReadFuel : Nat → Nat
  | 0 => 4
  | n + 1 => 6 + preservingMovedFuel 1 n

/-- Complete preserving indexed witness read for every valid index. -/
theorem preservingRead_forall
    (i : Nat) (witness tail : BitString)
    (h : i < witness.length) :
    preservingReadMachine.run (preservingReadFuel i)
      { state := preservingReadMachine.initial,
        tape := preservingReadTape witness i tail } =
      { state := .halt (witness.getD i false),
        tape :=
          { left := witness.map some,
            head := none,
            right := List.replicate (i + 1) none ++ tail.map some } } := by
  cases i with
  | zero =>
      cases witness with
      | nil =>
          simp at h
      | cons b witnessTail =>
          simpa [preservingReadFuel, List.getD_cons_zero] using
            preservingRead_zero b witnessTail tail
  | succ n =>
      cases witness with
      | nil =>
          simp at h
      | cons b witnessTail =>
          have htail : n < witnessTail.length := by
            simpa using h
          rw [show preservingReadFuel (n + 1) =
              6 + preservingMovedFuel 1 n by rfl]
          rw [run_add]
          rw [preservingRead_start_successor b witnessTail tail n]
          have hm :=
            preservingMoved_forall b [] witnessTail tail n htail
          rw [show n + 1 + 1 = 1 + n + 1 by omega]
          simpa [List.getD_cons_succ, List.map_append,
            List.append_assoc] using hm

theorem preservingRead_forall_value
    (i : Nat) (witness tail : BitString)
    (h : i < witness.length) :
    (preservingReadMachine.run (preservingReadFuel i)
      { state := preservingReadMachine.initial,
        tape := preservingReadTape witness i tail }).state =
      .halt (witness.getD i false) := by
  rw [preservingRead_forall i witness tail h]



/-- Quadratic envelope for the exact moved-prefix fuel. -/
theorem preservingMovedFuel_le (m n : Nat) :
    preservingMovedFuel m n ≤
      (4 * (m + n) + 6) * n + 5 * (m + n) + 6 := by
  induction n generalizing m with
  | zero =>
      simp [preservingMovedFuel]
  | succ n ih =>
      simp only [preservingMovedFuel]
      have h := ih (m + 1)
      rw [show m + 1 + n = m + (n + 1) by omega] at h
      have h2 :
          (4 * (m + (n + 1)) + 6) * n +
              5 * (m + (n + 1)) + 6 + (4 * m + 6) ≤
            (4 * (m + (n + 1)) + 6) * (n + 1) +
              5 * (m + (n + 1)) + 6 := by
        rw [Nat.mul_succ]
        omega
      omega

/-- A complete preserving indexed read is quadratically bounded in the unary
index. -/
theorem preservingReadFuel_le (i : Nat) :
    preservingReadFuel i ≤ 5 * (i + 1) * (i + 1) + 6 := by
  cases i with
  | zero =>
      simp [preservingReadFuel]
  | succ n =>
      simp only [preservingReadFuel]
      have h := preservingMovedFuel_le 1 n
      have e1 :
          (4 * (1 + n) + 6) * n =
            4 * (n * n) + 10 * n := by
        simp only [Nat.add_mul, Nat.mul_add, Nat.mul_one, Nat.mul_assoc]
        omega
      have e2 :
          5 * (n + 1 + 1) * (n + 1 + 1) =
            5 * (n * n) + 20 * n + 20 := by
        simp only [Nat.add_mul, Nat.mul_add, Nat.mul_one, Nat.one_mul,
          Nat.mul_assoc]
        omega
      omega

#print axioms MCore.Real.P01WitnessIndexedReadPreserving.preservingReadFuel_le
#print axioms MCore.Real.P01WitnessIndexedReadPreserving.preservingMovedFuel_le
#print axioms MCore.Real.P01WitnessIndexedReadPreserving.preservingRead_forall
#print axioms MCore.Real.P01WitnessIndexedReadPreserving.preservingRead_forall_value
#print axioms MCore.Real.P01WitnessIndexedReadPreserving.preservingMoved_forall
#print axioms MCore.Real.P01WitnessIndexedReadPreserving.movedBits_false_finalize
#print axioms MCore.Real.P01WitnessIndexedReadPreserving.preservingRead_start_successor
#print axioms MCore.Real.P01WitnessIndexedReadPreserving.replicate_none_extend
#print axioms MCore.Real.P01WitnessIndexedReadPreserving.seekMoved_over_blanks
#print axioms MCore.Real.P01WitnessIndexedReadPreserving.scanMoved_step_cons
#print axioms MCore.Real.P01WitnessIndexedReadPreserving.scanMoved_over_bits
#print axioms MCore.Real.P01WitnessIndexedReadPreserving.returnMoved_step_cons
#print axioms MCore.Real.P01WitnessIndexedReadPreserving.returnMoved_over_bits
#print axioms MCore.Real.P01WitnessIndexedReadPreserving.returnBlanks_over_blanks
#print axioms MCore.Real.P01WitnessIndexedReadPreserving.preservingMovedConfig_eq_bits
#print axioms MCore.Real.P01WitnessIndexedReadPreserving.seekMoved_step_bit
#print axioms MCore.Real.P01WitnessIndexedReadPreserving.capture_write_to_stream
#print axioms MCore.Real.P01WitnessIndexedReadPreserving.returnMovedTape_eq_stream
#print axioms MCore.Real.P01WitnessIndexedReadPreserving.replicate_none_cons
#print axioms MCore.Real.P01WitnessIndexedReadPreserving.rightStreamTape_blank_block
#print axioms MCore.Real.P01WitnessIndexedReadPreserving.preservingMoved_cycle
#print axioms MCore.Real.P01WitnessIndexedReadPreserving.preservingRead_zero
#print axioms MCore.Real.P01WitnessIndexedReadPreserving.preservingRead_zero_value
#print axioms MCore.Real.P01WitnessIndexedReadPreserving.preservingRead_one
#print axioms MCore.Real.P01WitnessIndexedReadPreserving.preservingRead_one_value

end P01WitnessIndexedReadPreserving
end Real
end MCore
