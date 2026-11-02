import MCore.Real.P01PreservingUnaryWitnessMachine
import MCore.Real.MachineRunLemmas

namespace MCore
namespace Real
namespace P01PreservingUnaryPhysicalRuns

open CanonicalFinalProof
open CanonicalCircuitBits
open P01WitnessIndexedRead
open P01PreservingUnaryWitnessMachine
open MachineRunLemmas

theorem replicate_none_extend
    (k : Nat) (right : List (Option Bool)) :
    List.replicate (k + 1) none ++ (none :: right) =
      List.replicate (k + 2) none ++ right := by
  induction k with
  | zero => rfl
  | succ k ih =>
      simp only [Nat.succ_add, List.replicate_succ, List.cons_append]
      congr 1

theorem seekBlanks_over_blanks
    (k : Nat) (b : Bool)
    (left right : List (Option Bool)) :
    preservingUnaryReadMachine.run (k + 1)
      { state := .seekBlanks
        tape :=
          { left := List.replicate k none ++ (some b :: left)
            head := none
            right := right } } =
      { state := .seekBlanks
        tape :=
          { left := left
            head := some b
            right := List.replicate (k + 1) none ++ right } } := by
  induction k generalizing right with
  | zero =>
      simp [preservingUnaryReadMachine, TM.run, TM.step,
        Tape.write, Tape.move]
  | succ k ih =>
      rw [show Nat.succ k + 1 = (k + 1) + 1 by omega]
      rw [TM.run]
      simp only [show preservingUnaryReadMachine.halting (.seekBlanks) = false by rfl,
        Bool.false_eq_true, if_false]
      change preservingUnaryReadMachine.run (k + 1)
        { state := .seekBlanks
          tape :=
            { left := List.replicate k none ++ (some b :: left)
              head := none
              right := none :: right } } =
        { state := .seekBlanks
          tape :=
            { left := left
              head := some b
              right := List.replicate (Nat.succ k + 1) none ++ right } }
      rw [ih (none :: right)]
      apply congrArg
        (fun r : List (Option Bool) =>
          ({ state := .seekBlanks
             tape := { left := left, head := some b, right := r } } :
            Configuration PreservingReadState (Option Bool)))
      simpa [Nat.succ_eq_add_one, Nat.add_assoc] using
        replicate_none_extend k right

def seekBitsTape
    (bits : BitString) (b : Bool)
    (left right : List (Option Bool)) :
    Tape (Option Bool) :=
  match bits with
  | [] =>
      { left := some b :: left
        head := none
        right := right }
  | x :: xs =>
      { left := xs.map some ++ (none :: some b :: left)
        head := some x
        right := right }

theorem seekBlanks_step_bit
    (first b : Bool) (bits : BitString)
    (left right : List (Option Bool)) :
    preservingUnaryReadMachine.step
      { state := .seekBlanks
        tape :=
          { left := bits.map some ++ (none :: some b :: left)
            head := some first
            right := right } } =
      { state := .seekBits
        tape := seekBitsTape bits b left (some first :: right) } := by
  cases bits <;>
    simp [seekBitsTape, preservingUnaryReadMachine,
      TM.step, Tape.write, Tape.move]

theorem seekBits_step_cons
    (x b : Bool) (xs : BitString)
    (left right : List (Option Bool)) :
    preservingUnaryReadMachine.step
      { state := .seekBits
        tape := seekBitsTape (x :: xs) b left right } =
      { state := .seekBits
        tape := seekBitsTape xs b left (some x :: right) } := by
  cases xs <;>
    simp [seekBitsTape, preservingUnaryReadMachine,
      TM.step, Tape.write, Tape.move]

theorem seekBits_over_bits
    (bits : BitString) (b : Bool)
    (left right : List (Option Bool)) :
    preservingUnaryReadMachine.run (bits.length + 1)
      { state := .seekBits
        tape := seekBitsTape bits b left right } =
      { state := .shiftRead
        tape :=
          { left := left
            head := some b
            right := none :: (bits.reverse.map some ++ right) } } := by
  induction bits generalizing right with
  | nil =>
      simp [seekBitsTape, preservingUnaryReadMachine,
        TM.run, TM.step, Tape.write, Tape.move]
  | cons x xs ih =>
      rw [show (x :: xs).length + 1 = (xs.length + 1) + 1 by simp]
      rw [TM.run]
      simp only [show preservingUnaryReadMachine.halting (.seekBits) = false by rfl,
        Bool.false_eq_true, if_false]
      rw [seekBits_step_cons]
      rw [ih (some x :: right)]
      apply congrArg
        (fun r : List (Option Bool) =>
          ({ state := .shiftRead
             tape := { left := left, head := some b, right := r } } :
            Configuration PreservingReadState (Option Bool)))
      simp [List.reverse_cons, List.map_append, List.append_assoc]

def rightStreamTape
    (left stream : List (Option Bool)) :
    Tape (Option Bool) :=
  match stream with
  | [] =>
      { left := left, head := none, right := [] }
  | x :: xs =>
      { left := left, head := x, right := xs }

theorem shift_carry_return_to_stream
    (b : Bool) (left stream : List (Option Bool)) :
    preservingUnaryReadMachine.run 3
      { state := .shiftRead
        tape := { left := left, head := some b, right := none :: stream } } =
      { state := .returnBits
        tape := rightStreamTape (none :: left) (some b :: stream) } := by
  cases b <;> cases stream <;>
    simp [rightStreamTape, preservingUnaryReadMachine,
      TM.run, TM.step, Tape.write, Tape.move]

def returnBitsTape
    (bits : BitString)
    (left after : List (Option Bool)) :
    Tape (Option Bool) :=
  match bits with
  | [] =>
      rightStreamTape left (none :: after)
  | x :: xs =>
      { left := left
        head := some x
        right := xs.map some ++ (none :: after) }

theorem returnBits_step_cons
    (x : Bool) (xs : BitString)
    (left after : List (Option Bool)) :
    preservingUnaryReadMachine.step
      { state := .returnBits
        tape := returnBitsTape (x :: xs) left after } =
      { state := .returnBits
        tape := returnBitsTape xs (some x :: left) after } := by
  cases xs <;>
    simp [returnBitsTape, rightStreamTape, preservingUnaryReadMachine,
      TM.step, Tape.write, Tape.move]

theorem returnBits_over_bits
    (bits : BitString)
    (left after : List (Option Bool)) :
    preservingUnaryReadMachine.run (bits.length + 1)
      { state := .returnBits
        tape := returnBitsTape bits left after } =
      { state := .returnBlanks
        tape :=
          rightStreamTape
            (none :: (bits.reverse.map some ++ left))
            after } := by
  induction bits generalizing left with
  | nil =>
      cases after <;>
        simp [returnBitsTape, rightStreamTape, preservingUnaryReadMachine,
          TM.run, TM.step, Tape.write, Tape.move]
  | cons x xs ih =>
      rw [show (x :: xs).length + 1 = (xs.length + 1) + 1 by simp]
      rw [TM.run]
      simp only [show preservingUnaryReadMachine.halting (.returnBits) = false by rfl,
        Bool.false_eq_true, if_false]
      rw [returnBits_step_cons]
      rw [ih (some x :: left)]
      apply congrArg
        (fun l : List (Option Bool) =>
          ({ state := .returnBlanks
             tape := rightStreamTape l after } :
            Configuration PreservingReadState (Option Bool)))
      simp [List.reverse_cons, List.map_append, List.append_assoc]

theorem returnBlanks_over_blanks
    (k : Nat) (b : Bool)
    (left right : List (Option Bool)) :
    preservingUnaryReadMachine.run (k + 2)
      { state := .returnBlanks
        tape :=
          { left := left
            head := none
            right := List.replicate k none ++ (some b :: right) } } =
      { state := .indexSome
        tape :=
          { left := List.replicate (k + 1) none ++ left
            head := some b
            right := right } } := by
  induction k generalizing left with
  | zero =>
      simp [preservingUnaryReadMachine, TM.run, TM.step,
        Tape.write, Tape.move]
  | succ k ih =>
      rw [show Nat.succ k + 2 = (k + 2) + 1 by omega]
      rw [TM.run]
      simp only [show preservingUnaryReadMachine.halting (.returnBlanks) = false by rfl,
        Bool.false_eq_true, if_false]
      change preservingUnaryReadMachine.run (k + 2)
        { state := .returnBlanks
          tape :=
            { left := none :: left
              head := none
              right := List.replicate k none ++ (some b :: right) } } =
        { state := .indexSome
          tape :=
            { left := List.replicate (Nat.succ k + 1) none ++ left
              head := some b
              right := right } }
      rw [ih (none :: left)]
      apply congrArg
        (fun l : List (Option Bool) =>
          ({ state := .indexSome
             tape := { left := l, head := some b, right := right } } :
            Configuration PreservingReadState (Option Bool)))
      simpa [Nat.succ_eq_add_one, Nat.add_assoc] using
        replicate_none_extend k left

theorem replicate_none_cons
    (k : Nat) (source : List (Option Bool)) :
    List.replicate k none ++ (none :: source) =
      none :: (List.replicate k none ++ source) := by
  induction k with
  | zero => rfl
  | succ k ih =>
      simpa [List.replicate_succ] using
        congrArg (fun xs : List (Option Bool) => none :: xs) ih

theorem rightStreamTape_blank_block
    (k : Nat)
    (left source : List (Option Bool)) :
    rightStreamTape left
        (List.replicate k none ++ (none :: source)) =
      { left := left
        head := none
        right := List.replicate k none ++ source } := by
  rw [replicate_none_cons]
  rfl

def indexSomeBitsTape
    (pref suffix source : BitString) :
    Tape (Option Bool) :=
  match source with
  | [] =>
      { left := List.replicate pref.length none ++
          pref.map some ++ none :: suffix.map some
        head := none
        right := [] }
  | x :: xs =>
      { left := List.replicate pref.length none ++
          pref.map some ++ none :: suffix.map some
        head := some x
        right := xs.map some }

def indexSomeBitsConfig
    (pref suffix source : BitString) :
    Configuration PreservingReadState (Option Bool) :=
  { state := .indexSome
    tape := indexSomeBitsTape pref suffix source }

theorem indexSomeConfig_eq_bits
    (pref suffix : BitString) (n : Nat) :
    indexSomeConfig pref suffix n =
      indexSomeBitsConfig pref suffix (encodeNat n) := by
  cases n <;> rfl

theorem indexSome_cycle_bits
    (first b next : Bool)
    (prefTail witnessTail sourceTail : BitString) :
    preservingUnaryReadMachine.run (4 * (first :: prefTail).length + 8)
      (indexSomeBitsConfig
        (first :: prefTail) (b :: witnessTail)
        (true :: next :: sourceTail)) =
      indexSomeBitsConfig
        ((first :: prefTail) ++ [b]) witnessTail
        (next :: sourceTail) := by
  let m : Nat := prefTail.length
  let pref : BitString := first :: prefTail
  let witnessSuffix : List (Option Bool) := witnessTail.map some
  let src : List (Option Bool) := some next :: sourceTail.map some
  let after : List (Option Bool) :=
    List.replicate m none ++ (none :: src)
  let stream : List (Option Bool) :=
    pref.reverse.map some ++ (none :: after)
  let returnedBits : BitString := b :: pref.reverse
  let restoredLeft : List (Option Bool) :=
    none :: (pref.map some ++ (some b :: none :: witnessSuffix))

  let C0 : Configuration PreservingReadState (Option Bool) :=
    indexSomeBitsConfig pref (b :: witnessTail) (true :: next :: sourceTail)
  let C1 : Configuration PreservingReadState (Option Bool) :=
    { state := .seekBlanks
      tape :=
        { left :=
            List.replicate m none ++
              (some first ::
                (prefTail.map some ++
                  (none :: some b :: witnessSuffix)))
          head := none
          right := none :: src } }
  let C2 : Configuration PreservingReadState (Option Bool) :=
    { state := .seekBlanks
      tape :=
        { left :=
            prefTail.map some ++ (none :: some b :: witnessSuffix)
          head := some first
          right := List.replicate (m + 1) none ++ (none :: src) } }
  let C3 : Configuration PreservingReadState (Option Bool) :=
    { state := .seekBits
      tape := seekBitsTape prefTail b witnessSuffix
        (some first :: (List.replicate (m + 1) none ++ (none :: src))) }
  let C4 : Configuration PreservingReadState (Option Bool) :=
    { state := .shiftRead
      tape :=
        { left := witnessSuffix
          head := some b
          right := none :: stream } }
  let C5 : Configuration PreservingReadState (Option Bool) :=
    { state := .returnBits
      tape := returnBitsTape returnedBits (none :: witnessSuffix) after }
  let C6 : Configuration PreservingReadState (Option Bool) :=
    { state := .returnBlanks
      tape := rightStreamTape restoredLeft after }
  let C6e : Configuration PreservingReadState (Option Bool) :=
    { state := .returnBlanks
      tape :=
        { left := restoredLeft
          head := none
          right := List.replicate m none ++ src } }
  let C7e : Configuration PreservingReadState (Option Bool) :=
    { state := .indexSome
      tape :=
        { left := List.replicate (m + 1) none ++ restoredLeft
          head := some next
          right := sourceTail.map some } }
  let C7 : Configuration PreservingReadState (Option Bool) :=
    indexSomeBitsConfig (pref ++ [b]) witnessTail (next :: sourceTail)

  have h01 : preservingUnaryReadMachine.run 1 C0 = C1 := by
    dsimp [C0, C1, pref, m, witnessSuffix, src,
      indexSomeBitsConfig, indexSomeBitsTape]
    simp [preservingUnaryReadMachine, TM.run, TM.step,
      Tape.write, Tape.move, List.replicate_succ, List.append_assoc]

  have h12 : preservingUnaryReadMachine.run (m + 1) C1 = C2 := by
    dsimp [C1, C2]
    simpa using
      seekBlanks_over_blanks m first
        (prefTail.map some ++ (none :: some b :: witnessSuffix))
        (none :: src)

  have h23 : preservingUnaryReadMachine.run 1 C2 = C3 := by
    dsimp [C2, C3]
    simpa [TM.run] using
      seekBlanks_step_bit first b prefTail witnessSuffix
        (List.replicate (m + 1) none ++ (none :: src))

  have h34 : preservingUnaryReadMachine.run (m + 1) C3 = C4 := by
    dsimp [C3, C4, stream, pref, after, src, m]
    simpa [List.reverse_cons, List.map_append,
      List.replicate_succ, List.append_assoc] using
      seekBits_over_bits prefTail b witnessSuffix
        (some first ::
          (List.replicate (prefTail.length + 1) none ++
            (none :: (some next :: sourceTail.map some))))

  have h45 : preservingUnaryReadMachine.run 3 C4 = C5 := by
    dsimp [C4, C5, stream, returnedBits, pref]
    simpa [pref, returnBitsTape, List.reverse_cons, List.map_append,
      List.append_assoc] using
      shift_carry_return_to_stream b witnessSuffix
        (pref.reverse.map some ++ (none :: after))

  have h56 : preservingUnaryReadMachine.run (m + 3) C5 = C6 := by
    dsimp [C5, C6, returnedBits, restoredLeft, pref, m]
    simpa [pref, List.reverse_cons, List.reverse_reverse,
      List.map_append, List.append_assoc] using
      returnBits_over_bits (b :: pref.reverse)
        (none :: witnessSuffix) after

  have h6eq : C6 = C6e := by
    dsimp [C6, C6e, after]
    exact congrArg
      (fun t : Tape (Option Bool) =>
        ({ state := .returnBlanks, tape := t } :
          Configuration PreservingReadState (Option Bool)))
      (rightStreamTape_blank_block m restoredLeft src)

  have h67 : preservingUnaryReadMachine.run (m + 2) C6e = C7e := by
    dsimp [C6e, C7e, src]
    simpa using
      returnBlanks_over_blanks m next restoredLeft (sourceTail.map some)

  have hleft :
      List.replicate (m + 1) none ++ restoredLeft =
        List.replicate ((pref ++ [b]).length) none ++
          (pref ++ [b]).map some ++ (none :: witnessSuffix) := by
    have h :=
      replicate_none_extend m
        ((pref ++ [b]).map some ++ (none :: witnessSuffix))
    dsimp [restoredLeft, pref, m] at h ⊢
    simpa [List.map_append, List.append_assoc] using h

  have h7eq : C7e = C7 := by
    dsimp [C7e, C7, indexSomeBitsConfig, indexSomeBitsTape, src]
    rw [hleft]

  have h56e : preservingUnaryReadMachine.run (m + 3) C5 = C6e := by
    rw [h56, h6eq]

  have h67t : preservingUnaryReadMachine.run (m + 2) C6e = C7 := by
    rw [h67, h7eq]

  have h02 :
      preservingUnaryReadMachine.run (1 + (m + 1)) C0 = C2 := by
    rw [run_add, h01, h12]
  have h03 :
      preservingUnaryReadMachine.run ((1 + (m + 1)) + 1) C0 = C3 := by
    rw [run_add, h02, h23]
  have h04 :
      preservingUnaryReadMachine.run (((1 + (m + 1)) + 1) + (m + 1)) C0 = C4 := by
    rw [run_add, h03, h34]
  have h05 :
      preservingUnaryReadMachine.run
        ((((1 + (m + 1)) + 1) + (m + 1)) + 3) C0 = C5 := by
    rw [run_add, h04, h45]
  have h06 :
      preservingUnaryReadMachine.run
        (((((1 + (m + 1)) + 1) + (m + 1)) + 3) + (m + 3)) C0 = C6e := by
    rw [run_add, h05, h56e]
  have h07 :
      preservingUnaryReadMachine.run
        ((((((1 + (m + 1)) + 1) + (m + 1)) + 3) + (m + 3)) + (m + 2)) C0 =
        C7 := by
    rw [run_add, h06, h67t]

  have hFuel :
      4 * (first :: prefTail).length + 8 =
        ((((((1 + (m + 1)) + 1) + (m + 1)) + 3) + (m + 3)) + (m + 2)) := by
    dsimp [m]
    omega
  rw [hFuel]
  simpa [C0, C7, pref] using h07

theorem indexSome_run_advance
    (pref : BitString) (b : Bool) (suffix : BitString) (n : Nat)
    (hpref : pref ≠ []) :
    preservingUnaryReadMachine.run (4 * pref.length + 8)
        (indexSomeConfig pref (b :: suffix) (n + 1)) =
      indexSomeConfig (pref ++ [b]) suffix n := by
  rcases pref with _ | ⟨first, prefTail⟩
  · contradiction
  cases n with
  | zero =>
      simpa [indexSomeConfig_eq_bits, encodeNat] using
        indexSome_cycle_bits first b false prefTail suffix []
  | succ n =>
      simpa [indexSomeConfig_eq_bits, encodeNat] using
        indexSome_cycle_bits first b true prefTail suffix (encodeNat n)


def finalSeekBitsTape := seekBitsTape

theorem finalSeekBlanks_over_blanks
    (k : Nat) (b : Bool)
    (left right : List (Option Bool)) :
    preservingUnaryReadMachine.run (k + 1)
      { state := .finalSeekBlanks
        tape :=
          { left := List.replicate k none ++ (some b :: left)
            head := none
            right := right } } =
      { state := .finalSeekBlanks
        tape :=
          { left := left
            head := some b
            right := List.replicate (k + 1) none ++ right } } := by
  induction k generalizing right with
  | zero =>
      simp [preservingUnaryReadMachine, TM.run, TM.step,
        Tape.write, Tape.move]
  | succ k ih =>
      rw [show Nat.succ k + 1 = (k + 1) + 1 by omega]
      rw [TM.run]
      simp only [show preservingUnaryReadMachine.halting (.finalSeekBlanks) = false by rfl,
        Bool.false_eq_true, if_false]
      change preservingUnaryReadMachine.run (k + 1)
        { state := .finalSeekBlanks
          tape :=
            { left := List.replicate k none ++ (some b :: left)
              head := none
              right := none :: right } } =
        { state := .finalSeekBlanks
          tape :=
            { left := left
              head := some b
              right := List.replicate (Nat.succ k + 1) none ++ right } }
      rw [ih (none :: right)]
      apply congrArg
        (fun r : List (Option Bool) =>
          ({ state := .finalSeekBlanks
             tape := { left := left, head := some b, right := r } } :
            Configuration PreservingReadState (Option Bool)))
      simpa [Nat.succ_eq_add_one, Nat.add_assoc] using
        replicate_none_extend k right

theorem finalSeekBlanks_step_bit
    (first b : Bool) (bits : BitString)
    (left right : List (Option Bool)) :
    preservingUnaryReadMachine.step
      { state := .finalSeekBlanks
        tape :=
          { left := bits.map some ++ (none :: some b :: left)
            head := some first
            right := right } } =
      { state := .finalSeekBits
        tape := finalSeekBitsTape bits b left (some first :: right) } := by
  cases bits <;>
    simp [finalSeekBitsTape, seekBitsTape, preservingUnaryReadMachine,
      TM.step, Tape.write, Tape.move]

theorem finalSeekBits_step_cons
    (x b : Bool) (xs : BitString)
    (left right : List (Option Bool)) :
    preservingUnaryReadMachine.step
      { state := .finalSeekBits
        tape := finalSeekBitsTape (x :: xs) b left right } =
      { state := .finalSeekBits
        tape := finalSeekBitsTape xs b left (some x :: right) } := by
  cases xs <;>
    simp [finalSeekBitsTape, seekBitsTape, preservingUnaryReadMachine,
      TM.step, Tape.write, Tape.move]

theorem finalSeekBits_over_bits
    (bits : BitString) (b : Bool)
    (left right : List (Option Bool)) :
    preservingUnaryReadMachine.run (bits.length + 1)
      { state := .finalSeekBits
        tape := finalSeekBitsTape bits b left right } =
      { state := .finalRead
        tape :=
          { left := left
            head := some b
            right := none :: (bits.reverse.map some ++ right) } } := by
  induction bits generalizing right with
  | nil =>
      simp [finalSeekBitsTape, seekBitsTape, preservingUnaryReadMachine,
        TM.run, TM.step, Tape.write, Tape.move]
  | cons x xs ih =>
      rw [show (x :: xs).length + 1 = (xs.length + 1) + 1 by simp]
      rw [TM.run]
      simp only [show preservingUnaryReadMachine.halting (.finalSeekBits) = false by rfl,
        Bool.false_eq_true, if_false]
      rw [finalSeekBits_step_cons]
      rw [ih (some x :: right)]
      apply congrArg
        (fun r : List (Option Bool) =>
          ({ state := .finalRead
             tape := { left := left, head := some b, right := r } } :
            Configuration PreservingReadState (Option Bool)))
      simp [List.reverse_cons, List.map_append, List.append_assoc]

def rewindInspectState : Bool → PreservingReadState
  | false => .rewindInspectFalse
  | true => .rewindInspectTrue

def cleanupState : Bool → PreservingReadState
  | false => .cleanupFalse
  | true => .cleanupTrue

def haltState : Bool → PreservingReadState
  | false => .haltFalse
  | true => .haltTrue

def rewindConfig
    (result : Bool) (left : List (Option Bool))
    (bits : BitString) (after : List (Option Bool)) :
    Configuration PreservingReadState (Option Bool) :=
  { state := rewindInspectState result
    tape := rightStreamTape (none :: left) (bits.map some ++ after) }

theorem finalRead_to_rewind
    (result : Bool) (left : List (Option Bool))
    (bits : BitString) (after : List (Option Bool)) :
    preservingUnaryReadMachine.run 2
      { state := .finalRead
        tape :=
          { left := left
            head := some result
            right := none :: (bits.map some ++ after) } } =
      rewindConfig result (some result :: left) bits after := by
  cases result <;> cases bits <;> cases after <;>
    simp [rewindConfig, rewindInspectState, rightStreamTape,
      preservingUnaryReadMachine, TM.run, TM.step, Tape.write, Tape.move]

theorem rewind_step_cons
    (result x : Bool) (xs : BitString)
    (left : List (Option Bool)) (after : List (Option Bool)) :
    preservingUnaryReadMachine.run 3
      (rewindConfig result left (x :: xs) after) =
      rewindConfig result (some x :: left) xs after := by
  cases result <;> cases x <;> cases xs <;> cases after <;>
    simp [rewindConfig, rewindInspectState, rightStreamTape,
      preservingUnaryReadMachine, TM.run, TM.step, Tape.write, Tape.move,
      List.append_assoc]

theorem rewind_over_bits
    (result : Bool) (bits : BitString)
    (left : List (Option Bool)) (after : List (Option Bool)) :
    preservingUnaryReadMachine.run (3 * bits.length)
      (rewindConfig result left bits after) =
      rewindConfig result (bits.reverse.map some ++ left) [] after := by
  induction bits generalizing left with
  | nil =>
      rfl
  | cons x xs ih =>
      rw [show 3 * (x :: xs).length = 3 + 3 * xs.length by
        simp
        omega]
      rw [run_add]
      rw [rewind_step_cons]
      rw [ih (some x :: left)]
      apply congrArg
        (fun l : List (Option Bool) =>
          rewindConfig result l [] after)
      simp [List.reverse_cons, List.map_append, List.append_assoc]

theorem rewind_empty_to_cleanup
    (result : Bool) (left stream : List (Option Bool)) :
    preservingUnaryReadMachine.run 1
      (rewindConfig result left [] (none :: stream)) =
      { state := cleanupState result
        tape := rightStreamTape (none :: none :: left) stream } := by
  cases result <;> cases stream <;>
    simp [rewindConfig, rewindInspectState, cleanupState, rightStreamTape,
      preservingUnaryReadMachine, TM.run, TM.step, Tape.write, Tape.move]

theorem cleanup_run_halts
    (result : Bool) (k : Nat)
    (left : List (Option Bool)) :
    preservingUnaryReadMachine.run (k + 1)
      { state := cleanupState result
        tape := rightStreamTape left
          (List.replicate k none ++ [some false]) } =
      { state := haltState result
        tape :=
          { left := List.replicate (k + 1) none ++ left
            head := none
            right := [] } } := by
  induction k generalizing left with
  | zero =>
      cases result <;>
        simp [cleanupState, haltState, rightStreamTape,
          preservingUnaryReadMachine, TM.run, TM.step,
          Tape.write, Tape.move]
  | succ k ih =>
      rw [show Nat.succ k + 1 = 1 + (k + 1) by omega]
      rw [run_add]
      have hstep :
          preservingUnaryReadMachine.run 1
            { state := cleanupState result
              tape := rightStreamTape left
                (List.replicate (Nat.succ k) none ++ [some false]) } =
            { state := cleanupState result
              tape := rightStreamTape (none :: left)
                (List.replicate k none ++ [some false]) } := by
        cases k <;> cases result <;>
          simp [cleanupState, rightStreamTape, preservingUnaryReadMachine,
            TM.run, TM.step, Tape.write, Tape.move, List.replicate_succ,
            List.append_assoc]
      rw [hstep]
      rw [ih (none :: left)]
      apply congrArg
        (fun l : List (Option Bool) =>
          ({ state := haltState result
             tape := { left := l, head := none, right := [] } } :
            Configuration PreservingReadState (Option Bool)))
      have hidx : 1 + (k + 1) = k + 2 := by omega
      rw [hidx]
      exact replicate_none_extend k left

theorem replicate_none_two_extend
    (k : Nat) (left : List (Option Bool)) :
    List.replicate (k + 1) none ++ (none :: none :: left) =
      List.replicate (k + 3) none ++ left := by
  exact
    (replicate_none_extend k (none :: left)).trans
      (replicate_none_extend (k + 1) left)

def indexSomeFinalizeFuel (pref : BitString) : Nat :=
  6 * pref.length + 5

theorem indexSome_false_finalize
    (pref : BitString) (selected : Bool) (rest : BitString)
    (hpref : pref ≠ []) :
    preservingUnaryReadMachine.run (indexSomeFinalizeFuel pref)
      (indexSomeConfig pref (selected :: rest) 0) =
      { state := haltState selected
        tape :=
          { left :=
              List.replicate (pref.length + 2) none ++
                pref.map some ++ some selected :: rest.map some
            head := none
            right := [] } } := by
  rcases pref with _ | ⟨first, prefTail⟩
  · contradiction
  let m : Nat := prefTail.length
  let pref : BitString := first :: prefTail
  let witnessSuffix : List (Option Bool) := rest.map some
  let after : List (Option Bool) :=
    List.replicate (m + 1) none ++ [some false]
  let restoredWitness : List (Option Bool) :=
    pref.map some ++ (some selected :: witnessSuffix)

  let C0 : Configuration PreservingReadState (Option Bool) :=
    indexSomeConfig pref (selected :: rest) 0
  let C1 : Configuration PreservingReadState (Option Bool) :=
    { state := .finalSeekBlanks
      tape :=
        { left :=
            List.replicate m none ++
              (some first ::
                (prefTail.map some ++
                  (none :: some selected :: witnessSuffix)))
          head := none
          right := [some false] } }
  let C2 : Configuration PreservingReadState (Option Bool) :=
    { state := .finalSeekBlanks
      tape :=
        { left :=
            prefTail.map some ++ (none :: some selected :: witnessSuffix)
          head := some first
          right := List.replicate (m + 1) none ++ [some false] } }
  let C3 : Configuration PreservingReadState (Option Bool) :=
    { state := .finalSeekBits
      tape := finalSeekBitsTape prefTail selected witnessSuffix
        (some first :: (List.replicate (m + 1) none ++ [some false])) }
  let C4 : Configuration PreservingReadState (Option Bool) :=
    { state := .finalRead
      tape :=
        { left := witnessSuffix
          head := some selected
          right := none :: (pref.reverse.map some ++ after) } }
  let C5 : Configuration PreservingReadState (Option Bool) :=
    rewindConfig selected (some selected :: witnessSuffix) pref.reverse after
  let C6 : Configuration PreservingReadState (Option Bool) :=
    rewindConfig selected restoredWitness [] after
  let C7 : Configuration PreservingReadState (Option Bool) :=
    { state := cleanupState selected
      tape := rightStreamTape (none :: none :: restoredWitness)
        (List.replicate m none ++ [some false]) }
  let C8 : Configuration PreservingReadState (Option Bool) :=
    { state := haltState selected
      tape :=
        { left := List.replicate (m + 3) none ++ restoredWitness
          head := none
          right := [] } }

  have h01 : preservingUnaryReadMachine.run 1 C0 = C1 := by
    dsimp [C0, C1, pref, m, witnessSuffix]
    simp [indexSomeConfig, encodeNat, preservingUnaryReadMachine,
      TM.run, TM.step, Tape.write, Tape.move,
      List.replicate_succ, List.append_assoc]

  have h12 : preservingUnaryReadMachine.run (m + 1) C1 = C2 := by
    dsimp [C1, C2]
    simpa using
      finalSeekBlanks_over_blanks m first
        (prefTail.map some ++ (none :: some selected :: witnessSuffix))
        [some false]

  have h23 : preservingUnaryReadMachine.run 1 C2 = C3 := by
    dsimp [C2, C3]
    simpa [TM.run] using
      finalSeekBlanks_step_bit first selected prefTail witnessSuffix
        (List.replicate (m + 1) none ++ [some false])

  have h34 : preservingUnaryReadMachine.run (m + 1) C3 = C4 := by
    dsimp [C3, C4, pref, after, m]
    simpa [pref, List.reverse_cons, List.map_append,
      List.append_assoc] using
      finalSeekBits_over_bits prefTail selected witnessSuffix
        (some first ::
          (List.replicate (prefTail.length + 1) none ++ [some false]))

  have h45 : preservingUnaryReadMachine.run 2 C4 = C5 := by
    dsimp [C4, C5, pref, after]
    simpa [pref, List.reverse_cons, List.map_append,
      List.append_assoc] using
      finalRead_to_rewind selected witnessSuffix pref.reverse after

  have h56 :
      preservingUnaryReadMachine.run (3 * pref.length) C5 = C6 := by
    dsimp [C5, C6, restoredWitness]
    simpa [pref, List.reverse_reverse, List.map_append,
      List.append_assoc] using
      rewind_over_bits selected pref.reverse
        (some selected :: witnessSuffix) after

  have h67 : preservingUnaryReadMachine.run 1 C6 = C7 := by
    have hrep :
        List.replicate (m + 1) none ++ [some false] =
          none :: (List.replicate m none ++ [some false]) := by
      simp [List.replicate_succ]
    dsimp [C6, C7, after]
    rw [hrep]
    exact
      rewind_empty_to_cleanup selected restoredWitness
        (List.replicate m none ++ [some false])

  have h78 : preservingUnaryReadMachine.run (m + 1) C7 = C8 := by
    dsimp [C7, C8]
    rw [cleanup_run_halts selected m (none :: none :: restoredWitness)]
    apply congrArg
      (fun l : List (Option Bool) =>
        ({ state := haltState selected
           tape := { left := l, head := none, right := [] } } :
          Configuration PreservingReadState (Option Bool)))
    exact replicate_none_two_extend m restoredWitness

  have h02 :
      preservingUnaryReadMachine.run (1 + (m + 1)) C0 = C2 := by
    rw [run_add, h01, h12]
  have h03 :
      preservingUnaryReadMachine.run ((1 + (m + 1)) + 1) C0 = C3 := by
    rw [run_add, h02, h23]
  have h04 :
      preservingUnaryReadMachine.run (((1 + (m + 1)) + 1) + (m + 1)) C0 = C4 := by
    rw [run_add, h03, h34]
  have h05 :
      preservingUnaryReadMachine.run
        ((((1 + (m + 1)) + 1) + (m + 1)) + 2) C0 = C5 := by
    rw [run_add, h04, h45]
  have h06 :
      preservingUnaryReadMachine.run
        (((((1 + (m + 1)) + 1) + (m + 1)) + 2) +
          (3 * pref.length)) C0 = C6 := by
    rw [run_add, h05, h56]
  have h07 :
      preservingUnaryReadMachine.run
        ((((((1 + (m + 1)) + 1) + (m + 1)) + 2) +
          (3 * pref.length)) + 1) C0 = C7 := by
    rw [run_add, h06, h67]
  have h08 :
      preservingUnaryReadMachine.run
        (((((((1 + (m + 1)) + 1) + (m + 1)) + 2) +
          (3 * pref.length)) + 1) + (m + 1)) C0 = C8 := by
    rw [run_add, h07, h78]

  have hFuel :
      indexSomeFinalizeFuel pref =
        (((((((1 + (m + 1)) + 1) + (m + 1)) + 2) +
          (3 * pref.length)) + 1) + (m + 1)) := by
    dsimp [indexSomeFinalizeFuel, pref, m]
    omega
  rw [hFuel]
  simpa [C0, C8, pref, restoredWitness, m,
    List.map_append, List.append_assoc] using h08


def indexSomeFuel (prefLen : Nat) : Nat → Nat
  | 0 => 6 * prefLen + 5
  | n + 1 => (4 * prefLen + 8) + indexSomeFuel (prefLen + 1) n

theorem indexSome_forall
    (first : Bool) (prefTail rest : BitString) (n : Nat)
    (h : n < rest.length) :
    preservingUnaryReadMachine.run
      (indexSomeFuel (first :: prefTail).length n)
      (indexSomeConfig (first :: prefTail) rest n) =
      { state := haltState (rest.getD n false)
        tape :=
          { left :=
              List.replicate ((first :: prefTail).length + n + 2) none ++
                ((first :: prefTail) ++ rest).map some
            head := none
            right := [] } } := by
  induction n generalizing prefTail rest with
  | zero =>
      cases rest with
      | nil =>
          simp at h
      | cons selected restTail =>
          have hf :
              indexSomeFuel (first :: prefTail).length 0 =
                indexSomeFinalizeFuel (first :: prefTail) := by
            simp [indexSomeFuel, indexSomeFinalizeFuel]
          rw [hf]
          have hfin :=
            indexSome_false_finalize
              (first :: prefTail) selected restTail (by simp)
          simpa [List.map_append, List.append_assoc] using hfin
  | succ n ih =>
      cases rest with
      | nil =>
          simp at h
      | cons selected restTail =>
          have htail : n < restTail.length := by
            simpa using h
          rw [show
            indexSomeFuel (first :: prefTail).length (n + 1) =
              (4 * (first :: prefTail).length + 8) +
                indexSomeFuel
                  (first :: (prefTail ++ [selected])).length n by
              simp [indexSomeFuel]]
          rw [run_add]
          rw [indexSome_run_advance
            (first :: prefTail) selected restTail n (by simp)]
          change preservingUnaryReadMachine.run
            (indexSomeFuel
              (first :: (prefTail ++ [selected])).length n)
            (indexSomeConfig
              (first :: (prefTail ++ [selected])) restTail n) = _
          rw [ih (prefTail := prefTail ++ [selected])
            (rest := restTail) htail]
          simpa [List.getD_cons_succ, List.map_append, List.append_assoc,
            Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]

def preservingUnaryExactFuel : Nat → Nat
  | 0 => 5
  | n + 1 => 8 + indexSomeFuel 1 n

theorem preservingUnary_run_exact
    (witness : BitString) (i : Nat)
    (hi : i < witness.length) :
    preservingUnaryReadMachine.run (preservingUnaryExactFuel i)
      { state := preservingUnaryReadMachine.initial
        tape := witnessReadTape witness i } =
      { state := haltState (witness.getD i false)
        tape :=
          { left := List.replicate (i + 2) none ++ witness.map some
            head := none
            right := [] } } := by
  cases witness with
  | nil =>
      simp at hi
  | cons b tail =>
      cases i with
      | zero =>
          cases b with
          | false =>
              simpa [preservingUnaryExactFuel, zeroDoneTape, haltState,
                List.replicate_succ, List.append_assoc] using
                preservingRead_zero_run_five false tail
          | true =>
              simpa [preservingUnaryExactFuel, zeroDoneTape, haltState,
                List.replicate_succ, List.append_assoc] using
                preservingRead_zero_run_five true tail
      | succ n =>
          have hn : n < tail.length := by
            simpa using hi
          rw [show
            preservingUnaryExactFuel (n + 1) =
              8 + indexSomeFuel ([b] : BitString).length n by
                rfl]
          rw [run_add]
          rw [preservingRead_first_true_cycle b tail n]
          rw [indexSome_forall b [] tail n hn]
          simp [List.getD_cons_succ, List.map_append, List.append_assoc]
          omega


theorem indexSomeFuel_le (m n : Nat) :
    indexSomeFuel m n ≤
      (4 * (m + n) + 8) * n + 6 * (m + n) + 5 := by
  induction n generalizing m with
  | zero =>
      simp [indexSomeFuel]
  | succ n ih =>
      simp only [indexSomeFuel]
      have h := ih (m + 1)
      rw [show m + 1 + n = m + (n + 1) by omega] at h
      have hstep :
          (4 * (m + (n + 1)) + 8) * n +
              6 * (m + (n + 1)) + 5 +
              (4 * m + 8) ≤
            (4 * (m + (n + 1)) + 8) * (n + 1) +
              6 * (m + (n + 1)) + 5 := by
        rw [Nat.mul_succ]
        omega
      omega

theorem preservingUnaryExactFuel_le_quadratic (i : Nat) :
    preservingUnaryExactFuel i ≤ 16 * (i + 1) ^ 2 := by
  cases i with
  | zero =>
      simp [preservingUnaryExactFuel]
  | succ n =>
      simp only [preservingUnaryExactFuel]
      have h := indexSomeFuel_le 1 n
      have e1 :
          (4 * (1 + n) + 8) * n =
            4 * (n * n) + 12 * n := by
        simp only [Nat.add_mul, Nat.mul_add, Nat.mul_one, Nat.one_mul,
          Nat.mul_assoc]
        omega
      have e2 :
          16 * (n + 1 + 1) ^ 2 =
            16 * (n * n) + 64 * n + 64 := by
        simp only [Nat.pow_two, Nat.add_mul, Nat.mul_add, Nat.mul_one,
          Nat.one_mul, Nat.mul_assoc]
        omega
      rw [e1] at h
      rw [e2]
      omega

#print axioms MCore.Real.P01PreservingUnaryPhysicalRuns.indexSome_forall
#print axioms MCore.Real.P01PreservingUnaryPhysicalRuns.preservingUnary_run_exact
#print axioms MCore.Real.P01PreservingUnaryPhysicalRuns.indexSomeFuel_le
#print axioms MCore.Real.P01PreservingUnaryPhysicalRuns.preservingUnaryExactFuel_le_quadratic

#print axioms MCore.Real.P01PreservingUnaryPhysicalRuns.finalSeekBits_over_bits
#print axioms MCore.Real.P01PreservingUnaryPhysicalRuns.rewind_over_bits
#print axioms MCore.Real.P01PreservingUnaryPhysicalRuns.rewind_empty_to_cleanup
#print axioms MCore.Real.P01PreservingUnaryPhysicalRuns.cleanup_run_halts
#print axioms MCore.Real.P01PreservingUnaryPhysicalRuns.indexSome_false_finalize

#print axioms MCore.Real.P01PreservingUnaryPhysicalRuns.indexSome_run_advance

end P01PreservingUnaryPhysicalRuns
end Real
end MCore
