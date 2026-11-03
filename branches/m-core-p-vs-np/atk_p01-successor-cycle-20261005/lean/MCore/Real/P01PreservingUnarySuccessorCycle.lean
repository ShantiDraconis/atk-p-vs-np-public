import MCore.Real.P01PreservingUnaryWitnessMachine
import MCore.Real.MachineRunLemmas

namespace MCore
namespace Real
namespace P01PreservingUnarySuccessorCycle

open CanonicalFinalProof
open CanonicalCircuitBits
open MachineRunLemmas
open P01PreservingUnaryWitnessMachine

@[simp] theorem preserving_not_halt_seekBlanks :
    preservingUnaryReadMachine.halting .seekBlanks = false := rfl

@[simp] theorem preserving_not_halt_seekBits :
    preservingUnaryReadMachine.halting .seekBits = false := rfl

/-- Configuration while crossing erased unary blanks.
`pad` counts blanks still to the left of the blank currently under the head.
The right side is explicit because every left move pushes one blank onto it. -/
def seekBlanksConfig
    (pad : Nat) (pref suffix : BitString)
    (right : List (Option Bool)) :
    Configuration PreservingReadState (Option Bool) :=
  { state := .seekBlanks
    tape :=
      { left := List.replicate pad none ++ pref.map some ++ none :: suffix.map some
        head := none
        right := right } }

@[simp] theorem seekBlanksConfig_state
    (pad : Nat) (pref suffix : BitString)
    (right : List (Option Bool)) :
    (seekBlanksConfig pad pref suffix right).state = .seekBlanks := rfl

theorem replicate_none_push
    (pad : Nat) (right : List (Option Bool)) :
    List.replicate pad none ++ none :: right =
      none :: List.replicate pad none ++ right := by
  induction pad with
  | zero => rfl
  | succ pad ih =>
      simp [List.replicate_succ, ih, List.append_assoc]

theorem replicate_two_more_none
    (pad : Nat) (right : List (Option Bool)) :
    List.replicate (pad + 2) none ++ right =
      none :: none :: (List.replicate pad none ++ right) := by
  induction pad with
  | zero => rfl
  | succ pad ih =>
      simp [List.replicate_succ, List.append_assoc]

theorem indexSome_true_step
    (a b : Bool) (rest suffix : BitString) (n : Nat) :
    preservingUnaryReadMachine.step
      (indexSomeConfig (a :: rest) (b :: suffix) (n + 1)) =
    seekBlanksConfig rest.length (a :: rest) (b :: suffix)
      (none :: (encodeNat n).map some) := by
  cases a <;> cases b <;> cases n <;>
    simp [indexSomeConfig, seekBlanksConfig, encodeNat,
      preservingUnaryReadMachine, TM.step, Tape.write, Tape.move,
      List.replicate_succ, List.append_assoc]

theorem seekBlanks_step_succ
    (pad : Nat) (pref suffix : BitString)
    (right : List (Option Bool)) :
    preservingUnaryReadMachine.step
      (seekBlanksConfig (pad + 1) pref suffix right) =
    seekBlanksConfig pad pref suffix (none :: right) := by
  simp [seekBlanksConfig, preservingUnaryReadMachine, TM.step,
    Tape.write, Tape.move, List.replicate_succ, List.append_assoc]

/-- Crossing the current blank plus all `pad` blanks to its left reaches the
first traversed witness bit. -/
theorem seekBlanks_run_to_first_bit
    (pad : Nat) (c : Bool) (cs suffix : BitString)
    (right : List (Option Bool)) :
    preservingUnaryReadMachine.run (pad + 1)
      (seekBlanksConfig pad (c :: cs) suffix right) =
    { state := .seekBlanks
      tape :=
        { left := cs.map some ++ none :: suffix.map some
          head := some c
          right := List.replicate (pad + 1) none ++ right } } := by
  induction pad generalizing right with
  | zero =>
      simp [seekBlanksConfig, preservingUnaryReadMachine, TM.run, TM.step,
        Tape.write, Tape.move]
  | succ pad ih =>
      rw [show Nat.succ pad + 1 = 1 + (pad + 1) by omega]
      rw [run_add]
      have h1 :
          preservingUnaryReadMachine.run 1
            (seekBlanksConfig (Nat.succ pad) (c :: cs) suffix right) =
          seekBlanksConfig pad (c :: cs) suffix (none :: right) := by
        rw [TM.run]
        simp only [seekBlanksConfig_state, preserving_not_halt_seekBlanks,
          Bool.false_eq_true, if_false]
        simpa [Nat.succ_eq_add_one] using
          seekBlanks_step_succ pad (c :: cs) suffix right
      rw [h1]
      have hih := ih (right := none :: right)
      rw [replicate_none_push (pad + 1) right] at hih
      simpa [List.replicate_succ, List.append_assoc, Nat.one_add] using hih

/-- Configuration while seekBits crosses the Boolean prefix toward the unique
witness marker. -/
def seekBitsConfig
    (remaining suffix : BitString)
    (right : List (Option Bool)) :
    Configuration PreservingReadState (Option Bool) :=
  match remaining with
  | [] =>
      { state := .seekBits
        tape := { left := suffix.map some, head := none, right := right } }
  | c :: cs =>
      { state := .seekBits
        tape :=
          { left := cs.map some ++ none :: suffix.map some
            head := some c
            right := right } }

@[simp] theorem seekBitsConfig_state
    (remaining suffix : BitString)
    (right : List (Option Bool)) :
    (seekBitsConfig remaining suffix right).state = .seekBits := by
  cases remaining <;> rfl

theorem seekBlanks_first_bit_step
    (c : Bool) (cs suffix : BitString)
    (right : List (Option Bool)) :
    preservingUnaryReadMachine.step
      { state := PreservingReadState.seekBlanks
        tape :=
          { left := cs.map some ++ none :: suffix.map some
            head := some c
            right := right } } =
    seekBitsConfig cs suffix (some c :: right) := by
  cases cs <;>
    simp [seekBitsConfig, preservingUnaryReadMachine, TM.step,
      Tape.write, Tape.move, List.append_assoc]

theorem seekBits_step_cons
    (c : Bool) (cs suffix : BitString)
    (right : List (Option Bool)) :
    preservingUnaryReadMachine.step
      (seekBitsConfig (c :: cs) suffix right) =
    seekBitsConfig cs suffix (some c :: right) := by
  cases cs <;>
    simp [seekBitsConfig, preservingUnaryReadMachine, TM.step,
      Tape.write, Tape.move, List.append_assoc]

/-- Configuration with the selected next witness bit under shiftRead. -/
def shiftReadConfig
    (b : Bool) (suffix : BitString)
    (right : List (Option Bool)) :
    Configuration PreservingReadState (Option Bool) :=
  { state := .shiftRead
    tape := { left := suffix.map some, head := some b, right := none :: right } }

/-- Configuration after the marker has moved across b and the machine has
returned onto b, ready to scan right across the traversed bits. -/
def returnBitsConfig
    (b : Bool) (suffix : BitString)
    (right : List (Option Bool)) :
    Configuration PreservingReadState (Option Bool) :=
  { state := .returnBits
    tape := { left := none :: suffix.map some, head := some b, right := right } }

theorem seekBits_marker_step
    (b : Bool) (suffix : BitString)
    (right : List (Option Bool)) :
    preservingUnaryReadMachine.step
      (seekBitsConfig [] (b :: suffix) right) =
    shiftReadConfig b suffix right := by
  simp [seekBitsConfig, shiftReadConfig, preservingUnaryReadMachine,
    TM.step, Tape.write, Tape.move]

theorem shift_carry_return_run_three
    (b : Bool) (suffix : BitString)
    (right : List (Option Bool)) :
    preservingUnaryReadMachine.run 3
      (shiftReadConfig b suffix right) =
    returnBitsConfig b suffix right := by
  cases b <;>
    simp [shiftReadConfig, returnBitsConfig, preservingUnaryReadMachine,
      TM.run, TM.step, Tape.write, Tape.move]

/-- Rightward scan configuration after the marker shift.
`processed` is stored in physical left-stack order; each right move conses
the bit just crossed onto this list. -/
def returnBitsScanConfig
    (processed remaining suffix : BitString)
    (rightTail : List (Option Bool)) :
    Configuration PreservingReadState (Option Bool) :=
  match remaining with
  | [] =>
      { state := .returnBits
        tape :=
          { left := processed.map some ++ none :: suffix.map some
            head := none
            right := rightTail } }
  | x :: xs =>
      { state := .returnBits
        tape :=
          { left := processed.map some ++ none :: suffix.map some
            head := some x
            right := xs.map some ++ none :: rightTail } }

@[simp] theorem returnBitsScanConfig_state
    (processed remaining suffix : BitString)
    (rightTail : List (Option Bool)) :
    (returnBitsScanConfig processed remaining suffix rightTail).state =
      .returnBits := by
  cases remaining <;> rfl

@[simp] theorem preserving_not_halt_returnBits :
    preservingUnaryReadMachine.halting .returnBits = false := rfl

theorem returnBits_step_cons
    (processed : BitString) (x : Bool) (xs suffix : BitString)
    (rightTail : List (Option Bool)) :
    preservingUnaryReadMachine.step
      (returnBitsScanConfig processed (x :: xs) suffix rightTail) =
    returnBitsScanConfig (x :: processed) xs suffix rightTail := by
  cases xs <;>
    simp [returnBitsScanConfig, preservingUnaryReadMachine, TM.step,
      Tape.write, Tape.move, List.append_assoc]

theorem returnBitsConfig_as_scan
    (pref : BitString) (b : Bool) (suffix : BitString) (n : Nat) :
    returnBitsConfig b suffix
        (pref.reverse.map some ++
          List.replicate pref.length none ++
          none :: (encodeNat n).map some) =
      returnBitsScanConfig [] (b :: pref.reverse) suffix
        (List.replicate pref.length none ++ (encodeNat n).map some) := by
  simp [returnBitsConfig, returnBitsScanConfig, List.map_append,
    List.append_assoc]
  rw [replicate_none_push pref.length ((encodeNat n).map some)]
  rfl

/-- Exact finite scan across all restored Boolean cells. -/
theorem returnBits_run
    (processed bits suffix : BitString)
    (rightTail : List (Option Bool)) :
    preservingUnaryReadMachine.run bits.length
      (returnBitsScanConfig processed bits suffix rightTail) =
    returnBitsScanConfig (bits.reverse ++ processed) [] suffix rightTail := by
  induction bits generalizing processed with
  | nil =>
      rfl
  | cons x xs ih =>
      rw [List.length_cons]
      simp only [TM.run, returnBitsScanConfig_state,
        preserving_not_halt_returnBits, Bool.false_eq_true, if_false]
      rw [returnBits_step_cons]
      have hih := ih (processed := x :: processed)
      rw [hih]
      simp [List.reverse_cons, List.append_assoc]

/-- Exact finite scan of the traversed witness-prefix tail. -/
theorem seekBits_run
    (remaining suffix : BitString)
    (right : List (Option Bool)) :
    preservingUnaryReadMachine.run remaining.length
      (seekBitsConfig remaining suffix right) =
    seekBitsConfig [] suffix (remaining.reverse.map some ++ right) := by
  induction remaining generalizing right with
  | nil =>
      rfl
  | cons c cs ih =>
      rw [List.length_cons]
      simp only [TM.run, seekBitsConfig_state, preserving_not_halt_seekBits,
        Bool.false_eq_true, if_false]
      rw [seekBits_step_cons]
      have hih := ih (right := some c :: right)
      rw [hih]
      simp [List.reverse_cons, List.map_append, List.append_assoc]

/-- Configuration for the final rightward scan across erased unary blanks.
`pad` counts blanks including the blank currently under the head. -/
def returnBlanksScanConfig
    (pad : Nat)
    (leftBase : List (Option Bool))
    (bit : Bool) (rest : List (Option Bool)) :
    Configuration PreservingReadState (Option Bool) :=
  match pad with
  | 0 =>
      { state := .returnBlanks
        tape := { left := leftBase, head := some bit, right := rest } }
  | k + 1 =>
      { state := .returnBlanks
        tape :=
          { left := leftBase
            head := none
            right := List.replicate k none ++ some bit :: rest } }

@[simp] theorem returnBlanksScanConfig_state
    (pad : Nat) (leftBase : List (Option Bool))
    (bit : Bool) (rest : List (Option Bool)) :
    (returnBlanksScanConfig pad leftBase bit rest).state = .returnBlanks := by
  cases pad <;> rfl

@[simp] theorem preserving_not_halt_returnBlanks :
    preservingUnaryReadMachine.halting .returnBlanks = false := rfl

theorem returnBlanks_step_succ
    (pad : Nat) (leftBase : List (Option Bool))
    (bit : Bool) (rest : List (Option Bool)) :
    preservingUnaryReadMachine.step
      (returnBlanksScanConfig (pad + 1) leftBase bit rest) =
    returnBlanksScanConfig pad (none :: leftBase) bit rest := by
  cases pad <;>
    simp [returnBlanksScanConfig, preservingUnaryReadMachine, TM.step,
      Tape.write, Tape.move, List.replicate_succ, List.append_assoc]

/-- Crossing exactly `pad` erased blanks preserves the Boolean payload and
moves all blanks onto Tape.left. -/
theorem returnBlanks_run
    (pad : Nat) (leftBase : List (Option Bool))
    (bit : Bool) (rest : List (Option Bool)) :
    preservingUnaryReadMachine.run pad
      (returnBlanksScanConfig pad leftBase bit rest) =
    returnBlanksScanConfig 0
      (List.replicate pad none ++ leftBase) bit rest := by
  induction pad generalizing leftBase with
  | zero => rfl
  | succ pad ih =>
      rw [TM.run]
      simp only [returnBlanksScanConfig_state, preserving_not_halt_returnBlanks,
        Bool.false_eq_true, if_false]
      have hstep :
          preservingUnaryReadMachine.step
            (returnBlanksScanConfig (Nat.succ pad) leftBase bit rest) =
          returnBlanksScanConfig pad (none :: leftBase) bit rest := by
        simpa [Nat.succ_eq_add_one] using
          returnBlanks_step_succ pad leftBase bit rest
      rw [hstep]
      have hih := ih (leftBase := none :: leftBase)
      rw [hih]
      rw [replicate_none_push pad leftBase]
      simp [List.replicate_succ, List.append_assoc]

theorem returnBits_blank_to_returnBlanks
    (pad : Nat) (rebuilt suffix : BitString)
    (bit : Bool) (rest : List (Option Bool)) :
    preservingUnaryReadMachine.step
      (returnBitsScanConfig rebuilt [] suffix
        (List.replicate (pad + 1) none ++ some bit :: rest)) =
    returnBlanksScanConfig (pad + 1)
      (none :: rebuilt.map some ++ none :: suffix.map some) bit rest := by
  simp [returnBitsScanConfig, returnBlanksScanConfig,
    preservingUnaryReadMachine, TM.step, Tape.write, Tape.move,
    List.replicate_succ, List.append_assoc]

/-- Once the next unary symbol is under the head, returnBlanks re-enters the
canonical indexSome control state without changing the tape. -/
theorem returnBlanks_to_indexSome
    (leftBase : List (Option Bool))
    (bit : Bool) (rest : List (Option Bool)) :
    preservingUnaryReadMachine.step
      (returnBlanksScanConfig 0 leftBase bit rest) =
    { state := .indexSome
      tape := { left := leftBase, head := some bit, right := rest } } := by
  simp [returnBlanksScanConfig, preservingUnaryReadMachine, TM.step,
    Tape.write, Tape.move]

def forwardPhaseFuel (pref : BitString) : Nat :=
  2 * pref.length + 5

/-- Physical forward half of a later unary cycle:
indexSome(true) -> selected next witness bit -> returnBits. -/
theorem forwardPhase_run
    (a b : Bool) (rest suffix : BitString) (n : Nat) :
    preservingUnaryReadMachine.run (forwardPhaseFuel (a :: rest))
      (indexSomeConfig (a :: rest) (b :: suffix) (n + 1)) =
    returnBitsConfig b suffix
      ((a :: rest).reverse.map some ++
        List.replicate (a :: rest).length none ++
        none :: (encodeNat n).map some) := by
  let pref : BitString := a :: rest
  let right0 : List (Option Bool) := none :: (encodeNat n).map some
  let right1 : List (Option Bool) :=
    List.replicate pref.length none ++ right0
  let right2 : List (Option Bool) :=
    pref.reverse.map some ++ right1

  have hp : pref.length = rest.length + 1 := by
    simp [pref]

  have h0 :
      preservingUnaryReadMachine.run 1
        (indexSomeConfig pref (b :: suffix) (n + 1)) =
      seekBlanksConfig rest.length pref (b :: suffix) right0 := by
    rw [TM.run]
    simp [indexSomeConfig_state, preservingUnaryReadMachine]
    simpa [pref, right0] using indexSome_true_step a b rest suffix n

  have h1 :
      preservingUnaryReadMachine.run (rest.length + 1)
        (seekBlanksConfig rest.length pref (b :: suffix) right0) =
      { state := PreservingReadState.seekBlanks
        tape :=
          { left := rest.map some ++ none :: (b :: suffix).map some
            head := some a
            right := right1 } } := by
    have h :=
      seekBlanks_run_to_first_bit rest.length a rest (b :: suffix) right0
    simpa [right1, pref, hp, right0, List.append_assoc] using h

  have h2 :
      preservingUnaryReadMachine.run 1
        { state := PreservingReadState.seekBlanks
          tape :=
            { left := rest.map some ++ none :: (b :: suffix).map some
              head := some a
              right := right1 } } =
      seekBitsConfig rest (b :: suffix) (some a :: right1) := by
    rw [TM.run]
    simp only [preserving_not_halt_seekBlanks, Bool.false_eq_true, if_false]
    exact seekBlanks_first_bit_step a rest (b :: suffix) right1

  have h3 :
      preservingUnaryReadMachine.run rest.length
        (seekBitsConfig rest (b :: suffix) (some a :: right1)) =
      seekBitsConfig [] (b :: suffix) right2 := by
    have h := seekBits_run rest (b :: suffix) (some a :: right1)
    simpa [right2, pref, List.reverse_cons, List.map_append,
      List.append_assoc] using h

  have h4 :
      preservingUnaryReadMachine.run 1
        (seekBitsConfig [] (b :: suffix) right2) =
      shiftReadConfig b suffix right2 := by
    rw [TM.run]
    simp only [seekBitsConfig_state, preserving_not_halt_seekBits,
      Bool.false_eq_true, if_false]
    exact seekBits_marker_step b suffix right2

  have h5 :
      preservingUnaryReadMachine.run 3
        (shiftReadConfig b suffix right2) =
      returnBitsConfig b suffix right2 :=
    shift_carry_return_run_three b suffix right2

  have h01 :
      preservingUnaryReadMachine.run (1 + (rest.length + 1))
        (indexSomeConfig pref (b :: suffix) (n + 1)) =
      { state := PreservingReadState.seekBlanks
        tape :=
          { left := rest.map some ++ none :: (b :: suffix).map some
            head := some a
            right := right1 } } := by
    rw [run_add, h0, h1]

  have h012 :
      preservingUnaryReadMachine.run ((1 + (rest.length + 1)) + 1)
        (indexSomeConfig pref (b :: suffix) (n + 1)) =
      seekBitsConfig rest (b :: suffix) (some a :: right1) := by
    rw [run_add, h01, h2]

  have h0123 :
      preservingUnaryReadMachine.run
        (((1 + (rest.length + 1)) + 1) + rest.length)
        (indexSomeConfig pref (b :: suffix) (n + 1)) =
      seekBitsConfig [] (b :: suffix) right2 := by
    rw [run_add, h012, h3]

  have h01234 :
      preservingUnaryReadMachine.run
        ((((1 + (rest.length + 1)) + 1) + rest.length) + 1)
        (indexSomeConfig pref (b :: suffix) (n + 1)) =
      shiftReadConfig b suffix right2 := by
    rw [run_add, h0123, h4]

  have hall :
      preservingUnaryReadMachine.run
        (((((1 + (rest.length + 1)) + 1) + rest.length) + 1) + 3)
        (indexSomeConfig pref (b :: suffix) (n + 1)) =
      returnBitsConfig b suffix right2 := by
    rw [run_add, h01234, h5]

  have hfuel :
      (((((1 + (rest.length + 1)) + 1) + rest.length) + 1) + 3) =
        forwardPhaseFuel pref := by
    unfold forwardPhaseFuel
    rw [hp]
    omega
  rw [← hfuel]
  simpa [pref, right0, right1, right2, List.reverse_cons,
    List.map_append, List.append_assoc] using hall

#print axioms MCore.Real.P01PreservingUnarySuccessorCycle.forwardPhase_run

def returnPhaseFuel (pref : BitString) : Nat :=
  2 * pref.length + 3

/-- Full physical return phase on every reachable nonempty prefix. -/
theorem returnPhase_run
    (a b : Bool) (rest suffix : BitString) (n : Nat) :
    preservingUnaryReadMachine.run (returnPhaseFuel (a :: rest))
      (returnBitsConfig b suffix
        ((a :: rest).reverse.map some ++
          List.replicate (a :: rest).length none ++
          none :: (encodeNat n).map some)) =
      indexSomeConfig ((a :: rest) ++ [b]) suffix n := by
  let pref : BitString := a :: rest
  have hp : pref.length = rest.length + 1 := by
    simp [pref]

  have hbridge :
      returnBitsConfig b suffix
          (pref.reverse.map some ++
            List.replicate pref.length none ++
            none :: (encodeNat n).map some) =
        returnBitsScanConfig [] (b :: pref.reverse) suffix
          (List.replicate pref.length none ++ (encodeNat n).map some) :=
    returnBitsConfig_as_scan pref b suffix n

  rw [show (a :: rest) = pref by rfl]
  rw [hbridge]
  unfold returnPhaseFuel

  have hbits :
      preservingUnaryReadMachine.run (pref.length + 1)
        (returnBitsScanConfig [] (b :: pref.reverse) suffix
          (List.replicate pref.length none ++ (encodeNat n).map some)) =
      returnBitsScanConfig (pref ++ [b]) [] suffix
        (List.replicate pref.length none ++ (encodeNat n).map some) := by
    have h :=
      returnBits_run [] (b :: pref.reverse) suffix
        (List.replicate pref.length none ++ (encodeNat n).map some)
    simpa [List.reverse_cons, List.length_reverse, List.append_assoc] using h

  rw [show 2 * pref.length + 3 =
    (pref.length + 1) + (1 + (pref.length + 1)) by omega]
  rw [run_add, hbits]

  cases n with
  | zero =>
      rw [run_add]
      have hblank :
          preservingUnaryReadMachine.run 1
            (returnBitsScanConfig (pref ++ [b]) [] suffix
              (List.replicate pref.length none ++ (encodeNat 0).map some)) =
          returnBlanksScanConfig pref.length
            (none :: (pref ++ [b]).map some ++ none :: suffix.map some)
            false [] := by
        rw [TM.run]
        simp only [returnBitsScanConfig_state, preserving_not_halt_returnBits,
          Bool.false_eq_true, if_false]
        simpa [pref, encodeNat, hp, Nat.succ_eq_add_one] using
          returnBits_blank_to_returnBlanks rest.length (pref ++ [b]) suffix false []
      rw [hblank]
      rw [run_add]
      rw [returnBlanks_run]
      rw [TM.run]
      simp only [returnBlanksScanConfig_state, preserving_not_halt_returnBlanks,
        Bool.false_eq_true, if_false]
      rw [returnBlanks_to_indexSome]
      simp [indexSomeConfig, encodeNat, pref, hp, List.replicate_succ,
        List.append_assoc, replicate_none_push]
      rfl
  | succ n =>
      rw [run_add]
      have hblank :
          preservingUnaryReadMachine.run 1
            (returnBitsScanConfig (pref ++ [b]) [] suffix
              (List.replicate pref.length none ++ (encodeNat (n + 1)).map some)) =
          returnBlanksScanConfig pref.length
            (none :: (pref ++ [b]).map some ++ none :: suffix.map some)
            true ((encodeNat n).map some) := by
        rw [TM.run]
        simp only [returnBitsScanConfig_state, preserving_not_halt_returnBits,
          Bool.false_eq_true, if_false]
        simpa [pref, encodeNat, hp, Nat.succ_eq_add_one] using
          returnBits_blank_to_returnBlanks rest.length (pref ++ [b]) suffix
            true ((encodeNat n).map some)
      rw [hblank]
      rw [run_add]
      rw [returnBlanks_run]
      rw [TM.run]
      simp only [returnBlanksScanConfig_state, preserving_not_halt_returnBlanks,
        Bool.false_eq_true, if_false]
      rw [returnBlanks_to_indexSome]
      simp [indexSomeConfig, encodeNat, pref, hp, List.replicate_succ,
        List.append_assoc, replicate_none_push]
      rfl

def successorCycleFuel (pref : BitString) : Nat :=
  4 * pref.length + 8

/-- Exact universal physical successor cycle on every reachable nonempty
prefix.  No endpoint axiom is used: the theorem is the composition of the
material forward and return phases. -/
theorem preservingRead_indexSome_one_cycle
    (a b : Bool) (rest suffix : BitString) (n : Nat) :
    preservingUnaryReadMachine.run (successorCycleFuel (a :: rest))
      (indexSomeConfig (a :: rest) (b :: suffix) (n + 1)) =
    indexSomeConfig ((a :: rest) ++ [b]) suffix n := by
  rw [show successorCycleFuel (a :: rest) =
    forwardPhaseFuel (a :: rest) + returnPhaseFuel (a :: rest) by
      simp [successorCycleFuel, forwardPhaseFuel, returnPhaseFuel]
      omega]
  rw [run_add]
  rw [forwardPhase_run]
  exact returnPhase_run a b rest suffix n

#print axioms MCore.Real.P01PreservingUnarySuccessorCycle.preservingRead_indexSome_one_cycle

#print axioms MCore.Real.P01PreservingUnarySuccessorCycle.returnPhase_run

#print axioms MCore.Real.P01PreservingUnarySuccessorCycle.returnBits_run
#print axioms MCore.Real.P01PreservingUnarySuccessorCycle.returnBlanks_run
#print axioms MCore.Real.P01PreservingUnarySuccessorCycle.returnBlanks_to_indexSome

#print axioms MCore.Real.P01PreservingUnarySuccessorCycle.seekBlanks_run_to_first_bit
#print axioms MCore.Real.P01PreservingUnarySuccessorCycle.seekBits_marker_step
#print axioms MCore.Real.P01PreservingUnarySuccessorCycle.shift_carry_return_run_three
#print axioms MCore.Real.P01PreservingUnarySuccessorCycle.seekBits_run

end P01PreservingUnarySuccessorCycle
end Real
end MCore
