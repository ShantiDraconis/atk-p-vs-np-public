import MCore.Real.P01PreservingUnarySuccessorCycle

namespace MCore
namespace Real
namespace P01PreservingUnaryFinalRead

open CanonicalFinalProof
open CanonicalCircuitBits
open P01PreservingUnaryWitnessMachine
open P01PreservingUnarySuccessorCycle
open MachineRunLemmas

def selectedConfig
    (pref : BitString) (b : Bool) (suffix : BitString) :
    Configuration PreservingReadState (Option Bool) :=
  { state := if b then .selectedTrue else .selectedFalse
    tape :=
      { left := some b :: suffix.map some
        head := none
        right :=
          pref.reverse.map some ++
            List.replicate pref.length none ++ [some false] } }

@[simp] theorem finalSeekBlanks_not_halting :
    preservingUnaryReadMachine.halting .finalSeekBlanks = false := rfl

@[simp] theorem finalSeekBits_not_halting :
    preservingUnaryReadMachine.halting .finalSeekBits = false := rfl

@[simp] theorem finalRead_not_halting :
    preservingUnaryReadMachine.halting .finalRead = false := rfl

def finalSeekBlanksConfig
    (pad : Nat) (pref suffix : BitString)
    (right : List (Option Bool)) :
    Configuration PreservingReadState (Option Bool) :=
  { state := .finalSeekBlanks
    tape :=
      { left := List.replicate pad none ++ pref.map some ++ none :: suffix.map some
        head := none
        right := right } }

@[simp] theorem finalSeekBlanksConfig_state
    (pad : Nat) (pref suffix : BitString)
    (right : List (Option Bool)) :
    (finalSeekBlanksConfig pad pref suffix right).state = .finalSeekBlanks := rfl

theorem final_indexSome_zero_step
    (a b : Bool) (rest suffix : BitString) :
    preservingUnaryReadMachine.step
      (indexSomeConfig (a :: rest) (b :: suffix) 0) =
    finalSeekBlanksConfig rest.length (a :: rest) (b :: suffix) [some false] := by
  cases a <;> cases b <;>
    simp [indexSomeConfig, finalSeekBlanksConfig, encodeNat,
      preservingUnaryReadMachine, TM.step, Tape.write, Tape.move,
      List.replicate_succ, List.append_assoc]

theorem finalSeekBlanks_step_succ
    (pad : Nat) (pref suffix : BitString)
    (right : List (Option Bool)) :
    preservingUnaryReadMachine.step
      (finalSeekBlanksConfig (pad + 1) pref suffix right) =
    finalSeekBlanksConfig pad pref suffix (none :: right) := by
  simp [finalSeekBlanksConfig, preservingUnaryReadMachine,
    TM.step, Tape.write, Tape.move, List.replicate_succ,
    List.append_assoc]

theorem finalSeekBlanks_run_to_first_bit
    (pad : Nat) (c : Bool) (cs suffix : BitString)
    (right : List (Option Bool)) :
    preservingUnaryReadMachine.run (pad + 1)
      (finalSeekBlanksConfig pad (c :: cs) suffix right) =
    { state := .finalSeekBlanks
      tape :=
        { left := cs.map some ++ none :: suffix.map some
          head := some c
          right := List.replicate (pad + 1) none ++ right } } := by
  induction pad generalizing right with
  | zero =>
      simp [finalSeekBlanksConfig, preservingUnaryReadMachine,
        TM.run, TM.step, Tape.write, Tape.move]
  | succ pad ih =>
      rw [show Nat.succ pad + 1 = 1 + (pad + 1) by omega]
      rw [run_add]
      have h1 :
          preservingUnaryReadMachine.run 1
            (finalSeekBlanksConfig (Nat.succ pad) (c :: cs) suffix right) =
          finalSeekBlanksConfig pad (c :: cs) suffix (none :: right) := by
        rw [TM.run]
        simp only [finalSeekBlanksConfig_state, finalSeekBlanks_not_halting,
          Bool.false_eq_true, if_false]
        simpa [Nat.succ_eq_add_one] using
          finalSeekBlanks_step_succ pad (c :: cs) suffix right
      rw [h1]
      have hih := ih (right := none :: right)
      rw [replicate_none_push (pad + 1) right] at hih
      simpa [List.replicate_succ, List.append_assoc, Nat.one_add] using hih

def finalSeekBitsConfig
    (remaining suffix : BitString)
    (right : List (Option Bool)) :
    Configuration PreservingReadState (Option Bool) :=
  match remaining with
  | [] =>
      { state := .finalSeekBits
        tape := { left := suffix.map some, head := none, right := right } }
  | c :: cs =>
      { state := .finalSeekBits
        tape :=
          { left := cs.map some ++ none :: suffix.map some
            head := some c
            right := right } }

@[simp] theorem finalSeekBitsConfig_state
    (remaining suffix : BitString)
    (right : List (Option Bool)) :
    (finalSeekBitsConfig remaining suffix right).state = .finalSeekBits := by
  cases remaining <;> rfl

theorem finalSeekBlanks_first_bit_step
    (c : Bool) (cs suffix : BitString)
    (right : List (Option Bool)) :
    preservingUnaryReadMachine.step
      { state := .finalSeekBlanks
        tape :=
          { left := cs.map some ++ none :: suffix.map some
            head := some c
            right := right } } =
    finalSeekBitsConfig cs suffix (some c :: right) := by
  cases cs <;>
    simp [finalSeekBitsConfig, preservingUnaryReadMachine,
      TM.step, Tape.write, Tape.move, List.append_assoc]

theorem finalSeekBits_step_cons
    (c : Bool) (cs suffix : BitString)
    (right : List (Option Bool)) :
    preservingUnaryReadMachine.step
      (finalSeekBitsConfig (c :: cs) suffix right) =
    finalSeekBitsConfig cs suffix (some c :: right) := by
  cases cs <;>
    simp [finalSeekBitsConfig, preservingUnaryReadMachine,
      TM.step, Tape.write, Tape.move, List.append_assoc]

theorem finalSeekBits_run
    (remaining suffix : BitString)
    (right : List (Option Bool)) :
    preservingUnaryReadMachine.run remaining.length
      (finalSeekBitsConfig remaining suffix right) =
    finalSeekBitsConfig [] suffix (remaining.reverse.map some ++ right) := by
  induction remaining generalizing right with
  | nil => rfl
  | cons c cs ih =>
      rw [List.length_cons]
      simp only [TM.run, finalSeekBitsConfig_state,
        finalSeekBits_not_halting, Bool.false_eq_true, if_false]
      rw [finalSeekBits_step_cons]
      have hih := ih (right := some c :: right)
      rw [hih]
      simp [List.reverse_cons, List.map_append, List.append_assoc]

def finalReadConfig
    (b : Bool) (suffix : BitString)
    (right : List (Option Bool)) :
    Configuration PreservingReadState (Option Bool) :=
  { state := .finalRead
    tape := { left := suffix.map some, head := some b, right := none :: right } }

theorem finalSeekBits_marker_step
    (b : Bool) (suffix : BitString)
    (right : List (Option Bool)) :
    preservingUnaryReadMachine.step
      (finalSeekBitsConfig [] (b :: suffix) right) =
    finalReadConfig b suffix right := by
  simp [finalSeekBitsConfig, finalReadConfig, preservingUnaryReadMachine,
    TM.step, Tape.write, Tape.move]

theorem finalRead_selected_step
    (pref : BitString) (b : Bool) (suffix : BitString) :
    preservingUnaryReadMachine.run 1
      (finalReadConfig b suffix
        (pref.reverse.map some ++
          List.replicate pref.length none ++ [some false])) =
      selectedConfig pref b suffix := by
  cases b <;>
    simp [finalReadConfig, selectedConfig, preservingUnaryReadMachine,
      TM.run, TM.step, Tape.write, Tape.move]

theorem preservingRead_final_select
    (a b : Bool) (rest suffix : BitString) :
    preservingUnaryReadMachine.run (2 * (a :: rest).length + 3)
      (indexSomeConfig (a :: rest) (b :: suffix) 0) =
      selectedConfig (a :: rest) b suffix := by
  let pref : BitString := a :: rest
  let right0 : List (Option Bool) := [some false]
  let right1 : List (Option Bool) :=
    List.replicate pref.length none ++ right0
  let right2 : List (Option Bool) :=
    pref.reverse.map some ++ right1

  have hp : pref.length = rest.length + 1 := by simp [pref]

  have h0 :
      preservingUnaryReadMachine.run 1
        (indexSomeConfig pref (b :: suffix) 0) =
      finalSeekBlanksConfig rest.length pref (b :: suffix) right0 := by
    rw [TM.run]
    simp [indexSomeConfig_state, preservingUnaryReadMachine]
    simpa [pref, right0] using final_indexSome_zero_step a b rest suffix

  have h1 :
      preservingUnaryReadMachine.run (rest.length + 1)
        (finalSeekBlanksConfig rest.length pref (b :: suffix) right0) =
      { state := .finalSeekBlanks
        tape :=
          { left := rest.map some ++ none :: (b :: suffix).map some
            head := some a
            right := right1 } } := by
    have h :=
      finalSeekBlanks_run_to_first_bit rest.length a rest (b :: suffix) right0
    simpa [right1, pref, hp, right0, List.append_assoc] using h

  have h2 :
      preservingUnaryReadMachine.run 1
        { state := .finalSeekBlanks
          tape :=
            { left := rest.map some ++ none :: (b :: suffix).map some
              head := some a
              right := right1 } } =
      finalSeekBitsConfig rest (b :: suffix) (some a :: right1) := by
    rw [TM.run]
    simp only [finalSeekBlanks_not_halting, Bool.false_eq_true, if_false]
    exact finalSeekBlanks_first_bit_step a rest (b :: suffix) right1

  have h3 :
      preservingUnaryReadMachine.run rest.length
        (finalSeekBitsConfig rest (b :: suffix) (some a :: right1)) =
      finalSeekBitsConfig [] (b :: suffix) right2 := by
    have h := finalSeekBits_run rest (b :: suffix) (some a :: right1)
    simpa [right2, pref, List.reverse_cons, List.map_append,
      List.append_assoc] using h

  have h4 :
      preservingUnaryReadMachine.run 1
        (finalSeekBitsConfig [] (b :: suffix) right2) =
      finalReadConfig b suffix right2 := by
    rw [TM.run]
    simp only [finalSeekBitsConfig_state, finalSeekBits_not_halting,
      Bool.false_eq_true, if_false]
    exact finalSeekBits_marker_step b suffix right2

  have h5 :
      preservingUnaryReadMachine.run 1
        (finalReadConfig b suffix right2) =
      selectedConfig pref b suffix := by
    simpa [right2, right1, right0] using finalRead_selected_step pref b suffix

  have hall :
      preservingUnaryReadMachine.run
        (((((1 + (rest.length + 1)) + 1) + rest.length) + 1) + 1)
        (indexSomeConfig pref (b :: suffix) 0) =
      selectedConfig pref b suffix := by
    calc
      preservingUnaryReadMachine.run
          (((((1 + (rest.length + 1)) + 1) + rest.length) + 1) + 1)
          (indexSomeConfig pref (b :: suffix) 0)
          =
        preservingUnaryReadMachine.run
          ((((rest.length + 1) + 1) + rest.length) + 1 + 1)
          (preservingUnaryReadMachine.run 1
            (indexSomeConfig pref (b :: suffix) 0)) := by
              rw [show (((((1 + (rest.length + 1)) + 1) + rest.length) + 1) + 1) =
                1 + ((((rest.length + 1) + 1) + rest.length) + 1 + 1) by omega]
              rw [run_add]
      _ =
        preservingUnaryReadMachine.run
          ((((rest.length + 1) + 1) + rest.length) + 1 + 1)
          (finalSeekBlanksConfig rest.length pref (b :: suffix) right0) := by
            rw [h0]
      _ =
        preservingUnaryReadMachine.run
          (((1 + rest.length) + 1) + 1)
          { state := .finalSeekBlanks
            tape :=
              { left := rest.map some ++ none :: (b :: suffix).map some
                head := some a
                right := right1 } } := by
            rw [show ((((rest.length + 1) + 1) + rest.length) + 1 + 1) =
              (rest.length + 1) + (((1 + rest.length) + 1) + 1) by omega]
            rw [run_add, h1]
      _ =
        preservingUnaryReadMachine.run
          ((rest.length + 1) + 1)
          (finalSeekBitsConfig rest (b :: suffix) (some a :: right1)) := by
            rw [show (((1 + rest.length) + 1) + 1) =
              1 + ((rest.length + 1) + 1) by omega]
            rw [run_add, h2]
      _ =
        preservingUnaryReadMachine.run 2
          (finalSeekBitsConfig [] (b :: suffix) right2) := by
            rw [show ((rest.length + 1) + 1) = rest.length + 2 by omega]
            rw [run_add, h3]
      _ =
        preservingUnaryReadMachine.run 1
          (finalReadConfig b suffix right2) := by
            rw [show 2 = 1 + 1 by omega]
            rw [run_add, h4]
      _ = selectedConfig pref b suffix := h5

  have hfuel :
      (((((1 + (rest.length + 1)) + 1) + rest.length) + 1) + 1) =
        2 * pref.length + 3 := by
    rw [hp]
    omega
  rw [← hfuel]
  simpa [pref] using hall

#print axioms MCore.Real.P01PreservingUnaryFinalRead.preservingRead_final_select

end P01PreservingUnaryFinalRead
end Real
end MCore
