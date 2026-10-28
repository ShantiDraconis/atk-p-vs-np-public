import MCore.Real.CanonicalSATVarPayloadMachine

namespace MCore
namespace Real
namespace CanonicalSATTagConsumerMachine

open CanonicalFinalProof

/--
Thirteen-state finite-control consumer for the six canonical three-bit tags.
Consumed tag cells are erased. Final states:
6=input, 7=const false, 8=const true, 9=not, 10=and, 11=or, 12=reject.
-/
def tagConsumeMachine : TM (Fin 13) (Option Bool) :=
  { initial := 0
    blank := none
    transition := fun q symbol =>
      if q = 0 then
        match symbol with
        | some false => (1, none, .right)
        | some true  => (2, none, .right)
        | none       => (12, none, .stay)
      else if q = 1 then
        match symbol with
        | some false => (3, none, .right)
        | some true  => (4, none, .right)
        | none       => (12, none, .stay)
      else if q = 2 then
        match symbol with
        | some false => (5, none, .right)
        | some true  => (12, none, .right)
        | none       => (12, none, .stay)
      else if q = 3 then
        match symbol with
        | some false => (6, none, .right)
        | some true  => (7, none, .right)
        | none       => (12, none, .stay)
      else if q = 4 then
        match symbol with
        | some false => (8, none, .right)
        | some true  => (9, none, .right)
        | none       => (12, none, .stay)
      else if q = 5 then
        match symbol with
        | some false => (10, none, .right)
        | some true  => (11, none, .right)
        | none       => (12, none, .stay)
      else
        (q, symbol, .stay)
    halting := fun q => decide (6 ≤ q.val) }

def tagConsumeConfig
    (q : Fin 13)
    (left : List (Option Bool))
    (bits : BitString) :
    Configuration (Fin 13) (Option Bool) :=
  match bits with
  | [] =>
      { state := q
        tape := { left := left, head := none, right := [] } }
  | b :: bs =>
      { state := q
        tape := { left := left, head := some b, right := bs.map some } }

@[simp] theorem tagConsumeConfig_state
    (q : Fin 13)
    (left : List (Option Bool))
    (bits : BitString) :
    (tagConsumeConfig q left bits).state = q := by
  cases bits <;> rfl

@[simp] theorem tagConsume_not_halted_0 :
    tagConsumeMachine.halting (0 : Fin 13) = false := by decide
@[simp] theorem tagConsume_not_halted_1 :
    tagConsumeMachine.halting (1 : Fin 13) = false := by decide
@[simp] theorem tagConsume_not_halted_2 :
    tagConsumeMachine.halting (2 : Fin 13) = false := by decide
@[simp] theorem tagConsume_not_halted_3 :
    tagConsumeMachine.halting (3 : Fin 13) = false := by decide
@[simp] theorem tagConsume_not_halted_4 :
    tagConsumeMachine.halting (4 : Fin 13) = false := by decide
@[simp] theorem tagConsume_not_halted_5 :
    tagConsumeMachine.halting (5 : Fin 13) = false := by decide

theorem tagConsume_halted_final
    (q : Fin 13)
    (h : 6 ≤ q.val) :
    tagConsumeMachine.halting q = true := by
  simp [tagConsumeMachine, h]

theorem step_0_false (left : List (Option Bool)) (rest : BitString) :
    tagConsumeMachine.step (tagConsumeConfig 0 left (false :: rest)) =
      tagConsumeConfig 1 (none :: left) rest := by
  cases rest <;>
    simp [tagConsumeMachine, tagConsumeConfig, TM.step, Tape.write, Tape.move]

theorem step_0_true (left : List (Option Bool)) (rest : BitString) :
    tagConsumeMachine.step (tagConsumeConfig 0 left (true :: rest)) =
      tagConsumeConfig 2 (none :: left) rest := by
  cases rest <;>
    simp [tagConsumeMachine, tagConsumeConfig, TM.step, Tape.write, Tape.move]

theorem step_1_false (left : List (Option Bool)) (rest : BitString) :
    tagConsumeMachine.step (tagConsumeConfig 1 left (false :: rest)) =
      tagConsumeConfig 3 (none :: left) rest := by
  cases rest <;>
    simp [tagConsumeMachine, tagConsumeConfig, TM.step, Tape.write, Tape.move]

theorem step_1_true (left : List (Option Bool)) (rest : BitString) :
    tagConsumeMachine.step (tagConsumeConfig 1 left (true :: rest)) =
      tagConsumeConfig 4 (none :: left) rest := by
  cases rest <;>
    simp [tagConsumeMachine, tagConsumeConfig, TM.step, Tape.write, Tape.move]

theorem step_2_false (left : List (Option Bool)) (rest : BitString) :
    tagConsumeMachine.step (tagConsumeConfig 2 left (false :: rest)) =
      tagConsumeConfig 5 (none :: left) rest := by
  cases rest <;>
    simp [tagConsumeMachine, tagConsumeConfig, TM.step, Tape.write, Tape.move]

theorem step_2_true_reject (left : List (Option Bool)) (rest : BitString) :
    tagConsumeMachine.step (tagConsumeConfig 2 left (true :: rest)) =
      tagConsumeConfig 12 (none :: left) rest := by
  cases rest <;>
    simp [tagConsumeMachine, tagConsumeConfig, TM.step, Tape.write, Tape.move]

theorem step_3_false (left : List (Option Bool)) (rest : BitString) :
    tagConsumeMachine.step (tagConsumeConfig 3 left (false :: rest)) =
      tagConsumeConfig 6 (none :: left) rest := by
  cases rest <;>
    simp [tagConsumeMachine, tagConsumeConfig, TM.step, Tape.write, Tape.move]

theorem step_3_true (left : List (Option Bool)) (rest : BitString) :
    tagConsumeMachine.step (tagConsumeConfig 3 left (true :: rest)) =
      tagConsumeConfig 7 (none :: left) rest := by
  cases rest <;>
    simp [tagConsumeMachine, tagConsumeConfig, TM.step, Tape.write, Tape.move]

theorem step_4_false (left : List (Option Bool)) (rest : BitString) :
    tagConsumeMachine.step (tagConsumeConfig 4 left (false :: rest)) =
      tagConsumeConfig 8 (none :: left) rest := by
  cases rest <;>
    simp [tagConsumeMachine, tagConsumeConfig, TM.step, Tape.write, Tape.move]

theorem step_4_true (left : List (Option Bool)) (rest : BitString) :
    tagConsumeMachine.step (tagConsumeConfig 4 left (true :: rest)) =
      tagConsumeConfig 9 (none :: left) rest := by
  cases rest <;>
    simp [tagConsumeMachine, tagConsumeConfig, TM.step, Tape.write, Tape.move]

theorem step_5_false (left : List (Option Bool)) (rest : BitString) :
    tagConsumeMachine.step (tagConsumeConfig 5 left (false :: rest)) =
      tagConsumeConfig 10 (none :: left) rest := by
  cases rest <;>
    simp [tagConsumeMachine, tagConsumeConfig, TM.step, Tape.write, Tape.move]

theorem step_5_true (left : List (Option Bool)) (rest : BitString) :
    tagConsumeMachine.step (tagConsumeConfig 5 left (true :: rest)) =
      tagConsumeConfig 11 (none :: left) rest := by
  cases rest <;>
    simp [tagConsumeMachine, tagConsumeConfig, TM.step, Tape.write, Tape.move]

theorem run_input_tag (left : List (Option Bool)) (tail : BitString) :
    tagConsumeMachine.run 3
      (tagConsumeConfig 0 left (false :: false :: false :: tail)) =
    tagConsumeConfig 6 ([none, none, none] ++ left) tail := by
  rw [TM.run, tagConsumeConfig_state, tagConsume_not_halted_0, step_0_false]
  rw [TM.run, tagConsumeConfig_state, tagConsume_not_halted_1, step_1_false]
  rw [TM.run, tagConsumeConfig_state, tagConsume_not_halted_3, step_3_false]
  rfl

theorem run_const_false_tag (left : List (Option Bool)) (tail : BitString) :
    tagConsumeMachine.run 3
      (tagConsumeConfig 0 left (false :: false :: true :: tail)) =
    tagConsumeConfig 7 ([none, none, none] ++ left) tail := by
  rw [TM.run, tagConsumeConfig_state, tagConsume_not_halted_0, step_0_false]
  rw [TM.run, tagConsumeConfig_state, tagConsume_not_halted_1, step_1_false]
  rw [TM.run, tagConsumeConfig_state, tagConsume_not_halted_3, step_3_true]
  rfl

theorem run_const_true_tag (left : List (Option Bool)) (tail : BitString) :
    tagConsumeMachine.run 3
      (tagConsumeConfig 0 left (false :: true :: false :: tail)) =
    tagConsumeConfig 8 ([none, none, none] ++ left) tail := by
  rw [TM.run, tagConsumeConfig_state, tagConsume_not_halted_0, step_0_false]
  rw [TM.run, tagConsumeConfig_state, tagConsume_not_halted_1, step_1_true]
  rw [TM.run, tagConsumeConfig_state, tagConsume_not_halted_4, step_4_false]
  rfl

theorem run_not_tag (left : List (Option Bool)) (tail : BitString) :
    tagConsumeMachine.run 3
      (tagConsumeConfig 0 left (false :: true :: true :: tail)) =
    tagConsumeConfig 9 ([none, none, none] ++ left) tail := by
  rw [TM.run, tagConsumeConfig_state, tagConsume_not_halted_0, step_0_false]
  rw [TM.run, tagConsumeConfig_state, tagConsume_not_halted_1, step_1_true]
  rw [TM.run, tagConsumeConfig_state, tagConsume_not_halted_4, step_4_true]
  rfl

theorem run_and_tag (left : List (Option Bool)) (tail : BitString) :
    tagConsumeMachine.run 3
      (tagConsumeConfig 0 left (true :: false :: false :: tail)) =
    tagConsumeConfig 10 ([none, none, none] ++ left) tail := by
  rw [TM.run, tagConsumeConfig_state, tagConsume_not_halted_0, step_0_true]
  rw [TM.run, tagConsumeConfig_state, tagConsume_not_halted_2, step_2_false]
  rw [TM.run, tagConsumeConfig_state, tagConsume_not_halted_5, step_5_false]
  rfl

theorem run_or_tag (left : List (Option Bool)) (tail : BitString) :
    tagConsumeMachine.run 3
      (tagConsumeConfig 0 left (true :: false :: true :: tail)) =
    tagConsumeConfig 11 ([none, none, none] ++ left) tail := by
  rw [TM.run, tagConsumeConfig_state, tagConsume_not_halted_0, step_0_true]
  rw [TM.run, tagConsumeConfig_state, tagConsume_not_halted_2, step_2_false]
  rw [TM.run, tagConsumeConfig_state, tagConsume_not_halted_5, step_5_true]
  rfl

theorem run_invalid_11_tag
    (left : List (Option Bool))
    (third : Bool)
    (tail : BitString) :
    (tagConsumeMachine.run 2
      (tagConsumeConfig 0 left (true :: true :: third :: tail))).state =
      (12 : Fin 13) := by
  rw [TM.run, tagConsumeConfig_state, tagConsume_not_halted_0, step_0_true]
  rw [TM.run, tagConsumeConfig_state, tagConsume_not_halted_2,
    step_2_true_reject]
  rfl

#print axioms MCore.Real.CanonicalSATTagConsumerMachine.run_input_tag
#print axioms MCore.Real.CanonicalSATTagConsumerMachine.run_const_false_tag
#print axioms MCore.Real.CanonicalSATTagConsumerMachine.run_const_true_tag
#print axioms MCore.Real.CanonicalSATTagConsumerMachine.run_not_tag
#print axioms MCore.Real.CanonicalSATTagConsumerMachine.run_and_tag
#print axioms MCore.Real.CanonicalSATTagConsumerMachine.run_or_tag
#print axioms MCore.Real.CanonicalSATTagConsumerMachine.run_invalid_11_tag

end CanonicalSATTagConsumerMachine
end Real
end MCore
