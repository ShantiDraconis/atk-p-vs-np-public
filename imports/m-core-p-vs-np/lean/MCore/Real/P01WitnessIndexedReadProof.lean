import MCore.Real.P01WitnessIndexedReadMachine
import MCore.Real.MachineRunLemmas

namespace MCore
namespace Real
namespace P01WitnessIndexedReadProof

open CanonicalFinalProof
open P01WitnessIndexedReadMachine

/-- State-3 configuration while crossing blank padding toward the selected
witness cell. `pad` counts additional blanks to the left of the current blank. -/
def witnessSeekConfig
    (pad : Nat) (b : Bool) (tail : BitString)
    (right : List (Option Bool)) :
    Configuration (Fin 6) (Option Bool) :=
  { state := 3
    tape :=
      { left := List.replicate pad none ++ some b :: tail.map some
        head := none
        right := right } }

@[simp] theorem witnessSeekConfig_state
    (pad : Nat) (b : Bool) (tail : BitString)
    (right : List (Option Bool)) :
    (witnessSeekConfig pad b tail right).state = (3 : Fin 6) := rfl

@[simp] theorem witnessIndexedReadMachine_not_halt3 :
    witnessIndexedReadMachine.halting (3 : Fin 6) = false := by decide

/-- One blank-crossing step decreases the physical padding by one. -/
theorem witnessSeek_step_succ
    (pad : Nat) (b : Bool) (tail : BitString)
    (right : List (Option Bool)) :
    witnessIndexedReadMachine.step
        (witnessSeekConfig (pad + 1) b tail right) =
      witnessSeekConfig pad b tail (none :: right) := by
  simp [witnessSeekConfig, witnessIndexedReadMachine, TM.step,
    Tape.write, Tape.move, List.replicate_succ, List.append_assoc]

/-- With no additional padding, one step reaches the selected witness cell. -/
theorem witnessSeek_step_zero
    (b : Bool) (tail : BitString)
    (right : List (Option Bool)) :
    witnessIndexedReadMachine.step
        (witnessSeekConfig 0 b tail right) =
      { state := (3 : Fin 6),
        tape :=
          { left := tail.map some
            head := some b
            right := none :: right } } := by
  simp [witnessSeekConfig, witnessIndexedReadMachine, TM.step,
    Tape.write, Tape.move]

/-- The following state-3 step classifies the selected Boolean and halts. -/
theorem witnessSeek_classify
    (b : Bool) (tail : BitString)
    (right : List (Option Bool)) :
    (witnessIndexedReadMachine.step
      { state := (3 : Fin 6),
        tape :=
          { left := tail.map some
            head := some b
            right := right } }).state =
      (if b then (4 : Fin 6) else (5 : Fin 6)) := by
  cases b <;>
    simp [witnessIndexedReadMachine, TM.step, Tape.write, Tape.move]

/-- Exact physical macro: crossing arbitrary blank padding returns the selected
witness bit in the finite halting state 4=true / 5=false. -/
theorem witnessSeek_run_state
    (pad : Nat) (b : Bool) (tail : BitString)
    (right : List (Option Bool)) :
    (witnessIndexedReadMachine.run (pad + 2)
      (witnessSeekConfig pad b tail right)).state =
      (if b then (4 : Fin 6) else (5 : Fin 6)) := by
  induction pad generalizing right with
  | zero =>
      cases b <;>
        simp [TM.run, witnessSeekConfig, witnessIndexedReadMachine,
          TM.step, Tape.write, Tape.move]
  | succ pad ih =>
      let cfg := witnessSeekConfig (Nat.succ pad) b tail right
      have hs :
          witnessIndexedReadMachine.step cfg =
            witnessSeekConfig pad b tail (none :: right) := by
        simpa [cfg, Nat.succ_eq_add_one] using
          witnessSeek_step_succ pad b tail right
      have hrun1 :
          witnessIndexedReadMachine.run 1 cfg =
            witnessSeekConfig pad b tail (none :: right) := by
        simp [TM.run, cfg, witnessIndexedReadMachine_not_halt3, hs]
      have hadd :=
        MachineRunLemmas.run_add witnessIndexedReadMachine
          1 (pad + 2) cfg
      have htotal :
          witnessIndexedReadMachine.run (Nat.succ pad + 2) cfg =
            witnessIndexedReadMachine.run (pad + 2)
              (witnessSeekConfig pad b tail (none :: right)) := by
        calc
          witnessIndexedReadMachine.run (Nat.succ pad + 2) cfg =
              witnessIndexedReadMachine.run (1 + (pad + 2)) cfg := by
                congr 1
                omega
          _ = witnessIndexedReadMachine.run (pad + 2)
                (witnessIndexedReadMachine.run 1 cfg) := hadd
          _ = witnessIndexedReadMachine.run (pad + 2)
                (witnessSeekConfig pad b tail (none :: right)) := by rw [hrun1]
      change
        (witnessIndexedReadMachine.run (Nat.succ pad + 2) cfg).state =
          (if b then (4 : Fin 6) else (5 : Fin 6))
      rw [htotal]
      exact ih (none :: right)

theorem witnessSeek_run_halts
    (pad : Nat) (b : Bool) (tail : BitString)
    (right : List (Option Bool)) :
    witnessIndexedReadMachine.HaltsWithin (pad + 2)
      (witnessSeekConfig pad b tail right) := by
  unfold TM.HaltsWithin
  rw [witnessSeek_run_state]
  cases b <;> simp [witnessIndexedReadMachine]

#print axioms MCore.Real.P01WitnessIndexedReadProof.witnessSeek_run_state
#print axioms MCore.Real.P01WitnessIndexedReadProof.witnessSeek_run_halts

end P01WitnessIndexedReadProof
end Real
end MCore
