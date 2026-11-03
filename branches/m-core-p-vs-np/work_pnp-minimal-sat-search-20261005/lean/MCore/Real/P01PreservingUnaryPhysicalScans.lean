import MCore.Real.P01PreservingUnaryWitnessMachine
import MCore.Real.MachineRunLemmas

namespace MCore
namespace Real
namespace P01PreservingUnaryPhysicalScans

open P01PreservingUnaryWitnessMachine
open MachineRunLemmas

/-- Canonical seekBlanks configuration. `pad` is the number of additional
blank cells to the left of the current blank before the first Boolean cell. -/
def seekBlanksConfig
    (pad : Nat) (leftBits : List (Option Bool)) (bit : Bool)
    (right : List (Option Bool)) :
    Configuration PreservingReadState (Option Bool) :=
  { state := .seekBlanks
    tape :=
      { left := List.replicate pad none ++ some bit :: leftBits
        head := none
        right := right } }

@[simp] theorem seekBlanksConfig_state
    (pad : Nat) (leftBits : List (Option Bool)) (bit : Bool)
    (right : List (Option Bool)) :
    (seekBlanksConfig pad leftBits bit right).state = .seekBlanks := rfl

@[simp] theorem preservingUnaryReadMachine_not_halt_seekBlanks :
    preservingUnaryReadMachine.halting .seekBlanks = false := rfl

/-- One physical blank-crossing step decreases pad by one. -/
theorem seekBlanks_step_succ
    (pad : Nat) (leftBits : List (Option Bool)) (bit : Bool)
    (right : List (Option Bool)) :
    preservingUnaryReadMachine.step
        (seekBlanksConfig (pad + 1) leftBits bit right) =
      seekBlanksConfig pad leftBits bit (none :: right) := by
  simp [seekBlanksConfig, preservingUnaryReadMachine, TM.step,
    Tape.write, Tape.move, List.replicate_succ, List.append_assoc]

/-- With no additional padding, one step exposes the first Boolean cell while
remaining in seekBlanks; the following machine step enters seekBits. -/
theorem seekBlanks_step_zero
    (leftBits : List (Option Bool)) (bit : Bool)
    (right : List (Option Bool)) :
    preservingUnaryReadMachine.step
        (seekBlanksConfig 0 leftBits bit right) =
      { state := .seekBlanks
        tape :=
          { left := leftBits
            head := some bit
            right := none :: right } } := by
  simp [seekBlanksConfig, preservingUnaryReadMachine, TM.step,
    Tape.write, Tape.move]

/-- Physical scan across arbitrary erased unary padding. -/
theorem seekBlanks_run_replicate
    (pad : Nat) (leftBits : List (Option Bool)) (bit : Bool)
    (right : List (Option Bool)) :
    preservingUnaryReadMachine.run (pad + 1)
      (seekBlanksConfig pad leftBits bit right) =
      { state := .seekBlanks
        tape :=
          { left := leftBits
            head := some bit
            right := List.replicate (pad + 1) none ++ right } } := by
  induction pad generalizing right with
  | zero =>
      simpa [TM.run, preservingUnaryReadMachine_not_halt_seekBlanks] using
        seekBlanks_step_zero leftBits bit right
  | succ pad ih =>
      let cfg := seekBlanksConfig (Nat.succ pad) leftBits bit right
      have hs :
          preservingUnaryReadMachine.step cfg =
            seekBlanksConfig pad leftBits bit (none :: right) := by
        simpa [cfg, Nat.succ_eq_add_one] using
          seekBlanks_step_succ pad leftBits bit right
      have hrun1 :
          preservingUnaryReadMachine.run 1 cfg =
            seekBlanksConfig pad leftBits bit (none :: right) := by
        simp [TM.run, cfg, preservingUnaryReadMachine_not_halt_seekBlanks, hs]
      have hadd :=
        MachineRunLemmas.run_add preservingUnaryReadMachine
          1 (pad + 1) cfg
      have htotal :
          preservingUnaryReadMachine.run (Nat.succ pad + 1) cfg =
            preservingUnaryReadMachine.run (pad + 1)
              (seekBlanksConfig pad leftBits bit (none :: right)) := by
        calc
          preservingUnaryReadMachine.run (Nat.succ pad + 1) cfg =
              preservingUnaryReadMachine.run (1 + (pad + 1)) cfg := by
                congr 1
                omega
          _ = preservingUnaryReadMachine.run (pad + 1)
                (preservingUnaryReadMachine.run 1 cfg) := hadd
          _ = preservingUnaryReadMachine.run (pad + 1)
                (seekBlanksConfig pad leftBits bit (none :: right)) := by rw [hrun1]
      rw [htotal]
      rw [ih (none :: right)]
      have hrep :
          List.replicate pad none ++ none :: right =
            none :: (List.replicate pad none ++ right) := by
        induction pad with
        | zero => rfl
        | succ pad ihpad =>
            simp [List.replicate_succ, ihpad, List.append_assoc]
      rw [hrep]
      rfl

#print axioms MCore.Real.P01PreservingUnaryPhysicalScans.seekBlanks_step_succ
#print axioms MCore.Real.P01PreservingUnaryPhysicalScans.seekBlanks_step_zero
#print axioms MCore.Real.P01PreservingUnaryPhysicalScans.seekBlanks_run_replicate

end P01PreservingUnaryPhysicalScans
end Real
end MCore
