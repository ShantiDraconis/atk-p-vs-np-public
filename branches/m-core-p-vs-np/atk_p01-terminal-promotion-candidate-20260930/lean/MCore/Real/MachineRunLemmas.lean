import MCore.Real.Model

namespace MCore
namespace Real
namespace MachineRunLemmas

theorem run_halted
    {State Symbol : Type}
    (machine : TM State Symbol)
    (config : Configuration State Symbol)
    (hhalt : machine.halting config.state = true)
    (fuel : Nat) :
    machine.run fuel config = config := by
  induction fuel with
  | zero =>
      rfl
  | succ fuel ih =>
      simp [TM.run, hhalt]

theorem run_add
    {State Symbol : Type}
    (machine : TM State Symbol)
    (m n : Nat)
    (config : Configuration State Symbol) :
    machine.run (m + n) config =
      machine.run n (machine.run m config) := by
  induction m generalizing config with
  | zero =>
      simp [TM.run]
  | succ m ih =>
      rw [Nat.succ_add]
      rw [TM.run]
      by_cases h : machine.halting config.state = true
      · simp only [h, if_pos]
        have hm :
            machine.run (m + 1) config = config :=
          run_halted machine config h (m + 1)
        rw [hm]
        exact (run_halted machine config h n).symm
      · have hf : machine.halting config.state = false := by
          cases hh : machine.halting config.state <;> simp_all
        simp only [hf, Bool.false_eq_true, if_false]
        rw [ih (machine.step config)]
        have hrunSucc :
            machine.run (m + 1) config =
              machine.run m (machine.step config) := by
          rw [TM.run]
          simp [hf]
        rw [hrunSucc]

theorem haltsWithin_mono
    {State Symbol : Type}
    (machine : TM State Symbol)
    (config : Configuration State Symbol)
    {m n : Nat}
    (hmn : m ≤ n)
    (hhalt : machine.HaltsWithin m config) :
    machine.HaltsWithin n config := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hmn
  unfold TM.HaltsWithin at hhalt ⊢
  rw [run_add]
  rw [run_halted machine (machine.run m config) hhalt]
  exact hhalt

theorem run_to_larger_fuel_of_halt
    {State Symbol : Type}
    (machine : TM State Symbol)
    (config halted : Configuration State Symbol)
    {m n : Nat}
    (hmn : m ≤ n)
    (hrun : machine.run m config = halted)
    (hhalt : machine.halting halted.state = true) :
    machine.run n config = halted := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hmn
  rw [run_add, hrun]
  exact run_halted machine halted hhalt k

#print axioms MCore.Real.MachineRunLemmas.run_add
#print axioms MCore.Real.MachineRunLemmas.run_halted
#print axioms MCore.Real.MachineRunLemmas.haltsWithin_mono
#print axioms MCore.Real.MachineRunLemmas.run_to_larger_fuel_of_halt

end MachineRunLemmas
end Real
end MCore
