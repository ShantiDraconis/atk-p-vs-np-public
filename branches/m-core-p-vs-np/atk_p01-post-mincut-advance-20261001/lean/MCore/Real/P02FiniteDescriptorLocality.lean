import MCore.Real.P02BoundedComputationTape
import MCore.Real.P02FiniteDescriptorStructuralLaws

namespace MCore
namespace Real
namespace P02FiniteDescriptorLocality

open CanonicalFinalProof
open P02BoundedComputationTape
open P02FiniteDescriptorReduction
open P02FiniteDescriptorStructuralLaws

/-- Two configurations are indistinguishable inside the radius-k tape window
reachable from the current head. This is a concrete machine-local relation. -/
def ConfigWindowEq
    {State : Type}
    (M : TM State (Option Bool))
    (k : Nat)
    (c₁ c₂ : Configuration State (Option Bool)) : Prop :=
  c₁.state = c₂.state ∧
  c₁.tape.head = c₂.tape.head ∧
  (∀ i : Nat, i < k →
    c₁.tape.left.getD i M.blank =
      c₂.tape.left.getD i M.blank) ∧
  (∀ i : Nat, i < k →
    c₁.tape.right.getD i M.blank =
      c₂.tape.right.getD i M.blank)

theorem step_windowEq
    {State : Type}
    (M : TM State (Option Bool))
    (k : Nat)
    {c₁ c₂ : Configuration State (Option Bool)}
    (h : ConfigWindowEq M (k + 1) c₁ c₂) :
    ConfigWindowEq M k (M.step c₁) (M.step c₂) := by
  rcases h with ⟨hState, hHead, hLeft, hRight⟩
  rcases hTrans : M.transition c₁.state c₁.tape.head with
    ⟨qNext, write, dir⟩
  have hTrans₂ :
      M.transition c₂.state c₂.tape.head =
        (qNext, write, dir) := by
    rw [← hState, ← hHead]
    exact hTrans
  unfold TM.step
  simp only [hTrans, hTrans₂]
  cases dir with
  | stay =>
      refine ⟨rfl, ?_, ?_, ?_⟩
      · rfl
      · intro i hi
        simpa [Tape.move, Tape.write] using
          hLeft i (Nat.lt_succ_of_lt hi)
      · intro i hi
        simpa [Tape.move, Tape.write] using
          hRight i (Nat.lt_succ_of_lt hi)
  | left =>
      refine ⟨rfl, ?_, ?_, ?_⟩
      · rw [move_left_head_getD, move_left_head_getD]
        simpa [Tape.write] using
          hLeft 0 (Nat.zero_lt_succ k)
      · intro i hi
        rw [move_left_left_getD, move_left_left_getD]
        simpa [Tape.write] using
          hLeft (i + 1) (by omega)
      · intro i hi
        cases i with
        | zero =>
            rw [move_left_right_zero, move_left_right_zero]
            simp [Tape.write]
        | succ i =>
            rw [move_left_right_succ, move_left_right_succ]
            simpa [Tape.write] using hRight i (by omega)
  | right =>
      refine ⟨rfl, ?_, ?_, ?_⟩
      · rw [move_right_head_getD, move_right_head_getD]
        simpa [Tape.write] using
          hRight 0 (Nat.zero_lt_succ k)
      · intro i hi
        cases i with
        | zero =>
            rw [move_right_left_zero, move_right_left_zero]
            simp [Tape.write]
        | succ i =>
            rw [move_right_left_succ, move_right_left_succ]
            simpa [Tape.write] using hLeft i (by omega)
      · intro i hi
        rw [move_right_right_getD, move_right_right_getD]
        simpa [Tape.write] using
          hRight (i + 1) (by omega)

/-- Locality of the deterministic finite-control state after the supplied fuel. -/
theorem run_state_eq_of_windowEq
    {State : Type}
    (M : TM State (Option Bool))
    (fuel : Nat)
    {c₁ c₂ : Configuration State (Option Bool)}
    (h : ConfigWindowEq M fuel c₁ c₂) :
    (M.run fuel c₁).state = (M.run fuel c₂).state := by
  induction fuel generalizing c₁ c₂ with
  | zero =>
      simpa [TM.run] using h.1
  | succ fuel ih =>
      have hState : c₁.state = c₂.state := h.1
      by_cases hHalt : M.halting c₁.state = true
      · have hHalt₂ : M.halting c₂.state = true := by
          rw [← hState]
          exact hHalt
        simp [TM.run, hHalt, hHalt₂, hState]
      · have hFalse : M.halting c₁.state = false := by
          cases hh : M.halting c₁.state <;> simp_all
        have hFalse₂ : M.halting c₂.state = false := by
          rw [← hState]
          exact hFalse
        simp only [TM.run, hFalse, hFalse₂, Bool.false_eq_true, if_false]
        exact ih (step_windowEq M fuel h)

theorem initial_left_window_eq
    {stateCount : Nat}
    (M : TM (Fin (stateCount + 1)) (Option Bool))
    (x y : BitString)
    (k : Nat) :
    ∀ i : Nat, i < k →
      (initialTMConfig M x).tape.left.getD i M.blank =
        (initialTMConfig M y).tape.left.getD i M.blank := by
  intro i hi
  cases x <;> cases y <;>
    simp [initialTMConfig, inputTape]

theorem canonical_run_state_eq_of_right_window
    {stateCount : Nat}
    (M : TM (Fin (stateCount + 1)) (Option Bool))
    (fuel : Nat)
    (x y : BitString)
    (hHead :
      (initialTMConfig M x).tape.head =
        (initialTMConfig M y).tape.head)
    (hRight :
      ∀ i : Nat, i < fuel →
        (initialTMConfig M x).tape.right.getD i M.blank =
          (initialTMConfig M y).tape.right.getD i M.blank) :
    (M.run fuel (initialTMConfig M x)).state =
      (M.run fuel (initialTMConfig M y)).state := by
  apply run_state_eq_of_windowEq M fuel
  exact
    ⟨rfl, hHead,
      initial_left_window_eq M x y fuel,
      hRight⟩

#print axioms MCore.Real.P02FiniteDescriptorLocality.step_windowEq
#print axioms MCore.Real.P02FiniteDescriptorLocality.run_state_eq_of_windowEq
#print axioms MCore.Real.P02FiniteDescriptorLocality.canonical_run_state_eq_of_right_window

end P02FiniteDescriptorLocality
end Real
end MCore
