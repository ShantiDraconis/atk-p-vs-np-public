import MCore.Real.P012FailClosed

namespace MCore
namespace Real
namespace DivZeroP012

/-- Fail-closed symbolic division state.
No arithmetic division by zero is used to obtain closure. -/
inductive DivState
| indet      -- 0/0
| inf        -- n/0 with n ≠ 0
| open0      -- defined ratio, but not n/n
| closed1    -- n/n with n ≠ 0
deriving DecidableEq, Repr

/-- Classify a symbolic fraction without relying on Lean's totalized Nat.div. -/
def classify (num den : Nat) : DivState :=
  if hden : den = 0 then
    if hnum : num = 0 then .indet else .inf
  else if hEq : num = den then
    .closed1
  else
    .open0

/-- Only closed1 is admitted as a rigid symbolic state. -/
def IsRigidCore (s : DivState) : Prop :=
  s = .closed1

@[simp] theorem classify_zero_zero :
    classify 0 0 = .indet := by
  simp [classify]

@[simp] theorem classify_nonzero_zero
    (n : Nat) (hn : n ≠ 0) :
    classify n 0 = .inf := by
  simp [classify, hn]

@[simp] theorem classify_same_nonzero
    (n : Nat) (hn : n ≠ 0) :
    classify n n = .closed1 := by
  simp [classify, hn]

/-- Core fail-closed characterization:
a symbolic fraction reaches closed1 iff it is n/n with a nonzero denominator. -/
theorem classify_eq_closed1_iff
    (num den : Nat) :
    classify num den = .closed1 ↔ den ≠ 0 ∧ num = den := by
  by_cases hden : den = 0
  · subst den
    simp [classify]
  · by_cases hEq : num = den
    · simp [classify, hden, hEq]
    · simp [classify, hden, hEq]

/-- This is the requested kernel gate: only n/n, n ≠ 0, enters the rigid state. -/
theorem only_n_over_n_enters_core
    (num den : Nat) :
    IsRigidCore (classify num den) ↔ den ≠ 0 ∧ num = den := by
  simpa [IsRigidCore] using classify_eq_closed1_iff num den

/-- 0/0 is explicitly isolated from the rigid core. -/
theorem zero_zero_not_rigid :
    ¬ IsRigidCore (classify 0 0) := by
  simp [IsRigidCore]

/-- n/0 is never rigid, for any nonzero numerator. -/
theorem nonzero_over_zero_not_rigid
    (n : Nat) (hn : n ≠ 0) :
    ¬ IsRigidCore (classify n 0) := by
  simp [IsRigidCore, classify, hn]

/-- Every nonzero n/n is rigid. -/
theorem n_over_n_is_rigid
    (n : Nat) (hn : n ≠ 0) :
    IsRigidCore (classify n n) := by
  simp [IsRigidCore, classify, hn]

/-- AND-composition for two fail-closed symbolic gates.
Only closed1 + closed1 remains closed1. -/
def FinalTwoGapState (a b : DivState) : DivState :=
  if a = .closed1 ∧ b = .closed1 then .closed1 else .open0

@[simp] theorem finalTwoGap_closed_closed :
    FinalTwoGapState .closed1 .closed1 = .closed1 := by
  simp [FinalTwoGapState]

theorem finalTwoGap_closed_iff
    (a b : DivState) :
    FinalTwoGapState a b = .closed1 ↔
      a = .closed1 ∧ b = .closed1 := by
  by_cases h : a = .closed1 ∧ b = .closed1
  · simp [FinalTwoGapState, h]
  · simp [FinalTwoGapState, h]

/-- A non-rigid left input can never be promoted by the AND gate. -/
theorem finalTwoGap_left_not_closed
    (a b : DivState)
    (ha : a ≠ .closed1) :
    FinalTwoGapState a b ≠ .closed1 := by
  intro h
  have hc := (finalTwoGap_closed_iff a b).mp h
  exact ha hc.1

/-- A non-rigid right input can never be promoted by the AND gate. -/
theorem finalTwoGap_right_not_closed
    (a b : DivState)
    (hb : b ≠ .closed1) :
    FinalTwoGapState a b ≠ .closed1 := by
  intro h
  have hc := (finalTwoGap_closed_iff a b).mp h
  exact hb hc.2

/-- Numeric closure does not manufacture P-vs-NP proofs.
Actual terminal inhabitants are still required explicitly. -/
def rigid_state_with_real_producers
    (hP01 : P01FinalCertificate.P01ConstructionGap)
    (hG21 : P02G21G22Attack.G21Pointwise) :
    P012FailClosed.RigidCore :=
  ⟨hP01, hG21⟩

#print axioms MCore.Real.DivZeroP012.classify_eq_closed1_iff
#print axioms MCore.Real.DivZeroP012.only_n_over_n_enters_core
#print axioms MCore.Real.DivZeroP012.zero_zero_not_rigid
#print axioms MCore.Real.DivZeroP012.nonzero_over_zero_not_rigid
#print axioms MCore.Real.DivZeroP012.n_over_n_is_rigid
#print axioms MCore.Real.DivZeroP012.finalTwoGap_closed_iff
#print axioms MCore.Real.DivZeroP012.rigid_state_with_real_producers

end DivZeroP012
end Real
end MCore
