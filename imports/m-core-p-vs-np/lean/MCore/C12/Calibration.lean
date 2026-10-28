import MCore.C11.BranchingCost

/-!
# C11/C12 Potential calibration against formula size

This module replaces the historical placeholder

    def S_OfficialComplexityCalibration : Prop :=
      ∀ ρ t, MCore.C11.PaysOff 1 1 ρ t → True

(audit/C12/C12_Calibration.lean on `audit/multistate-proof-refutation-v1`),
whose conclusion `True` carried no content.

What is proved here is a genuine, unconditional calibration:

    Potential α β t ≤ (α + 5 * β) * size t ^ 2

so every lower bound on `Potential` is a lower bound on the de Morgan
*formula* size of the same tree.

Scope, stated explicitly:
* `FormulaTree` is the tree type `CircuitK1.Circuit`; there is no gate sharing.
  The official measure reached here is formula size, not general circuit size.
* A super-polynomial formula-size lower bound for SAT would give
  NP ⊄ (non-uniform) NC¹. It does not by itself give SAT ∉ P, because P ⊆ NC¹
  is not known to fail.
* `Potential` is syntactic (`audit/C12/SRepresentationCounterexample.lean`), so a
  lower bound must be proved for every formula computing the target function.
-/

namespace MCore
namespace C12
namespace Calibration

open CircuitK1 CircuitC3 C9 C11

theorem eraseDups_loop_length_le {α : Type} [BEq α] (as bs : List α) :
    (List.eraseDups.loop as bs).length ≤ as.length + bs.length := by
  induction as generalizing bs with
  | nil => simp [List.eraseDups.loop]
  | cons a as ih =>
    unfold List.eraseDups.loop
    split
    · have := ih bs
      simp
      omega
    · have := ih (a :: bs)
      simp at this ⊢
      omega

theorem eraseDups_length_le {α : Type} [BEq α] (as : List α) :
    as.eraseDups.length ≤ as.length := by
  have := eraseDups_loop_length_le as []
  simpa [List.eraseDups] using this

theorem one_le_size (t : FormulaTree) : 1 ≤ size t := by
  cases t <;> simp [size]

theorem freeVarList_length_le_size (t : FormulaTree) :
    (freeVarList t).length ≤ size t := by
  induction t with
  | input i => simp [freeVarList, size]
  | const b => simp [freeVarList, size]
  | not c ih => simp [freeVarList, size]; omega
  | and a b iha ihb => simp [freeVarList, size]; omega
  | or a b iha ihb => simp [freeVarList, size]; omega

theorem vars_le_size (t : FormulaTree) : vars t ≤ size t :=
  Nat.le_trans (eraseDups_length_le _) (freeVarList_length_le_size t)

theorem depth_le_size (t : FormulaTree) : depth t ≤ size t := by
  induction t with
  | input i => simp [depth, size]
  | const b => simp [depth, size]
  | not c ih => simp [depth, size]; omega
  | and a b iha ihb => simp only [depth, size]; omega
  | or a b iha ihb => simp only [depth, size]; omega

theorem mu_le_two_mul_size (t : FormulaTree) : mu t ≤ 2 * size t := by
  have h := depth_le_size t
  simp only [mu, potential, μ]
  omega

theorem stateRank_le (t : FormulaTree) :
    stateRank t ≤ 5 * size t ^ 2 := by
  have hv := vars_le_size t
  have hm := mu_le_two_mul_size t
  have h1 := one_le_size t
  simp only [stateRank, CircuitC8.recurrenceRank]
  have hprod : vars t * (mu t + 1) ≤ size t * (2 * size t + 1) :=
    Nat.mul_le_mul hv (by omega)
  have hsq : size t ≤ size t ^ 2 := by
    rw [Nat.pow_two]
    exact Nat.le_mul_of_pos_left _ h1
  have hexp : size t * (2 * size t + 1) = 2 * size t ^ 2 + size t := by
    rw [Nat.pow_two, Nat.mul_add, Nat.mul_one, Nat.mul_left_comm]
  omega

/-- Unconditional calibration of the C11 potential against formula size. -/
theorem potential_le_formula_size_sq (α β : Nat) (t : FormulaTree) :
    Potential α β t ≤ (α + 5 * β) * size t ^ 2 := by
  have hv := vars_le_size t
  have hr := stateRank_le t
  have h1 := one_le_size t
  have hsq : size t ≤ size t ^ 2 := by
    rw [Nat.pow_two]
    exact Nat.le_mul_of_pos_left _ h1
  simp only [Potential]
  have ha : α * vars t ≤ α * size t ^ 2 :=
    Nat.mul_le_mul_left α (Nat.le_trans hv hsq)
  have hb : β * stateRank t ≤ β * (5 * size t ^ 2) :=
    Nat.mul_le_mul_left β hr
  calc α * vars t + β * stateRank t
      ≤ α * size t ^ 2 + β * (5 * size t ^ 2) := Nat.add_le_add ha hb
    _ = (α + 5 * β) * size t ^ 2 := by
      rw [Nat.add_mul, Nat.mul_assoc, Nat.mul_left_comm β 5]

/-- The calibration obligation, now stated with real content. -/
def S_OfficialComplexityCalibration : Prop :=
  ∀ (α β : Nat) (t : FormulaTree),
    Potential α β t ≤ (α + 5 * β) * size t ^ 2

theorem s_officialComplexityCalibration : S_OfficialComplexityCalibration :=
  potential_le_formula_size_sq

/-- Transfer: a lower bound on the potential of a tree is a lower bound on
its formula size (up to the explicit square and constant). -/
theorem formula_size_lower_bound_of_potential
    {α β L : Nat} {t : FormulaTree}
    (h : L ≤ Potential α β t) :
    L ≤ (α + 5 * β) * size t ^ 2 :=
  Nat.le_trans h (potential_le_formula_size_sq α β t)

#print axioms MCore.C12.Calibration.potential_le_formula_size_sq
#print axioms MCore.C12.Calibration.s_officialComplexityCalibration
#print axioms MCore.C12.Calibration.formula_size_lower_bound_of_potential

end Calibration
end C12
end MCore
