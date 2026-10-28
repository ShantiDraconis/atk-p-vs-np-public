import MCore.C11.VarsMonotone

namespace MCore
namespace C12

open C9 C10 C11 CircuitK1 CircuitC2

/-- Fix exactly one syntactic input variable to `true`; every other input
remains free. This is a concrete restriction, not a choice axiom. -/
def fixVarTrue (i : Nat) : Restriction :=
  fun j => if j = i then some true else none

@[simp] theorem fixVarTrue_self (i : Nat) :
    fixVarTrue i i = some true := by
  simp [fixVarTrue]

@[simp] theorem fixVarTrue_ne {i j : Nat} (h : j ≠ i) :
    fixVarTrue i j = none := by
  simp [fixVarTrue, h]

/-- The variable selected by `fixVarTrue` is absent after raw restriction. -/
theorem fixedVar_not_mem_restrict (i : Nat) :
    ∀ t : FormulaTree,
      i ∉ freeVarList (restrict (fixVarTrue i) t)
  | .input j => by
      by_cases h : j = i
      · subst j
        simp [restrict, fixVarTrue, freeVarList]
      · simp [restrict, fixVarTrue, freeVarList, h, Ne.symm h]
  | .const b => by
      simp [restrict, freeVarList]
  | .not c => by
      simpa [restrict, freeVarList] using fixedVar_not_mem_restrict i c
  | .and a b => by
      simp [restrict, freeVarList, fixedVar_not_mem_restrict i a,
        fixedVar_not_mem_restrict i b]
  | .or a b => by
      simp [restrict, freeVarList, fixedVar_not_mem_restrict i a,
        fixedVar_not_mem_restrict i b]

/-- Simplification cannot reintroduce the variable removed by `fixVarTrue`. -/
theorem fixedVar_not_mem_D (i : Nat) (t : FormulaTree) :
    i ∉ freeVarList (D (fixVarTrue i) t) := by
  intro hiD
  have hir : i ∈ freeVarList (restrict (fixVarTrue i) t) := by
    apply mem_freeVarList_simplify (restrict (fixVarTrue i) t)
    simpa [D] using hiD
  exact fixedVar_not_mem_restrict i t hir

/-- If one list is included in another and misses an element present in the
larger list, its distinct-element cardinality is strictly smaller. -/
theorem eraseDups_length_lt_of_subset_of_missing
    {l₁ l₂ : List Nat} {i : Nat}
    (hsub : l₁ ⊆ l₂) (hi : i ∈ l₂) (hmiss : i ∉ l₁) :
    l₁.eraseDups.length < l₂.eraseDups.length := by
  have hiD : i ∈ l₂.eraseDups := (mem_eraseDups_nat).2 hi
  have hsubErase : l₁.eraseDups ⊆ (l₂.eraseDups).erase i := by
    intro x hx
    have hx₁ : x ∈ l₁ := (mem_eraseDups_nat).1 hx
    have hx₂ : x ∈ l₂ := hsub hx₁
    have hxi : x ≠ i := by
      intro hxi
      subst x
      exact hmiss hx₁
    exact (List.mem_erase_of_ne hxi).2 ((mem_eraseDups_nat).2 hx₂)
  have hrightNodup : ((l₂.eraseDups).erase i).Nodup := by
    exact List.Pairwise.erase i (eraseDups_nodup_nat l₂)
  have hle :
      l₁.eraseDups.length ≤ ((l₂.eraseDups).erase i).length :=
    nodup_length_le_of_subset_nat
      (eraseDups_nodup_nat l₁) hrightNodup hsubErase
  have hlen :
      ((l₂.eraseDups).erase i).length = l₂.eraseDups.length - 1 :=
    List.length_erase_of_mem hiD
  rw [hlen] at hle
  have hpos : 1 ≤ l₂.eraseDups.length := List.length_pos_of_mem hiD
  omega

/-- Positive distinct-variable count provides an actual free-variable witness. -/
theorem exists_freeVar_of_vars_pos (t : FormulaTree)
    (hvars : 0 < vars t) :
    ∃ i : Nat, i ∈ freeVarList t := by
  unfold vars at hvars
  cases hD : (freeVarList t).eraseDups with
  | nil =>
      simp [hD] at hvars
  | cons i rest =>
      refine ⟨i, ?_⟩
      apply (mem_eraseDups_nat).1
      rw [hD]
      simp

/-- Fixing any variable that really occurs in a formula strictly lowers the
number of distinct syntactic variables after restriction and simplification. -/
theorem vars_D_lt_fixVarTrue
    (i : Nat) (t : FormulaTree)
    (hi : i ∈ freeVarList t) :
    vars (D (fixVarTrue i) t) < vars t := by
  unfold vars
  apply eraseDups_length_lt_of_subset_of_missing
  · intro x hx
    exact mem_freeVarList_D (fixVarTrue i) t hx
  · exact hi
  · exact fixedVar_not_mem_D i t

theorem strictProgress_fix_present
    (i : Nat) (t : FormulaTree)
    (hi : i ∈ freeVarList t) :
    StrictRestrictionProgress (fixVarTrue i) t := by
  left
  exact vars_D_lt_fixVarTrue i t hi

/-- C12 closes C10's remaining structural coverage obligation: every formula
with at least one syntactically free variable admits a concrete restriction that
strictly decreases the certified recurrence rank. -/
theorem progressCoverage_closed : ProgressCoverageObligation := by
  intro t hvars
  obtain ⟨i, hi⟩ := exists_freeVar_of_vars_pos t hvars
  refine ⟨fixVarTrue i, ?_⟩
  exact restrictionProgress_of_strict
    (fixVarTrue i) t (strictProgress_fix_present i t hi)

/-- Direct corollary: every positive-variable formula has an explicit
rank-decreasing restriction. This is a structural termination statement only;
it does not state a SAT runtime bound or a circuit lower bound. -/
theorem exists_rank_decreasing_restriction
    (t : FormulaTree) (hvars : 0 < vars t) :
    ∃ ρ : Restriction, stateRank (D ρ t) < stateRank t := by
  obtain ⟨ρ, hρ⟩ := progressCoverage_closed t hvars
  exact ⟨ρ, stateRank_D_decreases_of_restriction_progress ρ t hρ⟩

theorem c12_classical_endpoint_not_promoted :
    ¬ Nonempty (ProofCertificate k6_dependency.target) :=
  c11_classical_endpoint_not_promoted

theorem c12_k10_not_promoted :
    ¬ Nonempty (ProofCertificate k10_obligation_node) :=
  c11_k10_not_promoted

end C12
end MCore
