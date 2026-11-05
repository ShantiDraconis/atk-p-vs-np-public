import MCore.Real.P02BoundedComputationEncoding

namespace MCore.Real.Claim7VariableCoverage

open MCore
open MCore.CircuitK1
open MCore.Real.P02BoundedComputationEncoding

/-- Canonical CNF variable list from the Claim7 source state. -/
def cnfVarList (f : CNF) : List Nat :=
  (f.flatMap fun clause => clause.map Literal.var).eraseDups

/-- Canonical CNF variable bound from the Claim7 source state. -/
def clauseVarBound (c : Clause) : Nat :=
  c.foldl (fun acc l => max acc (l.var + 1)) 0

def cnfVarBound (f : CNF) : Nat :=
  f.foldl (fun acc c => max acc (clauseVarBound c)) 0

/-- Symmetric coupling gadget from the Claim7 source state. -/
def coverageClauses (base i v : Nat) : CNF :=
  [ [pos v, pos (base + 2 * i)]
  , [neg v, pos (base + 2 * i + 1)] ]

def coverageCore (payload : CNF) : CNF :=
  let base := cnfVarBound payload
  ((cnfVarList payload).zipIdx.flatMap
    (fun vi => coverageClauses base vi.2 vi.1))

/-- v4.19 compatibility: eraseDups preserves membership. -/
private theorem mem_eraseDups_loop_iff
    {α : Type} [BEq α] [LawfulBEq α] (a : α) :
    ∀ (l acc : List α),
      a ∈ List.eraseDups.loop l acc ↔ a ∈ l ∨ a ∈ acc := by
  intro l
  induction l with
  | nil =>
      intro acc
      simp [List.eraseDups.loop]
  | cons b bs ih =>
      intro acc
      simp only [List.eraseDups.loop]
      split
      · rename_i h
        have hbmem : b ∈ acc := List.mem_of_elem_eq_true h
        rw [ih]
        by_cases hab : a = b
        · subst b
          simp [hbmem]
        · simp [hab]
      · rename_i h
        have hbnot : b ∉ acc := by
          intro hb
          have heq : acc.elem b = true := List.elem_eq_true_of_mem hb
          rw [h] at heq
          contradiction
        rw [ih]
        by_cases hab : a = b
        · subst b
          simp [hbnot]
        · simp [hab]

theorem mem_eraseDups_iff
    {α : Type} [BEq α] [LawfulBEq α] {a : α} {l : List α} :
    a ∈ l.eraseDups ↔ a ∈ l := by
  unfold List.eraseDups
  rw [mem_eraseDups_loop_iff]
  simp

/-- Every literal variable occurring in a payload is recorded by cnfVarList. -/
theorem literal_var_mem_cnfVarList
    {f : CNF} {c : Clause} {l : Literal}
    (hc : c ∈ f) (hl : l ∈ c) :
    l.var ∈ cnfVarList f := by
  apply mem_eraseDups_iff.mpr
  simp
  exact ⟨c, hc, l, hl, rfl⟩

/-- cnfVarList is monotone under append. -/
theorem cnfVarList_left_subset_append
    (a b : CNF) :
    ∀ v, v ∈ cnfVarList a → v ∈ cnfVarList (a ++ b) := by
  intro v hv
  apply mem_eraseDups_iff.mpr
  rw [List.flatMap_append]
  exact List.mem_append.mpr (Or.inl (mem_eraseDups_iff.mp hv))

theorem cnfVarList_right_subset_append
    (a b : CNF) :
    ∀ v, v ∈ cnfVarList b → v ∈ cnfVarList (a ++ b) := by
  intro v hv
  apply mem_eraseDups_iff.mpr
  rw [List.flatMap_append]
  exact List.mem_append.mpr (Or.inr (mem_eraseDups_iff.mp hv))

#print axioms MCore.Real.Claim7VariableCoverage.literal_var_mem_cnfVarList
#print axioms MCore.Real.Claim7VariableCoverage.cnfVarList_left_subset_append
#print axioms MCore.Real.Claim7VariableCoverage.cnfVarList_right_subset_append

end MCore.Real.Claim7VariableCoverage
