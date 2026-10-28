import MCore.C9.Mu

namespace MCore
namespace C9

open CircuitK1 CircuitC2

/-- Finite set corresponding exactly to the distinct identifiers counted by `vars`. -/
def freeVarSet (t : FormulaTree) : Finset Nat := (freeVarList t).toFinset

@[simp] theorem mem_freeVarSet {t : FormulaTree} {v : Nat} :
    v ∈ freeVarSet t ↔ v ∈ freeVarList t := by
  simp [freeVarSet]

theorem vars_eq_card (t : FormulaTree) : vars t = (freeVarSet t).card := by
  simp [vars, freeVarSet, List.toFinset_card_of_eraseDups]

/-- Restriction never introduces a new input identifier. -/
theorem mem_freeVarList_restrict (ρ : Restriction) (t : FormulaTree) (v : Nat)
    (h : v ∈ freeVarList (restrict ρ t)) : v ∈ freeVarList t := by
  induction t with
  | input i =>
      cases hr : ρ i with
      | none => simpa [restrict, freeVarList, hr] using h
      | some b => simp [restrict, freeVarList, hr] at h
  | const b => simp [restrict, freeVarList] at h
  | not c ih =>
      exact ih (by simpa [restrict, freeVarList] using h)
  | and a b iha ihb =>
      simp only [restrict, freeVarList, List.mem_append] at h ⊢
      exact h.elim (fun ha => Or.inl (iha ha)) (fun hb => Or.inr (ihb hb))
  | or a b iha ihb =>
      simp only [restrict, freeVarList, List.mem_append] at h ⊢
      exact h.elim (fun ha => Or.inl (iha ha)) (fun hb => Or.inr (ihb hb))

/-- A fixed identifier is absent after restriction. -/
theorem fixed_not_mem_restrict (ρ : Restriction) (t : FormulaTree) (v : Nat) (b : Bool)
    (hfix : ρ v = some b) : v ∉ freeVarList (restrict ρ t) := by
  induction t with
  | input i =>
      intro h
      by_cases hiv : i = v
      · subst i
        simp [restrict, freeVarList, hfix] at h
      · cases hr : ρ i <;> simp [restrict, freeVarList, hr, hiv] at h
  | const c => simp [restrict, freeVarList]
  | not c ih => simpa [restrict, freeVarList] using ih
  | and a c iha ihc =>
      simp only [restrict, freeVarList, List.mem_append, not_or]
      exact ⟨iha, ihc⟩
  | or a c iha ihc =>
      simp only [restrict, freeVarList, List.mem_append, not_or]
      exact ⟨iha, ihc⟩

/-- Current C2 simplification only deletes structure/variables; it never creates an input. -/
theorem mem_freeVarList_simplify (t : FormulaTree) (v : Nat)
    (h : v ∈ freeVarList (simplify t)) : v ∈ freeVarList t := by
  induction t with
  | input i => simpa [simplify, freeVarList] using h
  | const b => simp [simplify, freeVarList] at h
  | not c ih =>
      simp only [simplify] at h
      cases hs : simplify c <;> simp [freeVarList, hs] at h ⊢
      exact ih h
  | and a b iha ihb =>
      simp only [simplify] at h
      cases ha : simplify a <;> cases hb : simplify b <;>
        simp [freeVarList, ha, hb] at h ⊢
      all_goals
        first
        | exact Or.inl (iha h)
        | exact Or.inr (ihb h)
        | exact h.elim (fun x => Or.inl (iha x)) (fun x => Or.inr (ihb x))
  | or a b iha ihb =>
      simp only [simplify] at h
      cases ha : simplify a <;> cases hb : simplify b <;>
        simp [freeVarList, ha, hb] at h ⊢
      all_goals
        first
        | exact Or.inl (iha h)
        | exact Or.inr (ihb h)
        | exact h.elim (fun x => Or.inl (iha x)) (fun x => Or.inr (ihb x))

theorem mem_freeVarList_D (ρ : Restriction) (t : FormulaTree) (v : Nat)
    (h : v ∈ freeVarList (D ρ t)) : v ∈ freeVarList t :=
  mem_freeVarList_restrict ρ t v
    (mem_freeVarList_simplify (restrict ρ t) v (by simpa [D, restrictedSimplified] using h))

theorem fixed_not_mem_D (ρ : Restriction) (t : FormulaTree) (v : Nat) (b : Bool)
    (hfix : ρ v = some b) : v ∉ freeVarList (D ρ t) := by
  intro h
  have hr : v ∈ freeVarList (restrict ρ t) :=
    mem_freeVarList_simplify (restrict ρ t) v (by simpa [D, restrictedSimplified] using h)
  exact fixed_not_mem_restrict ρ t v b hfix hr

theorem freeVarSet_D_subset (ρ : Restriction) (t : FormulaTree) :
    freeVarSet (D ρ t) ⊆ freeVarSet t := by
  intro v hv
  exact (mem_freeVarSet).2 (mem_freeVarList_D ρ t v ((mem_freeVarSet).1 hv))

theorem vars_D_le (ρ : Restriction) (t : FormulaTree) : vars (D ρ t) ≤ vars t := by
  rw [vars_eq_card, vars_eq_card]
  exact Finset.card_le_card (freeVarSet_D_subset ρ t)

end C9
end MCore
