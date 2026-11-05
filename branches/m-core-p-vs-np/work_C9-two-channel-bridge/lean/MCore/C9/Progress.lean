import MCore.C9.Good0

namespace MCore
namespace C9

open CircuitK1

def deltaN (ρ : Restriction) (t : FormulaTree) : Nat :=
  vars t - vars (D ρ t)

theorem good0_vars_strict {t : FormulaTree} {ρ : Restriction}
    (h : Good0 t ρ) : vars (D ρ t) < vars t := by
  obtain ⟨v, b, hv, hfix⟩ := h.2
  rw [vars_eq_card, vars_eq_card]
  apply Finset.card_lt_card
  · exact freeVarSet_D_subset ρ t
  · intro heq
    have hvT : v ∈ freeVarSet t := (mem_freeVarSet).2 hv
    have hvD : v ∈ freeVarSet (D ρ t) := by simpa [heq] using hvT
    exact fixed_not_mem_D ρ t v b hfix ((mem_freeVarSet).1 hvD)

theorem good0_deltaN_pos {t : FormulaTree} {ρ : Restriction}
    (h : Good0 t ρ) : 0 < deltaN ρ t := by
  unfold deltaN
  omega

theorem good0_two_channel_progress {t : FormulaTree} {ρ : Restriction}
    (h : Good0 t ρ) : 0 < deltaN ρ t ∨ 0 < delta ρ t :=
  Or.inl (good0_deltaN_pos h)

def fixesZeroFalse : Restriction
  | 0 => some false
  | _ => none

theorem single_channel_counterexample :
    Good0 (.input 0) fixesZeroFalse ∧
    delta fixesZeroFalse (.input 0) = 0 ∧
    deltaN fixesZeroFalse (.input 0) = 1 := by
  constructor
  · constructor
    · simp [IsConst]
    · exact ⟨0, false, by simp [freeVarList], rfl⟩
  · constructor
    · rfl
    · rfl

end C9
end MCore
