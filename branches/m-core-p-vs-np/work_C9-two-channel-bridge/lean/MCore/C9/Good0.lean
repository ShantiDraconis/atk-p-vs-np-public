import MCore.C9.FreeVars

namespace MCore
namespace C9

open CircuitK1

def IsConst : FormulaTree → Prop
  | .const _ => True
  | _ => False

def TouchesVars (t : FormulaTree) (ρ : Restriction) : Prop :=
  ∃ v b, v ∈ freeVarList t ∧ ρ v = some b

def Good0 (t : FormulaTree) (ρ : Restriction) : Prop :=
  ¬ IsConst t ∧ TouchesVars t ρ

theorem touchesVars_not_const {t : FormulaTree} {ρ : Restriction}
    (h : TouchesVars t ρ) : ¬ IsConst t := by
  intro hc
  cases t <;> simp [IsConst, TouchesVars, freeVarList] at h hc

theorem good0_iff_touches {t : FormulaTree} {ρ : Restriction} :
    Good0 t ρ ↔ TouchesVars t ρ := by
  constructor
  · exact fun h => h.2
  · exact fun h => ⟨touchesVars_not_const h, h⟩

end C9
end MCore
