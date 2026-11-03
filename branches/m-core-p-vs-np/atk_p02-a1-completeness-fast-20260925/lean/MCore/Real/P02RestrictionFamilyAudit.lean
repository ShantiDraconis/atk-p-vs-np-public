import Mathlib.Tactic
import MCore.Real.CNFStructure
import MCore.C11.BranchingCost
import MCore.C10.RestrictionProgress

namespace MCore
namespace Real
namespace P02RestrictionFamilyAudit

open CircuitK1 CircuitC2
open C9 C10 C11

theorem reducibleExample_isCNF :
    IsCNF reducibleExample := by
  simp [reducibleExample, IsCNF, IsClause]

theorem reducibleExample_paysOff :
    PaysOff 1 1 fixesZeroTrue reducibleExample := by
  change 5 < 16
  decide

theorem reducibleExample_progress :
    RestrictionProgress fixesZeroTrue reducibleExample :=
  reducibleExample_restriction_progress

/-- Therefore any candidate hard family containing every CNF formula cannot
satisfy a universal persistent-deficit condition over all progressing
restrictions. -/
theorem allCNF_universal_deficit_refuted :
    ¬ (∀ (t : FormulaTree),
        IsCNF t →
        ∀ ρ : Restriction,
          RestrictionProgress ρ t →
            ¬ PaysOff 1 1 ρ t) := by
  intro h
  exact (h reducibleExample reducibleExample_isCNF
    fixesZeroTrue reducibleExample_progress) reducibleExample_paysOff

#print axioms MCore.Real.P02RestrictionFamilyAudit.reducibleExample_paysOff
#print axioms MCore.Real.P02RestrictionFamilyAudit.allCNF_universal_deficit_refuted

end P02RestrictionFamilyAudit
end Real
end MCore
