import MCore.Real.P02RestrictionLowerBoundPattern
import MCore.Real.P02RestrictionFamilyAudit

namespace MCore
namespace Real
namespace P02PaddingInheritanceAudit

open CircuitK1 CircuitC2
open C9 C10 C11
open P02BoundedComputationEncoding
open P02RestrictionLowerBoundPattern

def reducibleCNF : CNF :=
  [[pos 0], [pos 1]]

theorem cnfCircuit_reducibleCNF :
    cnfCircuit reducibleCNF =
      .and (.or (.input 0) (.const false))
        (.and (.or (.input 1) (.const false)) (.const true)) := by
  rfl

theorem empty_core_sat :
    SATLanguage (cnfCircuit ([] : CNF)) := by
  refine ⟨cnfCircuit_isCNF [], fun _ => false, ?_⟩
  rfl

theorem empty_core_deficit_vacuous (c : Nat) :
    DeficitAtLeast c ([] : CNF) := by
  intro ρ hprog
  unfold RestrictionProgress at hprog
  simp [cnfCircuit, C9.vars, C9.freeVarList, C9.D, C9.mu,
    CircuitC3.drop, CircuitC3.potential,
    CircuitC2.restrictedSimplified, CircuitK1.restrict,
    CircuitC2.simplify] at hprog

/-- The current append-inheritance principle is strictly stronger than
"the core is satisfiable and has DeficitAtLeast": for the empty satisfiable
core it would require every CNF to inherit the margin. -/
theorem paddingInheritance_empty_core_implies_all
    (c : Nat)
    (h : PaddingDeficitInheritance (fun _ => ([] : CNF)) c) :
    ∀ f : CNF, DeficitAtLeast c f := by
  intro f
  have hc : DeficitAtLeast c ([] : CNF) :=
    empty_core_deficit_vacuous c
  simpa using h 0 f hc

#print axioms MCore.Real.P02PaddingInheritanceAudit.empty_core_deficit_vacuous
#print axioms MCore.Real.P02PaddingInheritanceAudit.paddingInheritance_empty_core_implies_all

end P02PaddingInheritanceAudit
end Real
end MCore
