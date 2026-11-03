import Mathlib.Tactic
import MCore.Real.P02RestrictionLowerBoundPattern

namespace MCore
namespace Real
namespace P02CNFEncodingDeficitAudit

open CircuitK1 CircuitC2
open C9 C10 C11
open P02BoundedComputationEncoding
open P02RestrictionLowerBoundPattern

def oneClauseCore : CNF := [[pos 0]]

theorem free_progress_oneClauseCore :
    RestrictionProgress leavesZeroFree (cnfCircuit oneClauseCore) := by
  change 1 ≤ 1 ∧ (1 < 1 ∨ 0 < 6)
  decide

theorem free_cost_zero_oneClauseCore :
    costBits leavesZeroFree (cnfCircuit oneClauseCore) = 0 := by
  change 0 = 0
  rfl

theorem free_amortizedDrop_pos_oneClauseCore :
    0 < amortizedDrop 1 1 leavesZeroFree (cnfCircuit oneClauseCore) := by
  change 0 < 12
  decide

theorem oneClauseCore_not_deficit (c : Nat) :
    ¬ DeficitAtLeast c oneClauseCore := by
  intro h
  have hd := h leavesZeroFree free_progress_oneClauseCore
  have hcost := free_cost_zero_oneClauseCore
  have hdrop := free_amortizedDrop_pos_oneClauseCore
  omega

#print axioms MCore.Real.P02CNFEncodingDeficitAudit.oneClauseCore_not_deficit

end P02CNFEncodingDeficitAudit
end Real
end MCore
