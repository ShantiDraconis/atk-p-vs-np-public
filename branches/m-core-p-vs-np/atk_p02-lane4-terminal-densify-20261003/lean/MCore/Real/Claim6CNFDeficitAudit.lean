import Mathlib.Tactic
import MCore.C11.BranchingCost
import MCore.C10.RestrictionProgress
import MCore.Real.P02BoundedComputationEncoding

namespace MCore.Real.Claim6CNFDeficitAudit

open MCore
open MCore.CircuitK1 MCore.CircuitC2
open MCore.C9 MCore.C10 MCore.C11
open MCore.Real.P02BoundedComputationEncoding

/-- Exact amortized structural drop used by the 7732c120 audit source state. -/
def amortizedDrop (α β : Nat) (ρ : Restriction) (t : FormulaTree) : Nat :=
  Potential α β t - Potential α β (D ρ t)

/-- Exact local deficit predicate from the 7732c120 audit source state. -/
def DeficitAtLeast (c : Nat) (f : CNF) : Prop :=
  ∀ ρ : Restriction,
    RestrictionProgress ρ (cnfCircuit f) →
      amortizedDrop 1 1 ρ (cnfCircuit f) ≤
        costBits ρ (cnfCircuit f) ∧
      c ≤ costBits ρ (cnfCircuit f) -
        amortizedDrop 1 1 ρ (cnfCircuit f)

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

#print axioms MCore.Real.Claim6CNFDeficitAudit.oneClauseCore_not_deficit

end MCore.Real.Claim6CNFDeficitAudit
