import MCore.Real.P02RestrictionLowerBoundPattern

namespace MCore
namespace Real
namespace P02SharedVariableCoverageAudit

open CircuitK1 CircuitC2
open C9 C10 C11
open P02BoundedComputationEncoding
open P02RestrictionLowerBoundPattern

/-- Payload has one private variable 0.  Core uses variable 1.  In a realistic
one-output coupling, variable 1 would be the shared/output variable while
variable 0 remains internal payload structure. -/
def payload : CNF := [[pos 0]]
def core : CNF := [[pos 1]]

def fixPayloadOnly : Restriction := fun i =>
  if i = 0 then some true else none

theorem core_untouched :
    D fixPayloadOnly (cnfCircuit core) = cnfCircuit core := by
  rfl

theorem core_has_no_progress :
    ¬ RestrictionProgress fixPayloadOnly (cnfCircuit core) := by
  intro h
  rcases h with ⟨_, hprog⟩
  rcases hprog with hv | hd
  · simp [core, cnfCircuit, clauseCircuit, literalCircuit,
      fixPayloadOnly, D, vars, freeVarList, restrictedSimplified,
      restrict, simplify] at hv
  · simp [core, cnfCircuit, clauseCircuit, literalCircuit,
      fixPayloadOnly, D, delta, mu, CircuitC3.drop,
      CircuitC3.potential, restrictedSimplified, restrict, simplify,
      CircuitK1.size, CircuitK1.depth] at hd

theorem padded_has_progress :
    RestrictionProgress fixPayloadOnly (cnfCircuit (payload ++ core)) := by
  constructor
  · simp [payload, core, cnfCircuit, clauseCircuit, literalCircuit,
      fixPayloadOnly, D, vars, freeVarList, restrictedSimplified,
      restrict, simplify]
  · left
    simp [payload, core, cnfCircuit, clauseCircuit, literalCircuit,
      fixPayloadOnly, D, vars, freeVarList, restrictedSimplified,
      restrict, simplify]

/-- A single shared/output variable does not force core-aware coverage when the
payload retains any private variable on which a restriction can make progress. -/
theorem one_shared_variable_does_not_force_coverage :
    ¬ CoreAwareProgressCoverage payload core := by
  intro h
  have hc := h fixPayloadOnly padded_has_progress
  exact core_has_no_progress hc.2

#print axioms MCore.Real.P02SharedVariableCoverageAudit.one_shared_variable_does_not_force_coverage

end P02SharedVariableCoverageAudit
end Real
end MCore
