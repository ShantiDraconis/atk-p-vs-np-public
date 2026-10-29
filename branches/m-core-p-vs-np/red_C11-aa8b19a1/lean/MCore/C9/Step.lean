import MCore.C9.Good

namespace MCore
namespace C9

open CircuitC8

/-- Combined syntactic-state rank inherited from the certified C8 recurrence
measure, now instantiated with C9's explicit variable count and potential. -/
def stateRank (t : FormulaTree) : Nat :=
  recurrenceRank (vars t) (mu t)

/-- A C9 progress step records exactly the data needed to certify strict descent.
It does not assert that every formula admits such a step. -/
structure ProgressStep where
  before : FormulaTree
  after : FormulaTree
  fixedVars : Nat
  fixedVars_le : fixedVars ≤ vars before
  vars_after : vars after = vars before - fixedVars
  mu_nonincrease : mu after ≤ mu before
  progress : 0 < fixedVars ∨ mu after < mu before

/-- Every explicitly certified C9 progress step strictly decreases the C8
well-founded recurrence rank. The theorem is conditional on the supplied step
data and therefore does not manufacture an algorithmic speedup. -/
theorem stateRank_decreases (s : ProgressStep) :
    stateRank s.after < stateRank s.before := by
  unfold stateRank
  rw [s.vars_after]
  rcases s.progress with hfix | hmu
  · exact rank_decreases_when_variable_fixed
      (vars s.before) (mu s.before) s.fixedVars (mu s.after)
      hfix s.fixedVars_le s.mu_nonincrease
  · by_cases hfix : 0 < s.fixedVars
    · exact rank_decreases_when_variable_fixed
        (vars s.before) (mu s.before) s.fixedVars (mu s.after)
        hfix s.fixedVars_le s.mu_nonincrease
    · have hz : s.fixedVars = 0 := Nat.eq_zero_of_not_pos hfix
      simpa [hz] using
        rank_decreases_when_potential_drops
          (vars s.before) (mu s.before) (mu s.after) hmu

theorem progressStep_no_stutter (s : ProgressStep) :
    stateRank s.after ≠ stateRank s.before :=
  Nat.ne_of_lt (stateRank_decreases s)

end C9
end MCore
