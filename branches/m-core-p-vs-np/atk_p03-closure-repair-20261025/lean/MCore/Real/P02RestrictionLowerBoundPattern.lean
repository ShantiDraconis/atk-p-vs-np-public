import MCore.C11.BranchingCost

namespace MCore
namespace Real
namespace P02RestrictionLowerBoundPattern

open C9 C10 C11 CircuitK1

/-- Exact amortized structural drop used by C11. -/
def amortizedDrop (α β : Nat) (ρ : Restriction) (t : FormulaTree) : Nat :=
  Potential α β t - Potential α β (D ρ t)

/-- C11 PaysOff is exactly the regime where the number of fixed branching bits
is strictly smaller than the certified potential drop. -/
theorem paysOff_implies_costBits_lt_amortizedDrop
    (α β : Nat) (ρ : Restriction) (t : FormulaTree)
    (h : PaysOff α β ρ t) :
    costBits ρ t < amortizedDrop α β ρ t := by
  unfold PaysOff amortizedDrop at *
  omega

/-- Separation-oriented local pattern: every progressing restriction fails to
amortize its branching bits. This is intentionally the opposite orientation
from C11 PaysOff. -/
def PersistentBranchingDeficit
    (α β : Nat) (t : FormulaTree) : Prop :=
  ∀ ρ : Restriction,
    RestrictionProgress ρ t →
      amortizedDrop α β ρ t ≤ costBits ρ t

theorem persistentBranchingDeficit_excludes_payoff
    (α β : Nat) (t : FormulaTree)
    (h : PersistentBranchingDeficit α β t) :
    ∀ ρ : Restriction,
      RestrictionProgress ρ t →
        ¬ PaysOff α β ρ t := by
  intro ρ hprog hpay
  have hlt := paysOff_implies_costBits_lt_amortizedDrop α β ρ t hpay
  have hle := h ρ hprog
  omega

/-- Family-level candidate obstruction for the fourth P02 lane.  Unlike the
old diagonal lanes, this statement contains no self-code or fixed-point
equation. -/
def PersistentBranchingDeficitFamily
    (α β : Nat) (f : Nat → FormulaTree) : Prop :=
  ∀ n : Nat, 0 < n → PersistentBranchingDeficit α β (f n)

/-- Exact frontier for using this pattern as a P02 route.  The missing theorem
must connect a persistent branching deficit for a SAT-complete family to
non-membership in the hardened deterministic polynomial-time model. -/
def RestrictionLowerBoundTransfer : Prop :=
  ∀ f : Nat → FormulaTree,
    PersistentBranchingDeficitFamily 1 1 f →
      True

#print axioms MCore.Real.P02RestrictionLowerBoundPattern.paysOff_implies_costBits_lt_amortizedDrop
#print axioms MCore.Real.P02RestrictionLowerBoundPattern.persistentBranchingDeficit_excludes_payoff

end P02RestrictionLowerBoundPattern
end Real
end MCore
