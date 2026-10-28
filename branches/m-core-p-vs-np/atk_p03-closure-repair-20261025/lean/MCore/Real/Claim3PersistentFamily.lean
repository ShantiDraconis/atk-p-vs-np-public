import MCore.C11.BranchingCost

namespace MCore.Real.Claim3PersistentFamily

open MCore
open MCore.C9 MCore.C10 MCore.C11 MCore.CircuitK1

def amortizedDrop (α β : Nat) (ρ : Restriction) (t : FormulaTree) : Nat :=
  Potential α β t - Potential α β (D ρ t)

def PersistentBranchingDeficitFamily
    (α β : Nat) (f : Nat → FormulaTree) : Prop :=
  ∃ (c n0 : Nat), 0 < c ∧
    ∀ n : Nat, n0 ≤ n →
      ∀ ρ : Restriction,
        RestrictionProgress ρ (f n) →
          amortizedDrop α β ρ (f n) ≤ costBits ρ (f n) ∧
          c ≤ costBits ρ (f n) - amortizedDrop α β ρ (f n)

theorem paysOff_implies_costBits_lt_amortizedDrop
    (α β : Nat) (ρ : Restriction) (t : FormulaTree)
    (h : PaysOff α β ρ t) :
    costBits ρ t < amortizedDrop α β ρ t := by
  unfold PaysOff amortizedDrop at *
  omega

theorem persistentFamily_excludes_eventual_payoff
    {α β : Nat} {f : Nat → FormulaTree}
    (h : PersistentBranchingDeficitFamily α β f) :
    ∃ n0 : Nat, ∀ n : Nat, n0 ≤ n →
      ∀ ρ : Restriction,
        RestrictionProgress ρ (f n) →
          ¬ PaysOff α β ρ (f n) := by
  rcases h with ⟨c, n0, hc, h⟩
  refine ⟨n0, ?_⟩
  intro n hn ρ hprog hpay
  have hdef := (h n hn ρ hprog).1
  have hlt :=
    paysOff_implies_costBits_lt_amortizedDrop α β ρ (f n) hpay
  omega

#print axioms MCore.Real.Claim3PersistentFamily.persistentFamily_excludes_eventual_payoff

end MCore.Real.Claim3PersistentFamily
