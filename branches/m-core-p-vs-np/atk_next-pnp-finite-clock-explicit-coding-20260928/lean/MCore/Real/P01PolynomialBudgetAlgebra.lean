import MCore.Real.CanonicalFinalProof

namespace MCore
namespace Real
namespace P01PolynomialBudgetAlgebra

open CanonicalFinalProof

def addTimeBound (T U : TimeBound) : TimeBound :=
  fun n => T n + U n

def DegreeBound (T : TimeBound) (k : Nat) : Prop :=
  ∃ c : Nat, ∀ n : Nat,
    T n ≤ c * (n + 1) ^ k

theorem degreeBound_add
    {T U : TimeBound} {k : Nat}
    (hT : DegreeBound T k)
    (hU : DegreeBound U k) :
    DegreeBound (addTimeBound T U) k := by
  rcases hT with ⟨cT, hT⟩
  rcases hU with ⟨cU, hU⟩
  refine ⟨cT + cU, ?_⟩
  intro n
  unfold addTimeBound
  calc
    T n + U n ≤
        cT * (n + 1) ^ k + cU * (n + 1) ^ k :=
      Nat.add_le_add (hT n) (hU n)
    _ = (cT + cU) * (n + 1) ^ k := by
      rw [Nat.add_mul]

theorem degreeBound_add3
    {T U V : TimeBound} {k : Nat}
    (hT : DegreeBound T k)
    (hU : DegreeBound U k)
    (hV : DegreeBound V k) :
    DegreeBound
      (addTimeBound (addTimeBound T U) V) k := by
  exact degreeBound_add (degreeBound_add hT hU) hV

theorem degreeBound_implies_polynomial
    {T : TimeBound} {k : Nat}
    (h : DegreeBound T k) :
    PolynomialTimeBound T := by
  rcases h with ⟨c, hc⟩
  exact ⟨c, k, hc⟩

#print axioms MCore.Real.P01PolynomialBudgetAlgebra.degreeBound_add
#print axioms MCore.Real.P01PolynomialBudgetAlgebra.degreeBound_add3
#print axioms MCore.Real.P01PolynomialBudgetAlgebra.degreeBound_implies_polynomial

end P01PolynomialBudgetAlgebra
end Real
end MCore
