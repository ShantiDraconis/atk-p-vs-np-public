import MCore.CircuitC6

namespace MCore
namespace CircuitC7

open CircuitK1 CircuitC2 CircuitC3 CircuitC4 CircuitC5 CircuitC6

/-- Total weight carried by restrictions whose certified drop reaches `minDrop`. -/
def goodWeight (sample : List WeightedRestriction) (c : Circuit) (minDrop : Nat) : Nat :=
  sample.foldr (fun x acc => if minDrop ≤ drop x.restriction c then x.weight + acc else acc) 0

/-- A family-level quantitative condition: at least `minGoodWeight` total sample
weight lies on restrictions with drop at least `minDrop`. -/
def GoodMassWitness
    (sample : List WeightedRestriction) (c : Circuit)
    (minGoodWeight minDrop : Nat) : Prop :=
  minGoodWeight ≤ goodWeight sample c minDrop

/-- The aggregate weighted drop dominates threshold times the weight of all
restrictions meeting that threshold. -/
theorem minDrop_mul_goodWeight_le_weightedDrop
    (sample : List WeightedRestriction) (c : Circuit) (minDrop : Nat) :
    minDrop * goodWeight sample c minDrop ≤ weightedDrop sample c := by
  induction sample with
  | nil => simp [goodWeight, weightedDrop]
  | cons x xs ih =>
      by_cases hgood : minDrop ≤ drop x.restriction c
      · rw [goodWeight, List.foldr_cons, if_pos hgood, weightedDrop, List.foldr_cons]
        rw [Nat.mul_add]
        apply Nat.add_le_add
        · simpa [Nat.mul_comm] using Nat.mul_le_mul_left x.weight hgood
        · exact ih
      · rw [goodWeight, List.foldr_cons, if_neg hgood, weightedDrop, List.foldr_cons]
        exact Nat.le_trans ih (Nat.le_add_left _ _)

/-- Aggregate good mass yields a product lower bound without selecting a single
witness member. -/
theorem good_mass_implies_weightedDrop_lower_bound
    (sample : List WeightedRestriction) (c : Circuit)
    (minGoodWeight minDrop : Nat)
    (h : GoodMassWitness sample c minGoodWeight minDrop) :
    minDrop * minGoodWeight ≤ weightedDrop sample c := by
  exact Nat.le_trans (Nat.mul_le_mul_left minDrop h)
    (minDrop_mul_goodWeight_le_weightedDrop sample c minDrop)

/-- The C4 demonstration sample has exactly one unit of weight at drop threshold 3. -/
theorem demo_goodWeight_three : goodWeight demoSample reducibleExample 3 = 1 := by
  simp [goodWeight, demoSample, drop, potential, restrictedSimplified,
    reducibleExample, fixesZeroTrue, leavesZeroFree, restrict, simplify, μ, size, depth]

theorem demoGoodMassWitness : GoodMassWitness demoSample reducibleExample 1 3 := by
  simp [GoodMassWitness, demo_goodWeight_three]

theorem demo_good_mass_lower_bound : 3 ≤ weightedDrop demoSample reducibleExample := by
  simpa using good_mass_implies_weightedDrop_lower_bound
    demoSample reducibleExample 1 3 demoGoodMassWitness

/-- The zero-drop adversarial family has no mass at any strictly positive drop threshold. -/
theorem zero_sample_goodWeight_positive_threshold (minDrop : Nat) (h0 : 0 < minDrop) :
    goodWeight zeroDropSample oneInput minDrop = 0 := by
  simp [goodWeight, zeroDropSample, drop, potential, restrictedSimplified,
    leavesZeroFree, oneInput, restrict, simplify, μ, size, depth, Nat.not_le_of_gt h0]

/-- Positive good mass at a positive threshold is not universal. -/
theorem not_every_family_has_positive_good_mass :
    ¬ (∀ (sample : List WeightedRestriction) (c : Circuit),
      0 < totalWeight sample → ∃ minGoodWeight minDrop : Nat,
        0 < minGoodWeight ∧ 0 < minDrop ∧
        GoodMassWitness sample c minGoodWeight minDrop) := by
  intro h
  rcases h zeroDropSample oneInput (by simp) with ⟨mw, md, hmw, hmd, hgood⟩
  have hz := zero_sample_goodWeight_positive_threshold md hmd
  unfold GoodMassWitness at hgood
  rw [hz] at hgood
  have hm0 : mw = 0 := Nat.eq_zero_of_le_zero hgood
  subst mw
  exact Nat.lt_irrefl 0 hmw

theorem c7_classical_endpoint_not_promoted : ¬ Nonempty (ProofCertificate k6_dependency.target) :=
  c6_classical_endpoint_not_promoted

theorem c7_k10_not_promoted : ¬ Nonempty (ProofCertificate k10_obligation_node) :=
  c6_k10_not_promoted

end CircuitC7
end MCore
