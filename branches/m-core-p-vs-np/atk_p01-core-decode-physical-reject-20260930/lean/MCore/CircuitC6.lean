import MCore.CircuitC5

namespace MCore
namespace CircuitC6

open CircuitK1 CircuitC2 CircuitC3 CircuitC4 CircuitC5

/-- Quantitative structural condition: some sampled restriction has at least
`minWeight` weight and at least `minDrop` circuit-potential drop. -/
def QuantitativeDropWitness
    (sample : List WeightedRestriction) (c : Circuit)
    (minWeight minDrop : Nat) : Prop :=
  ∃ x ∈ sample, minWeight ≤ x.weight ∧ minDrop ≤ drop x.restriction c

/-- A quantitative witness contributes at least the product of its two certified
lower bounds to the total weighted drop. -/
theorem quantitative_witness_implies_weightedDrop_lower_bound
    (sample : List WeightedRestriction) (c : Circuit)
    (minWeight minDrop : Nat)
    (h : QuantitativeDropWitness sample c minWeight minDrop) :
    minWeight * minDrop ≤ weightedDrop sample c := by
  rcases h with ⟨x, hx, hw, hd⟩
  have hmul : minWeight * minDrop ≤ x.weight * drop x.restriction c :=
    Nat.mul_le_mul hw hd
  exact Nat.le_trans hmul (member_contribution_le_weightedDrop sample c x hx)

/-- Strictly positive quantitative lower bounds recover the qualitative C5
positive-drop witness. -/
theorem quantitative_positive_implies_positive_witness
    (sample : List WeightedRestriction) (c : Circuit)
    (minWeight minDrop : Nat)
    (hw0 : 0 < minWeight) (hd0 : 0 < minDrop)
    (h : QuantitativeDropWitness sample c minWeight minDrop) :
    PositiveDropWitness sample c := by
  rcases h with ⟨x, hx, hw, hd⟩
  refine ⟨x, hx, Nat.lt_of_lt_of_le hw0 hw, Nat.lt_of_lt_of_le hd0 hd⟩

/-- Cross-multiplied finite-average lower bound obtained from a quantitative
witness. This remains a statement about an explicit finite weighted sample. -/
theorem quantitative_witness_implies_expectedDropAtLeast
    (sample : List WeightedRestriction) (c : Circuit)
    (minWeight minDrop : Nat)
    (h : QuantitativeDropWitness sample c minWeight minDrop) :
    ExpectedDropAtLeast sample c
      (minWeight * minDrop) (totalWeight sample) := by
  unfold ExpectedDropAtLeast
  have hb := Nat.mul_le_mul_left (totalWeight sample)
    (quantitative_witness_implies_weightedDrop_lower_bound sample c minWeight minDrop h)
  simpa [Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using hb

/-- Exact quantitative witness for the C4/C5 demonstration family. -/
theorem demoQuantitativeWitness :
    QuantitativeDropWitness demoSample reducibleExample 1 3 := by
  refine ⟨{ restriction := fixesZeroTrue, weight := 1 }, ?_, by decide, ?_⟩
  · simp [demoSample]
  · simp [drop, potential, restrictedSimplified, reducibleExample,
      fixesZeroTrue, restrict, simplify, μ, size, depth]

theorem demo_quantitative_lower_bound :
    3 ≤ weightedDrop demoSample reducibleExample := by
  simpa using quantitative_witness_implies_weightedDrop_lower_bound
    demoSample reducibleExample 1 3 demoQuantitativeWitness

/-- The zero-drop adversarial family cannot certify any strictly positive
minimum drop, regardless of the requested minimum weight. -/
theorem zero_sample_no_positive_minDrop (minWeight minDrop : Nat)
    (hd0 : 0 < minDrop) :
    ¬ QuantitativeDropWitness zeroDropSample oneInput minWeight minDrop := by
  rintro ⟨x, hx, _hw, hd⟩
  have hx' : x = { restriction := leavesZeroFree, weight := 1 } := by
    simpa [zeroDropSample] using hx
  subst x
  have hz : drop leavesZeroFree oneInput = 0 := by
    simp [drop, potential, restrictedSimplified, leavesZeroFree, oneInput,
      restrict, simplify, μ, size, depth]
  rw [hz] at hd
  have hzero : minDrop = 0 := Nat.eq_zero_of_le_zero hd
  subst minDrop
  exact Nat.lt_irrefl 0 hd0

/-- No universal theorem can assign a positive minimum drop to every nonempty
positive-weight finite sample in this model. -/
theorem not_every_family_has_positive_quantitative_witness :
    ¬ (∀ (sample : List WeightedRestriction) (c : Circuit),
      0 < totalWeight sample → ∃ minWeight minDrop : Nat,
        0 < minWeight ∧ 0 < minDrop ∧
        QuantitativeDropWitness sample c minWeight minDrop) := by
  intro h
  rcases h zeroDropSample oneInput (by simp) with ⟨mw, md, _hmw, hmd, hq⟩
  exact zero_sample_no_positive_minDrop mw md hmd hq

theorem c6_classical_endpoint_not_promoted : ¬ Nonempty (ProofCertificate k6_dependency.target) :=
  c5_classical_endpoint_not_promoted

theorem c6_k10_not_promoted : ¬ Nonempty (ProofCertificate k10_obligation_node) :=
  c5_k10_not_promoted

end CircuitC6
end MCore
