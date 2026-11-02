import MCore.CircuitC4

namespace MCore
namespace CircuitC5

open CircuitK1 CircuitC2 CircuitC3 CircuitC4

/-- Propositional structural condition: the finite family contains a member
with positive weight and positive circuit-potential drop. -/
def PositiveDropWitness (sample : List WeightedRestriction) (c : Circuit) : Prop :=
  ∃ x ∈ sample, 0 < x.weight ∧ 0 < drop x.restriction c

/-- Weighted drop dominates the contribution of any member of the sample. -/
theorem member_contribution_le_weightedDrop
    (sample : List WeightedRestriction) (c : Circuit) (x : WeightedRestriction)
    (hx : x ∈ sample) :
    x.weight * drop x.restriction c ≤ weightedDrop sample c := by
  induction sample with
  | nil => simp at hx
  | cons a rest ih =>
      simp only [List.mem_cons] at hx
      simp [weightedDrop]
      rcases hx with rfl | hx
      · exact Nat.le_add_right _ _
      · exact Nat.le_trans (ih hx) (Nat.le_add_left _ _)

/-- A positive-weight member with positive drop is sufficient for positive
weighted drop of the whole finite family. -/
theorem positive_witness_implies_weightedDrop_positive
    (sample : List WeightedRestriction) (c : Circuit)
    (h : PositiveDropWitness sample c) :
    0 < weightedDrop sample c := by
  rcases h with ⟨x, hx, hw, hd⟩
  have hp : 0 < x.weight * drop x.restriction c := Nat.mul_pos hw hd
  exact Nat.lt_of_lt_of_le hp (member_contribution_le_weightedDrop sample c x hx)

/-- The C4 demo family has an explicit positive-drop witness. -/
theorem demoPositiveWitness : PositiveDropWitness demoSample reducibleExample := by
  refine ⟨{ restriction := fixesZeroTrue, weight := 1 }, ?_, by decide, ?_⟩
  · simp [demoSample]
  · simp [drop, potential, restrictedSimplified, reducibleExample,
      fixesZeroTrue, restrict, simplify, μ, size, depth]

theorem demo_positive_from_structural_condition :
    0 < weightedDrop demoSample reducibleExample :=
  positive_witness_implies_weightedDrop_positive demoSample reducibleExample demoPositiveWitness

/-- The zero-drop adversarial family has no positive-drop witness on oneInput. -/
theorem zero_sample_has_no_positive_witness :
    ¬ PositiveDropWitness zeroDropSample oneInput := by
  rintro ⟨x, hx, _hw, hd⟩
  have hx' : x = { restriction := leavesZeroFree, weight := 1 } := by
    simpa [zeroDropSample] using hx
  subst x
  simpa [drop, potential, restrictedSimplified, leavesZeroFree, oneInput,
    restrict, simplify, μ, size, depth] using hd

/-- The structural sufficient condition is not universal over arbitrary samples
and circuits. -/
theorem not_every_family_has_positive_witness :
    ¬ (∀ (sample : List WeightedRestriction) (c : Circuit),
      0 < totalWeight sample → PositiveDropWitness sample c) := by
  intro h
  exact zero_sample_has_no_positive_witness (h zeroDropSample oneInput (by simp))

theorem c5_classical_endpoint_not_promoted : ¬ Nonempty (ProofCertificate k6_dependency.target) :=
  c4_classical_endpoint_not_promoted

theorem c5_k10_not_promoted : ¬ Nonempty (ProofCertificate k10_obligation_node) :=
  c4_k10_not_promoted

end CircuitC5
end MCore
