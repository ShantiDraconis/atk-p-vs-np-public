import MCore.CircuitC3

namespace MCore
namespace CircuitC4

open CircuitK1 CircuitC2 CircuitC3

structure WeightedRestriction where
  restriction : Restriction
  weight : Nat

def weightedDrop (sample : List WeightedRestriction) (c : Circuit) : Nat :=
  sample.foldr (fun x acc => x.weight * drop x.restriction c + acc) 0

def totalWeight (sample : List WeightedRestriction) : Nat :=
  sample.foldr (fun x acc => x.weight + acc) 0

/-- Cross-multiplied finite weighted-average lower bound; no division is used. -/
def ExpectedDropAtLeast
    (sample : List WeightedRestriction) (c : Circuit)
    (numerator denominator : Nat) : Prop :=
  numerator * totalWeight sample ≤ denominator * weightedDrop sample c

def demoSample : List WeightedRestriction :=
  [{ restriction := fixesZeroTrue, weight := 1 },
   { restriction := leavesZeroFree, weight := 1 }]

@[simp] theorem demo_totalWeight : totalWeight demoSample = 2 := by rfl

@[simp] theorem demo_weightedDrop : weightedDrop demoSample reducibleExample = 3 := by
  simp [weightedDrop, demoSample, drop, potential, restrictedSimplified,
    reducibleExample, fixesZeroTrue, leavesZeroFree, restrict, simplify, μ, size, depth]

theorem demo_expected_drop_three_halves :
    ExpectedDropAtLeast demoSample reducibleExample 3 2 := by
  simp [ExpectedDropAtLeast]

def zeroDropSample : List WeightedRestriction :=
  [{ restriction := leavesZeroFree, weight := 1 },
   { restriction := leavesZeroFree, weight := 1 }]

@[simp] theorem zero_sample_weightedDrop :
    weightedDrop zeroDropSample oneInput = 0 := by
  simp [weightedDrop, zeroDropSample, drop, potential, restrictedSimplified,
    leavesZeroFree, oneInput, restrict, simplify, μ, size, depth]

@[simp] theorem zero_sample_totalWeight : totalWeight zeroDropSample = 2 := by rfl

theorem not_all_samples_positive :
    ¬ (∀ (sample : List WeightedRestriction) (c : Circuit),
      0 < totalWeight sample → 0 < weightedDrop sample c) := by
  intro h
  have hs : 0 < weightedDrop zeroDropSample oneInput :=
    h zeroDropSample oneInput (by simp)
  rw [zero_sample_weightedDrop] at hs
  exact Nat.not_lt_zero 0 hs

theorem c4_classical_endpoint_not_promoted : ¬ Nonempty (ProofCertificate k6_dependency.target) :=
  c3_classical_endpoint_not_promoted

theorem c4_k10_not_promoted : ¬ Nonempty (ProofCertificate k10_obligation_node) :=
  c3_k10_not_promoted

end CircuitC4
end MCore
