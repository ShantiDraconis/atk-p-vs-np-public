import MCore.Real.P01MaterialGlobalBudget
import MCore.Real.P01CheckedEvalRunBoundedCertificate
import MCore.Real.P01CheckedVerifierInvariant

namespace MCore
namespace Real
namespace P01CoreDecodeFailureBudget

open CanonicalFinalProof
open CanonicalCircuitBits
open CircuitK1
open P01CheckedEvalRunBoundedCertificate
open P01CheckedVerifierGlobalBudget
open P01MaterialGlobalBudget

/-- Source-length potential for malformed recursive decoding.

One source bit carries 32 common loop envelopes. At the root this is bounded
by the existing 8192-cubic material envelope.
-/
def coreRejectPotential (sourceLength n : Nat) : Nat :=
  32 * (sourceLength + 1) * checkedLoopStepEnvelope n

theorem loop_le_potential
    (sourceLength n : Nat) :
    checkedLoopStepEnvelope n ≤ coreRejectPotential sourceLength n := by
  unfold coreRejectPotential
  have hc : 1 ≤ 32 * (sourceLength + 1) := by omega
  simpa [Nat.mul_assoc] using
    Nat.mul_le_mul_right (checkedLoopStepEnvelope n) hc

theorem tag_plus_recursive_le
    (restLength n : Nat) :
    checkedLoopStepEnvelope n +
        coreRejectPotential restLength n ≤
      coreRejectPotential (restLength + 3) n := by
  unfold coreRejectPotential
  rw [← Nat.add_mul]
  exact Nat.mul_le_mul_right (checkedLoopStepEnvelope n) (by omega)

theorem eval_budget_le_encoding_units
    (phi : Circuit) (n : Nat) :
    checkedCircuitBudget phi n ≤
      (24 * (encodeCircuit phi).length + 8) *
        checkedLoopStepEnvelope n := by
  have hs :
      evalStepCount phi ≤ 3 * (encodeCircuit phi).length :=
    evalStepCount_le_three_mul_encoding phi
  have hc :
      8 * (evalStepCount phi + 1) ≤
        24 * (encodeCircuit phi).length + 8 := by
    omega
  unfold checkedCircuitBudget
  exact Nat.mul_le_mul_right (checkedLoopStepEnvelope n) hc

/-- Root tag + a whole valid left child + binary continuation + recursive
failure in the right child fit in the potential of the complete parent source.
-/
theorem binary_right_path_le
    (phi : Circuit) (rightLength n : Nat) :
    checkedLoopStepEnvelope n +
        checkedCircuitBudget phi n +
        checkedLoopStepEnvelope n +
        coreRejectPotential rightLength n ≤
      coreRejectPotential
        (3 + (encodeCircuit phi).length + rightLength) n := by
  let E := checkedLoopStepEnvelope n
  have he :=
    eval_budget_le_encoding_units phi n
  have hsum :
      checkedLoopStepEnvelope n +
          checkedCircuitBudget phi n +
          checkedLoopStepEnvelope n +
          coreRejectPotential rightLength n ≤
        (1 + (24 * (encodeCircuit phi).length + 8) + 1 +
          32 * (rightLength + 1)) * E := by
    unfold coreRejectPotential
    dsimp [E]
    exact Nat.add_le_add
      (Nat.add_le_add
        (Nat.le_refl _)
        (Nat.add_le_add he (Nat.le_refl _)))
      (Nat.le_refl _)
  have hc :
      1 + (24 * (encodeCircuit phi).length + 8) + 1 +
          32 * (rightLength + 1) ≤
        32 * (3 + (encodeCircuit phi).length + rightLength + 1) := by
    omega
  have hmul :=
    Nat.mul_le_mul_right E hc
  unfold coreRejectPotential
  exact Nat.le_trans hsum (by
    simpa [E, Nat.add_assoc] using hmul)

/-- Root tag plus immediate rejection while attempting the first decoded child
also fits in the parent potential. -/
theorem binary_left_semantic_reject_le
    (phi : Circuit) (rightLength n : Nat) :
    checkedLoopStepEnvelope n +
        checkedCircuitBudget phi n ≤
      coreRejectPotential
        (3 + (encodeCircuit phi).length + rightLength) n := by
  let E := checkedLoopStepEnvelope n
  have he := eval_budget_le_encoding_units phi n
  have hsum :
      checkedLoopStepEnvelope n + checkedCircuitBudget phi n ≤
        (1 + (24 * (encodeCircuit phi).length + 8)) * E := by
    dsimp [E]
    exact Nat.add_le_add (Nat.le_refl _) he
  have hc :
      1 + (24 * (encodeCircuit phi).length + 8) ≤
        32 * (3 + (encodeCircuit phi).length + rightLength + 1) := by
    omega
  have hmul := Nat.mul_le_mul_right E hc
  unfold coreRejectPotential
  exact Nat.le_trans hsum (by
    simpa [E, Nat.add_assoc] using hmul)

/-- At root, source potential is below the global material cubic envelope. -/
theorem root_potential_le_material
    (sourceLength n : Nat)
    (h : sourceLength ≤ n) :
    coreRejectPotential sourceLength n ≤
      materialVerifierGlobalTimeBound n := by
  unfold coreRejectPotential checkedLoopStepEnvelope
    materialVerifierGlobalTimeBound
  have hc : 32 * (sourceLength + 1) ≤ 32 * (n + 1) :=
    Nat.mul_le_mul_left 32 (by omega)
  have hmul :=
    Nat.mul_le_mul_right (256 * (n + 1)^2) hc
  calc
    32 * (sourceLength + 1) * (256 * (n + 1)^2)
        ≤ 32 * (n + 1) * (256 * (n + 1)^2) := hmul
    _ = 8192 * (n + 1)^3 := by
      simp [Nat.pow_succ, Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]

#print axioms MCore.Real.P01CoreDecodeFailureBudget.tag_plus_recursive_le
#print axioms MCore.Real.P01CoreDecodeFailureBudget.binary_right_path_le
#print axioms MCore.Real.P01CoreDecodeFailureBudget.root_potential_le_material

end P01CoreDecodeFailureBudget
end Real
end MCore
