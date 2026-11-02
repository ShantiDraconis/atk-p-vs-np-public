import MCore.Real.P01ExactBoundedCircuitProducer
import MCore.Real.P01CheckedVerifierGlobalBudget

namespace MCore
namespace Real
namespace P01ExactVerifierGlobalBudget

open CanonicalFinalProof
open CanonicalCircuitBits
open P01EncodedStackEvaluator
open P01CheckedVerifierGlobalBudget
open P01ExactBoundedCircuitProducer
open P01CheckedEvalRunBoundedCertificate

/-- Cubic envelope matched to the exact compositional certificate. -/
def checkedVerifierExactTimeBound : TimeBound :=
  fun n => 8192 * (n + 1) ^ 3

theorem checkedVerifierExactTimeBound_poly :
    PolynomialTimeBound checkedVerifierExactTimeBound := by
  refine ⟨8192, 3, ?_⟩
  intro n
  exact Nat.le_refl _

/-- The exact compositional circuit budget is globally cubic whenever the
canonical encoding fits in n bits. -/
theorem checkedCircuitBudget_le_exact_global
    (n : Nat) (phi : CircuitK1.Circuit)
    (henc : (encodeCircuit phi).length ≤ n) :
    checkedCircuitBudget phi n ≤
      6144 * (n + 1) ^ 3 := by
  have hsteps :
      evalStepCount phi + 1 ≤ 3 * (n + 1) := by
    have h0 :
        evalStepCount phi ≤ 3 * n := by
      exact Nat.le_trans
        (evalStepCount_le_three_mul_encoding phi)
        (Nat.mul_le_mul_left 3 henc)
    omega
  unfold checkedCircuitBudget
  unfold checkedLoopStepEnvelope
  have hmul :=
    Nat.mul_le_mul_right (256 * (n + 1) ^ 2)
      (Nat.mul_le_mul_left 8 hsteps)
  calc
    8 * (evalStepCount phi + 1) * (256 * (n + 1) ^ 2)
        ≤ (8 * (3 * (n + 1))) * (256 * (n + 1) ^ 2) := hmul
    _ = 6144 * (n + 1) ^ 3 := by
      simp [Nat.pow_succ, Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]

/-- Exact evaluator budget plus scanner/entry overhead fits one fixed cubic
verifier budget. -/
theorem exact_evaluation_plus_scan_le_global
    (n : Nat) (phi : CircuitK1.Circuit)
    (henc : (encodeCircuit phi).length ≤ n) :
    checkedCircuitBudget phi n +
        256 * (n + 1) ^ 2 ≤
      checkedVerifierExactTimeBound n := by
  have heval := checkedCircuitBudget_le_exact_global n phi henc
  have hscan := checkedScanEntryEnvelope_le n
  unfold checkedVerifierExactTimeBound
  calc
    checkedCircuitBudget phi n + 256 * (n + 1) ^ 2
        ≤ 6144 * (n + 1) ^ 3 + 256 * (n + 1) ^ 3 :=
          Nat.add_le_add heval hscan
    _ ≤ 8192 * (n + 1) ^ 3 := by
      omega

#print axioms MCore.Real.P01ExactVerifierGlobalBudget.checkedVerifierExactTimeBound_poly
#print axioms MCore.Real.P01ExactVerifierGlobalBudget.checkedCircuitBudget_le_exact_global
#print axioms MCore.Real.P01ExactVerifierGlobalBudget.exact_evaluation_plus_scan_le_global

end P01ExactVerifierGlobalBudget
end Real
end MCore
