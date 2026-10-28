import MCore.Real.P01CheckedVerifierBudget
import MCore.Real.P01EncodedStackEvaluator

namespace MCore
namespace Real
namespace P01CheckedVerifierGlobalBudget

open CanonicalFinalProof
open CanonicalCircuitBits
open P01EncodedStackEvaluator
open P01CheckedVerifierBudget

/-- Uniform per-semantic-step envelope for the checked evaluator.

The checked 000 input route includes the syntax/tag guard in addition to the
already-bounded physical input primitive, so its certified coefficient is 256,
not the 128 coefficient of the unchecked evalStep core. -/
def checkedLoopStepEnvelope (n : Nat) : Nat :=
  256 * (n + 1) ^ 2

/-- Global cubic envelope used by the checked verifier packaging.

Three semantic transitions per encoded source bit, each under the checked
quadratic envelope, cost at most 768·(n+1)^3.  The coefficient 1024 leaves
another 256·(n+1)^3 for the source-end scan, verifier entry, and terminal
normalization. -/
def checkedVerifierGlobalTimeBound : TimeBound :=
  fun n => 1024 * (n + 1) ^ 3

theorem checkedVerifierGlobalTimeBound_poly :
    PolynomialTimeBound checkedVerifierGlobalTimeBound := by
  refine ⟨1024, 3, ?_⟩
  intro n
  exact Nat.le_refl _

theorem checkedStepEnvelope_le_loopEnvelope
    (n : Nat) :
    checkedStepEnvelope n ≤ checkedLoopStepEnvelope n := by
  unfold checkedStepEnvelope checkedLoopStepEnvelope
  exact Nat.mul_le_mul_right ((n + 1) ^ 2) (by omega)

/-- All checked evaluator transitions for one encoded circuit fit below
768·(n+1)^3 whenever the canonical encoding fits in n bits. -/
theorem evalStepCount_mul_checkedLoopEnvelope_le
    (n : Nat) (phi : CircuitK1.Circuit)
    (henc : (encodeCircuit phi).length ≤ n) :
    evalStepCount phi * checkedLoopStepEnvelope n ≤
      768 * (n + 1) ^ 3 := by
  have hsteps :
      evalStepCount phi ≤ 3 * n := by
    exact Nat.le_trans
      (evalStepCount_le_three_mul_encoding phi)
      (Nat.mul_le_mul_left 3 henc)
  unfold checkedLoopStepEnvelope
  have hmul :
      evalStepCount phi * (256 * (n + 1) ^ 2) ≤
        (3 * n) * (256 * (n + 1) ^ 2) :=
    Nat.mul_le_mul_right (256 * (n + 1) ^ 2) hsteps
  have hn : n ≤ n + 1 := Nat.le_succ n
  have hcube :
      (3 * n) * (256 * (n + 1) ^ 2) ≤
        768 * (n + 1) ^ 3 := by
    calc
      (3 * n) * (256 * (n + 1) ^ 2)
          = 768 * (n * (n + 1) ^ 2) := by
              simp [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]
      _ ≤ 768 * ((n + 1) * (n + 1) ^ 2) := by
              exact Nat.mul_le_mul_left 768
                (Nat.mul_le_mul_right ((n + 1) ^ 2) hn)
      _ = 768 * (n + 1) ^ 3 := by
              simp [Nat.pow_succ, Nat.mul_assoc]
  exact Nat.le_trans hmul hcube

/-- A checked quadratic scan/entry allowance fits in the remaining quarter of
the global cubic envelope. -/
theorem checkedScanEntryEnvelope_le
    (n : Nat) :
    256 * (n + 1) ^ 2 ≤
      256 * (n + 1) ^ 3 := by
  have h1 : 1 ≤ n + 1 := by omega
  have hmul :
      (n + 1) ^ 2 ≤ (n + 1) ^ 2 * (n + 1) := by
    simpa using Nat.mul_le_mul_left ((n + 1) ^ 2) h1
  have hpow :
      (n + 1) ^ 2 ≤ (n + 1) ^ 3 := by
    simpa [Nat.pow_succ, Nat.mul_assoc] using hmul
  exact Nat.mul_le_mul_left 256 hpow

/-- Evaluator work plus source scan/entry fits the single 1024-cubic budget. -/
theorem evaluation_plus_scan_le_global
    (n : Nat) (phi : CircuitK1.Circuit)
    (henc : (encodeCircuit phi).length ≤ n) :
    evalStepCount phi * checkedLoopStepEnvelope n +
        256 * (n + 1) ^ 2 ≤
      checkedVerifierGlobalTimeBound n := by
  have heval :=
    evalStepCount_mul_checkedLoopEnvelope_le n phi henc
  have hscan := checkedScanEntryEnvelope_le n
  unfold checkedVerifierGlobalTimeBound
  have hsum :
      768 * (n + 1) ^ 3 + 256 * (n + 1) ^ 3 =
        1024 * (n + 1) ^ 3 := by
    omega
  calc
    evalStepCount phi * checkedLoopStepEnvelope n +
          256 * (n + 1) ^ 2
        ≤ 768 * (n + 1) ^ 3 + 256 * (n + 1) ^ 3 :=
          Nat.add_le_add heval hscan
    _ = 1024 * (n + 1) ^ 3 := hsum

#print axioms MCore.Real.P01CheckedVerifierGlobalBudget.checkedVerifierGlobalTimeBound_poly
#print axioms MCore.Real.P01CheckedVerifierGlobalBudget.checkedStepEnvelope_le_loopEnvelope
#print axioms MCore.Real.P01CheckedVerifierGlobalBudget.evalStepCount_mul_checkedLoopEnvelope_le
#print axioms MCore.Real.P01CheckedVerifierGlobalBudget.checkedScanEntryEnvelope_le
#print axioms MCore.Real.P01CheckedVerifierGlobalBudget.evaluation_plus_scan_le_global

end P01CheckedVerifierGlobalBudget
end Real
end MCore
