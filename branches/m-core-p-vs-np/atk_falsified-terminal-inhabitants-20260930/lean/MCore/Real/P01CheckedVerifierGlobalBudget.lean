import MCore.Real.P01CheckedVerifierBudget
import MCore.Real.P01EncodedStackEvaluator

namespace MCore
namespace Real
namespace P01CheckedVerifierGlobalBudget

open CanonicalFinalProof
open CanonicalCircuitBits
open P01EncodedStackEvaluator
open P01CheckedVerifierBudget

/-- Global cubic envelope used by the checked verifier packaging.

The coefficient deliberately leaves room for the source-end scan / verifier
entry in addition to all semantic evaluator transitions. -/
def checkedVerifierGlobalTimeBound : TimeBound :=
  fun n => 512 * (n + 1) ^ 3

theorem checkedVerifierGlobalTimeBound_poly :
    PolynomialTimeBound checkedVerifierGlobalTimeBound := by
  refine ⟨512, 3, ?_⟩
  intro n
  exact Nat.le_refl _

/-- All physical evaluator transitions for one encoded circuit fit below
384·(n+1)^3 whenever the canonical encoding fits in n bits.

This is the exact arithmetic bridge between:
* semantic transition count <= 3·|encodeCircuit phi|;
* checked physical cost per transition <= 128·(n+1)^2. -/
theorem evalStepCount_mul_checkedEnvelope_le
    (n : Nat) (phi : CircuitK1.Circuit)
    (henc : (encodeCircuit phi).length ≤ n) :
    evalStepCount phi * checkedStepEnvelope n ≤
      384 * (n + 1) ^ 3 := by
  have hsteps :
      evalStepCount phi ≤ 3 * n := by
    exact Nat.le_trans
      (evalStepCount_le_three_mul_encoding phi)
      (Nat.mul_le_mul_left 3 henc)
  unfold checkedStepEnvelope
  have hmul :
      evalStepCount phi * (128 * (n + 1) ^ 2) ≤
        (3 * n) * (128 * (n + 1) ^ 2) :=
    Nat.mul_le_mul_right (128 * (n + 1) ^ 2) hsteps
  have hn : n ≤ n + 1 := Nat.le_succ n
  have hcube :
      (3 * n) * (128 * (n + 1) ^ 2) ≤
        384 * (n + 1) ^ 3 := by
    calc
      (3 * n) * (128 * (n + 1) ^ 2)
          = 384 * (n * (n + 1) ^ 2) := by
              ring
      _ ≤ 384 * ((n + 1) * (n + 1) ^ 2) := by
              exact Nat.mul_le_mul_left 384
                (Nat.mul_le_mul_right ((n + 1) ^ 2) hn)
      _ = 384 * (n + 1) ^ 3 := by
              simp [Nat.pow_succ, Nat.mul_assoc]
  exact Nat.le_trans hmul hcube

/-- A quadratic scan/entry allowance fits in the remaining quarter of the
global cubic envelope. -/
theorem scanEntryEnvelope_le
    (n : Nat) :
    128 * (n + 1) ^ 2 ≤
      128 * (n + 1) ^ 3 := by
  have h : (n + 1) ^ 2 ≤ (n + 1) ^ 3 := by
    rw [show (n + 1) ^ 3 = (n + 1) ^ 2 * (n + 1) by
      simp [Nat.pow_succ, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc]]
    exact Nat.le_mul_of_pos_right _ (by omega)
  exact Nat.mul_le_mul_left 128 h

/-- Evaluator work plus source scan/entry fits the single 512-cubic budget. -/
theorem evaluation_plus_scan_le_global
    (n : Nat) (phi : CircuitK1.Circuit)
    (henc : (encodeCircuit phi).length ≤ n) :
    evalStepCount phi * checkedStepEnvelope n +
        128 * (n + 1) ^ 2 ≤
      checkedVerifierGlobalTimeBound n := by
  have heval :=
    evalStepCount_mul_checkedEnvelope_le n phi henc
  have hscan := scanEntryEnvelope_le n
  unfold checkedVerifierGlobalTimeBound
  have hsum :
      384 * (n + 1) ^ 3 + 128 * (n + 1) ^ 3 =
        512 * (n + 1) ^ 3 := by
    ring
  calc
    evalStepCount phi * checkedStepEnvelope n +
          128 * (n + 1) ^ 2
        ≤ 384 * (n + 1) ^ 3 + 128 * (n + 1) ^ 3 :=
          Nat.add_le_add heval hscan
    _ = 512 * (n + 1) ^ 3 := hsum

#print axioms MCore.Real.P01CheckedVerifierGlobalBudget.checkedVerifierGlobalTimeBound_poly
#print axioms MCore.Real.P01CheckedVerifierGlobalBudget.evalStepCount_mul_checkedEnvelope_le
#print axioms MCore.Real.P01CheckedVerifierGlobalBudget.scanEntryEnvelope_le
#print axioms MCore.Real.P01CheckedVerifierGlobalBudget.evaluation_plus_scan_le_global

end P01CheckedVerifierGlobalBudget
end Real
end MCore
