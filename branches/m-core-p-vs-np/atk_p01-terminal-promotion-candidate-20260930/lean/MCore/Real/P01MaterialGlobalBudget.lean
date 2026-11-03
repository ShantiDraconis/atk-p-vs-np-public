import MCore.Real.P01CheckedEvalRunBoundedCertificate
import MCore.Real.P01CheckedVerifierCompositeNTM
import MCore.Real.P01CheckedVerifierDeterminism

namespace MCore
namespace Real
namespace P01MaterialGlobalBudget

open CanonicalFinalProof
open CanonicalCircuitBits
open P01EncodedStackEvaluator
open P01CheckedEvalRunBoundedCertificate
open P01CheckedVerifierGlobalBudget
open P01CheckedVerifierCompositeNTM

/--
Global polynomial envelope compatible with the exact bounded recursive
certificate.  The previous 1024-cubic envelope bounded one semantic-step
accounting.  The exact compositional certificate deliberately carries an
extra factor 8, so the terminal packaging uses the larger, proved envelope.
-/
def materialVerifierGlobalTimeBound : TimeBound :=
  fun n => 8192 * (n + 1) ^ 3

theorem materialVerifierGlobalTimeBound_poly :
    PolynomialTimeBound materialVerifierGlobalTimeBound := by
  refine ⟨8192, 3, ?_⟩
  intro n
  exact Nat.le_refl _

/-- The exact compositional circuit budget fits below 6144 cubic whenever the
canonical encoding fits in the source length. -/
theorem checkedCircuitBudget_le_6144_cubic
    (n : Nat) (phi : CircuitK1.Circuit)
    (henc : (encodeCircuit phi).length ≤ n) :
    checkedCircuitBudget phi n ≤ 6144 * (n + 1) ^ 3 := by
  have hsteps :
      evalStepCount phi ≤ 3 * n := by
    exact Nat.le_trans
      (evalStepCount_le_three_mul_encoding phi)
      (Nat.mul_le_mul_left 3 henc)
  have hsteps1 :
      evalStepCount phi + 1 ≤ 3 * (n + 1) := by
    omega
  have hcoef :
      8 * (evalStepCount phi + 1) ≤ 24 * (n + 1) := by
    have h := Nat.mul_le_mul_left 8 hsteps1
    simpa [Nat.mul_assoc] using h
  unfold checkedCircuitBudget checkedLoopStepEnvelope
  calc
    8 * (evalStepCount phi + 1) * (256 * (n + 1) ^ 2)
        ≤ (24 * (n + 1)) * (256 * (n + 1) ^ 2) :=
          Nat.mul_le_mul_right (256 * (n + 1) ^ 2) hcoef
    _ = 6144 * (n + 1) ^ 3 := by
          simp [Nat.pow_succ, Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]

/-- The whole wrapper-entry allowance is dominated by the remaining quarter
of the 8192-cubic envelope. -/
theorem scan_entry_le_2048_cubic
    (n : Nat) :
    n + 3 ≤ 2048 * (n + 1) ^ 3 := by
  have hlin : n + 3 ≤ 3 * (n + 1) := by omega
  have hpow : 3 * (n + 1) ≤ 3 * (n + 1) ^ 3 := by
    have h1 : 1 ≤ (n + 1)^2 := by
      have hn : 1 ≤ n + 1 := by omega
      have := Nat.mul_le_mul hn hn
      simpa [Nat.pow_two] using this
    calc
      3 * (n + 1) = 3 * (n + 1) * 1 := by simp
      _ ≤ 3 * (n + 1) * (n + 1)^2 :=
        Nat.mul_le_mul_left (3 * (n + 1)) h1
      _ = 3 * (n + 1)^3 := by
        simp [Nat.pow_succ, Nat.mul_assoc]
  have hcoef : 3 * (n + 1)^3 ≤ 2048 * (n + 1)^3 :=
    Nat.mul_le_mul_right ((n + 1)^3) (by omega)
  exact Nat.le_trans hlin (Nat.le_trans hpow hcoef)

/-- Entry plus the exact recursive evaluator budget fits the final material
8192-cubic bound. -/
theorem entry_plus_checkedCircuitBudget_le_material
    (n : Nat) (phi : CircuitK1.Circuit)
    (henc : (encodeCircuit phi).length ≤ n) :
    n + 3 + checkedCircuitBudget phi n ≤
      materialVerifierGlobalTimeBound n := by
  have hentry := scan_entry_le_2048_cubic n
  have heval := checkedCircuitBudget_le_6144_cubic n phi henc
  unfold materialVerifierGlobalTimeBound
  calc
    n + 3 + checkedCircuitBudget phi n
        ≤ 2048 * (n + 1)^3 + 6144 * (n + 1)^3 :=
          Nat.add_le_add hentry heval
    _ = 8192 * (n + 1)^3 := by omega

#print axioms MCore.Real.P01MaterialGlobalBudget.materialVerifierGlobalTimeBound_poly
#print axioms MCore.Real.P01MaterialGlobalBudget.checkedCircuitBudget_le_6144_cubic
#print axioms MCore.Real.P01MaterialGlobalBudget.scan_entry_le_2048_cubic

/-- Final whole-wrapper budget.  The 8192-cubic material budget is reserved
for evaluator work; this doubled envelope also absorbs source scan/handoff
and malformed-source rejection without changing polynomial degree. -/
def terminalVerifierTimeBound : TimeBound :=
  fun n => 16384 * (n + 1) ^ 3

theorem terminalVerifierTimeBound_poly :
    PolynomialTimeBound terminalVerifierTimeBound := by
  refine ⟨16384, 3, ?_⟩
  intro n
  exact Nat.le_refl _

theorem material_le_terminal
    (n : Nat) :
    materialVerifierGlobalTimeBound n ≤ terminalVerifierTimeBound n := by
  unfold materialVerifierGlobalTimeBound terminalVerifierTimeBound
  exact Nat.mul_le_mul_right ((n + 1)^3) (by omega)

theorem entry_plus_material_le_terminal
    (n : Nat) :
    n + 3 + materialVerifierGlobalTimeBound n ≤
      terminalVerifierTimeBound n := by
  have hentry := scan_entry_le_2048_cubic n
  unfold materialVerifierGlobalTimeBound terminalVerifierTimeBound
  calc
    n + 3 + 8192 * (n + 1)^3
        ≤ 2048 * (n + 1)^3 + 8192 * (n + 1)^3 :=
          Nat.add_le_add_right hentry _
    _ ≤ 16384 * (n + 1)^3 := by
          exact Nat.mul_le_mul_right ((n + 1)^3) (by omega)

#print axioms MCore.Real.P01MaterialGlobalBudget.terminalVerifierTimeBound_poly
#print axioms MCore.Real.P01MaterialGlobalBudget.material_le_terminal
#print axioms MCore.Real.P01MaterialGlobalBudget.entry_plus_material_le_terminal

#print axioms MCore.Real.P01MaterialGlobalBudget.entry_plus_checkedCircuitBudget_le_material

end P01MaterialGlobalBudget
end Real
end MCore
