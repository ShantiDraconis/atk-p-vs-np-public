import MCore.Real.P01FullVerifierStackSemantics
import MCore.Real.CanonicalFinalProof

namespace MCore
namespace Real
namespace P01PhysicalVerifierBudget

open CanonicalFinalProof
open P01FullVerifierStackSemantics

/-- A fixed cubic envelope for the physical verifier.  The constant is part of
one machine-level budget and is independent of the circuit, witness and input
indices.  This theorem supplies only the polynomial field; halting within this
budget must still be proved for the concrete fixed TM. -/
def physicalVerifierTimeBound : TimeBound :=
  fun n => 16 * (n + 1) ^ 3

theorem physicalVerifierTimeBound_poly :
    PolynomialTimeBound physicalVerifierTimeBound := by
  refine ⟨16, 3, ?_⟩
  intro n
  exact Nat.le_refl _

/-- The semantic stack program has at most n instructions when n is the
canonical circuit encoding length. -/
theorem evalProgram_steps_le_input_length
    (phi : CircuitK1.Circuit) :
    (evalProgram phi).length ≤ (CanonicalCircuitBits.encodeCircuit phi).length := by
  exact evalProgram_length_le_encoding phi

/-- A convenient quadratic shuttle envelope for any index bounded by n. -/
def perInstructionEnvelope (n : Nat) : Nat :=
  4 * (n + 1) ^ 2

theorem accumulated_instruction_envelope
    (m n : Nat) (hm : m ≤ n) :
    m * perInstructionEnvelope n ≤ 4 * (n + 1) ^ 3 := by
  unfold perInstructionEnvelope
  have hmn1 : m ≤ n + 1 := Nat.le_trans hm (Nat.le_succ n)
  calc
    m * (4 * (n + 1) ^ 2)
        = 4 * (m * (n + 1) ^ 2) := by
          simp [Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm]
    _ ≤ 4 * ((n + 1) * (n + 1) ^ 2) := by
      exact Nat.mul_le_mul_left 4
        (Nat.mul_le_mul_right ((n + 1) ^ 2) hmn1)
    _ = 4 * (n + 1) ^ 3 := by
      simp [Nat.pow_succ, Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]

#print axioms MCore.Real.P01PhysicalVerifierBudget.physicalVerifierTimeBound_poly
#print axioms MCore.Real.P01PhysicalVerifierBudget.evalProgram_steps_le_input_length
#print axioms MCore.Real.P01PhysicalVerifierBudget.accumulated_instruction_envelope

end P01PhysicalVerifierBudget
end Real
end MCore
