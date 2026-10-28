import MCore.Real.P01FullVerifierInputShuttleV2
import MCore.Real.P01PhysicalVerifierFoundations
import MCore.Real.P01PhysicalVerifierBudget

namespace MCore
namespace Real
namespace P01PhysicalVerifierUniformCosts

open CanonicalFinalProof
open CanonicalCircuitBits
open CanonicalSATWitness
open P01FullVerifierStackSemantics
open P01FullVerifierInputShuttleV2
open P01PhysicalVerifierFoundations
open P01PhysicalVerifierBudget

/-- On every reachable semantic evaluation stack, we only need the coarse
invariant that stack depth is bounded by the number of instructions already
processed, hence by the total program length and therefore by canonical input
length.  This predicate is deliberately numerical: it does not smuggle any
machine execution into the bound proof. -/
def StackLengthBound
    (phi : CircuitK1.Circuit) (stack : List Bool) : Prop :=
  stack.length ≤ (encodeCircuit phi).length

/-- Every valid finite witness index is bounded by canonical source length. -/
theorem witness_index_lt_source_length
    {phi : CircuitK1.Circuit}
    (w : SATWitness phi)
    (i : Nat)
    (hi : i < (witnessBits w).length) :
    i < (encodeCircuit phi).length := by
  exact Nat.lt_of_lt_of_le hi (witness_fits_canonical_input w)

/-- The physical V2 witness shuttle offset is uniformly linear in the canonical
source length whenever stack depth is bounded by source length. -/
theorem witnessOffsetV2_le_linear
    {phi : CircuitK1.Circuit}
    (w : SATWitness phi)
    (stack : List Bool)
    (i : Nat)
    (hstack : StackLengthBound phi stack)
    (hi : i < (witnessBits w).length) :
    witnessOffsetV2 stack (encodeCircuit phi) i ≤
      3 * ((encodeCircuit phi).length + 1) := by
  have hi' : i < (encodeCircuit phi).length :=
    witness_index_lt_source_length w i hi
  unfold witnessOffsetV2 StackLengthBound at *
  omega

/-- Hence a complete witness round trip is uniformly linear as well. -/
theorem witness_roundTripV2_le_linear
    {phi : CircuitK1.Circuit}
    (w : SATWitness phi)
    (stack : List Bool)
    (i : Nat)
    (hstack : StackLengthBound phi stack)
    (hi : i < (witnessBits w).length) :
    (moveToWitnessSeqV2 stack (encodeCircuit phi) i ++
      moveBackToStackSeqV2 stack (encodeCircuit phi) i).length ≤
      6 * ((encodeCircuit phi).length + 1) := by
  rw [witness_roundTripV2_length]
  have h :=
    witnessOffsetV2_le_linear w stack i hstack hi
  omega

/-- A uniform per-instruction envelope used by the global verifier budget.
The constant additive allowance covers finite local push/pop/ALU control. -/
def physicalInstructionCostBound (n : Nat) : Nat :=
  8 * (n + 1)

/-- The envelope itself is polynomial, with degree one. -/
theorem physicalInstructionCostBound_poly :
    PolynomialTimeBound physicalInstructionCostBound := by
  refine ⟨8, 1, ?_⟩
  intro n
  simp [physicalInstructionCostBound]

/-- Every witness round trip fits inside the per-instruction physical envelope. -/
theorem witness_roundTripV2_le_instruction_cost
    {phi : CircuitK1.Circuit}
    (w : SATWitness phi)
    (stack : List Bool)
    (i : Nat)
    (hstack : StackLengthBound phi stack)
    (hi : i < (witnessBits w).length) :
    (moveToWitnessSeqV2 stack (encodeCircuit phi) i ++
      moveBackToStackSeqV2 stack (encodeCircuit phi) i).length ≤
      physicalInstructionCostBound (encodeCircuit phi).length := by
  have h := witness_roundTripV2_le_linear w stack i hstack hi
  unfold physicalInstructionCostBound
  omega

/-- If at most n semantic instructions are executed and each physical
instruction costs at most 8(n+1), the whole evaluation phase is bounded by
8(n+1)^2.  This is intentionally independent of phi, w and instruction data. -/
theorem total_instruction_cost_quadratic
    (m n : Nat)
    (hm : m ≤ n) :
    m * physicalInstructionCostBound n ≤ 8 * (n + 1) ^ 2 := by
  unfold physicalInstructionCostBound
  have hm' : m ≤ n + 1 := Nat.le_trans hm (Nat.le_succ n)
  have hmul :
      m * (n + 1) ≤ (n + 1) * (n + 1) :=
    Nat.mul_le_mul_right (n + 1) hm'
  calc
    m * (8 * (n + 1)) = 8 * (m * (n + 1)) := by
      simp [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]
    _ ≤ 8 * ((n + 1) * (n + 1)) :=
      Nat.mul_le_mul_left 8 hmul
    _ = 8 * (n + 1) ^ 2 := by
      simp [Nat.pow_two]

/-- The certified semantic evaluator executes no more than n instructions when
n is the canonical encoded source length, so the physical instruction budget
is quadratically bounded once the one-machine refinement theorem is supplied. -/
theorem evalProgram_physical_cost_quadratic
    (phi : CircuitK1.Circuit) :
    (evalProgram phi).length *
        physicalInstructionCostBound (encodeCircuit phi).length
      ≤ 8 * ((encodeCircuit phi).length + 1) ^ 2 := by
  exact total_instruction_cost_quadratic
    (evalProgram phi).length
    (encodeCircuit phi).length
    (program_fits_canonical_input phi)

#print axioms MCore.Real.P01PhysicalVerifierUniformCosts.witnessOffsetV2_le_linear
#print axioms MCore.Real.P01PhysicalVerifierUniformCosts.witness_roundTripV2_le_linear
#print axioms MCore.Real.P01PhysicalVerifierUniformCosts.physicalInstructionCostBound_poly
#print axioms MCore.Real.P01PhysicalVerifierUniformCosts.total_instruction_cost_quadratic
#print axioms MCore.Real.P01PhysicalVerifierUniformCosts.evalProgram_physical_cost_quadratic

end P01PhysicalVerifierUniformCosts
end Real
end MCore
