import MCore.Real.CanonicalSATWitness

namespace MCore
namespace Real
namespace P01WitnessBoundNormalization

open CircuitK1
open CanonicalFinalProof
open CanonicalCircuitBits
open CanonicalSATWitness

/-- Assignment read directly from a Boolean tape prefix. -/
def assignmentOfBits (bits : BitString) : Assignment :=
  fun i => bits.getD i false

/-- Extend the exact canonical witness to the encoded-source length.
The extension is inert padding only; the canonical witness prefix is unchanged. -/
def paddedWitnessBits
    {φ : Circuit}
    (w : SATWitness φ) : BitString :=
  witnessBits w ++
    List.replicate ((encodeCircuit φ).length - varBound φ) false

theorem paddedWitnessBits_length
    {φ : Circuit}
    (w : SATWitness φ) :
    (paddedWitnessBits w).length = (encodeCircuit φ).length := by
  have hle := varBound_le_encoded_length φ
  simp [paddedWitnessBits, witnessBits_length]
  omega

theorem paddedWitnessBits_agree_below
    {φ : Circuit}
    (w : SATWitness φ)
    (i : Nat)
    (hi : i < varBound φ) :
    assignmentOfBits (paddedWitnessBits w) i =
      assignmentOfWitness φ w i := by
  have hiBits : i < (witnessBits w).length := by
    simpa [witnessBits_length] using hi
  simp [assignmentOfBits, paddedWitnessBits, List.getD,
    List.getElem?_append_left, assignmentOfWitness,
    witnessBits, hi, hiBits]

/-- Padding the guessed witness out to source length is semantically inert. -/
theorem paddedWitnessBits_preserves_eval
    {φ : Circuit}
    (w : SATWitness φ) :
    evalCircuit (assignmentOfBits (paddedWitnessBits w)) φ =
      evalCircuit (assignmentOfWitness φ w) φ := by
  apply evalCircuit_eq_of_agree_below
  intro i hi
  exact paddedWitnessBits_agree_below w i hi

/-- The concrete guesser may guess one bit per encoded-source bit; every exact
canonical SAT witness therefore has a source-length extension accepted by the
same circuit semantics. -/
theorem canonical_witness_has_source_length_extension
    {φ : Circuit}
    (w : SATWitness φ) :
    ∃ bits : BitString,
      bits.length = (encodeCircuit φ).length ∧
      evalCircuit (assignmentOfBits bits) φ =
        evalCircuit (assignmentOfWitness φ w) φ := by
  exact ⟨paddedWitnessBits w, paddedWitnessBits_length w,
    paddedWitnessBits_preserves_eval w⟩

#print axioms MCore.Real.P01WitnessBoundNormalization.paddedWitnessBits_length
#print axioms MCore.Real.P01WitnessBoundNormalization.paddedWitnessBits_agree_below
#print axioms MCore.Real.P01WitnessBoundNormalization.paddedWitnessBits_preserves_eval
#print axioms MCore.Real.P01WitnessBoundNormalization.canonical_witness_has_source_length_extension

end P01WitnessBoundNormalization
end Real
end MCore
