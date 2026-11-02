import MCore.Real.CanonicalSATVerifier

namespace MCore
namespace Real
namespace P01WitnessBoundNormalization

open CircuitK1
open CanonicalFinalProof
open CanonicalCircuitBits
open CanonicalSATWitness
open CanonicalSATVerifier

/-- Interpret an arbitrary finite bitstring as a total Boolean assignment,
padding with false after the end. -/
def assignmentOfBits (bits : BitString) : Assignment :=
  fun i => bits.getD i false

/-- Canonical finite witness obtained from an arbitrary guessed bitstring.
Only indices strictly below varBound are retained by the dependent type. -/
def witnessOfBits (phi : Circuit) (bits : BitString) : SATWitness phi :=
  fun i => bits.getD i.val false

/-- Inside the canonical variable bound, the dependent witness and the raw
bitstring assignment agree exactly. -/
theorem assignmentOfWitness_witnessOfBits_agrees
    (phi : Circuit) (bits : BitString) :
    forall i, i < varBound phi ->
      assignmentOfWitness phi (witnessOfBits phi bits) i =
        assignmentOfBits bits i := by
  intro i hi
  simp [assignmentOfWitness, witnessOfBits, assignmentOfBits, hi]

/-- Normalizing an arbitrary bitstring to SATWitness does not change circuit
evaluation relative to the raw bitstring assignment. Bits outside varBound are
therefore semantically inert. -/
theorem evalCircuit_witnessOfBits_eq
    (phi : Circuit) (bits : BitString) :
    evalCircuit (assignmentOfWitness phi (witnessOfBits phi bits)) phi =
      evalCircuit (assignmentOfBits bits) phi := by
  apply evalCircuit_eq_of_agree_below
  exact assignmentOfWitness_witnessOfBits_agrees phi bits

/-- Two guessed bitstrings that agree below varBound induce identical circuit
semantics, regardless of any excess suffix. -/
theorem excess_bits_ignored
    (phi : Circuit) (a b : BitString)
    (hAgree : forall i, i < varBound phi ->
      a.getD i false = b.getD i false) :
    evalCircuit (assignmentOfBits a) phi =
      evalCircuit (assignmentOfBits b) phi := by
  apply evalCircuit_eq_of_agree_below
  intro i hi
  exact hAgree i hi

/-- The normalized representation always has exactly the canonical witness
length, independent of how many excess bits the preparation phase guessed. -/
def normalizedWitnessBits (phi : Circuit) (bits : BitString) : BitString :=
  witnessBits (witnessOfBits phi bits)

theorem normalizedWitnessBits_length
    (phi : Circuit) (bits : BitString) :
    (normalizedWitnessBits phi bits).length = varBound phi := by
  simp [normalizedWitnessBits, witnessBits_length]

/-- The canonical witness extracted from a source-length guess is always short
enough for the canonical encoding. -/
theorem normalizedWitnessBits_le_encoding
    (phi : Circuit) (bits : BitString) :
    (normalizedWitnessBits phi bits).length <= (encodeCircuit phi).length := by
  rw [normalizedWitnessBits_length phi bits]
  exact varBound_le_encoded_length phi

/-- Verification of the normalized dependent witness is the same Boolean
circuit evaluation as reading the original guessed bitstring below varBound,
apart from the independent CNF well-formedness guard. -/
theorem verifyWitness_normalized
    (phi : Circuit) (bits : BitString) :
    verifyWitness phi (witnessOfBits phi bits) =
      Bool.and (isCNFBool phi) (evalCircuit (assignmentOfBits bits) phi) := by
  unfold verifyWitness
  rw [evalCircuit_witnessOfBits_eq]

#print axioms MCore.Real.P01WitnessBoundNormalization.assignmentOfWitness_witnessOfBits_agrees
#print axioms MCore.Real.P01WitnessBoundNormalization.evalCircuit_witnessOfBits_eq
#print axioms MCore.Real.P01WitnessBoundNormalization.excess_bits_ignored
#print axioms MCore.Real.P01WitnessBoundNormalization.normalizedWitnessBits_length
#print axioms MCore.Real.P01WitnessBoundNormalization.normalizedWitnessBits_le_encoding
#print axioms MCore.Real.P01WitnessBoundNormalization.verifyWitness_normalized

end P01WitnessBoundNormalization
end Real
end MCore
