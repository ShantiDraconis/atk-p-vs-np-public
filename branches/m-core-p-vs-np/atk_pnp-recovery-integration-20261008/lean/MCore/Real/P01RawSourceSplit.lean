import MCore.Real.P01GuessedWitnessRelation

namespace MCore
namespace Real
namespace P01RawSourceSplit

open CanonicalFinalProof
open CircuitK1
open CanonicalCircuitBits
open P01GuessedWitnessRelation

/-- Every raw source either is exactly one canonical circuit encoding or the
canonical decoder fails.  This is purely semantic and introduces no new
machine assumption. -/
theorem exact_encoding_or_decode_none
    (bs : BitString) :
    (∃ phi : Circuit, bs = encodeCircuit phi) ∨
      decodeCircuit bs = none := by
  cases hdec : decodeCircuit bs with
  | none =>
      exact Or.inr rfl
  | some phi =>
      have hdec' : decodeCircuit bs = some phi := by simpa using hdec
      exact Or.inl ⟨phi, decodeCircuit_sound bs phi hdec'⟩

/-- Decoder failure makes the concrete verifier relation false for every
witness. -/
theorem verifyBits_false_of_decode_none
    (bs w : BitString)
    (hdec : decodeCircuit bs = none) :
    ¬ VerifyBits bs w := by
  intro h
  rcases h with ⟨phi, hphi, hcnf, heval⟩
  rw [hdec] at hphi
  cases hphi


#print axioms MCore.Real.P01RawSourceSplit.exact_encoding_or_decode_none
#print axioms MCore.Real.P01RawSourceSplit.verifyBits_false_of_decode_none

end P01RawSourceSplit
end Real
end MCore
