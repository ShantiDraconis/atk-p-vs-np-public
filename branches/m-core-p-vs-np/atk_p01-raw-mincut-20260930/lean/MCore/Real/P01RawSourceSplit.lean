import MCore.Real.P01GuessedWitnessRelation
import MCore.Real.CanonicalSATSlotParserSpec

namespace MCore
namespace Real
namespace P01RawSourceSplit

open CanonicalFinalProof
open CircuitK1
open CanonicalCircuitBits
open CanonicalSATSlotParserSpec
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
      exact Or.inr hdec
  | some phi =>
      exact Or.inl ⟨phi, decodeCircuit_sound bs phi hdec⟩

/-- Decoder failure makes the concrete verifier relation false for every
witness. -/
theorem verifyBits_false_of_decode_none
    (bs w : BitString)
    (hdec : decodeCircuit bs = none) :
    ¬ VerifyBits bs w := by
  intro h
  rcases h with ⟨phi, hphi, hcnf, heval⟩
  rw [hdec] at hphi
  contradiction

/-- Exact canonical source recovery from parser acceptance. -/
theorem exact_encoding_of_slotAccept
    (bs : BitString)
    (h : slotAccept bs = true) :
    ∃ phi : Circuit, bs = encodeCircuit phi :=
  (slotAccept_iff_exists_exact_encoding bs).1 h

/-- Parser rejection is equivalent to absence of any exact canonical encoding. -/
theorem slotReject_iff_no_exact_encoding
    (bs : BitString) :
    slotAccept bs = false ↔
      ¬ ∃ phi : Circuit, bs = encodeCircuit phi := by
  constructor
  · intro hfalse hex
    have htrue := (slotAccept_iff_exists_exact_encoding bs).2 hex
    rw [hfalse] at htrue
    contradiction
  · intro hnone
    cases h : slotAccept bs with
    | false => exact h
    | true =>
        exfalso
        exact hnone ((slotAccept_iff_exists_exact_encoding bs).1 h)

#print axioms MCore.Real.P01RawSourceSplit.exact_encoding_or_decode_none
#print axioms MCore.Real.P01RawSourceSplit.verifyBits_false_of_decode_none
#print axioms MCore.Real.P01RawSourceSplit.exact_encoding_of_slotAccept
#print axioms MCore.Real.P01RawSourceSplit.slotReject_iff_no_exact_encoding

end P01RawSourceSplit
end Real
end MCore
