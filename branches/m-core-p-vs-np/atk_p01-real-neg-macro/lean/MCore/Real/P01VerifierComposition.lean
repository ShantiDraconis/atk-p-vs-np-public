import MCore.Real.P01ParserWitnessComposition
import MCore.Real.CanonicalSATVerifier

namespace MCore
namespace Real
namespace P01VerifierComposition

open CanonicalFinalProof
open CanonicalCircuitBits
open CanonicalSATWitness
open CanonicalSATVerifier
open P01VerifiedRelation

/-- T1.3 semantic verifier correctness, reused without endpoint assumptions. -/
theorem verifier_correct
    (φ : CircuitK1.Circuit)
    (w : SATWitness φ) :
    verifyWitness φ w = true ↔ SATWitnessAccepts φ w :=
  verifyWitness_correct φ w

/-- The high-level verifier work measure is linearly bounded by the canonical
encoding length. This is deliberately not renamed as a TM step theorem. -/
theorem verifier_cost_linear
    (φ : CircuitK1.Circuit) :
    verificationCost φ ≤ 2 * (encodeCircuit φ).length :=
  verificationCost_linear_encoding_bound φ

/-- Exact semantic composition needed by the eventual integrated machine:
successful canonical decoding plus a verified finite witness is equivalent to
SATBits. -/
theorem decode_verify_iff_satBits
    (x : BitString) :
    (∃ φ : CircuitK1.Circuit,
        decodeCircuit x = some φ ∧
        ∃ w : SATWitness φ, verifyWitness φ w = true) ↔
      CanonicalSATBoundary.SATBits circuitBitEncoding x :=
  (satBits_iff_verified_witness x).symm

#print axioms MCore.Real.P01VerifierComposition.verifier_correct
#print axioms MCore.Real.P01VerifierComposition.verifier_cost_linear
#print axioms MCore.Real.P01VerifierComposition.decode_verify_iff_satBits

end P01VerifierComposition
end Real
end MCore
