import MCore.Real.CanonicalSATVerifier

namespace MCore
namespace Real
namespace P01VerifiedRelation

open CircuitK1
open CanonicalFinalProof
open CanonicalCircuitBits
open CanonicalSATBoundary
open CanonicalSATWitness
open CanonicalSATVerifier

/-!
Positive P01 reduction: expose SATBits as an exact bounded verifier relation.

This is not yet InNP in the repository's hardened single-tape machine model.
It proves that after successful canonical parsing, membership is exactly
existence of a finite witness accepted by the already-certified verifier.
-/

theorem satBits_iff_verified_witness
    (x : BitString) :
    SATBits circuitBitEncoding x ↔
      ∃ φ : Circuit,
        decodeCircuit x = some φ ∧
        ∃ w : SATWitness φ,
          verifyWitness φ w = true := by
  constructor
  · rintro ⟨φ, hdecode, hsat⟩
    rcases (satLanguage_iff_exists_finite_witness φ).mp hsat with ⟨w, hw⟩
    exact ⟨φ, hdecode, w, (verifyWitness_correct φ w).mpr hw⟩
  · rintro ⟨φ, hdecode, w, hverify⟩
    refine ⟨φ, hdecode, ?_⟩
    exact (satLanguage_iff_exists_finite_witness φ).mpr
      ⟨w, (verifyWitness_correct φ w).mp hverify⟩

theorem satBits_iff_short_verified_witness
    (x : BitString) :
    SATBits circuitBitEncoding x ↔
      ∃ φ : Circuit,
        decodeCircuit x = some φ ∧
        ∃ w : SATWitness φ,
          verifyWitness φ w = true ∧
          (witnessBits w).length ≤ (encodeCircuit φ).length := by
  constructor
  · rintro ⟨φ, hdecode, hsat⟩
    rcases (sat_has_short_verified_witness φ).mp hsat with
      ⟨w, hverify, hlen⟩
    exact ⟨φ, hdecode, w, hverify, hlen⟩
  · rintro ⟨φ, hdecode, w, hverify, hlen⟩
    refine ⟨φ, hdecode, ?_⟩
    exact (sat_has_short_verified_witness φ).mpr
      ⟨w, hverify, hlen⟩

/-- On a canonical encoding, the bit-language verifier relation specializes
exactly to the original SATLanguage statement. -/
theorem encoded_sat_has_short_verified_witness
    (φ : Circuit) :
    SATBits circuitBitEncoding (encodeCircuit φ) ↔
      ∃ w : SATWitness φ,
        verifyWitness φ w = true ∧
        (witnessBits w).length ≤ (encodeCircuit φ).length :=
  (encoded_sat_equivalence φ).trans (sat_has_short_verified_witness φ)

#print axioms MCore.Real.P01VerifiedRelation.satBits_iff_verified_witness
#print axioms MCore.Real.P01VerifiedRelation.satBits_iff_short_verified_witness
#print axioms MCore.Real.P01VerifiedRelation.encoded_sat_has_short_verified_witness

end P01VerifiedRelation
end Real
end MCore
