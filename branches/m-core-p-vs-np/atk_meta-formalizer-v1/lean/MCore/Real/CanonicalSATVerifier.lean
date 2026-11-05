import MCore.Real.CanonicalSATWitness

namespace MCore
namespace Real
namespace CanonicalSATVerifier

open CircuitK1
open CanonicalCircuitBits
open CanonicalSATWitness

def verifyWitness
    (φ : Circuit)
    (w : SATWitness φ) : Bool :=
  Bool.and
    (isCNFBool φ)
    (evalCircuit (assignmentOfWitness φ w) φ)

theorem verifyWitness_correct
    (φ : Circuit)
    (w : SATWitness φ) :
    verifyWitness φ w = true ↔ SATWitnessAccepts φ w := by
  unfold verifyWitness SATWitnessAccepts
  rw [bool_and_eq_true_iff]
  rw [isCNFBool_eq_true_iff]

/-- Structural work budget for the high-level verifier. This is NOT yet a
    theorem about canonical Turing-machine steps. -/
def verificationCost (φ : Circuit) : Nat :=
  CircuitK1.size φ + varBound φ

theorem verificationCost_linear_encoding_bound
    (φ : Circuit) :
    verificationCost φ ≤ 2 * (encodeCircuit φ).length := by
  unfold verificationCost
  have hs := size_le_encodeCircuit_length φ
  have hv := varBound_le_encoded_length φ
  omega

theorem sat_has_short_verified_witness
    (φ : Circuit) :
    SATLanguage φ ↔
      ∃ w : SATWitness φ,
        verifyWitness φ w = true ∧
        (witnessBits w).length ≤ (encodeCircuit φ).length := by
  constructor
  · intro hSAT
    rcases (satLanguage_iff_exists_finite_witness φ).mp hSAT with ⟨w, hw⟩
    refine ⟨w, (verifyWitness_correct φ w).mpr hw, witness_bits_linear_bound w⟩
  · rintro ⟨w, hVerify, _⟩
    exact (satLanguage_iff_exists_finite_witness φ).mpr
      ⟨w, (verifyWitness_correct φ w).mp hVerify⟩

/-- Exact remaining G1 operational bridge after encoding+witness+verifier. -/
structure VerifierToCanonicalNTMBridge where
  realization :
    CanonicalSATBoundary.SATInNPGap
      CanonicalCircuitBits.circuitBitEncoding

def CanonicalSATOperationalGap : Prop :=
  Nonempty VerifierToCanonicalNTMBridge

theorem operational_bridge_closes_sat_in_np
    (B : VerifierToCanonicalNTMBridge) :
    CanonicalSATBoundary.SATInNPGap
      CanonicalCircuitBits.circuitBitEncoding :=
  B.realization

#print axioms MCore.Real.CanonicalSATVerifier.verifyWitness_correct
#print axioms MCore.Real.CanonicalSATVerifier.verificationCost_linear_encoding_bound
#print axioms MCore.Real.CanonicalSATVerifier.sat_has_short_verified_witness
#print axioms MCore.Real.CanonicalSATVerifier.operational_bridge_closes_sat_in_np

end CanonicalSATVerifier
end Real
end MCore
