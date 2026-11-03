import MCore.Real.P01VerifiedRelation
import MCore.Real.CanonicalSATVerifier

namespace MCore
namespace Real
namespace P01VerifierComposition

open CircuitK1
open CanonicalFinalProof
open CanonicalCircuitBits
open CanonicalSATWitness
open CanonicalSATBoundary
open CanonicalSATVerifier
open P01VerifiedRelation

/-- Semantic verifier relation already certified and reused verbatim. -/
theorem satBits_exact_verified_relation
    (x : BitString) :
    SATBits circuitBitEncoding x ↔
      ∃ phi : Circuit,
        decodeCircuit x = some phi ∧
        ∃ w : SATWitness phi,
          verifyWitness phi w = true :=
  satBits_iff_verified_witness x

/-- T1.C remains the operational single-machine realization of the verified
relation, not the high-level relation itself. -/
def VerifierCompositionGap : Prop :=
  CanonicalSATOperationalGap

#print axioms MCore.Real.P01VerifierComposition.satBits_exact_verified_relation

end P01VerifierComposition
end Real
end MCore
