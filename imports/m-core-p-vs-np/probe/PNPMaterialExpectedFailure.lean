import MCore.Real.CanonicalCircuitBits
import MCore.Real.CanonicalFinalProof

namespace MCore.Real.PNPMaterialProbe

open CanonicalFinalProof
open CanonicalSATBoundary
open CanonicalCircuitBits

/-
EXPECTED FAILURE TARGET.
No LowerBoundWitness.not_in_p, SeparationCertificate, or universal-failure
oracle is supplied.
-/
example :
    InNP (SATBits circuitBitEncoding) ∧
    UniversalFailure (SATBits circuitBitEncoding) := by

end MCore.Real.PNPMaterialProbe
