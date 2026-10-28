import MCore.Real.CanonicalCircuitBits
import MCore.Real.CanonicalFinalProof

namespace MCore

open Real
open Real.CanonicalFinalProof
open Real.CanonicalSATBoundary
open Real.CanonicalCircuitBits

/-- Canonical material P-vs-NP target on the fixed bitstring SAT encoding.
The NP side and deterministic universal-failure side refer to the SAME language. -/
def MinimalSeparationInhabitant : Prop :=
  InNP (SATBits circuitBitEncoding) ∧
  UniversalFailure (SATBits circuitBitEncoding)

/-- Pure transport only: a genuine inhabitant of the canonical target closes
the internal P≠NP statement. -/
theorem minimalSeparationInhabitant_closes
    (h : MinimalSeparationInhabitant) :
    PneqNP :=
  target_failure_implies_p_ne_np h.1 h.2

#print axioms MCore.minimalSeparationInhabitant_closes

end MCore
