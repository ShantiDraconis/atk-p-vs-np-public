import MCore.Real.CanonicalSATBoundary
import MCore.Real.CanonicalCircuitBits
import MCore.Real.FailProofAllGaps

namespace MCore
namespace Real
namespace P02TerminalFrontier

open CanonicalFinalProof
open CanonicalCircuitBits
open CanonicalSATBoundary
open FailProofAllGaps

/-- Exact P02 target for the same canonical SAT bit-language used by P01. -/
abbrev P02Target : Prop :=
  SATFailGap circuitBitEncoding

/-- P02 is exactly deterministic polynomial-time non-membership for the same
canonical SAT bit-language. No finite benchmark or asymptotic proxy can replace
this proposition. -/
theorem p02_target_iff_sat_not_in_p :
    P02Target ↔ ¬ InP (SATBits circuitBitEncoding) := by
  unfold P02Target SATFailGap
  rw [failure_generator_iff_universal_failure]
  exact universal_failure_iff_not_in_p

/-- A P01 witness plus the exact P02 target closes the internal separation. -/
theorem p01_p02_close_internal_separation
    (hP01 : SATInNPGap circuitBitEncoding)
    (hP02 : P02Target) :
    PneqNP := by
  have hFailGen : Nonempty (FailureGenerator (SATBits circuitBitEncoding)) :=
    hP02
  rcases hFailGen with ⟨G⟩
  exact target_failure_implies_p_ne_np
    hP01
    (failure_generator_implies_universal_failure G)

/-- Certificate-shaped pairing of the two terminal P-vs-NP producers. -/
structure PNPFinalPair where
  p01 : SATInNPGap circuitBitEncoding
  p02 : P02Target

theorem pnp_final_pair_closes
    (C : PNPFinalPair) :
    PneqNP :=
  p01_p02_close_internal_separation C.p01 C.p02

#print axioms MCore.Real.P02TerminalFrontier.p02_target_iff_sat_not_in_p
#print axioms MCore.Real.P02TerminalFrontier.p01_p02_close_internal_separation
#print axioms MCore.Real.P02TerminalFrontier.pnp_final_pair_closes

end P02TerminalFrontier
end Real
end MCore
