import MCore.Real.P02UniversalFailureAlgebra

namespace MCore
namespace Real
namespace P02ClockFailureBranch

open CanonicalFinalProof
open CanonicalCircuitBits
open CanonicalSATBoundary
open P02UniversalFailureAlgebra

theorem clock_failure_gives_g21_witness
    (M : PolyDTMCandidate)
    (h : ¬ DeclaredClockTotal M) :
    ∃ x : BitString,
      ¬ M.CorrectAt (SATBits circuitBitEncoding) x := by
  rcases (not_declaredClockTotal_iff_exists_clock_failure M).mp h with ⟨x, hx⟩
  exact ⟨x,
    (not_correctAt_iff_clock_or_semantic_mismatch M x).mpr (Or.inl hx)⟩

theorem clock_failure_gives_normalized_witness
    (M : PolyDTMCandidate)
    (h : ¬ DeclaredClockTotal M) :
    ∃ x : BitString,
      ¬ DeclaredHalts M x ∨ SemanticMismatch M x := by
  rcases (not_declaredClockTotal_iff_exists_clock_failure M).mp h with ⟨x, hx⟩
  exact ⟨x, Or.inl hx⟩

#print axioms MCore.Real.P02ClockFailureBranch.clock_failure_gives_g21_witness
#print axioms MCore.Real.P02ClockFailureBranch.clock_failure_gives_normalized_witness

end P02ClockFailureBranch
end Real
end MCore
