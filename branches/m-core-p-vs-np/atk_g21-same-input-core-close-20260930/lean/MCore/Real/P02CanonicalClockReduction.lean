import MCore.Real.P02CanonicalNormalization
import MCore.Real.P02TerminalFrontier

namespace MCore
namespace Real
namespace P02CanonicalClockReduction

open CanonicalFinalProof
open CanonicalCircuitBits
open CanonicalSATBoundary
open P02CanonicalNormalization
open P02TerminalFrontier

/-- Universal failure restricted to the canonical-clock representatives.

This is not a weakening of the final target: every original candidate admits
such a representative that preserves every input on which the original
candidate is correct. -/
def CanonicalClockFailure (L : BitLanguage) : Prop :=
  ∀ (M : PolyDTMCandidate) (coefficient exponent : Nat),
    ∃ x : BitString,
      ¬ (normalizedCandidate M coefficient exponent).CorrectAt L x

/-- Failure of a normalized representative transfers backwards to failure of
the original candidate, provided the representative clock dominates the
original clock. -/
theorem normalized_failure_reflects
    (L : BitLanguage)
    (M : PolyDTMCandidate)
    (coefficient exponent : Nat)
    (hbound :
      ∀ n : Nat,
        M.timeBound n ≤ canonicalTimeBound coefficient exponent n)
    (x : BitString)
    (hbad :
      ¬ (normalizedCandidate M coefficient exponent).CorrectAt L x) :
    ¬ M.CorrectAt L x := by
  intro hgood
  exact hbad
    (normalizedCandidate_correctAt
      M coefficient exponent hbound L x hgood)

/-- Main reduction: diagonalizing only canonical polynomial clocks is enough
to obtain the original UniversalFailure proposition. -/
theorem canonicalClockFailure_to_universalFailure
    {L : BitLanguage}
    (h : CanonicalClockFailure L) :
    UniversalFailure L := by
  intro M
  rcases M.time_poly with ⟨coefficient, exponent, hbound⟩
  rcases h M coefficient exponent with ⟨x, hbad⟩
  exact ⟨x,
    normalized_failure_reflects
      L M coefficient exponent hbound x hbad⟩

/-- Canonical-clock diagonal failure therefore closes the exact P02 target for
canonical SAT. -/
theorem canonicalClockFailure_closes_P02
    (h : CanonicalClockFailure (SATBits circuitBitEncoding)) :
    P02Target := by
  unfold P02Target SATFailGap
  exact ⟨canonicalClockFailure_to_universalFailure h⟩

/-- Paired with the existing SAT-in-NP producer, the same normalized failure
closes the internal separation theorem. -/
theorem canonicalClockFailure_closes_internal
    (hP01 : SATInNPGap circuitBitEncoding)
    (hP02 : CanonicalClockFailure (SATBits circuitBitEncoding)) :
    PneqNP := by
  exact p01_p02_close_internal_separation
    hP01 (canonicalClockFailure_closes_P02 hP02)

#print axioms MCore.Real.P02CanonicalClockReduction.normalized_failure_reflects
#print axioms MCore.Real.P02CanonicalClockReduction.canonicalClockFailure_to_universalFailure
#print axioms MCore.Real.P02CanonicalClockReduction.canonicalClockFailure_closes_P02

end P02CanonicalClockReduction
end Real
end MCore
