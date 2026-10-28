import MCore.Real.P02UniversalLowerBoundMaster
import MCore.Real.P02ExactDiagonalFrontier
import MCore.Real.P02CanonicalClockReduction
import MCore.Real.P02FinalCompression

namespace MCore
namespace Real
namespace P02TerminalEquivalenceAudit

open CanonicalFinalProof
open CanonicalSATBoundary
open CanonicalCircuitBits
open P02OperatorKernel
open P02FinalCompression
open P02UniversalLowerBound
open P02UniversalLowerBoundMaster
open P02CanonicalClockReduction
open P02ExactDiagonalFrontier
open P02UniversalFailureMinCut

abbrev SATTarget : BitLanguage := SATBits circuitBitEncoding

/-- All exact terminal forms collapse to one proposition. -/
theorem final_open_math_iff_universal_failure :
    P02FinalCompression.FINAL_OPEN_MATH ↔
      UniversalFailure SATTarget := by
  exact p02Producer_iff_universalFailure

theorem final_open_math_iff_universal_lower_bound :
    P02FinalCompression.FINAL_OPEN_MATH ↔
      UniversalSATLowerBound := by
  calc
    P02FinalCompression.FINAL_OPEN_MATH
        ↔ UniversalFailure SATTarget :=
          final_open_math_iff_universal_failure
    _ ↔ UniversalSATLowerBound :=
          universalSATLowerBound_iff_universalFailure.symm

theorem final_open_math_iff_not_in_p :
    P02FinalCompression.FINAL_OPEN_MATH ↔
      ¬ InP SATTarget :=
  P02FinalCompression.final_open_math_iff_sat_not_in_p

theorem final_open_math_iff_normalized_adversary :
    P02FinalCompression.FINAL_OPEN_MATH ↔
      Nonempty NormalizedAdversary := by
  calc
    P02FinalCompression.FINAL_OPEN_MATH
        ↔ UniversalSATLowerBound :=
          final_open_math_iff_universal_lower_bound
    _ ↔ Nonempty NormalizedAdversary :=
          normalizedAdversary_iff_universalSATLowerBound.symm

theorem final_open_math_iff_exact_diagonal :
    P02FinalCompression.FINAL_OPEN_MATH ↔
      TotalExactDiagonalProducer := by
  calc
    P02FinalCompression.FINAL_OPEN_MATH
        ↔ UniversalFailure SATTarget :=
          final_open_math_iff_universal_failure
    _ ↔ TotalExactDiagonalProducer :=
          total_exact_diagonal_iff_universal_failure.symm

theorem final_open_math_iff_counterexample_producer :
    P02FinalCompression.FINAL_OPEN_MATH ↔
      Nonempty UniversalCounterexampleProducer := by
  calc
    P02FinalCompression.FINAL_OPEN_MATH
        ↔ UniversalFailure SATTarget :=
          final_open_math_iff_universal_failure
    _ ↔ Nonempty UniversalCounterexampleProducer :=
          producer_iff_universal_failure.symm

/-- The aliases appearing across the repository are not separate mathematical
gaps; they are exact normal forms of the same terminal proposition. -/
theorem terminal_exact_forms :
    (P02FinalCompression.FINAL_OPEN_MATH ↔ UniversalSATLowerBound) ∧
    (P02FinalCompression.FINAL_OPEN_MATH ↔ TotalExactDiagonalProducer) ∧
    (P02FinalCompression.FINAL_OPEN_MATH ↔ Nonempty NormalizedAdversary) ∧
    (P02FinalCompression.FINAL_OPEN_MATH ↔ Nonempty UniversalCounterexampleProducer) ∧
    (P02FinalCompression.FINAL_OPEN_MATH ↔ ¬ InP SATTarget) := by
  exact ⟨final_open_math_iff_universal_lower_bound,
    final_open_math_iff_exact_diagonal,
    final_open_math_iff_normalized_adversary,
    final_open_math_iff_counterexample_producer,
    final_open_math_iff_not_in_p⟩

#print axioms MCore.Real.P02TerminalEquivalenceAudit.final_open_math_iff_universal_failure
#print axioms MCore.Real.P02TerminalEquivalenceAudit.final_open_math_iff_universal_lower_bound
#print axioms MCore.Real.P02TerminalEquivalenceAudit.final_open_math_iff_normalized_adversary
#print axioms MCore.Real.P02TerminalEquivalenceAudit.final_open_math_iff_exact_diagonal
#print axioms MCore.Real.P02TerminalEquivalenceAudit.final_open_math_iff_counterexample_producer
#print axioms MCore.Real.P02TerminalEquivalenceAudit.terminal_exact_forms

end P02TerminalEquivalenceAudit
end Real
end MCore
