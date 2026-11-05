import MCore.Real.P02FinalCompression
import MCore.Real.P02UniversalLowerBound
import MCore.Real.P02CanonicalClockReduction
import MCore.Real.P02KleeneKernel
import MCore.Real.P02EffectiveAlignment
import MCore.Real.P01PostMinCutClosure

namespace MCore
namespace Real
namespace P02UniversalLowerBoundMaster

open CanonicalFinalProof
open CanonicalSATBoundary
open CanonicalCircuitBits
open P02OperatorKernel
open P02FinalCompression
open P02UniversalLowerBound
open P02CanonicalClockReduction
open P02KleeneKernel
open P02EffectiveAlignment

/-- Canonical terminal lower bound. -/
abbrev UNIVERSAL_LOWER_BOUND : Prop :=
  UniversalSATLowerBound

/-- Exact semantic form. -/
theorem universal_lower_bound_iff_not_in_p :
    UNIVERSAL_LOWER_BOUND ↔
      ¬ InP (SATBits circuitBitEncoding) :=
  universalSATLowerBound_iff_notInP

/-- Exact counterexample-operator form. -/
theorem universal_lower_bound_iff_p02_operator :
    UNIVERSAL_LOWER_BOUND ↔
      Nonempty CanonicalSATP02Producer := by
  rw [universal_lower_bound_iff_not_in_p]
  exact canonicalSATProducer_iff_notInP.symm

/-- Exact monomial-clock normal form. -/
theorem universal_lower_bound_iff_normalized_adversary :
    UNIVERSAL_LOWER_BOUND ↔
      Nonempty NormalizedAdversary := by
  exact normalizedAdversary_iff_universalSATLowerBound.symm

/-- Operational decomposition into clock failure or semantic disagreement. -/
theorem universal_lower_bound_iff_operational :
    UNIVERSAL_LOWER_BOUND ↔
      ∀ M : PolyDTMCandidate,
        ∃ x : BitString,
          ¬ HaltsAtDeclaredBound M x ∨
            SemanticMismatch M x :=
  universalSATLowerBound_iff_operational

/-- Uniform effective Kleene/SAT coverage is a sufficient constructive route
to the exact lower bound. -/
theorem effective_coverage_implies_universal_lower_bound
    (U : UniformEffectiveCoverage) :
    UNIVERSAL_LOWER_BOUND := by
  apply universal_lower_bound_iff_not_in_p.mpr
  exact uniform_effective_coverage_closes_p02 U

/-- The recovered P01 witness consumes the universal lower bound and closes the
internal separation endpoint. -/
theorem universal_lower_bound_closes_internal
    (h : UNIVERSAL_LOWER_BOUND) :
    PneqNP := by
  exact target_failure_implies_p_ne_np
    P01PostMinCutClosure.canonical_sat_in_np_closed
    (universalSATLowerBound_iff_universalFailure.mp h)

/-- No structural producer remains below this proposition. -/
abbrev FINAL_OPEN_MATH : Prop :=
  UNIVERSAL_LOWER_BOUND

end P02UniversalLowerBoundMaster
end Real
end MCore
