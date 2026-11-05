import MCore.Real.P02KleeneKernel

namespace MCore
namespace Real
namespace P02EffectiveAlignment

open CanonicalFinalProof
open CanonicalSATBoundary
open CanonicalCircuitBits
open P02KleeneKernel

/-- Effective presentation attached to one canonical deterministic candidate.
This does not assert any lower bound; it only supplies the recursion-theoretic
compiler required to enter the Kleene code universe. -/
structure EffectivePresentation (M : PolyDTMCandidate) where
  compiler : EffectiveDiagonalCompiler M

/-- Semantic SAT realization attached to an effective presentation. -/
structure EffectiveSATRealization
    (M : PolyDTMCandidate)
    (E : EffectivePresentation M) where
  realizer : SATFixedPointRealizer M E.compiler

/-- Uniform effective coverage of every canonical deterministic candidate. -/
structure UniformEffectiveCoverage where
  presentation : ∀ M : PolyDTMCandidate, EffectivePresentation M
  realization :
    ∀ M : PolyDTMCandidate,
      EffectiveSATRealization M (presentation M)

/-- Uniform effective coverage is exactly sufficient to build the already
isolated Kleene/SAT bridge. -/
def UniformEffectiveCoverage.toKleeneSATBridge
    (U : UniformEffectiveCoverage) :
    KleeneSATBridge :=
  { compiler := fun M => (U.presentation M).compiler
    realizer := fun M => (U.realization M).realizer }

/-- Therefore no further logical or endpoint bridge is required after uniform
effective coverage is constructed. -/
theorem uniform_effective_coverage_closes_p02
    (U : UniformEffectiveCoverage) :
    ¬ InP (SATBits circuitBitEncoding) := by
  exact kleene_bridge_closes_not_in_p
    ⟨U.toKleeneSATBridge⟩

end P02EffectiveAlignment
end Real
end MCore
