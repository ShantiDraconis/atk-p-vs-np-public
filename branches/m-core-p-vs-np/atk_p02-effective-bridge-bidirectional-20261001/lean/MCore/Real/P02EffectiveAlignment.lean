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


/-- The effective-coverage package is not an additional mathematical burden:
it is exactly a repackaging of the Kleene/SAT bridge fields. -/
def UniformEffectiveCoverage.ofKleeneSATBridge
    (B : KleeneSATBridge) :
    UniformEffectiveCoverage :=
  { presentation := fun M =>
      { compiler := B.compiler M }
    realization := fun M =>
      { realizer := B.realizer M } }

/-- Exact adapter closure between the two constructive formulations.  Hence
there is no independent OPEN_MATH gap between UniformEffectiveCoverage and
KleeneSATBridge; the genuine content is the per-candidate SAT fixed-point
realizer itself. -/
theorem uniformEffectiveCoverage_iff_kleeneSATBridge :
    Nonempty UniformEffectiveCoverage ↔
      Nonempty KleeneSATBridge := by
  constructor
  · rintro ⟨U⟩
    exact ⟨U.toKleeneSATBridge⟩
  · rintro ⟨B⟩
    exact ⟨UniformEffectiveCoverage.ofKleeneSATBridge B⟩

/-- Therefore no further logical or endpoint bridge is required after uniform
effective coverage is constructed. -/
theorem uniform_effective_coverage_closes_p02
    (U : UniformEffectiveCoverage) :
    ¬ InP (SATBits circuitBitEncoding) := by
  exact kleene_bridge_closes_not_in_p
    ⟨U.toKleeneSATBridge⟩

#print axioms MCore.Real.P02EffectiveAlignment.uniformEffectiveCoverage_iff_kleeneSATBridge

end P02EffectiveAlignment
end Real
end MCore
