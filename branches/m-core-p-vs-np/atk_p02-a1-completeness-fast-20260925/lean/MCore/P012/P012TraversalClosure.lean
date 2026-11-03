import MCore.P012.P012TraversalTheorem
import MCore.P012.P012MetaClosure

namespace MCore
namespace P012

/-- Closed package for the arithmetic/metamodel traversal theory.
This certificate contains only proved P012 facts and no Clay endpoint. -/
structure TraversalTheoryCertificate where
  twoPrime : Nat.Prime 2
  reflection : reflectState ⟨-2⟩ = ⟨2⟩
  reflectionDisplacement : displacementNumerator ⟨-2⟩ ⟨2⟩ = 4
  oddGap : displacementNumerator ⟨-5⟩ ⟨5⟩ = 10
  noPrimeUnitCrossing :
    ¬ (∀ s ∈ fullCrossingPath, PrimeThirdState s)
  noOddPureCrossing :
    ¬ (∀ s ∈ fullCrossingPath, PureOddPrimeThirdState s)
  generalPositive :
    ∀ p q : Nat,
      toOneDisplacementNumerator p q = Int.ofNat (p + q)
  generalNegative :
    ∀ p q : Nat,
      toNegOneDisplacementNumerator p q = -(Int.ofNat (p + q))

def traversalTheoryCertificate : TraversalTheoryCertificate where
  twoPrime := two_is_prime
  reflection := kernel_reflection
  reflectionDisplacement := kernel_reflection_displacement
  oddGap := central_odd_prime_gap_displacement
  noPrimeUnitCrossing := fullCrossingPath_contains_nonprime_transition_states
  noOddPureCrossing := no_pure_odd_prime_canonical_crossing
  generalPositive := toOneDisplacementNumerator_eq
  generalNegative := toNegOneDisplacementNumerator_eq

theorem traversalTheory_closed :
    Nonempty TraversalTheoryCertificate :=
  ⟨traversalTheoryCertificate⟩

/-- The P012 traversal package is observationally compatible with the existing
metaclosure vocabulary, but does not construct real P01/G21 producers. -/
theorem traversal_finish_has_closed_label :
    signedThirdPipelineState demoKernelTraversal.finish = .closed :=
  demo_finish_is_closed_label

#print axioms MCore.P012.traversalTheoryCertificate
#print axioms MCore.P012.traversalTheory_closed
#print axioms MCore.P012.traversal_finish_has_closed_label

end P012
end MCore
