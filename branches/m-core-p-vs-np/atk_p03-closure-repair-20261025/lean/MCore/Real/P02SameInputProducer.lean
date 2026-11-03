import MCore.Real.P02UniversalFailureMinCut
import MCore.Real.P02KleeneKernel

namespace MCore
namespace Real
namespace P02SameInputProducer

open CanonicalFinalProof
open CanonicalSATBoundary
open CanonicalCircuitBits
open P02UniversalFailureMinCut
open P02KleeneKernel

/--
Exact same-input semantic diagonal producer.

For every deterministic polynomial-time candidate M, produce one canonical SAT
bitstring x_M satisfying the semantic flip on that very same M and x_M.
No bare fixed-point statement is accepted.
-/
structure SameInputSemanticDiagonalProducer where
  diagonalInput : PolyDTMCandidate → BitString
  flip :
    ∀ M : PolyDTMCandidate,
      SATTarget (diagonalInput M) ↔
        ¬ DeclaredAccept M (diagonalInput M)

/-- A same-input semantic diagonal immediately yields the exact universal
counterexample producer. -/
def SameInputSemanticDiagonalProducer.toUniversalCounterexample
    (P : SameInputSemanticDiagonalProducer) :
    UniversalCounterexampleProducer where
  counterexample := P.diagonalInput
  failure := by
    intro M
    exact
      (failureMode_iff_not_correctAt M (P.diagonalInput M)).mpr
        (fixed_flip_fails M (P.diagonalInput M) (P.flip M))

/-- Hence this is a sufficient material producer for the remaining P02 lower
bound after P01. -/
theorem sameInputSemanticDiagonal_closes_p02
    (P : SameInputSemanticDiagonalProducer) :
    PneqNP :=
  producer_closes_internal_endpoint P.toUniversalCounterexample

#print axioms MCore.Real.P02SameInputProducer.SameInputSemanticDiagonalProducer.toUniversalCounterexample
#print axioms MCore.Real.P02SameInputProducer.sameInputSemanticDiagonal_closes_p02

end P02SameInputProducer
end Real
end MCore
