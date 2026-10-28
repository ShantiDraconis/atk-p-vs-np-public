import Mathlib
import MCore.Real.OpenMathCore.SATCircuitCompiler
import MCore.Real.P02DiagonalCompilerFrontierV2

namespace MCore.Real.OpenMathCore

open CanonicalFinalProof
open CanonicalSATBoundary
open P02DiagonalFrontier
open P02UniversalFailureAlgebra
open P02DiagonalCompilerFrontierV2

/-- Terminal non-circular object. The same bitstring appears as SAT instance
and as the candidate input. -/
structure SameInputClosure where
  witness : PolyDTMCandidate → BitString
  valid :
    ∀ M, CanonicalSATValid (witness M)
  simulation_exact :
    ∀ M,
      SATBits CanonicalCircuitBits.circuitBitEncoding (witness M) ↔
        ¬ AcceptsAtDeclaredBound M (witness M)

def SameInputClosure.toDiagonalCompilerV2
    (S : SameInputClosure) : DiagonalCompilerV2 where
  compile := S.witness
  valid := S.valid
  flip := S.simulation_exact

theorem sameInputClosure_gives_mismatch
    (S : SameInputClosure)
    (M : PolyDTMCandidate) :
    P02UniversalFailureAlgebra.SemanticMismatch M (S.witness M) := by
  exact diagonalCompilerV2_gives_semanticMismatch S.toDiagonalCompilerV2 M

end MCore.Real.OpenMathCore
