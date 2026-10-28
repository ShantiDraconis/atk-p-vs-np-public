import MCore.Real.P02UniversalFailureAlgebra

namespace MCore
namespace Real
namespace P02DiagonalCompilerFrontierV2

open CanonicalFinalProof
open CanonicalCircuitBits
open CanonicalSATBoundary
open P02DiagonalFrontier
open P02UniversalFailureAlgebra
open P02SemanticSelfEmbedding
open P02TerminalFrontier

structure DiagonalCompilerV2 where
  compile : PolyDTMCandidate → BitString
  valid : ∀ M, CanonicalSATValid (compile M)
  flip : ∀ M,
    SATBits circuitBitEncoding (compile M) ↔
      ¬ AcceptsAtDeclaredBound M (compile M)

def DiagonalCompilerV2Gap : Prop := Nonempty DiagonalCompilerV2

def DiagonalCompilerV2.toFamily
    (D : DiagonalCompilerV2) : DiagonalFamily where
  witness := fun M =>
    { bits := D.compile M
      valid := D.valid M
      flips := D.flip M }

theorem diagonalCompilerV2_closes_p02
    (D : DiagonalCompilerV2) :
    P02TerminalFrontier.P02Target := by
  exact diagonal_family_closes_p02 D.toFamily

theorem diagonalCompilerV2_gives_semanticMismatch
    (D : DiagonalCompilerV2)
    (M : PolyDTMCandidate) :
    SemanticMismatch M (D.compile M) := by
  exact self_embed_witness_gives_semanticMismatch
    M (D.compile M) (D.flip M)

#print axioms MCore.Real.P02DiagonalCompilerFrontierV2.diagonalCompilerV2_closes_p02
#print axioms MCore.Real.P02DiagonalCompilerFrontierV2.diagonalCompilerV2_gives_semanticMismatch

end P02DiagonalCompilerFrontierV2
end Real
end MCore
