import MCore.Real.P02FinalAttack
import MCore.Real.P02SemanticSelfEmbedding

namespace MCore
namespace Real
namespace PNP_D3_SEMANTIC_SELFREF_FRONTIER_20260926

open P02FinalAttack
open P02SemanticSelfEmbedding
open P02DiagonalFrontier

/-- Exact D3 frontier. No inhabitant is asserted here. -/
def Frontier : Prop := D3SemanticSelfReference

theorem frontier_iff_semantic_self_embedding :
    Frontier ↔ SemanticSelfEmbeddingGap := by
  unfold Frontier D3SemanticSelfReference
  exact (semantic_self_embedding_gap_iff_diagonal_fixed_point_gap).symm

theorem frontier_closes_p02
    (h : Frontier) :
    P02TerminalFrontier.P02Target :=
  D3_to_P02Target h

#print axioms frontier_iff_semantic_self_embedding
#print axioms frontier_closes_p02

end PNP_D3_SEMANTIC_SELFREF_FRONTIER_20260926
end Real
end MCore
