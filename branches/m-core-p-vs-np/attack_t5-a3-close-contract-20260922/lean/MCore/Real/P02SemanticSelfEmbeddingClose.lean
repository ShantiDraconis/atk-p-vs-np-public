import MCore.Real.P02SemanticSelfEmbedding

namespace MCore
namespace Real
namespace P02SemanticSelfEmbeddingClose

open CanonicalFinalProof
open CanonicalCircuitBits
open CanonicalSATBoundary
open P02DiagonalFrontier
open P02SemanticSelfEmbedding

def UniversalWitnessExists : Prop :=
  ∀ M : PolyDTMCandidate,
    ∃ x : BitString,
      CanonicalSATValid x ∧
      (SATBits circuitBitEncoding x ↔
        ¬ AcceptsAtDeclaredBound M x)

theorem universal_witness_iff_pointwise :
    UniversalWitnessExists ↔ PointwiseSemanticSelfEmbedding := by
  rfl

theorem universal_witness_builds_semantic_self_embedder
    (h : UniversalWitnessExists) :
    SemanticSelfEmbeddingGap := by
  exact
    (semantic_self_embedding_gap_iff_pointwise).mpr h

theorem universal_witness_closes_p02
    (h : UniversalWitnessExists) :
    P02TerminalFrontier.P02Target := by
  exact semantic_self_embedding_closes_p02
    (universal_witness_builds_semantic_self_embedder h)

structure DiagonalSATConstruction where
  bits : PolyDTMCandidate → BitString
  valid : ∀ M, CanonicalSATValid (bits M)
  flip : ∀ M,
    SATBits circuitBitEncoding (bits M) ↔
      ¬ AcceptsAtDeclaredBound M (bits M)

theorem diagonalSATConstruction_iff_universal_witness :
    Nonempty DiagonalSATConstruction ↔ UniversalWitnessExists := by
  constructor
  · rintro ⟨D⟩ M
    exact ⟨D.bits M, D.valid M, D.flip M⟩
  · intro h
    classical
    let bits : PolyDTMCandidate → BitString :=
      fun M => Classical.choose (h M)
    refine ⟨{
      bits := bits
      valid := ?_
      flip := ?_
    }⟩
    · intro M
      exact (Classical.choose_spec (h M)).1
    · intro M
      exact (Classical.choose_spec (h M)).2

#print axioms MCore.Real.P02SemanticSelfEmbeddingClose.universal_witness_iff_pointwise
#print axioms MCore.Real.P02SemanticSelfEmbeddingClose.universal_witness_builds_semantic_self_embedder
#print axioms MCore.Real.P02SemanticSelfEmbeddingClose.universal_witness_closes_p02
#print axioms MCore.Real.P02SemanticSelfEmbeddingClose.diagonalSATConstruction_iff_universal_witness

end P02SemanticSelfEmbeddingClose
end Real
end MCore
