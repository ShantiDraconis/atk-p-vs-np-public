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

/-- Universal witness existence is exactly the pointwise unpacking of the
SemanticSelfEmbedder data. This construction uses only explicit witnesses
supplied by h; it does not invoke the falsified literal fixed-point route. -/
noncomputable def semanticSelfEmbedderOfUniversalWitness
    (h : UniversalWitnessExists) :
    SemanticSelfEmbedder where
  bits := fun M => Classical.choose (h M)
  valid := by
    intro M
    exact (Classical.choose_spec (h M)).1
  flips := by
    intro M
    exact (Classical.choose_spec (h M)).2

theorem universal_witness_builds_semantic_self_embedder
    (h : UniversalWitnessExists) :
    SemanticSelfEmbeddingGap := by
  exact ⟨semanticSelfEmbedderOfUniversalWitness h⟩

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
    exact ⟨{
      bits := fun M => Classical.choose (h M)
      valid := by
        intro M
        exact (Classical.choose_spec (h M)).1
      flip := by
        intro M
        exact (Classical.choose_spec (h M)).2
    }⟩

#print axioms MCore.Real.P02SemanticSelfEmbeddingClose.semanticSelfEmbedderOfUniversalWitness
#print axioms MCore.Real.P02SemanticSelfEmbeddingClose.universal_witness_builds_semantic_self_embedder
#print axioms MCore.Real.P02SemanticSelfEmbeddingClose.universal_witness_closes_p02
#print axioms MCore.Real.P02SemanticSelfEmbeddingClose.diagonalSATConstruction_iff_universal_witness

end P02SemanticSelfEmbeddingClose
end Real
end MCore
