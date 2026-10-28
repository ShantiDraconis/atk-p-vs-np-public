import MCore.Real.P02DiagonalFrontier
import MCore.Real.P02LiteralFixedPointCountermodel

namespace MCore
namespace Real
namespace P02SemanticSelfEmbedding

open CanonicalFinalProof
open CanonicalCircuitBits
open CanonicalSATBoundary
open P02TerminalFrontier
open P02DiagonalFrontier

/-- Exact semantic payload required by T5.A2.  This packages a bitstring
construction together with canonical validity and the semantic flip law.
No existence claim is made here. -/
structure SemanticSelfEmbedder where
  bits : PolyDTMCandidate → BitString
  valid :
    ∀ M : PolyDTMCandidate,
      CanonicalSATValid (bits M)
  flips :
    ∀ M : PolyDTMCandidate,
      SATBits circuitBitEncoding (bits M) ↔
        ¬ AcceptsAtDeclaredBound M (bits M)

def SemanticSelfEmbeddingGap : Prop :=
  Nonempty SemanticSelfEmbedder

def SemanticSelfEmbedder.toDiagonalFamily
    (S : SemanticSelfEmbedder) :
    DiagonalFamily where
  witness := fun M =>
    { bits := S.bits M
      valid := S.valid M
      flips := S.flips M }

def diagonalFamilyToSemanticSelfEmbedder
    (D : DiagonalFamily) :
    SemanticSelfEmbedder where
  bits := fun M => (D.witness M).bits
  valid := fun M => (D.witness M).valid
  flips := fun M => (D.witness M).flips

theorem semantic_self_embedding_gap_iff_diagonal_fixed_point_gap :
    SemanticSelfEmbeddingGap ↔ DiagonalFixedPointGap := by
  constructor
  · rintro ⟨S⟩
    exact ⟨S.toDiagonalFamily⟩
  · rintro ⟨D⟩
    exact ⟨diagonalFamilyToSemanticSelfEmbedder D⟩

theorem semantic_self_embedding_closes_p02
    (h : SemanticSelfEmbeddingGap) :
    P02Target := by
  exact diagonal_fixed_point_gap_closes_p02
    ((semantic_self_embedding_gap_iff_diagonal_fixed_point_gap).mp h)

theorem semantic_self_embedding_implies_sat_not_in_p
    (h : SemanticSelfEmbeddingGap) :
    ¬ InP (SATBits circuitBitEncoding) := by
  exact (p02_target_iff_sat_not_in_p.mp
    (semantic_self_embedding_closes_p02 h))

theorem sat_in_p_refutes_semantic_self_embedding
    (hP : InP (SATBits circuitBitEncoding)) :
    ¬ SemanticSelfEmbeddingGap := by
  intro h
  exact (semantic_self_embedding_implies_sat_not_in_p h) hP


theorem literal_fixed_point_route_not_universal :
    ¬ ∀ M : PolyDTMCandidate,
        ∃ x : BitString,
          P02ClockedDiagonalCompiler.semanticDiagonalBits M x = x := by
  exact P02LiteralFixedPointCountermodel.no_universal_literal_fixed_point


def PointwiseSemanticSelfEmbedding : Prop :=
  ∀ M : PolyDTMCandidate,
    ∃ x : BitString,
      CanonicalSATValid x ∧
      (SATBits circuitBitEncoding x ↔
        ¬ AcceptsAtDeclaredBound M x)

theorem semantic_self_embedding_gap_iff_pointwise :
    SemanticSelfEmbeddingGap ↔ PointwiseSemanticSelfEmbedding := by
  constructor
  · rintro ⟨S⟩ M
    exact ⟨S.bits M, S.valid M, S.flips M⟩
  · intro h
    classical
    let chooseBits : PolyDTMCandidate → BitString :=
      fun M => Classical.choose (h M)
    refine ⟨{
      bits := chooseBits
      valid := ?_
      flips := ?_
    }⟩
    · intro M
      exact (Classical.choose_spec (h M)).1
    · intro M
      exact (Classical.choose_spec (h M)).2


#print axioms MCore.Real.P02SemanticSelfEmbedding.semantic_self_embedding_gap_iff_diagonal_fixed_point_gap
#print axioms MCore.Real.P02SemanticSelfEmbedding.semantic_self_embedding_gap_iff_pointwise
#print axioms MCore.Real.P02SemanticSelfEmbedding.literal_fixed_point_route_not_universal
#print axioms MCore.Real.P02SemanticSelfEmbedding.semantic_self_embedding_implies_sat_not_in_p
#print axioms MCore.Real.P02SemanticSelfEmbedding.sat_in_p_refutes_semantic_self_embedding
#print axioms MCore.Real.P02SemanticSelfEmbedding.semantic_self_embedding_closes_p02

end P02SemanticSelfEmbedding
end Real
end MCore
