import MCore.Real.P02SemanticSelfEmbedding

namespace MCore
namespace Real
namespace P02KleeneBridgeFrontier

open CanonicalFinalProof
open CanonicalCircuitBits
open CanonicalSATBoundary
open P02SemanticSelfEmbedding

/-- Exact bridge required to reuse an external recursion theorem safely.
It must encode every hardened deterministic candidate as data and decode enough
structure to build a canonical SAT bitstring witnessing semantic self-reference.
No inhabitant is asserted here. -/
structure CandidateCodingBridge where
  code : PolyDTMCandidate -> Nat
  selfBits : PolyDTMCandidate -> BitString
  valid :
    forall M : PolyDTMCandidate,
      P02DiagonalFrontier.CanonicalSATValid (selfBits M)
  flips :
    forall M : PolyDTMCandidate,
      SATBits circuitBitEncoding (selfBits M) <->
        ¬ P02DiagonalFrontier.AcceptsAtDeclaredBound M (selfBits M)

def CandidateCodingBridgeGap : Prop :=
  Nonempty CandidateCodingBridge

def CandidateCodingBridge.toSemanticSelfEmbedder
    (B : CandidateCodingBridge) :
    SemanticSelfEmbedder where
  bits := B.selfBits
  valid := B.valid
  flips := B.flips


/-- The current bridge's numeric `code` field is not consumed by the
semantic transport.  Consequently its gap is propositionally equivalent to
the already-existing semantic self-embedding gap.  This prevents treating
mere machine numbering as an additional mathematical blocker. -/
def semanticSelfEmbedderToCandidateCodingBridge
    (S : SemanticSelfEmbedder) :
    CandidateCodingBridge where
  code := fun _ => 0
  selfBits := S.bits
  valid := S.valid
  flips := S.flips

theorem candidate_coding_bridge_gap_iff_semantic_self_embedding_gap :
    CandidateCodingBridgeGap ↔ SemanticSelfEmbeddingGap := by
  constructor
  · rintro ⟨B⟩
    exact ⟨B.toSemanticSelfEmbedder⟩
  · rintro ⟨S⟩
    exact ⟨semanticSelfEmbedderToCandidateCodingBridge S⟩

theorem candidate_coding_bridge_closes_semantic_self_embedding
    (h : CandidateCodingBridgeGap) :
    SemanticSelfEmbeddingGap := by
  rcases h with ⟨B⟩
  exact ⟨B.toSemanticSelfEmbedder⟩

theorem candidate_coding_bridge_closes_p02
    (h : CandidateCodingBridgeGap) :
    P02TerminalFrontier.P02Target := by
  exact semantic_self_embedding_closes_p02
    (candidate_coding_bridge_closes_semantic_self_embedding h)

#print axioms MCore.Real.P02KleeneBridgeFrontier.candidate_coding_bridge_gap_iff_semantic_self_embedding_gap
#print axioms MCore.Real.P02KleeneBridgeFrontier.candidate_coding_bridge_closes_semantic_self_embedding
#print axioms MCore.Real.P02KleeneBridgeFrontier.candidate_coding_bridge_closes_p02

end P02KleeneBridgeFrontier
end Real
end MCore
