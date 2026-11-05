import MCore.Real.P01FinalCertificate
import MCore.Real.P02SemanticSelfEmbeddingClose
import MCore.Real.CookNormalizedG3Contract
import MCore.Real.FinalExternalCertificate

namespace MCore
namespace Real
namespace FinalExternalLiveTwoProducer

open CanonicalCircuitBits
open CanonicalSATBoundary
open P01FinalCertificate
open P02TerminalFrontier
open P02SemanticSelfEmbeddingClose
open CookNormalizedG3Contract
open FinalExternalCertificate

/-- Current exact live blockers: concrete P01 machine construction and
the T5-A2 universal semantic diagonal witness. G3 is already closed. -/
def FinalExternalLiveTwoProducer : Prop :=
  P01ConstructionGap ∧ UniversalWitnessExists

theorem final_external_gap_of_live_two_producers
    (h : FinalExternalLiveTwoProducer) :
    FinalExternalGap := by
  rcases h with ⟨hP01, hA2⟩
  have hG1 : SATInNPGap circuitBitEncoding :=
    construction_closes_p01 hP01
  have hP02 : P02Target :=
    universal_witness_closes_p02 hA2
  rcases hP02 with ⟨G⟩
  exact ⟨{
    g1 := hG1
    g2 := G
    g3 := cookNormalizedExternalContract
  }⟩

#print axioms MCore.Real.FinalExternalLiveTwoProducer.final_external_gap_of_live_two_producers

end FinalExternalLiveTwoProducer
end Real
end MCore
