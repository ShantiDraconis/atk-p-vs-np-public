import MCore.Real.CanonicalSATBoundary
import MCore.Real.CanonicalCircuitBits
import MCore.Real.P02SemanticSelfEmbedding

namespace MCore
namespace Real
namespace P02LowerBoundProducer

open CanonicalFinalProof
open FailProofAllGaps
open CanonicalSATBoundary
open CanonicalCircuitBits
open P02SemanticSelfEmbedding

/--
All producer lanes terminate in the already-hardened canonical object
`FailureGenerator (SATBits circuitBitEncoding)`.
No new notion of lower bound is introduced here.
-/
structure DiagonalAdviceData where
  fail_generator : FailureGenerator (SATBits circuitBitEncoding)

structure NonNaturalData where
  fail_generator : FailureGenerator (SATBits circuitBitEncoding)

structure GCTData where
  fail_generator : FailureGenerator (SATBits circuitBitEncoding)

structure MetaComplexityData where
  fail_generator : FailureGenerator (SATBits circuitBitEncoding)

/-- Existing semantic self-embedding route, recovered from the historical T5-A2 lane. -/
def semanticSelfEmbeddingToFailureGenerator
    (S : SemanticSelfEmbedder) :
    FailureGenerator (SATBits circuitBitEncoding) :=
  S.toDiagonalFamily.toFailureGenerator

inductive LowerBoundProducer where
  | diagonalAdvice (d : DiagonalAdviceData)
  | nonNatural (d : NonNaturalData)
  | gct (d : GCTData)
  | metaComplexity (d : MetaComplexityData)
  | semanticSelfEmbedding (S : SemanticSelfEmbedder)

/-- Every admitted producer is only a typed route to the existing fail
generator.  Hence transport is kernel-trivial and cannot weaken the target. -/
def LowerBoundProducer.toFailureGenerator :
    LowerBoundProducer →
      FailureGenerator (SATBits circuitBitEncoding)
  | .diagonalAdvice d => d.fail_generator
  | .nonNatural d => d.fail_generator
  | .gct d => d.fail_generator
  | .metaComplexity d => d.fail_generator
  | .semanticSelfEmbedding S => semanticSelfEmbeddingToFailureGenerator S

/-- Single normative OPEN_MATH root for all competing lower-bound lanes. -/
def LowerBoundProducerGap : Prop :=
  Nonempty LowerBoundProducer

theorem producer_gap_closes_sat_fail
    (h : LowerBoundProducerGap) :
    SATFailGap circuitBitEncoding := by
  rcases h with ⟨P⟩
  exact ⟨P.toFailureGenerator⟩

theorem producer_gap_closes_internal_separation
    (hNP : SATInNPGap circuitBitEncoding)
    (h : LowerBoundProducerGap) :
    PneqNP := by
  exact sat_internal_closure_implies_p_ne_np
    { encoding := circuitBitEncoding
      sat_in_np := hNP
      fail_generator := (Classical.choice (producer_gap_closes_sat_fail h)) }

/-- No producer is postulated here.  The theorem records the exact remaining
mathematical payload without adding unproved proof terms. -/
theorem producer_gap_iff_sat_fail :
    LowerBoundProducerGap ↔ SATFailGap circuitBitEncoding := by
  constructor
  · exact producer_gap_closes_sat_fail
  · intro h
    rcases h with ⟨G⟩
    exact ⟨.diagonalAdvice ⟨G⟩⟩

#print axioms MCore.Real.P02LowerBoundProducer.semanticSelfEmbeddingToFailureGenerator
#print axioms MCore.Real.P02LowerBoundProducer.producer_gap_closes_sat_fail
#print axioms MCore.Real.P02LowerBoundProducer.producer_gap_closes_internal_separation
#print axioms MCore.Real.P02LowerBoundProducer.producer_gap_iff_sat_fail

end P02LowerBoundProducer
end Real
end MCore
