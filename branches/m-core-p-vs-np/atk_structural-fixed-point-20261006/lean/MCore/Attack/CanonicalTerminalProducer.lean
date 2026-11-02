import MCore.Real.CanonicalComplexityBridge
import MCore.Real.FailProofAllGaps
import MCore.Real.P01RawTotalizationProducer
import MCore.BackwardAudit.OrientedWitnessBoundary

namespace MCore
namespace Attack

/-- Exact fixed official-model witness target for the canonical bit-language model. -/
structure CanonicalNotInPWitness where
  language : Real.CanonicalFinalProof.BitLanguage
  in_np : Real.CanonicalComplexityBridge.canonicalInterface.inNP language
  not_in_p : ¬ Real.CanonicalComplexityBridge.canonicalInterface.inP language



/-- The completed P01 machine construction materially closes the NP side for
the exact canonical SAT bit-language.  No lower-bound hypothesis is used. -/
theorem canonicalSATInNP_closed :
    Real.CanonicalComplexityBridge.canonicalInterface.inNP
      (Real.CanonicalSATBoundary.SATBits
        Real.CanonicalCircuitBits.circuitBitEncoding) := by
  change Real.CanonicalFinalProof.InNP
    (Real.CanonicalSATBoundary.SATBits
      Real.CanonicalCircuitBits.circuitBitEncoding)
  exact
    Real.P01FinalCertificate.construction_closes_p01
      Real.P01RawTotalizationProducer.p01ConstructionGap_closed

/-- Material terminal producer.  Unlike `CanonicalNotInPWitness`, this object
does not store the endpoint proposition `¬ inP language`.  It stores an
operational counterexample generator: for every deterministic polynomial-time
candidate it returns a concrete input on which that candidate is incorrect. -/
structure CanonicalFailureProducer where
  language : Real.CanonicalFinalProof.BitLanguage
  in_np : Real.CanonicalComplexityBridge.canonicalInterface.inNP language
  failure_generator : Real.FailProofAllGaps.FailureGenerator language

/-- A material failure producer derives the endpoint rather than receiving it
as an assumption or structure field. -/
theorem canonicalFailureProducer_not_in_p
    (w : CanonicalFailureProducer) :
    ¬ Real.CanonicalComplexityBridge.canonicalInterface.inP w.language := by
  have hFail : Real.CanonicalFinalProof.UniversalFailure w.language :=
    Real.FailProofAllGaps.failure_generator_implies_universal_failure
      w.failure_generator
  exact Real.CanonicalFinalProof.universal_failure_implies_not_in_p hFail

/-- Producer-first terminal closure: the separation theorem consumes only the
operational generator and the independently constructed NP witness. -/
theorem canonicalFailureProducer_closes_separation
    (w : CanonicalFailureProducer) :
    ClosedDiscriminant.SeparationFinal
      Real.CanonicalComplexityBridge.canonicalInterface.inP
      Real.CanonicalComplexityBridge.canonicalInterface.inNP := by
  exact BackwardAudit.typeB_closes_separation
    { language := w.language
      in_np := w.in_np
      not_in_p := canonicalFailureProducer_not_in_p w }

/-- Once the NP side is discharged by P01, the exact remaining material
producer is only the operational failure generator for the SAME SAT language. -/
theorem canonicalSAT_failure_generator_closes_separation
    (G : Real.FailProofAllGaps.FailureGenerator
      (Real.CanonicalSATBoundary.SATBits
        Real.CanonicalCircuitBits.circuitBitEncoding)) :
    ClosedDiscriminant.SeparationFinal
      Real.CanonicalComplexityBridge.canonicalInterface.inP
      Real.CanonicalComplexityBridge.canonicalInterface.inNP := by
  exact canonicalFailureProducer_closes_separation
    { language :=
        Real.CanonicalSATBoundary.SATBits
          Real.CanonicalCircuitBits.circuitBitEncoding
      in_np := canonicalSATInNP_closed
      failure_generator := G }

/-- The canonical interface already matches the repository's official InP/InNP predicates by rfl. -/
theorem canonicalModelMatch :
    ∀ L : Real.CanonicalFinalProof.BitLanguage,
      (Real.CanonicalComplexityBridge.canonicalInterface.inP L ↔
        Real.CanonicalFinalProof.InP L) ∧
      (Real.CanonicalComplexityBridge.canonicalInterface.inNP L ↔
        Real.CanonicalFinalProof.InNP L) := by
  intro L
  exact ⟨
    Real.CanonicalComplexityBridge.canonical_interface_p_match L,
    Real.CanonicalComplexityBridge.canonical_interface_np_match L
  ⟩

/-- A genuine fixed not-in-P witness is exactly enough for the separation lane. -/
theorem canonicalWitness_closes_separation
    (w : CanonicalNotInPWitness) :
    ClosedDiscriminant.SeparationFinal
      Real.CanonicalComplexityBridge.canonicalInterface.inP
      Real.CanonicalComplexityBridge.canonicalInterface.inNP := by
  exact BackwardAudit.typeB_closes_separation
    { language := w.language
      in_np := w.in_np
      not_in_p := w.not_in_p }

def terminalProducerStatus : String :=
  "OPEN_MATH: canonical SAT InNP is CLOSED by P01; the sole remaining material producer is FailureGenerator (SATBits circuitBitEncoding) without endpoint-equivalent premises"

#print axioms canonicalSATInNP_closed
#print axioms canonicalSAT_failure_generator_closes_separation
#print axioms canonicalFailureProducer_not_in_p
#print axioms canonicalFailureProducer_closes_separation
#print axioms canonicalModelMatch
#print axioms canonicalWitness_closes_separation

end Attack
end MCore
