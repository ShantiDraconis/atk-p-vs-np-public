import MCore.Real.P02UniversalFailureMinCut
import MCore.Real.FailProofAllGaps

namespace MCore
namespace Real
namespace P02FailureNormalForms

open CanonicalFinalProof
open CanonicalSATBoundary
open CanonicalCircuitBits
open FailProofAllGaps
open P02UniversalFailureMinCut

abbrev CanonicalSAT : BitLanguage :=
  P02UniversalFailureMinCut.CanonicalSAT

private def candidateAnswer
    (candidate : PolyDTMCandidate)
    (x : BitString) : Bool :=
  candidate.accepting
    (candidate.machine.run
      (candidate.timeBound x.length)
      (initialTMConfig candidate.machine x)).state

/-- Exact semantic disagreement normal form: either the deterministic
candidate accepts a non-SAT input, or rejects a SAT input. -/
inductive SemanticDisagreement
    (candidate : PolyDTMCandidate)
    (x : BitString) : Prop
  | falsePositive :
      candidateAnswer candidate x = true →
      ¬ CanonicalSAT x →
      SemanticDisagreement candidate x
  | falseNegative :
      candidateAnswer candidate x ≠ true →
      CanonicalSAT x →
      SemanticDisagreement candidate x

theorem semanticDisagreement_iff_not_semantic_correct
    (candidate : PolyDTMCandidate)
    (x : BitString) :
    SemanticDisagreement candidate x ↔
      ¬ (candidateAnswer candidate x = true ↔ CanonicalSAT x) := by
  constructor
  · intro h hIff
    cases h with
    | falsePositive hAns hNotSat =>
        exact hNotSat (hIff.mp hAns)
    | falseNegative hAns hSat =>
        exact hAns (hIff.mpr hSat)
  · intro h
    classical
    by_cases hAns : candidateAnswer candidate x = true
    · by_cases hSat : CanonicalSAT x
      · exfalso
        apply h
        constructor
        · intro _
          exact hSat
        · intro _
          exact hAns
      · exact SemanticDisagreement.falsePositive hAns hSat
    · by_cases hSat : CanonicalSAT x
      · exact SemanticDisagreement.falseNegative hAns hSat
      · exfalso
        apply h
        constructor
        · intro hTrue
          exact False.elim (hAns hTrue)
        · intro hSat'
          exact False.elim (hSat hSat')

/-- Fully normalized per-input failure: timeout, false positive, or false
negative. These are the only three ways to violate CorrectAt. -/
inductive NormalizedFailure
    (candidate : PolyDTMCandidate)
    (x : BitString) : Prop
  | timeout :
      ¬ candidate.machine.HaltsWithin
          (candidate.timeBound x.length)
          (initialTMConfig candidate.machine x) →
      NormalizedFailure candidate x
  | semantic :
      SemanticDisagreement candidate x →
      NormalizedFailure candidate x

theorem normalizedFailure_iff_not_correctAt
    (candidate : PolyDTMCandidate)
    (x : BitString) :
    NormalizedFailure candidate x ↔
      ¬ candidate.CorrectAt CanonicalSAT x := by
  constructor
  · intro h hCorrect
    rcases hCorrect with ⟨hHalt, hSem⟩
    cases h with
    | timeout hTimeout =>
        exact hTimeout hHalt
    | semantic hDis =>
        exact
          ((semanticDisagreement_iff_not_semantic_correct candidate x).mp hDis)
            hSem
  · intro h
    classical
    by_cases hHalt :
        candidate.machine.HaltsWithin
          (candidate.timeBound x.length)
          (initialTMConfig candidate.machine x)
    · apply NormalizedFailure.semantic
      apply (semanticDisagreement_iff_not_semantic_correct candidate x).mpr
      intro hSem
      exact h ⟨hHalt, hSem⟩
    · exact NormalizedFailure.timeout hHalt

/-- Candidate-indexed normal-form producer. This is equivalent to the P02
universal counterexample producer, but its semantic branch has no remaining
opaque iff-disagreement. -/
structure NormalizedCounterexampleProducer where
  counterexample : PolyDTMCandidate → BitString
  failure :
    ∀ candidate : PolyDTMCandidate,
      NormalizedFailure candidate (counterexample candidate)

def NormalizedCounterexampleProducer.toFailureGenerator
    (P : NormalizedCounterexampleProducer) :
    FailureGenerator CanonicalSAT where
  counterexample := P.counterexample
  fails := by
    intro candidate
    exact
      (normalizedFailure_iff_not_correctAt
        candidate (P.counterexample candidate)).mp
        (P.failure candidate)

theorem normalizedProducer_implies_universal_failure
    (P : NormalizedCounterexampleProducer) :
    UniversalFailure CanonicalSAT :=
  failure_generator_implies_universal_failure P.toFailureGenerator

noncomputable def normalizedProducerOfUniversalFailure
    (h : UniversalFailure CanonicalSAT) :
    NormalizedCounterexampleProducer := by
  classical
  let pick : PolyDTMCandidate → BitString :=
    fun candidate => Classical.choose (h candidate)
  refine
    { counterexample := pick
      failure := ?_ }
  intro candidate
  exact
    (normalizedFailure_iff_not_correctAt candidate (pick candidate)).mpr
      (Classical.choose_spec (h candidate))

theorem normalizedProducer_iff_universal_failure :
    Nonempty NormalizedCounterexampleProducer ↔
      UniversalFailure CanonicalSAT := by
  constructor
  · rintro ⟨P⟩
    exact normalizedProducer_implies_universal_failure P
  · intro h
    exact ⟨normalizedProducerOfUniversalFailure h⟩

theorem normalizedProducer_closes_internal_endpoint
    (P : NormalizedCounterexampleProducer) :
    PneqNP :=
  P01PostMinCutClosure.remaining_material_gap_implies_p_ne_np
    (normalizedProducer_implies_universal_failure P)

#print axioms MCore.Real.P02FailureNormalForms.semanticDisagreement_iff_not_semantic_correct
#print axioms MCore.Real.P02FailureNormalForms.normalizedFailure_iff_not_correctAt
#print axioms MCore.Real.P02FailureNormalForms.NormalizedCounterexampleProducer.toFailureGenerator
#print axioms MCore.Real.P02FailureNormalForms.normalizedProducer_iff_universal_failure
#print axioms MCore.Real.P02FailureNormalForms.normalizedProducer_closes_internal_endpoint

end P02FailureNormalForms
end Real
end MCore
