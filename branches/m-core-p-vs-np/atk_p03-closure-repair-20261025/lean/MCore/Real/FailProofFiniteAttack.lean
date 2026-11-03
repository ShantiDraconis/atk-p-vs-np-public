import MCore.Real.FailProofAllGaps

namespace MCore
namespace Real
namespace FailProofFiniteAttack

open CanonicalFinalProof

def EmptyLanguage : BitLanguage := fun _ => False

def alwaysRejectMachine : TM (Fin 1) (Option Bool) :=
  { initial := 0
    blank := none
    transition := fun q symbol => (q, symbol, .stay)
    halting := fun _ => true }

def alwaysRejectCandidate : PolyDTMCandidate :=
  { stateCount := 0
    machine := alwaysRejectMachine
    blank_none := rfl
    accepting := fun _ => false
    timeBound := fun _ => 0
    time_poly := by
      refine ⟨0, 0, ?_⟩
      intro n
      simp [CanonicalFinalProof.PolynomialTimeBound] }

theorem alwaysRejectCandidate_correct :
    ∀ x : BitString,
      alwaysRejectCandidate.CorrectAt EmptyLanguage x := by
  intro x
  simp [PolyDTMCandidate.CorrectAt,
    alwaysRejectCandidate, alwaysRejectMachine,
    EmptyLanguage, initialTMConfig, TM.HaltsWithin, TM.run]

def emptyLanguageRealization : PolyDTMRealization EmptyLanguage :=
  { candidate := alwaysRejectCandidate
    decides := alwaysRejectCandidate_correct }

theorem empty_language_in_p : InP EmptyLanguage := by
  exact ⟨emptyLanguageRealization⟩

theorem empty_language_not_universal_failure :
    ¬ UniversalFailure EmptyLanguage := by
  intro h
  exact (universal_failure_implies_not_in_p h) empty_language_in_p

/-- Finite sampled failure evidence over an explicitly listed candidate set. -/
def FiniteFailureEvidence
    (language : BitLanguage)
    (candidates : List PolyDTMCandidate) : Prop :=
  ∀ candidate ∈ candidates,
    ∃ x : BitString, ¬ candidate.CorrectAt language x

theorem empty_sample_evidence :
    FiniteFailureEvidence EmptyLanguage [] := by
  intro candidate h
  cases h

/-- The invalid promotion rule under attack. -/
def FiniteToUniversalPrinciple : Prop :=
  ∀ language : BitLanguage,
    ∀ candidates : List PolyDTMCandidate,
      FiniteFailureEvidence language candidates →
      UniversalFailure language

/-- Formal countermodel: finite sampled evidence, even when syntactically valid,
    does not by itself imply a universal lower bound. -/
theorem finite_to_universal_principle_refuted :
    ¬ FiniteToUniversalPrinciple := by
  intro h
  have hUniversal : UniversalFailure EmptyLanguage :=
    h EmptyLanguage [] empty_sample_evidence
  exact empty_language_not_universal_failure hUniversal

#print axioms MCore.Real.FailProofFiniteAttack.alwaysRejectCandidate_correct
#print axioms MCore.Real.FailProofFiniteAttack.empty_language_in_p
#print axioms MCore.Real.FailProofFiniteAttack.empty_language_not_universal_failure
#print axioms MCore.Real.FailProofFiniteAttack.finite_to_universal_principle_refuted

end FailProofFiniteAttack
end Real
end MCore
