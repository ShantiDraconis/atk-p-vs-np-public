import MCore.Real.P02TotalCandidateSemanticCore

namespace MCore
namespace Real
namespace P02SemanticFlipCore

open CanonicalFinalProof
open P02UniversalFailureMinCut
open P02FailureNormalForms
open P02TotalCandidateSemanticCore

abbrev SATTarget : BitLanguage :=
  P02UniversalFailureMinCut.CanonicalSAT

def DeclaredAccepts
    (M : PolyDTMCandidate)
    (x : BitString) : Prop :=
  M.accepting
    (M.machine.run
      (M.timeBound x.length)
      (initialTMConfig M.machine x)).state = true

/-- Exact Boolean diagonal law at one input.  This is semantic disagreement,
not a syntactic or literal fixed-point assumption. -/
def SemanticFlip
    (M : PolyDTMCandidate)
    (x : BitString) : Prop :=
  SATTarget x ↔ ¬ DeclaredAccepts M x

theorem semanticFlip_iff_semanticDisagreement
    (M : PolyDTMCandidate)
    (x : BitString) :
    SemanticFlip M x ↔ SemanticDisagreement M x := by
  constructor
  · intro h
    classical
    by_cases hAcc : DeclaredAccepts M x
    · apply SemanticDisagreement.falsePositive
      · exact hAcc
      · intro hSat
        exact (h.mp hSat) hAcc
    · apply SemanticDisagreement.falseNegative
      · exact hAcc
      · exact h.mpr hAcc
  · intro h
    constructor
    · intro hSat
      intro hAcc
      cases h with
      | falsePositive hA hNotSat =>
          exact hNotSat hSat
      | falseNegative hNotA hS =>
          exact hNotA hAcc
    · intro hNotAcc
      cases h with
      | falsePositive hA hNotSat =>
          exact False.elim (hNotAcc hA)
      | falseNegative hNotA hSat =>
          exact hSat

/-- Exact remaining semantic producer, restricted to candidates which already
halt within their own declared polynomial clock on every input. -/
def TotalCandidateSemanticFlipCore : Prop :=
  ∀ M : PolyDTMCandidate,
    DeclaredClockTotal M →
      ∃ x : BitString, SemanticFlip M x

theorem semantic_flip_core_implies_total_semantic_core
    (H : TotalCandidateSemanticFlipCore) :
    TotalCandidateSemanticCore := by
  intro M hTotal
  rcases H M hTotal with ⟨x, hFlip⟩
  exact ⟨x, (semanticFlip_iff_semanticDisagreement M x).mp hFlip⟩

theorem total_semantic_core_implies_semantic_flip_core
    (H : TotalCandidateSemanticCore) :
    TotalCandidateSemanticFlipCore := by
  intro M hTotal
  rcases H M hTotal with ⟨x, hDis⟩
  exact ⟨x, (semanticFlip_iff_semanticDisagreement M x).mpr hDis⟩

theorem semantic_flip_core_iff_total_semantic_core :
    TotalCandidateSemanticFlipCore ↔ TotalCandidateSemanticCore := by
  constructor
  · exact semantic_flip_core_implies_total_semantic_core
  · exact total_semantic_core_implies_semantic_flip_core

theorem semantic_flip_core_iff_universal_failure :
    TotalCandidateSemanticFlipCore ↔
      UniversalFailure SATTarget := by
  exact semantic_flip_core_iff_total_semantic_core.trans
    total_semantic_core_iff_universal_failure

theorem semantic_flip_core_closes_internal_endpoint
    (H : TotalCandidateSemanticFlipCore) :
    PneqNP :=
  total_semantic_core_closes_internal_endpoint
    (semantic_flip_core_implies_total_semantic_core H)

#print axioms MCore.Real.P02SemanticFlipCore.semanticFlip_iff_semanticDisagreement
#print axioms MCore.Real.P02SemanticFlipCore.semantic_flip_core_iff_total_semantic_core
#print axioms MCore.Real.P02SemanticFlipCore.semantic_flip_core_iff_universal_failure
#print axioms MCore.Real.P02SemanticFlipCore.semantic_flip_core_closes_internal_endpoint

end P02SemanticFlipCore
end Real
end MCore
