import MCore.Real.P02FailureNormalForms

namespace MCore
namespace Real
namespace P02TotalCandidateSemanticCore

open CanonicalFinalProof
open P02UniversalFailureMinCut
open P02FailureNormalForms

abbrev SATTarget : BitLanguage :=
  P02UniversalFailureMinCut.CanonicalSAT

def DeclaredHalts
    (M : PolyDTMCandidate)
    (x : BitString) : Prop :=
  M.machine.HaltsWithin
    (M.timeBound x.length)
    (initialTMConfig M.machine x)

def DeclaredClockTotal
    (M : PolyDTMCandidate) : Prop :=
  ∀ x : BitString, DeclaredHalts M x

/-- Exact remaining semantic core after timeout failures are removed.
Only candidates that halt within their own declared polynomial clock on every
input need a semantic SAT counterexample. -/
def TotalCandidateSemanticCore : Prop :=
  ∀ M : PolyDTMCandidate,
    DeclaredClockTotal M →
      ∃ x : BitString, SemanticDisagreement M x

theorem exists_timeout_of_not_total
    (M : PolyDTMCandidate)
    (h : ¬ DeclaredClockTotal M) :
    ∃ x : BitString, ¬ DeclaredHalts M x := by
  classical
  apply Classical.byContradiction
  intro hNo
  apply h
  intro x
  apply Classical.byContradiction
  intro hx
  exact hNo ⟨x, hx⟩

/-- The total-candidate semantic core yields one exact failure mode for every
candidate: semantic disagreement for total candidates, timeout otherwise. -/
theorem candidate_failure_of_total_semantic
    (H : TotalCandidateSemanticCore)
    (M : PolyDTMCandidate) :
    ∃ x : BitString, CandidateFailureMode M x := by
  classical
  by_cases hTotal : DeclaredClockTotal M
  · rcases H M hTotal with ⟨x, hSem⟩
    have hBad :
        ¬ M.CorrectAt SATTarget x := by
      exact (normalizedFailure_iff_not_correctAt M x).mp
        (NormalizedFailure.semantic hSem)
    exact ⟨x, (failureMode_iff_not_correctAt M x).mpr hBad⟩
  · rcases exists_timeout_of_not_total M hTotal with ⟨x, hx⟩
    exact ⟨x, CandidateFailureMode.timeout hx⟩

noncomputable def producerOfTotalSemanticCore
    (H : TotalCandidateSemanticCore) :
    UniversalCounterexampleProducer := by
  classical
  let pick : PolyDTMCandidate → BitString :=
    fun M => Classical.choose (candidate_failure_of_total_semantic H M)
  refine
    { counterexample := pick
      failure := ?_ }
  intro M
  exact Classical.choose_spec (candidate_failure_of_total_semantic H M)

theorem total_semantic_core_implies_universal_failure
    (H : TotalCandidateSemanticCore) :
    UniversalFailure SATTarget :=
  producer_implies_universal_failure
    (producerOfTotalSemanticCore H)

/-- UniversalFailure contains no additional material beyond the semantic
counterexample obligation for candidates that already satisfy declared-clock
totality. -/
theorem universal_failure_implies_total_semantic_core
    (h : UniversalFailure SATTarget) :
    TotalCandidateSemanticCore := by
  intro M hTotal
  rcases h M with ⟨x, hBad⟩
  have hNorm : NormalizedFailure M x :=
    (normalizedFailure_iff_not_correctAt M x).mpr hBad
  cases hNorm with
  | timeout hTimeout =>
      exact False.elim (hTimeout (hTotal x))
  | semantic hSem =>
      exact ⟨x, hSem⟩

theorem total_semantic_core_iff_universal_failure :
    TotalCandidateSemanticCore ↔ UniversalFailure SATTarget := by
  constructor
  · exact total_semantic_core_implies_universal_failure
  · exact universal_failure_implies_total_semantic_core

theorem total_semantic_core_closes_internal_endpoint
    (H : TotalCandidateSemanticCore) :
    PneqNP :=
  producer_closes_internal_endpoint
    (producerOfTotalSemanticCore H)

#print axioms MCore.Real.P02TotalCandidateSemanticCore.exists_timeout_of_not_total
#print axioms MCore.Real.P02TotalCandidateSemanticCore.candidate_failure_of_total_semantic
#print axioms MCore.Real.P02TotalCandidateSemanticCore.total_semantic_core_iff_universal_failure
#print axioms MCore.Real.P02TotalCandidateSemanticCore.total_semantic_core_closes_internal_endpoint

end P02TotalCandidateSemanticCore
end Real
end MCore
