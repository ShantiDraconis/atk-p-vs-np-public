import MCore.Real.P02KleeneUniversalBridge

namespace MCore
namespace Real
namespace P02TotalCandidateKleeneReduction

open CanonicalFinalProof
open P02UniversalFailureMinCut
open P02KleeneUniversalBridge

def DeclaredHalts
    (M : PolyDTMCandidate)
    (x : BitString) : Prop :=
  M.machine.HaltsWithin
    (M.timeBound x.length)
    (initialTMConfig M.machine x)

def DeclaredClockTotal
    (M : PolyDTMCandidate) : Prop :=
  ∀ x : BitString, DeclaredHalts M x

/-- Only candidates that survive the declared-clock totality check need the
semantic/Kleene self-reference construction. -/
def TotalCandidateKleeneBridge : Prop :=
  ∀ M : PolyDTMCandidate,
    DeclaredClockTotal M →
      Nonempty (CandidateKleeneBridge M)

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

theorem candidate_failure_of_total_kleene
    (B : TotalCandidateKleeneBridge)
    (M : PolyDTMCandidate) :
    ∃ x : BitString, CandidateFailureMode M x := by
  classical
  by_cases hTotal : DeclaredClockTotal M
  · let K : CandidateKleeneBridge M :=
      Classical.choice (B M hTotal)
    refine ⟨P02KleeneUniversalBridge.counterexample K, ?_⟩
    apply (failureMode_iff_not_correctAt
      M (P02KleeneUniversalBridge.counterexample K)).mpr
    exact P02KleeneUniversalBridge.counterexample_fails K
  · rcases exists_timeout_of_not_total M hTotal with ⟨x, hx⟩
    exact ⟨x, CandidateFailureMode.timeout hx⟩

noncomputable def producerOfTotalKleene
    (B : TotalCandidateKleeneBridge) :
    UniversalCounterexampleProducer := by
  classical
  let pick : PolyDTMCandidate → BitString :=
    fun M => Classical.choose (candidate_failure_of_total_kleene B M)
  refine
    { counterexample := pick
      failure := ?_ }
  intro M
  exact Classical.choose_spec (candidate_failure_of_total_kleene B M)

theorem total_candidate_kleene_implies_universal_failure
    (B : TotalCandidateKleeneBridge) :
    UniversalFailure CanonicalSAT :=
  producer_implies_universal_failure (producerOfTotalKleene B)

theorem total_candidate_kleene_closes_internal_endpoint
    (B : TotalCandidateKleeneBridge) :
    PneqNP :=
  producer_closes_internal_endpoint (producerOfTotalKleene B)

/-- Exact remaining sufficient self-reference target after all automatic
timeout failures have been removed. -/
abbrev TotalCandidateKleeneBridgeGap : Prop :=
  TotalCandidateKleeneBridge

#print axioms MCore.Real.P02TotalCandidateKleeneReduction.exists_timeout_of_not_total
#print axioms MCore.Real.P02TotalCandidateKleeneReduction.candidate_failure_of_total_kleene
#print axioms MCore.Real.P02TotalCandidateKleeneReduction.total_candidate_kleene_implies_universal_failure
#print axioms MCore.Real.P02TotalCandidateKleeneReduction.total_candidate_kleene_closes_internal_endpoint

end P02TotalCandidateKleeneReduction
end Real
end MCore
