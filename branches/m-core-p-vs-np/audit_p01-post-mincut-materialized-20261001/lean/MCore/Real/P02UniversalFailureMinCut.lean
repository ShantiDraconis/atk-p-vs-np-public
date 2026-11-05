import MCore.Real.P01PostMinCutClosure

namespace MCore
namespace Real
namespace P02UniversalFailureMinCut

open CanonicalFinalProof
open CanonicalSATBoundary
open CanonicalCircuitBits
open P01PostMinCutClosure

abbrev CanonicalSAT : BitLanguage :=
  SATBits circuitBitEncoding

/-- The two concrete ways a deterministic polynomial-time candidate can fail
at one canonical SAT input. -/
inductive CandidateFailureMode
    (candidate : PolyDTMCandidate)
    (x : BitString) : Prop
  | timeout :
      ¬ candidate.machine.HaltsWithin
          (candidate.timeBound x.length)
          (initialTMConfig candidate.machine x) →
      CandidateFailureMode candidate x
  | semantic :
      ¬ (candidate.accepting
            (candidate.machine.run
              (candidate.timeBound x.length)
              (initialTMConfig candidate.machine x)).state = true ↔
          CanonicalSAT x) →
      CandidateFailureMode candidate x

theorem failureMode_iff_not_correctAt
    (candidate : PolyDTMCandidate)
    (x : BitString) :
    CandidateFailureMode candidate x ↔
      ¬ candidate.CorrectAt CanonicalSAT x := by
  constructor
  · intro h hCorrect
    rcases hCorrect with ⟨hHalt, hSem⟩
    cases h with
    | timeout hTimeout =>
        exact hTimeout hHalt
    | semantic hBad =>
        exact hBad hSem
  · intro h
    classical
    by_cases hHalt :
        candidate.machine.HaltsWithin
          (candidate.timeBound x.length)
          (initialTMConfig candidate.machine x)
    · apply CandidateFailureMode.semantic
      intro hSem
      exact h ⟨hHalt, hSem⟩
    · exact CandidateFailureMode.timeout hHalt

/-- Exact candidate-indexed producer required after the P01 SAT-in-NP lane is
frozen: choose one canonical SAT bitstring and certify one concrete failure
mode for every deterministic polynomial-time candidate. -/
structure UniversalCounterexampleProducer where
  counterexample : PolyDTMCandidate → BitString
  failure :
    ∀ candidate : PolyDTMCandidate,
      CandidateFailureMode candidate (counterexample candidate)

theorem producer_implies_universal_failure
    (P : UniversalCounterexampleProducer) :
    UniversalFailure CanonicalSAT := by
  intro candidate
  refine ⟨P.counterexample candidate, ?_⟩
  exact (failureMode_iff_not_correctAt
    candidate (P.counterexample candidate)).mp
      (P.failure candidate)

noncomputable def producerOfUniversalFailure
    (h : UniversalFailure CanonicalSAT) :
    UniversalCounterexampleProducer := by
  classical
  let pick : PolyDTMCandidate → BitString :=
    fun candidate => Classical.choose (h candidate)
  refine
    { counterexample := pick
      failure := ?_ }
  intro candidate
  exact (failureMode_iff_not_correctAt candidate (pick candidate)).mpr
    (Classical.choose_spec (h candidate))

theorem producer_iff_universal_failure :
    Nonempty UniversalCounterexampleProducer ↔
      UniversalFailure CanonicalSAT := by
  constructor
  · rintro ⟨P⟩
    exact producer_implies_universal_failure P
  · intro h
    exact ⟨producerOfUniversalFailure h⟩

/-- Once a genuine producer is supplied, the frozen P01 SAT-in-NP result
completes the internal separation endpoint. -/
theorem producer_closes_internal_endpoint
    (P : UniversalCounterexampleProducer) :
    PneqNP :=
  remaining_material_gap_implies_p_ne_np
    (producer_implies_universal_failure P)

#print axioms MCore.Real.P02UniversalFailureMinCut.failureMode_iff_not_correctAt
#print axioms MCore.Real.P02UniversalFailureMinCut.producer_implies_universal_failure
#print axioms MCore.Real.P02UniversalFailureMinCut.producer_iff_universal_failure
#print axioms MCore.Real.P02UniversalFailureMinCut.producer_closes_internal_endpoint

end P02UniversalFailureMinCut
end Real
end MCore
