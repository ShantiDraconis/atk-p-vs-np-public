import MCore.Real.CanonicalCircuitBits
import MCore.Real.CanonicalSATBoundary
import MCore.Real.FailProofAllGaps

namespace MCore
namespace Real
namespace P02TotalCandidateFailureMinCut

open CanonicalFinalProof
open CanonicalSATBoundary
open CanonicalCircuitBits
open FailProofAllGaps

abbrev CanonicalSAT : BitLanguage :=
  SATBits circuitBitEncoding

/-- A candidate is total at exactly the polynomial clock it declares. -/
def DeclaredClockTotal (M : PolyDTMCandidate) : Prop :=
  ∀ x : BitString,
    M.machine.HaltsWithin
      (M.timeBound x.length)
      (initialTMConfig M.machine x)

/-- Non-totality exposes a concrete timeout input without requiring extra tactics. -/
theorem exists_timeout_of_not_total
    (M : PolyDTMCandidate)
    (h : ¬ DeclaredClockTotal M) :
    ∃ x : BitString,
      ¬ M.machine.HaltsWithin
        (M.timeBound x.length)
        (initialTMConfig M.machine x) := by
  classical
  apply Classical.byContradiction
  intro hNo
  apply h
  intro x
  apply Classical.byContradiction
  intro hx
  exact hNo ⟨x, hx⟩

/-- The only lower-bound content left after timeout failures are discharged:
for every candidate that really halts at its declared clock, produce one input
where its Boolean answer disagrees with canonical SAT. -/
structure TotalSemanticFailureProducer where
  counterexample :
    ∀ (M : PolyDTMCandidate), DeclaredClockTotal M → BitString
  disagrees :
    ∀ (M : PolyDTMCandidate) (hTotal : DeclaredClockTotal M),
      let x := counterexample M hTotal
      ¬ (M.accepting
          (M.machine.run
            (M.timeBound x.length)
            (initialTMConfig M.machine x)).state = true ↔
        CanonicalSAT x)

/-- A total semantic-failure producer gives the full FailureGenerator.
Non-total candidates need no new mathematics: classical witness extraction
selects an input where their declared polynomial clock already fails. -/
noncomputable def TotalSemanticFailureProducer.toFailureGenerator
    (P : TotalSemanticFailureProducer) :
    FailureGenerator CanonicalSAT := by
  classical
  let pick : PolyDTMCandidate → BitString :=
    fun M =>
      if h : DeclaredClockTotal M then
        P.counterexample M h
      else
        Classical.choose (exists_timeout_of_not_total M h)
  refine
    { counterexample := pick
      fails := ?_ }
  intro M
  by_cases hTotal : DeclaredClockTotal M
  · have hPick : pick M = P.counterexample M hTotal := by
      simp [pick, hTotal]
    rw [hPick]
    intro hCorrect
    exact P.disagrees M hTotal hCorrect.2
  · have hex := exists_timeout_of_not_total M hTotal
    have hPick :
        ¬ M.machine.HaltsWithin
          (M.timeBound (pick M).length)
          (initialTMConfig M.machine (pick M)) := by
      simp only [pick, hTotal, dite_false]
      exact Classical.choose_spec hex
    intro hCorrect
    exact hPick hCorrect.1

theorem totalSemanticFailureProducer_implies_universalFailure
    (P : TotalSemanticFailureProducer) :
    UniversalFailure CanonicalSAT :=
  failure_generator_implies_universal_failure P.toFailureGenerator

theorem totalSemanticFailureProducer_closes_internal_endpoint
    (hNP : InNP CanonicalSAT)
    (P : TotalSemanticFailureProducer) :
    PneqNP :=
  target_failure_implies_p_ne_np hNP
    (totalSemanticFailureProducer_implies_universalFailure P)


/-- Exactness audit: on declared-total candidates, any canonical universal
failure is necessarily semantic, so G2 reconstructs the total semantic
producer. This proves the mincut is an exact normal form, not an easier theorem. -/
noncomputable def totalSemanticFailureProducer_of_universalFailure
    (hFail : UniversalFailure CanonicalSAT) :
    TotalSemanticFailureProducer := by
  classical
  let pick :
      ∀ (M : PolyDTMCandidate), DeclaredClockTotal M → BitString :=
    fun M hTotal => Classical.choose (hFail M)
  refine
    { counterexample := pick
      disagrees := ?_ }
  intro M hTotal
  dsimp
  let x : BitString := pick M hTotal
  have hBad : ¬ M.CorrectAt CanonicalSAT x := by
    exact Classical.choose_spec (hFail M)
  change ¬ (M.accepting
      (M.machine.run
        (M.timeBound x.length)
        (initialTMConfig M.machine x)).state = true ↔
      CanonicalSAT x)
  intro hSem
  apply hBad
  exact ⟨hTotal x, hSem⟩

theorem totalSemanticFailureProducer_iff_universalFailure :
    Nonempty TotalSemanticFailureProducer ↔
      UniversalFailure CanonicalSAT := by
  constructor
  · rintro ⟨P⟩
    exact totalSemanticFailureProducer_implies_universalFailure P
  · intro h
    exact ⟨totalSemanticFailureProducer_of_universalFailure h⟩

/-- This is the narrowed material frontier. It contains no not-in-P field,
UniversalFailure field, or endpoint proposition. -/
def TOTAL_SEMANTIC_FAILURE_OPEN_MATH : Prop :=
  Nonempty TotalSemanticFailureProducer

#print axioms MCore.Real.P02TotalCandidateFailureMinCut.exists_timeout_of_not_total
#print axioms MCore.Real.P02TotalCandidateFailureMinCut.TotalSemanticFailureProducer.toFailureGenerator
#print axioms MCore.Real.P02TotalCandidateFailureMinCut.totalSemanticFailureProducer_implies_universalFailure
#print axioms MCore.Real.P02TotalCandidateFailureMinCut.totalSemanticFailureProducer_closes_internal_endpoint
#print axioms MCore.Real.P02TotalCandidateFailureMinCut.totalSemanticFailureProducer_of_universalFailure
#print axioms MCore.Real.P02TotalCandidateFailureMinCut.totalSemanticFailureProducer_iff_universalFailure

end P02TotalCandidateFailureMinCut
end Real
end MCore
