import MCore.Real.P02ComplementRunRealization

namespace MCore
namespace Real
namespace P02ExactDiagonalFrontier

open CanonicalFinalProof
open P02UniversalFailureMinCut
open P02KleeneUniversalBridge
open P02TotalCandidateKleeneReduction
open P02ComplementRunRealization
open P01PostMinCutClosure

/-- The exact candidate-indexed semantic object needed after the concrete
complement Cook--Levin reduction has been built.  No compiler, code type, or
fixed-point wrapper is stored here. -/
def ExactDiagonalWitness
    (M : PolyDTMCandidate) : Prop :=
  ∃ x : BitString,
    CanonicalSAT x ↔ ¬ DeclaredAccepts M x

/-- Exact uniform producer after timeout candidates have been split off.
This is intentionally stated without Kleene/compiler scaffolding. -/
def TotalExactDiagonalProducer : Prop :=
  ∀ M : PolyDTMCandidate,
    DeclaredClockTotal M →
      ExactDiagonalWitness M

/-- A semantic flip on one input is already a concrete correctness failure on
that input.  This is the contradiction step only; it assumes no universal
endpoint. -/
theorem flip_implies_not_correctAt
    (M : PolyDTMCandidate)
    (x : BitString)
    (hFlip :
      CanonicalSAT x ↔ ¬ DeclaredAccepts M x) :
    ¬ M.CorrectAt CanonicalSAT x := by
  intro hCorrect
  rcases hCorrect with ⟨_, hSem⟩
  by_cases hAcc : DeclaredAccepts M x
  · have hSat : CanonicalSAT x := hSem.mp hAcc
    exact (hFlip.mp hSat) hAcc
  · have hSat : CanonicalSAT x := hFlip.mpr hAcc
    exact hAcc (hSem.mpr hSat)

/-- Conversely, once the declared clock really halts on x, every correctness
failure is exactly a semantic flip on x.  Thus the flip is not weaker than the
original failure endpoint on total candidates. -/
theorem not_correctAt_implies_flip_of_halt
    (M : PolyDTMCandidate)
    (x : BitString)
    (hHalt : DeclaredHalts M x)
    (hBad : ¬ M.CorrectAt CanonicalSAT x) :
    CanonicalSAT x ↔ ¬ DeclaredAccepts M x := by
  classical
  have hSemBad :
      ¬ (DeclaredAccepts M x ↔ CanonicalSAT x) := by
    intro hSem
    exact hBad ⟨hHalt, hSem⟩
  constructor
  · intro hSat hAcc
    apply hSemBad
    constructor
    · intro _
      exact hSat
    · intro _
      exact hAcc
  · intro hNotAcc
    by_contra hNotSat
    apply hSemBad
    constructor
    · intro hAcc
      exact False.elim (hNotAcc hAcc)
    · intro hSat
      exact False.elim (hNotSat hSat)

/-- Pointwise exactness of the frontier after the timeout branch is removed. -/
theorem flip_iff_not_correctAt_of_halt
    (M : PolyDTMCandidate)
    (x : BitString)
    (hHalt : DeclaredHalts M x) :
    (CanonicalSAT x ↔ ¬ DeclaredAccepts M x) ↔
      ¬ M.CorrectAt CanonicalSAT x := by
  constructor
  · exact flip_implies_not_correctAt M x
  · exact not_correctAt_implies_flip_of_halt M x hHalt

/-- A genuine exact diagonal producer closes the universal failure target:
total candidates fail semantically; non-total candidates fail by timeout. -/
theorem total_exact_diagonal_implies_universal_failure
    (B : TotalExactDiagonalProducer) :
    UniversalFailure CanonicalSAT := by
  intro M
  classical
  by_cases hTotal : DeclaredClockTotal M
  · rcases B M hTotal with ⟨x, hFlip⟩
    exact ⟨x, flip_implies_not_correctAt M x hFlip⟩
  · rcases exists_timeout_of_not_total M hTotal with ⟨x, hTimeout⟩
    refine ⟨x, ?_⟩
    intro hCorrect
    exact hTimeout hCorrect.1

/-- The reverse direction is crucial for frontier accounting: on total
candidates, a universal failure proof reconstructs the exact semantic flip.
Therefore TotalExactDiagonalProducer must not be counted as an easier lemma or
as an independently closed bridge. -/
theorem universal_failure_implies_total_exact_diagonal
    (hFail : UniversalFailure CanonicalSAT) :
    TotalExactDiagonalProducer := by
  intro M hTotal
  rcases hFail M with ⟨x, hBad⟩
  exact ⟨x,
    not_correctAt_implies_flip_of_halt M x (hTotal x) hBad⟩

theorem total_exact_diagonal_iff_universal_failure :
    TotalExactDiagonalProducer ↔
      UniversalFailure CanonicalSAT := by
  constructor
  · exact total_exact_diagonal_implies_universal_failure
  · exact universal_failure_implies_total_exact_diagonal

/-- Once the exact producer is genuinely inhabited, all remaining transport to
the repository's internal P != NP endpoint is already closed. -/
theorem total_exact_diagonal_closes_internal_endpoint
    (B : TotalExactDiagonalProducer) :
    PneqNP :=
  remaining_material_gap_implies_p_ne_np
    (total_exact_diagonal_implies_universal_failure B)

#print axioms MCore.Real.P02ExactDiagonalFrontier.flip_implies_not_correctAt
#print axioms MCore.Real.P02ExactDiagonalFrontier.not_correctAt_implies_flip_of_halt
#print axioms MCore.Real.P02ExactDiagonalFrontier.flip_iff_not_correctAt_of_halt
#print axioms MCore.Real.P02ExactDiagonalFrontier.total_exact_diagonal_implies_universal_failure
#print axioms MCore.Real.P02ExactDiagonalFrontier.universal_failure_implies_total_exact_diagonal
#print axioms MCore.Real.P02ExactDiagonalFrontier.total_exact_diagonal_iff_universal_failure
#print axioms MCore.Real.P02ExactDiagonalFrontier.total_exact_diagonal_closes_internal_endpoint

end P02ExactDiagonalFrontier
end Real
end MCore
