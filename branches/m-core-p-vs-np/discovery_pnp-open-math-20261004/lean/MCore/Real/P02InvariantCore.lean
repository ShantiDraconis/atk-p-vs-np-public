import MCore.Real.P02BehavioralAlignment

namespace MCore
namespace Real
namespace P02InvariantCore

open CanonicalFinalProof
open P02UniversalFailureMinCut
open P02KleeneUniversalBridge
open P02TotalCandidateKleeneReduction
open P02ComplementRunRealization
open P02ExactDiagonalFrontier
open P02BehavioralAlignment

/-- Semantic failure at one point, separated from the timeout constructor. -/
def SemanticFailureAt
    (M : PolyDTMCandidate)
    (x : BitString) : Prop :=
  ¬ (DeclaredAccepts M x ↔ CanonicalSAT x)

/--
For a total candidate, semantic failure at the complemented Cook--Levin image
is exactly behavioral invariance between the source and its reduced image.

This removes the unnecessarily strong literal requirement reduce x = x.
-/
theorem semanticFailure_reduce_iff_invariant
    (M : PolyDTMCandidate)
    (hTotal : DeclaredClockTotal M)
    (x : BitString) :
    SemanticFailureAt M
        ((complementSemanticReduction M hTotal).reduce x) ↔
      (DeclaredAccepts M
          ((complementSemanticReduction M hTotal).reduce x) ↔
        DeclaredAccepts M x) := by
  classical
  let y : BitString :=
    (complementSemanticReduction M hTotal).reduce x
  have hReduce :
      CanonicalSAT y ↔ ¬ DeclaredAccepts M x := by
    simpa [y] using complement_reduce_correct M hTotal x
  constructor
  · intro hBad
    constructor
    · intro hAy
      by_contra hAx
      have hSat : CanonicalSAT y := hReduce.mpr hAx
      apply hBad
      constructor
      · intro _
        exact hSat
      · intro _
        exact hAy
    · intro hAx
      by_contra hAy
      have hNotSat : ¬ CanonicalSAT y := by
        intro hSat
        exact (hReduce.mp hSat) hAx
      apply hBad
      constructor
      · intro hAy'
        exact False.elim (hAy hAy')
      · intro hSat
        exact False.elim (hNotSat hSat)
  · intro hInv hSem
    by_cases hAx : DeclaredAccepts M x
    · have hAy : DeclaredAccepts M y := hInv.mpr hAx
      have hSat : CanonicalSAT y := hSem.mp hAy
      exact (hReduce.mp hSat) hAx
    · have hSat : CanonicalSAT y := hReduce.mpr hAx
      have hAy : DeclaredAccepts M y := hSem.mpr hSat
      exact hAx (hInv.mp hAy)

/-- Behavioral invariance yields the semantic failure constructor directly. -/
theorem invariant_gives_failureMode
    (M : PolyDTMCandidate)
    (hTotal : DeclaredClockTotal M)
    (x : BitString)
    (hInv :
      DeclaredAccepts M
          ((complementSemanticReduction M hTotal).reduce x) ↔
        DeclaredAccepts M x) :
    CandidateFailureMode M
      ((complementSemanticReduction M hTotal).reduce x) := by
  apply CandidateFailureMode.semantic
  exact (semanticFailure_reduce_iff_invariant M hTotal x).mpr hInv

/--
The exact remaining producer after the automatic timeout branch is removed.
No UniversalFailure, not-InP, separation certificate, or fixed-point object is
stored as a field.
-/
structure TotalCandidateInvariantProducer where
  witness :
    ∀ M : PolyDTMCandidate,
      DeclaredClockTotal M → BitString
  invariant :
    ∀ (M : PolyDTMCandidate)
      (hTotal : DeclaredClockTotal M),
      DeclaredAccepts M
          ((complementSemanticReduction M hTotal).reduce
            (witness M hTotal)) ↔
        DeclaredAccepts M (witness M hTotal)

/--
A total invariant producer gives a concrete failure witness for every
candidate. Non-total candidates fail by timeout; total candidates fail
semantically at the Cook--Levin image of the supplied witness.
-/
theorem candidate_failure_of_invariant
    (P : TotalCandidateInvariantProducer)
    (M : PolyDTMCandidate) :
    ∃ y : BitString, CandidateFailureMode M y := by
  classical
  by_cases hTotal : DeclaredClockTotal M
  · let x : BitString := P.witness M hTotal
    let y : BitString :=
      (complementSemanticReduction M hTotal).reduce x
    refine ⟨y, ?_⟩
    change CandidateFailureMode M
      ((complementSemanticReduction M hTotal).reduce x)
    apply invariant_gives_failureMode M hTotal x
    simpa [x] using P.invariant M hTotal
  · rcases exists_timeout_of_not_total M hTotal with ⟨x, hx⟩
    exact ⟨x, CandidateFailureMode.timeout hx⟩

/-- Mechanical promotion to the repository's canonical universal producer. -/
noncomputable def toUniversalCounterexampleProducer
    (P : TotalCandidateInvariantProducer) :
    UniversalCounterexampleProducer := by
  classical
  let pick : PolyDTMCandidate → BitString :=
    fun M => Classical.choose (candidate_failure_of_invariant P M)
  refine
    { counterexample := pick
      failure := ?_ }
  intro M
  exact Classical.choose_spec (candidate_failure_of_invariant P M)

theorem invariantProducer_implies_universalFailure
    (P : TotalCandidateInvariantProducer) :
    UniversalFailure CanonicalSAT :=
  producer_implies_universal_failure
    (toUniversalCounterexampleProducer P)

theorem invariantProducer_closes_internal_endpoint
    (P : TotalCandidateInvariantProducer) :
    PneqNP :=
  producer_closes_internal_endpoint
    (toUniversalCounterexampleProducer P)

/--
Abstract alternating system: growth plus recoverability of the previous state
does not force an invariant point.  The boolean component flips forever while
the depth strictly increases.
-/
structure FlipState where
  bit : Bool
  depth : Nat
  deriving DecidableEq

def flipStep (s : FlipState) : FlipState :=
  { bit := !s.bit
    depth := s.depth + 1 }

def flipAccept (s : FlipState) : Prop :=
  s.bit = true

def flipDecode (s : FlipState) : FlipState :=
  { bit := !s.bit
    depth := s.depth - 1 }

theorem flipStep_grows
    (s : FlipState) :
    (flipStep s).depth = s.depth + 1 := by
  rfl

theorem flipDecode_step
    (s : FlipState) :
    flipDecode (flipStep s) = s := by
  cases s with
  | mk bit depth =>
      cases bit <;> simp [flipDecode, flipStep]

theorem flipStep_injective :
    Function.Injective flipStep := by
  intro a b h
  have := congrArg flipDecode h
  simpa [flipDecode_step] using this

theorem flipStep_negates_accept
    (s : FlipState) :
    flipAccept (flipStep s) ↔ ¬ flipAccept s := by
  cases s with
  | mk bit depth =>
      cases bit <;> simp [flipAccept, flipStep]

theorem no_flip_invariant
    (s : FlipState) :
    ¬ (flipAccept (flipStep s) ↔ flipAccept s) := by
  cases s with
  | mk bit depth =>
      cases bit <;> simp [flipAccept, flipStep]

#print axioms MCore.Real.P02InvariantCore.semanticFailure_reduce_iff_invariant
#print axioms MCore.Real.P02InvariantCore.invariant_gives_failureMode
#print axioms MCore.Real.P02InvariantCore.candidate_failure_of_invariant
#print axioms MCore.Real.P02InvariantCore.toUniversalCounterexampleProducer
#print axioms MCore.Real.P02InvariantCore.invariantProducer_implies_universalFailure
#print axioms MCore.Real.P02InvariantCore.invariantProducer_closes_internal_endpoint
#print axioms MCore.Real.P02InvariantCore.flipDecode_step
#print axioms MCore.Real.P02InvariantCore.flipStep_injective
#print axioms MCore.Real.P02InvariantCore.flipStep_negates_accept
#print axioms MCore.Real.P02InvariantCore.no_flip_invariant

end P02InvariantCore
end Real
end MCore
