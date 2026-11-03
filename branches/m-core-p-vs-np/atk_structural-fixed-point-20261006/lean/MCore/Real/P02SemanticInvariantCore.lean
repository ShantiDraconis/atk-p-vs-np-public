import MCore.Real.P02TotalCandidateFailureMinCut

namespace MCore
namespace Real
namespace P02SemanticInvariantCore

open CanonicalFinalProof
open CanonicalSATBoundary
open CanonicalCircuitBits
open P02TotalCandidateFailureMinCut

abbrev CanonicalSAT : BitLanguage :=
  SATBits circuitBitEncoding

def DeclaredAccepts
    (M : PolyDTMCandidate)
    (x : BitString) : Prop :=
  M.accepting
    (M.machine.run
      (M.timeBound x.length)
      (initialTMConfig M.machine x)).state = true

/-- A semantic complement reduction for one total deterministic candidate. -/
structure ComplementSemanticReduction
    (M : PolyDTMCandidate)
    (hTotal : DeclaredClockTotal M) where
  reduce : BitString → BitString
  correct :
    ∀ x : BitString,
      CanonicalSAT (reduce x) ↔ ¬ DeclaredAccepts M x

/-- One behavioral invariant point for the complement reduction. -/
structure InvariantPoint
    {M : PolyDTMCandidate}
    {hTotal : DeclaredClockTotal M}
    (R : ComplementSemanticReduction M hTotal) where
  source : BitString
  invariant :
    DeclaredAccepts M (R.reduce source) ↔
      DeclaredAccepts M source

theorem invariantPoint_gives_semantic_failure
    {M : PolyDTMCandidate}
    {hTotal : DeclaredClockTotal M}
    (R : ComplementSemanticReduction M hTotal)
    (W : InvariantPoint R) :
    let y := R.reduce W.source
    ¬ (DeclaredAccepts M y ↔ CanonicalSAT y) := by
  dsimp
  have hComp := R.correct W.source
  intro hSem
  by_cases hx : DeclaredAccepts M W.source
  · have hy : DeclaredAccepts M (R.reduce W.source) :=
      W.invariant.mpr hx
    have hSat : CanonicalSAT (R.reduce W.source) :=
      hSem.mp hy
    exact (hComp.mp hSat) hx
  · have hSat : CanonicalSAT (R.reduce W.source) :=
      hComp.mpr hx
    have hy : DeclaredAccepts M (R.reduce W.source) :=
      hSem.mpr hSat
    exact hx (W.invariant.mp hy)

/-- If every total candidate has a complement reduction and one invariant
point, then the exact total semantic-failure producer is inhabited. -/
noncomputable def invariantFamily_to_totalSemanticFailure
    (R :
      ∀ (M : PolyDTMCandidate) (hTotal : DeclaredClockTotal M),
        ComplementSemanticReduction M hTotal)
    (W :
      ∀ (M : PolyDTMCandidate) (hTotal : DeclaredClockTotal M),
        InvariantPoint (R M hTotal)) :
    TotalSemanticFailureProducer := by
  classical
  refine
    { counterexample := fun M hTotal =>
        (R M hTotal).reduce (W M hTotal).source
      disagrees := ?_ }
  intro M hTotal
  exact invariantPoint_gives_semantic_failure
    (R M hTotal) (W M hTotal)

def TOTAL_INVARIANT_POINT_OPEN_MATH : Prop :=
  ∃ R :
      ∀ (M : PolyDTMCandidate) (hTotal : DeclaredClockTotal M),
        ComplementSemanticReduction M hTotal,
    ∀ (M : PolyDTMCandidate) (hTotal : DeclaredClockTotal M),
      Nonempty (InvariantPoint (R M hTotal))

theorem totalInvariantPoint_closes_G2
    (H : TOTAL_INVARIANT_POINT_OPEN_MATH) :
    UniversalFailure CanonicalSAT := by
  rcases H with ⟨R, hW⟩
  classical
  let W :
      ∀ (M : PolyDTMCandidate) (hTotal : DeclaredClockTotal M),
        InvariantPoint (R M hTotal) :=
    fun M hTotal => Classical.choice (hW M hTotal)
  exact totalSemanticFailureProducer_implies_universalFailure
    (invariantFamily_to_totalSemanticFailure R W)

#print axioms MCore.Real.P02SemanticInvariantCore.invariantPoint_gives_semantic_failure
#print axioms MCore.Real.P02SemanticInvariantCore.invariantFamily_to_totalSemanticFailure
#print axioms MCore.Real.P02SemanticInvariantCore.totalInvariantPoint_closes_G2

end P02SemanticInvariantCore
end Real
end MCore
