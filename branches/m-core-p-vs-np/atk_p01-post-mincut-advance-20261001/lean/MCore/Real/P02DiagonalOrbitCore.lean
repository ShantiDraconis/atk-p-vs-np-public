import MCore.Real.P02ComplementTableauDiagonal
import MCore.Real.P02SemanticTransformerDichotomy

namespace MCore
namespace Real
namespace P02DiagonalOrbitCore

open CanonicalFinalProof
open P02UniversalFailureMinCut
open P02FailureNormalForms
open P02TotalCandidateSemanticCore
open P02SemanticFlipCore
open P02ComplementTableauDiagonal
open P02SemanticTransformerDichotomy

abbrev SATTarget : BitLanguage :=
  P02UniversalFailureMinCut.CanonicalSAT

def orbit
    (M : PolyDTMCandidate)
    (seed : BitString) : Nat → BitString
  | 0 => seed
  | n + 1 => diagonalBits M (orbit M seed n)

@[simp] theorem orbit_zero
    (M : PolyDTMCandidate)
    (seed : BitString) :
    orbit M seed 0 = seed := rfl

@[simp] theorem orbit_succ
    (M : PolyDTMCandidate)
    (seed : BitString)
    (n : Nat) :
    orbit M seed (n + 1) =
      diagonalBits M (orbit M seed n) := rfl

/-- If the acceptance bit is not preserved by one diagonal step, Boolean
bivalence forces the candidate's answer at the transformed input to agree with
the SAT truth of that transformed input. -/
theorem not_alignment_implies_semantic_correct_next
    (M : PolyDTMCandidate)
    (x : BitString)
    (hNot : ¬ AcceptanceAligned M x) :
    DeclaredAccepts M (diagonalBits M x) ↔
      SATTarget (diagonalBits M x) := by
  have hSAT :=
    diagonalBits_sat_iff_not_declaredAccepts M x
  classical
  by_cases hNext : DeclaredAccepts M (diagonalBits M x)
  · have hNotX : ¬ DeclaredAccepts M x := by
      intro hX
      apply hNot
      constructor
      · intro _
        exact hX
      · intro _
        exact hNext
    constructor
    · intro _
      exact hSAT.mpr hNotX
    · intro _
      exact hNext
  · have hX : DeclaredAccepts M x := by
      apply Classical.byContradiction
      intro hNotX
      apply hNot
      constructor
      · intro h
        exact False.elim (hNext h)
      · intro h
        exact False.elim (hNotX h)
    constructor
    · intro h
      exact False.elim (hNext h)
    · intro hSat
      have hNotX := hSAT.mp hSat
      exact False.elim (hNotX hX)

/-- For a candidate total at its declared clock, every diagonal step gives an
exact dichotomy: alignment already yields the semantic-failure route, while
non-alignment means the candidate is CorrectAt on the transformed input. -/
theorem alignment_or_correctAt_next
    (M : PolyDTMCandidate)
    (hTotal : DeclaredClockTotal M)
    (x : BitString) :
    AcceptanceAligned M x ∨
      M.CorrectAt SATTarget (diagonalBits M x) := by
  classical
  by_cases hAlign : AcceptanceAligned M x
  · exact Or.inl hAlign
  · right
    constructor
    · exact hTotal (diagonalBits M x)
    · exact not_alignment_implies_semantic_correct_next M x hAlign

def OrbitCorrect
    (M : PolyDTMCandidate)
    (seed : BitString) : Prop :=
  ∀ n : Nat,
    M.CorrectAt SATTarget (orbit M seed n)

def OrbitHasAlignment
    (M : PolyDTMCandidate)
    (seed : BitString) : Prop :=
  ∃ n : Nat, AcceptanceAligned M (orbit M seed n)

theorem orbit_alignment_gives_semantic_disagreement
    (M : PolyDTMCandidate)
    (seed : BitString)
    (h : OrbitHasAlignment M seed) :
    ∃ y : BitString, SemanticDisagreement M y := by
  rcases h with ⟨n, hAlign⟩
  let x := orbit M seed n
  let y := diagonalBits M x
  refine ⟨y, ?_⟩
  have hFlip :
      SemanticFlip M y :=
    semanticFlip_diagonalBits_of_alignment M x hAlign
  exact (semanticFlip_iff_semanticDisagreement M y).mp hFlip

theorem orbit_correct_of_no_alignment
    (M : PolyDTMCandidate)
    (hTotal : DeclaredClockTotal M)
    (seed : BitString)
    (hSeed : M.CorrectAt SATTarget seed)
    (hNo : ¬ OrbitHasAlignment M seed) :
    OrbitCorrect M seed := by
  intro n
  induction n with
  | zero =>
      simpa [orbit] using hSeed
  | succ n ih =>
      have hNot :
          ¬ AcceptanceAligned M (orbit M seed n) := by
        intro hAlign
        exact hNo ⟨n, hAlign⟩
      have hStep :=
        alignment_or_correctAt_next
          M hTotal (orbit M seed n)
      rcases hStep with hAlign | hCorrect
      · exact False.elim (hNot hAlign)
      · simpa [orbit] using hCorrect

def ConstantOrbitCorrectPattern
    (M : PolyDTMCandidate) : Prop :=
  OrbitCorrect M falseBits ∧
  OrbitCorrect M trueBits

theorem constant_pattern_seed_correct
    (M : PolyDTMCandidate)
    (hTotal : DeclaredClockTotal M)
    (hPattern : ConstantCorrectPattern M) :
    M.CorrectAt SATTarget falseBits ∧
      M.CorrectAt SATTarget trueBits := by
  rcases hPattern with ⟨hFalse, hTrue⟩
  constructor
  · constructor
    · exact hTotal falseBits
    · constructor
      · intro hAcc
        exact False.elim (hFalse hAcc)
      · intro hSat
        exact False.elim (falseBits_not_sat hSat)
  · constructor
    · exact hTotal trueBits
    · constructor
      · intro _
        exact trueBits_sat
      · intro _
        exact hTrue

theorem orbit_alignment_or_constant_orbit_correct
    (M : PolyDTMCandidate)
    (hTotal : DeclaredClockTotal M)
    (hPattern : ConstantCorrectPattern M) :
    OrbitHasAlignment M falseBits ∨
    OrbitHasAlignment M trueBits ∨
    ConstantOrbitCorrectPattern M := by
  classical
  by_cases hf : OrbitHasAlignment M falseBits
  · exact Or.inl hf
  · by_cases ht : OrbitHasAlignment M trueBits
    · exact Or.inr (Or.inl ht)
    · right
      right
      have hSeed :=
        constant_pattern_seed_correct M hTotal hPattern
      exact
        ⟨orbit_correct_of_no_alignment M hTotal falseBits hSeed.1 hf,
         orbit_correct_of_no_alignment M hTotal trueBits hSeed.2 ht⟩

/-- After constants and all diagonal-orbit points are discharged, only this
residual semantic class remains. -/
def OrbitResidualCore : Prop :=
  ∀ M : PolyDTMCandidate,
    DeclaredClockTotal M →
    ConstantCorrectPattern M →
    ConstantOrbitCorrectPattern M →
      ∃ x : BitString, SemanticDisagreement M x

theorem orbit_residual_core_implies_constant_pattern_core
    (H : OrbitResidualCore) :
    ConstantPatternSemanticCore := by
  intro M hTotal hPattern
  rcases orbit_alignment_or_constant_orbit_correct M hTotal hPattern with
      hFalse | hRest
  · exact orbit_alignment_gives_semantic_disagreement M falseBits hFalse
  · rcases hRest with hTrue | hOrbit
    · exact orbit_alignment_gives_semantic_disagreement M trueBits hTrue
    · exact H M hTotal hPattern hOrbit

theorem constant_pattern_core_implies_orbit_residual_core
    (H : ConstantPatternSemanticCore) :
    OrbitResidualCore := by
  intro M hTotal hPattern _
  exact H M hTotal hPattern

theorem orbit_residual_core_iff_universal_failure :
    OrbitResidualCore ↔ UniversalFailure SATTarget := by
  constructor
  · intro H
    exact (constant_pattern_core_iff_universal_failure).mp
      (orbit_residual_core_implies_constant_pattern_core H)
  · intro h
    have hConst :
        ConstantPatternSemanticCore :=
      (constant_pattern_core_iff_universal_failure).mpr h
    exact constant_pattern_core_implies_orbit_residual_core hConst

theorem orbit_residual_core_closes_internal_endpoint
    (H : OrbitResidualCore) :
    PneqNP :=
  P02TotalCandidateSemanticCore.total_semantic_core_closes_internal_endpoint
    (constant_pattern_core_implies_total_semantic_core
      (orbit_residual_core_implies_constant_pattern_core H))

#print axioms MCore.Real.P02DiagonalOrbitCore.not_alignment_implies_semantic_correct_next
#print axioms MCore.Real.P02DiagonalOrbitCore.alignment_or_correctAt_next
#print axioms MCore.Real.P02DiagonalOrbitCore.orbit_correct_of_no_alignment
#print axioms MCore.Real.P02DiagonalOrbitCore.orbit_alignment_or_constant_orbit_correct
#print axioms MCore.Real.P02DiagonalOrbitCore.orbit_residual_core_iff_universal_failure

end P02DiagonalOrbitCore
end Real
end MCore
