import MCore.Real.P02G21G22Attack
import MCore.Real.P02SemanticSelfEmbedding

namespace MCore
namespace Real
namespace P02UniversalFailureAlgebra

open CanonicalFinalProof
open CanonicalCircuitBits
open CanonicalSATBoundary
open P02DiagonalFrontier
open P02G21G22Attack
open P02SemanticSelfEmbedding

def DeclaredHalts
    (M : PolyDTMCandidate) (x : BitString) : Prop :=
  M.machine.HaltsWithin
    (M.timeBound x.length)
    (initialTMConfig M.machine x)

def DeclaredSATMatch
    (M : PolyDTMCandidate) (x : BitString) : Prop :=
  AcceptsAtDeclaredBound M x ↔ SATBits circuitBitEncoding x

def SemanticMismatch
    (M : PolyDTMCandidate) (x : BitString) : Prop :=
  (AcceptsAtDeclaredBound M x ∧ ¬ SATBits circuitBitEncoding x) ∨
  (¬ AcceptsAtDeclaredBound M x ∧ SATBits circuitBitEncoding x)

def DeclaredClockTotal (M : PolyDTMCandidate) : Prop :=
  ∀ x : BitString, DeclaredHalts M x

def DeclaredSATCorrect (M : PolyDTMCandidate) : Prop :=
  ∀ x : BitString, DeclaredSATMatch M x

theorem correctAt_iff_declared_halts_and_match
    (M : PolyDTMCandidate) (x : BitString) :
    M.CorrectAt (SATBits circuitBitEncoding) x ↔
      DeclaredHalts M x ∧ DeclaredSATMatch M x := by
  rfl

theorem not_correctAt_iff_clock_or_match_failure
    (M : PolyDTMCandidate) (x : BitString) :
    ¬ M.CorrectAt (SATBits circuitBitEncoding) x ↔
      ¬ DeclaredHalts M x ∨ ¬ DeclaredSATMatch M x := by
  constructor
  · intro h
    by_cases hH : DeclaredHalts M x
    · right
      intro hM
      exact h ((correctAt_iff_declared_halts_and_match M x).mpr ⟨hH, hM⟩)
    · exact Or.inl hH
  · intro h hC
    have hc :=
      (correctAt_iff_declared_halts_and_match M x).mp hC
    rcases h with hH | hM
    · exact hH hc.1
    · exact hM hc.2

theorem not_declaredSATMatch_iff_semanticMismatch
    (M : PolyDTMCandidate) (x : BitString) :
    ¬ DeclaredSATMatch M x ↔ SemanticMismatch M x := by
  unfold DeclaredSATMatch SemanticMismatch
  constructor
  · intro h
    by_cases hA : AcceptsAtDeclaredBound M x
    · left
      refine ⟨hA, ?_⟩
      intro hS
      apply h
      constructor
      · intro _
        exact hS
      · intro _
        exact hA
    · by_cases hS : SATBits circuitBitEncoding x
      · exact Or.inr ⟨hA, hS⟩
      · exfalso
        apply h
        constructor
        · intro hAx
          exact False.elim (hA hAx)
        · intro hSx
          exact False.elim (hS hSx)
  · intro h hEq
    rcases h with ⟨hA, hNS⟩ | ⟨hNA, hS⟩
    · exact hNS (hEq.mp hA)
    · exact hNA (hEq.mpr hS)

theorem not_correctAt_iff_clock_or_semantic_mismatch
    (M : PolyDTMCandidate) (x : BitString) :
    ¬ M.CorrectAt (SATBits circuitBitEncoding) x ↔
      ¬ DeclaredHalts M x ∨ SemanticMismatch M x := by
  rw [not_correctAt_iff_clock_or_match_failure,
      not_declaredSATMatch_iff_semanticMismatch]

def ClockOrSemanticFailure : Prop :=
  ∀ M : PolyDTMCandidate,
    ∃ x : BitString,
      ¬ DeclaredHalts M x ∨ SemanticMismatch M x

theorem g21_iff_clock_or_semantic_failure :
    G21Pointwise ↔ ClockOrSemanticFailure := by
  constructor
  · intro h M
    rcases h M with ⟨x, hx⟩
    exact ⟨x, (not_correctAt_iff_clock_or_semantic_mismatch M x).mp hx⟩
  · intro h M
    rcases h M with ⟨x, hx⟩
    exact ⟨x, (not_correctAt_iff_clock_or_semantic_mismatch M x).mpr hx⟩

theorem not_declaredClockTotal_iff_exists_clock_failure
    (M : PolyDTMCandidate) :
    ¬ DeclaredClockTotal M ↔
      ∃ x : BitString, ¬ DeclaredHalts M x := by
  constructor
  · intro hNotTotal
    apply Classical.byContradiction
    intro hNoWitness
    apply hNotTotal
    intro x
    apply Classical.byContradiction
    intro hx
    exact hNoWitness ⟨x, hx⟩
  · rintro ⟨x, hx⟩ hTotal
    exact hx (hTotal x)

theorem total_candidate_failure_iff_exists_semanticMismatch
    (M : PolyDTMCandidate)
    (hTotal : DeclaredClockTotal M) :
    (∃ x : BitString,
      ¬ M.CorrectAt (SATBits circuitBitEncoding) x) ↔
    (∃ x : BitString, SemanticMismatch M x) := by
  constructor
  · rintro ⟨x, hx⟩
    have hsplit :=
      (not_correctAt_iff_clock_or_semantic_mismatch M x).mp hx
    rcases hsplit with hclock | hmismatch
    · exact False.elim (hclock (hTotal x))
    · exact ⟨x, hmismatch⟩
  · rintro ⟨x, hmismatch⟩
    exact ⟨x,
      (not_correctAt_iff_clock_or_semantic_mismatch M x).mpr
        (Or.inr hmismatch)⟩

def TotalityOrSemanticCounterexample : Prop :=
  ∀ M : PolyDTMCandidate,
    ¬ DeclaredClockTotal M ∨
      ∃ x : BitString, SemanticMismatch M x

theorem clock_or_semantic_failure_iff_totality_or_semantic :
    ClockOrSemanticFailure ↔ TotalityOrSemanticCounterexample := by
  constructor
  · intro h M
    by_cases hTotal : DeclaredClockTotal M
    · right
      rcases h M with ⟨x, hx⟩
      rcases hx with hclock | hmismatch
      · exact False.elim (hclock (hTotal x))
      · exact ⟨x, hmismatch⟩
    · exact Or.inl hTotal
  · intro h M
    rcases h M with hNotTotal | hMismatch
    · rcases (not_declaredClockTotal_iff_exists_clock_failure M).mp hNotTotal with
        ⟨x, hx⟩
      exact ⟨x, Or.inl hx⟩
    · rcases hMismatch with ⟨x, hx⟩
      exact ⟨x, Or.inr hx⟩

theorem g21_iff_totality_or_semantic_counterexample :
    G21Pointwise ↔ TotalityOrSemanticCounterexample := by
  exact g21_iff_clock_or_semantic_failure.trans
    clock_or_semantic_failure_iff_totality_or_semantic

theorem self_embed_witness_gives_semanticMismatch
    (M : PolyDTMCandidate)
    (x : BitString)
    (hflip :
      SATBits circuitBitEncoding x ↔
        ¬ AcceptsAtDeclaredBound M x) :
    SemanticMismatch M x := by
  unfold SemanticMismatch
  by_cases hacc : AcceptsAtDeclaredBound M x
  · left
    refine ⟨hacc, ?_⟩
    intro hsat
    exact (hflip.mp hsat) hacc
  · right
    exact ⟨hacc, hflip.mpr hacc⟩

theorem pointwise_self_embedding_implies_normalized_failure
    (h : PointwiseSemanticSelfEmbedding) :
    TotalityOrSemanticCounterexample := by
  intro M
  right
  rcases h M with ⟨x, _, hflip⟩
  exact ⟨x, self_embed_witness_gives_semanticMismatch M x hflip⟩

theorem totality_or_semantic_closes_p02
    (h : TotalityOrSemanticCounterexample) :
    P02TerminalFrontier.P02Target := by
  apply g21_pointwise_iff_p02_target.mp
  exact g21_iff_totality_or_semantic_counterexample.mpr h

#print axioms MCore.Real.P02UniversalFailureAlgebra.not_correctAt_iff_clock_or_semantic_mismatch
#print axioms MCore.Real.P02UniversalFailureAlgebra.g21_iff_totality_or_semantic_counterexample
#print axioms MCore.Real.P02UniversalFailureAlgebra.self_embed_witness_gives_semanticMismatch
#print axioms MCore.Real.P02UniversalFailureAlgebra.totality_or_semantic_closes_p02

end P02UniversalFailureAlgebra
end Real
end MCore
