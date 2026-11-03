import MCore.Real.P02AntiModels
import MCore.Real.P03TransitionSignature

namespace MCore
namespace Real
namespace P03CounterexampleLaws

open CanonicalFinalProof
open P02ComplementRunRealization
open P02OddSemanticRecurrence
open P02AntiModels
open P03TransitionSignature

/--
False finite-revisit principle: any three strictly ordered indices contain an
odd-separated pair.
-/
def ThreeRevisitsForceOdd : Prop :=
  ∀ i₁ i₂ i₃ : Nat,
    i₁ < i₂ →
    i₂ < i₃ →
    OddGap i₁ i₂ ∨ OddGap i₂ i₃ ∨ OddGap i₁ i₃

theorem three_revisits_force_odd_falsified :
    ¬ ThreeRevisitsForceOdd := by
  intro H
  have h := H 0 2 4 (by omega) (by omega)
  rcases h with h02 | h24 | h04
  · exact (three_revisits_can_all_have_even_gaps.2.2.1) h02
  · exact (three_revisits_can_all_have_even_gaps.2.2.2.1) h24
  · exact (three_revisits_can_all_have_even_gaps.2.2.2.2) h04

/-- False source-recovery principle using only the finite control state at the
initial configuration. -/
def InitialStateInjectsSource (candidate : PolyDTMCandidate) : Prop :=
  ∀ x y : BitString,
    (initialTMConfig candidate.machine x).state =
      (initialTMConfig candidate.machine y).state →
    x = y

theorem initial_state_injects_source_falsified
    (candidate : PolyDTMCandidate) :
    ¬ InitialStateInjectsSource candidate := by
  intro H
  have hEq :=
    H ([] : BitString) [false]
      (initial_state_same_for_all_inputs candidate [] [false])
  exact (equal_initial_state_does_not_determine_source candidate).2 hEq

/-- No complemented deterministic transition table admits two different
indexed entries at one fixed state/head-symbol pair. -/
theorem no_two_distinct_complement_entries
    (candidate : PolyDTMCandidate)
    (q : Fin (candidate.stateCount + 1))
    (a : Option Bool) :
    ¬ ∃ p1 p2 :
        Nat × (Fin (candidate.stateCount + 1) × Option Bool × Direction),
      p1 ∈ ntmIndexedTransitions
        ((complementToNTMCandidate candidate).machine.transition q a) ∧
      p2 ∈ ntmIndexedTransitions
        ((complementToNTMCandidate candidate).machine.transition q a) ∧
      p1 ≠ p2 := by
  rintro ⟨p1, p2, h1, h2, hne⟩
  exact hne
    (complement_indexed_entry_unique candidate q a h1 h2)

/-- The corresponding distinct-index formulation is impossible as well. -/
theorem no_two_distinct_complement_choice_indices
    (candidate : PolyDTMCandidate)
    (q : Fin (candidate.stateCount + 1))
    (a : Option Bool) :
    ¬ ∃ j1 j2 tr1 tr2,
      (j1, tr1) ∈ ntmIndexedTransitions
        ((complementToNTMCandidate candidate).machine.transition q a) ∧
      (j2, tr2) ∈ ntmIndexedTransitions
        ((complementToNTMCandidate candidate).machine.transition q a) ∧
      j1 ≠ j2 := by
  rintro ⟨j1, j2, tr1, tr2, h1, h2, hne⟩
  exact hne
    (complement_no_distinct_choice_indices
      candidate q a h1 h2)

#print axioms MCore.Real.P03CounterexampleLaws.three_revisits_force_odd_falsified
#print axioms MCore.Real.P03CounterexampleLaws.initial_state_injects_source_falsified
#print axioms MCore.Real.P03CounterexampleLaws.no_two_distinct_complement_entries
#print axioms MCore.Real.P03CounterexampleLaws.no_two_distinct_complement_choice_indices

end P03CounterexampleLaws
end Real
end MCore
