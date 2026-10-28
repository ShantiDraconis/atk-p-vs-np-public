import MCore.Real.P02BoundedComputationLogic
import MCore.Real.P02BoundedComputationTape

namespace MCore
namespace Real
namespace P02BoundedComputationSoundness

open CircuitK1
open CanonicalFinalProof
open P02BoundedComputationEncoding
open P02BoundedComputationLogic

def SnapshotMatches
    (sigma : Assignment)
    (M : PolyDTMCandidate)
    (x : BitString)
    (t s : Nat)
    (config : Configuration (Fin (M.stateCount + 1)) (Option Bool)) : Prop :=
  (∀ q : Fin (M.stateCount + 1),
      sigma (stateVar M t s q) = decide (q = config.state)) ∧
  (∀ a : Option Bool,
      sigma (headVar M t s a) = decide (a = config.tape.head)) ∧
  (∀ i : Nat, i < radius x t →
      ∀ a : Option Bool,
        sigma (leftVar M x t s i a) =
          decide (a = config.tape.left.getD i M.machine.blank)) ∧
  (∀ i : Nat, i < radius x t →
      ∀ a : Option Bool,
        sigma (rightVar M x t s i a) =
          decide (a = config.tape.right.getD i M.machine.blank))

theorem initialCNF_sound
    (sigma : Assignment)
    (M : PolyDTMCandidate)
    (x : BitString)
    (t : Nat)
    (hinit : evalCNF sigma (initialCNF M x t) = true) :
    SnapshotMatches sigma M x t 0 (initialTMConfig M.machine x) := by
  have hstate :
      evalCNF sigma
        (setStateClauses [] M t 0 M.machine.initial) = true := by
    apply evalCNF_subset_true sigma _ (initialCNF M x t) hinit
    intro c hc
    simp [initialCNF, hc]
  have hhead :
      evalCNF sigma
        (setSymbolClauses [] (headVar M t 0) (inputTape x).head) = true := by
    apply evalCNF_subset_true sigma _ (initialCNF M x t) hinit
    intro c hc
    simp [initialCNF, hc]
  unfold SnapshotMatches
  dsimp [initialTMConfig]
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro q
    exact setStateClauses_forces
      sigma [] M t 0 M.machine.initial q rfl hstate
  · intro a
    exact setSymbolClauses_forces
      sigma [] (headVar M t 0) (inputTape x).head a rfl hhead
  · intro i hi a
    let target := (inputTape x).left.getD i M.machine.blank
    have hcell :
        evalCNF sigma
          (setLeftCell [] M x t 0 i target) = true := by
      apply evalCNF_subset_true sigma _ (initialCNF M x t) hinit
      intro c hc
      simp only [initialCNF, List.mem_append, List.mem_flatMap,
        List.mem_range]
      exact Or.inl (Or.inr
        ⟨i, hi, by simpa [target] using hc⟩)
    exact setSymbolClauses_forces
      sigma [] (leftVar M x t 0 i) target a rfl hcell
  · intro i hi a
    let target := (inputTape x).right.getD i M.machine.blank
    have hcell :
        evalCNF sigma
          (setRightCell [] M x t 0 i target) = true := by
      apply evalCNF_subset_true sigma _ (initialCNF M x t) hinit
      intro c hc
      simp only [initialCNF, List.mem_append, List.mem_flatMap,
        List.mem_range]
      exact Or.inr
        ⟨i, hi, by simpa [target] using hc⟩
    exact setSymbolClauses_forces
      sigma [] (rightVar M x t 0 i) target a rfl hcell

theorem snapshot_transition_guard_false
    (sigma : Assignment)
    (M : PolyDTMCandidate)
    (x : BitString)
    (t s : Nat)
    (config : Configuration (Fin (M.stateCount + 1)) (Option Bool))
    (hmatch : SnapshotMatches sigma M x t s config) :
    evalClause sigma
      [neg (stateVar M t s config.state),
       neg (headVar M t s config.tape.head)] = false := by
  rcases hmatch with ⟨hstate, hhead, _, _⟩
  have hs :
      sigma (stateVar M t s config.state) = true := by
    simpa using hstate config.state
  have hh :
      sigma (headVar M t s config.tape.head) = true := by
    simpa using hhead config.tape.head
  simp [evalClause, evalLiteral, neg, hs, hh]


theorem boundedExecTableau_initial_sound
    (sigma : Assignment)
    (M : PolyDTMCandidate)
    (x : BitString)
    (t : Nat)
    (h : evalCNF sigma (boundedExecTableauCNF M x t) = true) :
    SnapshotMatches sigma M x t 0 (initialTMConfig M.machine x) := by
  apply initialCNF_sound
  apply evalCNF_subset_true sigma _ (boundedExecTableauCNF M x t) h
  intro c hc
  simp [boundedExecTableauCNF, hc]


theorem snapshot_state_true
    (sigma : Assignment)
    (M : PolyDTMCandidate)
    (x : BitString)
    (t s : Nat)
    (config : Configuration (Fin (M.stateCount + 1)) (Option Bool))
    (hmatch : SnapshotMatches sigma M x t s config) :
    sigma (stateVar M t s config.state) = true := by
  simpa using hmatch.1 config.state

theorem snapshot_head_true
    (sigma : Assignment)
    (M : PolyDTMCandidate)
    (x : BitString)
    (t s : Nat)
    (config : Configuration (Fin (M.stateCount + 1)) (Option Bool))
    (hmatch : SnapshotMatches sigma M x t s config) :
    sigma (headVar M t s config.tape.head) = true := by
  simpa using hmatch.2.1 config.tape.head


theorem acceptingStateList_false_of_nonaccepting_snapshot
    (sigma : Assignment)
    (M : PolyDTMCandidate)
    (t : Nat)
    (config : Configuration (Fin (M.stateCount + 1)) (Option Bool))
    (hstate :
      ∀ q : Fin (M.stateCount + 1),
        sigma (stateVar M t t q) = decide (q = config.state))
    (haccFalse : M.accepting config.state = false) :
    ∀ qs : List (Fin (M.stateCount + 1)),
      evalClause sigma
        (qs.filterMap fun q =>
          if M.accepting q = true then
            some (pos (stateVar M t t q))
          else none) = false := by
  intro qs
  induction qs with
  | nil =>
      rfl
  | cons q qs ih =>
      by_cases hq : M.accepting q = true
      · have hneq : q ≠ config.state := by
          intro heq
          subst q
          simp [haccFalse] at hq
        have hsigma : sigma (stateVar M t t q) = false := by
          rw [hstate q]
          simp [hneq]
        simp [hq, evalClause, evalLiteral, pos, hsigma]
        exact ih
      · simpa [hq] using ih

theorem acceptingStateLits_false_of_nonaccepting_snapshot
    (sigma : Assignment)
    (M : PolyDTMCandidate)
    (t : Nat)
    (config : Configuration (Fin (M.stateCount + 1)) (Option Bool))
    (hstate :
      ∀ q : Fin (M.stateCount + 1),
        sigma (stateVar M t t q) = decide (q = config.state))
    (haccFalse : M.accepting config.state = false) :
    evalClause sigma (acceptingStateLits M t) = false := by
  unfold acceptingStateLits
  exact acceptingStateList_false_of_nonaccepting_snapshot
    sigma M t config hstate haccFalse
    (List.ofFn fun q : Fin (M.stateCount + 1) => q)


theorem finalAcceptanceCNF_sound_of_snapshot
    (sigma : Assignment)
    (M : PolyDTMCandidate)
    (x : BitString)
    (t : Nat)
    (config : Configuration (Fin (M.stateCount + 1)) (Option Bool))
    (hmatch : SnapshotMatches sigma M x t t config)
    (hfinal : evalCNF sigma (finalAcceptanceCNF M t) = true) :
    M.accepting config.state = true := by
  have hclause :
      evalClause sigma (acceptingStateLits M t) = true := by
    simpa [finalAcceptanceCNF, evalCNF] using hfinal
  by_cases hacc : M.accepting config.state = true
  · exact hacc
  · have haccFalse : M.accepting config.state = false := by
      cases h : M.accepting config.state <;> simp_all
    have hallFalse :=
      acceptingStateLits_false_of_nonaccepting_snapshot
        sigma M t config hmatch.1 haccFalse
    rw [hallFalse] at hclause
    contradiction


theorem boundedExecTableau_final_acceptance_sound
    (sigma : Assignment)
    (M : PolyDTMCandidate)
    (x : BitString)
    (t : Nat)
    (config : Configuration (Fin (M.stateCount + 1)) (Option Bool))
    (hmatch : SnapshotMatches sigma M x t t config)
    (htableau : evalCNF sigma (boundedExecTableauCNF M x t) = true) :
    M.accepting config.state = true := by
  apply finalAcceptanceCNF_sound_of_snapshot sigma M x t config hmatch
  apply evalCNF_subset_true sigma _ (boundedExecTableauCNF M x t) htableau
  intro c hc
  simp [boundedExecTableauCNF, finalAcceptanceCNF] at hc ⊢
  exact Or.inr (Or.inr hc)


#print axioms MCore.Real.P02BoundedComputationSoundness.snapshot_transition_guard_false
#print axioms MCore.Real.P02BoundedComputationSoundness.acceptingStateList_false_of_nonaccepting_snapshot
#print axioms MCore.Real.P02BoundedComputationSoundness.acceptingStateLits_false_of_nonaccepting_snapshot
#print axioms MCore.Real.P02BoundedComputationSoundness.finalAcceptanceCNF_sound_of_snapshot
#print axioms MCore.Real.P02BoundedComputationSoundness.boundedExecTableau_final_acceptance_sound
#print axioms MCore.Real.P02BoundedComputationSoundness.snapshot_state_true
#print axioms MCore.Real.P02BoundedComputationSoundness.snapshot_head_true
#print axioms MCore.Real.P02BoundedComputationSoundness.boundedExecTableau_initial_sound


#print axioms MCore.Real.P02BoundedComputationSoundness.initialCNF_sound

end P02BoundedComputationSoundness
end Real
end MCore
