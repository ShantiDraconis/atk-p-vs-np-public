import MCore.Real.CanonicalFinalProof

namespace MCore
namespace Real
namespace CanonicalPSubsetNP

open CanonicalFinalProof

def toNTM
    (candidate : PolyDTMCandidate) :
    NTM (Fin (candidate.stateCount + 1)) (Option Bool) :=
  { initial := candidate.machine.initial
    blank := candidate.machine.blank
    transition := fun q symbol => [candidate.machine.transition q symbol]
    accepting := fun q =>
      Bool.and (candidate.machine.halting q) (candidate.accepting q)
    rejecting := fun q =>
      Bool.and (candidate.machine.halting q) (!(candidate.accepting q)) }

theorem accept_or_reject_eq_halting
    (candidate : PolyDTMCandidate)
    (q : Fin (candidate.stateCount + 1)) :
    ((toNTM candidate).accepting q || (toNTM candidate).rejecting q) =
      candidate.machine.halting q := by
  cases h : candidate.machine.halting q <;>
    cases a : candidate.accepting q <;>
    simp [toNTM, h, a]

theorem successors_toNTM
    (candidate : PolyDTMCandidate)
    (config :
      Configuration
        (Fin (candidate.stateCount + 1))
        (Option Bool)) :
    (toNTM candidate).successors config =
      [candidate.machine.step config] := by
  rfl

theorem tm_run_of_halted
    (candidate : PolyDTMCandidate)
    (config :
      Configuration
        (Fin (candidate.stateCount + 1))
        (Option Bool))
    (h : candidate.machine.halting config.state = true) :
    ∀ fuel : Nat, candidate.machine.run fuel config = config := by
  intro fuel
  cases fuel with
  | zero => rfl
  | succ n =>
      simp [TM.run, h]

theorem runBranches_to_tm_run
    (candidate : PolyDTMCandidate)
    (fuel : Nat)
    (config :
      Configuration
        (Fin (candidate.stateCount + 1))
        (Option Bool)) :
    (toNTM candidate).runBranches fuel [config] =
      [candidate.machine.run fuel config] := by
  induction fuel generalizing config with
  | zero =>
      rfl
  | succ n ih =>
      by_cases h : candidate.machine.halting config.state = true
      · have hstop :
          ((toNTM candidate).accepting config.state ||
            (toNTM candidate).rejecting config.state) = true := by
          rw [accept_or_reject_eq_halting]
          exact h
        have hHalted :
            [config].filter (fun c =>
              (toNTM candidate).accepting c.state ||
                (toNTM candidate).rejecting c.state) = [config] := by
          simp [hstop]
        have hActivePoint :
            Bool.not
              ((toNTM candidate).accepting config.state ||
                (toNTM candidate).rejecting config.state) = false := by
          rw [hstop]
          rfl
        have hActive :
            [config].filter (fun c =>
              !((toNTM candidate).accepting c.state ||
                (toNTM candidate).rejecting c.state)) = [] := by
          simp only [List.filter_cons, List.filter_nil]
          rw [hActivePoint]
          rfl
        calc
          (toNTM candidate).runBranches (n + 1) [config]
              = (toNTM candidate).runBranches n [config] := by
                  rw [NTM.runBranches]
                  rw [hActive, hHalted]
                  rfl
          _ = [candidate.machine.run n config] := ih config
          _ = [config] := by
                rw [tm_run_of_halted candidate config h n]
          _ = [candidate.machine.run (n + 1) config] := by
                simp [TM.run, h]
      · have hFalse : candidate.machine.halting config.state = false := by
          cases hval : candidate.machine.halting config.state <;> simp_all
        have hstop :
          ((toNTM candidate).accepting config.state ||
            (toNTM candidate).rejecting config.state) = false := by
          rw [accept_or_reject_eq_halting]
          exact hFalse
        have hHalted :
            [config].filter (fun c =>
              (toNTM candidate).accepting c.state ||
                (toNTM candidate).rejecting c.state) = [] := by
          simp [hstop]
        have hActivePoint :
            Bool.not
              ((toNTM candidate).accepting config.state ||
                (toNTM candidate).rejecting config.state) = true := by
          rw [hstop]
          rfl
        have hActive :
            [config].filter (fun c =>
              !((toNTM candidate).accepting c.state ||
                (toNTM candidate).rejecting c.state)) = [config] := by
          simp only [List.filter_cons, List.filter_nil]
          rw [hActivePoint]
          rfl
        calc
          (toNTM candidate).runBranches (n + 1) [config]
              = (toNTM candidate).runBranches n
                  ((toNTM candidate).successors config) := by
                  rw [NTM.runBranches]
                  rw [hActive, hHalted]
                  rfl
          _ = (toNTM candidate).runBranches n
                  [candidate.machine.step config] := by
                rw [successors_toNTM]
          _ = [candidate.machine.run n (candidate.machine.step config)] :=
                ih (candidate.machine.step config)
          _ = [candidate.machine.run (n + 1) config] := by
                simp [TM.run, h]

def toNTMCandidate
    (candidate : PolyDTMCandidate) :
    PolyNTMCandidate :=
  { stateCount := candidate.stateCount
    machine := toNTM candidate
    blank_none := candidate.blank_none
    timeBound := candidate.timeBound
    time_poly := candidate.time_poly }

theorem correctAt_to_ntm
    (candidate : PolyDTMCandidate)
    (language : BitLanguage)
    (x : BitString)
    (hCorrect : candidate.CorrectAt language x) :
    (toNTMCandidate candidate).CorrectAt language x := by
  rcases hCorrect with ⟨hHalt, hAccept⟩
  have hHaltEq :
      candidate.machine.halting
        (candidate.machine.run
          (candidate.timeBound x.length)
          (initialTMConfig candidate.machine x)).state = true :=
    hHalt
  constructor
  · intro reached hMem
    have hRuns :=
      runBranches_to_tm_run candidate
        (candidate.timeBound x.length)
        (initialTMConfig candidate.machine x)
    change
      reached ∈
        (toNTM candidate).runBranches
          (candidate.timeBound x.length)
          [initialTMConfig candidate.machine x] at hMem
    rw [hRuns] at hMem
    have hEq :
        reached =
          candidate.machine.run
            (candidate.timeBound x.length)
            (initialTMConfig candidate.machine x) := by
      simpa using hMem
    subst reached
    by_cases ha :
        candidate.accepting
          (candidate.machine.run
            (candidate.timeBound x.length)
            (initialTMConfig candidate.machine x)).state = true
    · left
      simp [toNTMCandidate, toNTM, hHaltEq, ha]
    · right
      have haFalse :
          candidate.accepting
            (candidate.machine.run
              (candidate.timeBound x.length)
              (initialTMConfig candidate.machine x)).state = false := by
        cases hval :
          candidate.accepting
            (candidate.machine.run
              (candidate.timeBound x.length)
              (initialTMConfig candidate.machine x)).state <;> simp_all
      simp [toNTMCandidate, toNTM, hHaltEq, haFalse]
  · constructor
    · intro hNAcc
      rcases hNAcc with ⟨reached, hMem, hAcc⟩
      have hRuns :=
        runBranches_to_tm_run candidate
          (candidate.timeBound x.length)
          (initialTMConfig candidate.machine x)
      change
        reached ∈
          (toNTM candidate).runBranches
            (candidate.timeBound x.length)
            [initialTMConfig candidate.machine x] at hMem
      rw [hRuns] at hMem
      have hEq :
          reached =
            candidate.machine.run
              (candidate.timeBound x.length)
              (initialTMConfig candidate.machine x) := by
        simpa using hMem
      subst reached
      have hCandidateAccept :
          candidate.accepting
              (candidate.machine.run
                (candidate.timeBound x.length)
                (initialTMConfig candidate.machine x)).state = true := by
        simpa [toNTMCandidate, toNTM, hHaltEq] using hAcc
      exact hAccept.mp hCandidateAccept
    · intro hLanguage
      have hCandidateAccept :
          candidate.accepting
              (candidate.machine.run
                (candidate.timeBound x.length)
                (initialTMConfig candidate.machine x)).state = true :=
        hAccept.mpr hLanguage
      refine ⟨
        candidate.machine.run
          (candidate.timeBound x.length)
          (initialTMConfig candidate.machine x),
        ?_, ?_⟩
      · change
          candidate.machine.run
              (candidate.timeBound x.length)
              (initialTMConfig candidate.machine x) ∈
            (toNTM candidate).runBranches
              (candidate.timeBound x.length)
              [initialTMConfig candidate.machine x]
        rw [runBranches_to_tm_run]
        simp
      · simp [toNTMCandidate, toNTM, hHaltEq, hCandidateAccept]

def realization_to_ntm
    {language : BitLanguage}
    (R : PolyDTMRealization language) :
    PolyNTMRealization language :=
  { candidate := toNTMCandidate R.candidate
    decides := fun x => correctAt_to_ntm R.candidate language x (R.decides x) }

theorem inP_subset_inNP
    (language : BitLanguage) :
    InP language → InNP language := by
  rintro ⟨R⟩
  exact ⟨realization_to_ntm R⟩

#print axioms MCore.Real.CanonicalPSubsetNP.accept_or_reject_eq_halting
#print axioms MCore.Real.CanonicalPSubsetNP.runBranches_to_tm_run
#print axioms MCore.Real.CanonicalPSubsetNP.correctAt_to_ntm
#print axioms MCore.Real.CanonicalPSubsetNP.inP_subset_inNP

end CanonicalPSubsetNP
end Real
end MCore
