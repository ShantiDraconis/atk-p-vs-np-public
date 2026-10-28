import MCore.Real.CanonicalPSubsetNP
import MCore.Real.P02TotalCandidateKleeneReduction
import MCore.Real.PNPNTMTableauClosure

namespace MCore
namespace Real
namespace P02ComplementRunRealization

open CanonicalFinalProof
open CanonicalPSubsetNP
open P02KleeneUniversalBridge
open P02TotalCandidateKleeneReduction
open PNPCookLevinMaterialMinCut
open PNPNTMTableauFrontier
open PNPNTMTableauClosure

/-- The bounded language complementary to the candidate's declared acceptance.
This is deliberately local to one candidate and contains no P/NP endpoint. -/
def ComplementDeclaredAccept
    (M : PolyDTMCandidate) : BitLanguage :=
  fun x => ¬ DeclaredAccepts M x

/-- Deterministic-as-nondeterministic simulation with the two terminal labels
swapped.  The transition graph and clock are unchanged. -/
def complementToNTM
    (candidate : PolyDTMCandidate) :
    NTM (Fin (candidate.stateCount + 1)) (Option Bool) :=
  { initial := candidate.machine.initial
    blank := candidate.machine.blank
    transition := fun q symbol => [candidate.machine.transition q symbol]
    accepting := fun q =>
      Bool.and (candidate.machine.halting q) (!(candidate.accepting q))
    rejecting := fun q =>
      Bool.and (candidate.machine.halting q) (candidate.accepting q) }

theorem complement_accept_or_reject_eq_halting
    (candidate : PolyDTMCandidate)
    (q : Fin (candidate.stateCount + 1)) :
    ((complementToNTM candidate).accepting q ||
      (complementToNTM candidate).rejecting q) =
        candidate.machine.halting q := by
  cases h : candidate.machine.halting q <;>
    cases a : candidate.accepting q <;>
    simp [complementToNTM, h, a]

theorem successors_complementToNTM
    (candidate : PolyDTMCandidate)
    (config :
      Configuration
        (Fin (candidate.stateCount + 1))
        (Option Bool)) :
    (complementToNTM candidate).successors config =
      [candidate.machine.step config] := by
  rfl

/-- Swapping the two terminal labels does not change the unique physical run. -/
theorem runBranches_complement_to_tm_run
    (candidate : PolyDTMCandidate)
    (fuel : Nat)
    (config :
      Configuration
        (Fin (candidate.stateCount + 1))
        (Option Bool)) :
    (complementToNTM candidate).runBranches fuel [config] =
      [candidate.machine.run fuel config] := by
  induction fuel generalizing config with
  | zero =>
      rfl
  | succ n ih =>
      by_cases h : candidate.machine.halting config.state = true
      · have hstop :
          ((complementToNTM candidate).accepting config.state ||
            (complementToNTM candidate).rejecting config.state) = true := by
          rw [complement_accept_or_reject_eq_halting]
          exact h
        have hHalted :
            [config].filter (fun c =>
              (complementToNTM candidate).accepting c.state ||
                (complementToNTM candidate).rejecting c.state) = [config] := by
          simp [hstop]
        have hActivePoint :
            Bool.not
              ((complementToNTM candidate).accepting config.state ||
                (complementToNTM candidate).rejecting config.state) = false := by
          rw [hstop]
          rfl
        have hActive :
            [config].filter (fun c =>
              !((complementToNTM candidate).accepting c.state ||
                (complementToNTM candidate).rejecting c.state)) = [] := by
          simp only [List.filter_cons, List.filter_nil]
          rw [hActivePoint]
          rfl
        calc
          (complementToNTM candidate).runBranches (n + 1) [config]
              = (complementToNTM candidate).runBranches n [config] := by
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
          ((complementToNTM candidate).accepting config.state ||
            (complementToNTM candidate).rejecting config.state) = false := by
          rw [complement_accept_or_reject_eq_halting]
          exact hFalse
        have hHalted :
            [config].filter (fun c =>
              (complementToNTM candidate).accepting c.state ||
                (complementToNTM candidate).rejecting c.state) = [] := by
          simp [hstop]
        have hActivePoint :
            Bool.not
              ((complementToNTM candidate).accepting config.state ||
                (complementToNTM candidate).rejecting config.state) = true := by
          rw [hstop]
          rfl
        have hActive :
            [config].filter (fun c =>
              !((complementToNTM candidate).accepting c.state ||
                (complementToNTM candidate).rejecting c.state)) = [config] := by
          simp only [List.filter_cons, List.filter_nil]
          rw [hActivePoint]
          rfl
        calc
          (complementToNTM candidate).runBranches (n + 1) [config]
              = (complementToNTM candidate).runBranches n
                  ((complementToNTM candidate).successors config) := by
                  rw [NTM.runBranches]
                  rw [hActive, hHalted]
                  rfl
          _ = (complementToNTM candidate).runBranches n
                  [candidate.machine.step config] := by
                rw [successors_complementToNTM]
          _ = [candidate.machine.run n (candidate.machine.step config)] :=
                ih (candidate.machine.step config)
          _ = [candidate.machine.run (n + 1) config] := by
                simp [TM.run, h]

def complementToNTMCandidate
    (candidate : PolyDTMCandidate) :
    PolyNTMCandidate :=
  { stateCount := candidate.stateCount
    machine := complementToNTM candidate
    blank_none := candidate.blank_none
    timeBound := candidate.timeBound
    time_poly := candidate.time_poly }

/-- A candidate whose declared clock is total has a concrete polynomial NTM
realization of the complement of its declared bounded acceptance. -/
theorem complement_correctAt
    (candidate : PolyDTMCandidate)
    (hTotal : DeclaredClockTotal candidate)
    (x : BitString) :
    (complementToNTMCandidate candidate).CorrectAt
      (ComplementDeclaredAccept candidate) x := by
  have hHalt := hTotal x
  have hHaltEq :
      candidate.machine.halting
        (candidate.machine.run
          (candidate.timeBound x.length)
          (initialTMConfig candidate.machine x)).state = true :=
    hHalt
  constructor
  · intro reached hMem
    have hRuns :=
      runBranches_complement_to_tm_run candidate
        (candidate.timeBound x.length)
        (initialTMConfig candidate.machine x)
    change
      reached ∈
        (complementToNTM candidate).runBranches
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
    · right
      simp [complementToNTMCandidate, complementToNTM, hHaltEq, ha]
    · left
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
      simp [complementToNTMCandidate, complementToNTM, hHaltEq, haFalse]
  · constructor
    · intro hNAcc hDeclared
      rcases hNAcc with ⟨reached, hMem, hAcc⟩
      have hRuns :=
        runBranches_complement_to_tm_run candidate
          (candidate.timeBound x.length)
          (initialTMConfig candidate.machine x)
      change
        reached ∈
          (complementToNTM candidate).runBranches
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
      have hCandidateFalse :
          candidate.accepting
              (candidate.machine.run
                (candidate.timeBound x.length)
                (initialTMConfig candidate.machine x)).state = false := by
        simpa [complementToNTMCandidate, complementToNTM, hHaltEq] using hAcc
      -- repair 2026-10-25: `DeclaredAccepts` is a definition, so `rw` cannot
      -- see the accepting-state equation inside it; expose it by ascription.
      have hDeclaredState :
          candidate.accepting
              (candidate.machine.run
                (candidate.timeBound x.length)
                (initialTMConfig candidate.machine x)).state = true :=
        hDeclared
      rw [hCandidateFalse] at hDeclaredState
      exact Bool.false_ne_true hDeclaredState
    · intro hNotDeclared
      have hCandidateFalse :
          candidate.accepting
              (candidate.machine.run
                (candidate.timeBound x.length)
                (initialTMConfig candidate.machine x)).state = false := by
        cases hval :
          candidate.accepting
            (candidate.machine.run
              (candidate.timeBound x.length)
              (initialTMConfig candidate.machine x)).state
        · rfl
        · exfalso
          exact hNotDeclared hval
      refine ⟨
        candidate.machine.run
          (candidate.timeBound x.length)
          (initialTMConfig candidate.machine x),
        ?_, ?_⟩
      · change
          candidate.machine.run
              (candidate.timeBound x.length)
              (initialTMConfig candidate.machine x) ∈
            (complementToNTM candidate).runBranches
              (candidate.timeBound x.length)
              [initialTMConfig candidate.machine x]
        rw [runBranches_complement_to_tm_run]
        simp
      · simp [complementToNTMCandidate, complementToNTM,
          hHaltEq, hCandidateFalse]

def complementRunRealization
    (candidate : PolyDTMCandidate)
    (hTotal : DeclaredClockTotal candidate) :
    PolyNTMRealization (ComplementDeclaredAccept candidate) :=
  { candidate := complementToNTMCandidate candidate
    decides := fun x => complement_correctAt candidate hTotal x }

/-- Concrete Cook--Levin reduction for the complemented bounded run. -/
def complementSemanticReduction
    (candidate : PolyDTMCandidate)
    (hTotal : DeclaredClockTotal candidate) :
    NTMToCanonicalSATSemanticReduction
      (complementRunRealization candidate hTotal) :=
  concreteNTMTableauProducer.toSemanticReduction
    (complementRunRealization candidate hTotal)

/-- Material semantic bridge obtained without a P/NP endpoint:
SAT of the generated tableau is exactly failure of declared acceptance on the
source input.  Notice that the generated SAT bitstring is [reduce x], not x. -/
theorem complement_reduce_correct
    (candidate : PolyDTMCandidate)
    (hTotal : DeclaredClockTotal candidate)
    (x : BitString) :
    PNPCookLevinMaterialMinCut.CanonicalSAT
        ((complementSemanticReduction candidate hTotal).reduce x) ↔
      ¬ DeclaredAccepts candidate x := by
  exact (complementSemanticReduction candidate hTotal).correct x |>.symm

/-- The remaining self-input obligation is exposed rather than assumed:
one must connect a source input with the SAT encoding generated from that same
input strongly enough to transfer the candidate's declared behavior. -/
def SelfInputAlignment
    (candidate : PolyDTMCandidate)
    (hTotal : DeclaredClockTotal candidate) : Prop :=
  ∃ x : BitString,
    (complementSemanticReduction candidate hTotal).reduce x = x

theorem selfInputAlignment_gives_flip
    (candidate : PolyDTMCandidate)
    (hTotal : DeclaredClockTotal candidate)
    (hAlign : SelfInputAlignment candidate hTotal) :
    ∃ x : BitString,
      PNPCookLevinMaterialMinCut.CanonicalSAT x ↔
        ¬ DeclaredAccepts candidate x := by
  rcases hAlign with ⟨x, hx⟩
  refine ⟨x, ?_⟩
  -- repair 2026-10-25: `rw [← hx]` also rewrote the `x` inside
  -- `DeclaredAccepts candidate x`; rewrite only the reduced SAT input.
  have h := complement_reduce_correct candidate hTotal x
  rw [hx] at h
  exact h

#print axioms MCore.Real.P02ComplementRunRealization.runBranches_complement_to_tm_run
#print axioms MCore.Real.P02ComplementRunRealization.complement_correctAt
#print axioms MCore.Real.P02ComplementRunRealization.complement_reduce_correct
#print axioms MCore.Real.P02ComplementRunRealization.selfInputAlignment_gives_flip

end P02ComplementRunRealization
end Real
end MCore
