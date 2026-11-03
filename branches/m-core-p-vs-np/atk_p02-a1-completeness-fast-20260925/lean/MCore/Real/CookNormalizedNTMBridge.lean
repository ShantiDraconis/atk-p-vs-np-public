import MCore.Real.CookNormalizedDTMBridge

namespace MCore
namespace Real
namespace CookNormalizedNTMBridge

open CanonicalFinalProof
open CookNormalizedMachineModel

def cookNTMOfInternal
    (C : PolyNTMCandidate) : CookNTM :=
  { stateCount := C.stateCount
    initial := C.machine.initial
    transition := C.machine.transition
    accepting := C.machine.accepting
    rejecting := C.machine.rejecting }

theorem cookNTMOfInternal_stepBranch_eq
    (C : PolyNTMCandidate)
    (config :
      Configuration (Fin (C.stateCount + 1)) (Option Bool))
    (choice :
      Fin (C.stateCount + 1) × Option Bool × Direction) :
    CookNTM.stepBranch (cookNTMOfInternal C) config choice =
      C.machine.stepBranch config choice := by
  simp [CookNTM.stepBranch, cookNTMOfInternal,
    NTM.stepBranch, C.blank_none]

theorem cookNTMOfInternal_successors_eq
    (C : PolyNTMCandidate)
    (config :
      Configuration (Fin (C.stateCount + 1)) (Option Bool)) :
    CookNTM.successors (cookNTMOfInternal C) config =
      C.machine.successors config := by
  unfold CookNTM.successors NTM.successors
  simp [cookNTMOfInternal, CookNTM.stepBranch,
    NTM.stepBranch, C.blank_none]

theorem cookNTMOfInternal_runBranches_eq
    (C : PolyNTMCandidate)
    (fuel : Nat)
    (configs :
      List (Configuration (Fin (C.stateCount + 1)) (Option Bool))) :
    CookNTM.runBranches (cookNTMOfInternal C) fuel configs =
      C.machine.runBranches fuel configs := by
  induction fuel generalizing configs with
  | zero => rfl
  | succ fuel ih =>
      rw [CookNTM.runBranches, NTM.runBranches]
      have hsucc :
          CookNTM.successors (cookNTMOfInternal C) =
            C.machine.successors := by
        funext config
        exact cookNTMOfInternal_successors_eq C config
      rw [hsucc]
      exact ih _

def cookNTMCandidateOfInternal
    (C : PolyNTMCandidate) : CookPolyNTMCandidate :=
  { machine := cookNTMOfInternal C
    timeBound := C.timeBound
    time_poly := C.time_poly }

theorem cookNTMOfInternal_acceptsWithin_iff
    (C : PolyNTMCandidate)
    (fuel : Nat)
    (config :
      Configuration (Fin (C.stateCount + 1)) (Option Bool)) :
    CookNTM.AcceptsWithin (cookNTMOfInternal C) fuel config ↔
      C.machine.AcceptsWithin fuel config := by
  unfold CookNTM.AcceptsWithin NTM.AcceptsWithin
  rw [cookNTMOfInternal_runBranches_eq]
  rfl

theorem cookNTMOfInternal_haltsWithin_iff
    (C : PolyNTMCandidate)
    (fuel : Nat)
    (config :
      Configuration (Fin (C.stateCount + 1)) (Option Bool)) :
    CookNTM.HaltsWithin (cookNTMOfInternal C) fuel config ↔
      C.machine.HaltsWithin fuel config := by
  unfold CookNTM.HaltsWithin NTM.HaltsWithin
  rw [cookNTMOfInternal_runBranches_eq]
  rfl

theorem cookNTMCandidateOfInternal_correctAt
    (C : PolyNTMCandidate)
    (L : BitLanguage)
    (x : BitString)
    (h : C.CorrectAt L x) :
    (cookNTMCandidateOfInternal C).CorrectAt L x := by
  unfold PolyNTMCandidate.CorrectAt at h
  unfold CookPolyNTMCandidate.CorrectAt
  dsimp [cookNTMCandidateOfInternal, initialCookNTMConfig,
    initialNTMConfig]
  rw [CookNormalizedDTMBridge.externalInputTape_eq_canonical]
  rcases h with ⟨hhalt, hsem⟩
  constructor
  · exact
      (cookNTMOfInternal_haltsWithin_iff C
        (C.timeBound x.length)
        { state := C.machine.initial, tape := inputTape x }).2 hhalt
  · exact
      (cookNTMOfInternal_acceptsWithin_iff C
        (C.timeBound x.length)
        { state := C.machine.initial, tape := inputTape x }).trans hsem

def internalNTM_to_cook
    {L : BitLanguage}
    (R : PolyNTMRealization L) :
    CookNPRealization L :=
  { candidate := cookNTMCandidateOfInternal R.candidate
    decides := fun x =>
      cookNTMCandidateOfInternal_correctAt
        R.candidate L x (R.decides x) }

def internalNTMOfCook
    (M : CookNTM) :
    NTM (Fin (M.stateCount + 1)) (Option Bool) :=
  { initial := M.initial
    blank := none
    transition := M.transition
    accepting := M.accepting
    rejecting := M.rejecting }

theorem internalNTMOfCook_stepBranch_eq
    (M : CookNTM)
    (config :
      Configuration (Fin (M.stateCount + 1)) (Option Bool))
    (choice :
      Fin (M.stateCount + 1) × Option Bool × Direction) :
    (internalNTMOfCook M).stepBranch config choice =
      CookNTM.stepBranch M config choice := by
  rfl

theorem internalNTMOfCook_successors_eq
    (M : CookNTM)
    (config :
      Configuration (Fin (M.stateCount + 1)) (Option Bool)) :
    (internalNTMOfCook M).successors config =
      CookNTM.successors M config := by
  rfl

theorem internalNTMOfCook_runBranches_eq
    (M : CookNTM)
    (fuel : Nat)
    (configs :
      List (Configuration (Fin (M.stateCount + 1)) (Option Bool))) :
    (internalNTMOfCook M).runBranches fuel configs =
      CookNTM.runBranches M fuel configs := by
  induction fuel generalizing configs with
  | zero => rfl
  | succ fuel ih =>
      rw [NTM.runBranches, CookNTM.runBranches]
      have hsucc :
          (internalNTMOfCook M).successors =
            CookNTM.successors M := by
        funext config
        exact internalNTMOfCook_successors_eq M config
      rw [hsucc]
      exact ih _

def internalNTMCandidateOfCook
    (C : CookPolyNTMCandidate) : PolyNTMCandidate :=
  { stateCount := C.machine.stateCount
    machine := internalNTMOfCook C.machine
    blank_none := rfl
    timeBound := C.timeBound
    time_poly := C.time_poly }

theorem internalNTMOfCook_acceptsWithin_iff
    (M : CookNTM)
    (fuel : Nat)
    (config :
      Configuration (Fin (M.stateCount + 1)) (Option Bool)) :
    (internalNTMOfCook M).AcceptsWithin fuel config ↔
      CookNTM.AcceptsWithin M fuel config := by
  unfold NTM.AcceptsWithin CookNTM.AcceptsWithin
  rw [internalNTMOfCook_runBranches_eq]
  rfl

theorem internalNTMOfCook_haltsWithin_iff
    (M : CookNTM)
    (fuel : Nat)
    (config :
      Configuration (Fin (M.stateCount + 1)) (Option Bool)) :
    (internalNTMOfCook M).HaltsWithin fuel config ↔
      CookNTM.HaltsWithin M fuel config := by
  unfold NTM.HaltsWithin CookNTM.HaltsWithin
  rw [internalNTMOfCook_runBranches_eq]
  rfl

theorem internalNTMCandidateOfCook_correctAt
    (C : CookPolyNTMCandidate)
    (L : BitLanguage)
    (x : BitString)
    (h : C.CorrectAt L x) :
    (internalNTMCandidateOfCook C).CorrectAt L x := by
  unfold CookPolyNTMCandidate.CorrectAt at h
  unfold PolyNTMCandidate.CorrectAt
  dsimp [internalNTMCandidateOfCook, initialCookNTMConfig,
    initialNTMConfig]
  rw [← CookNormalizedDTMBridge.externalInputTape_eq_canonical]
  rcases h with ⟨hhalt, hsem⟩
  constructor
  · exact
      (internalNTMOfCook_haltsWithin_iff C.machine
        (C.timeBound x.length)
        { state := C.machine.initial, tape := externalInputTape x }).2 hhalt
  · exact
      (internalNTMOfCook_acceptsWithin_iff C.machine
        (C.timeBound x.length)
        { state := C.machine.initial, tape := externalInputTape x }).trans hsem

def cookNTM_to_internal
    {L : BitLanguage}
    (R : CookNPRealization L) :
    PolyNTMRealization L :=
  { candidate := internalNTMCandidateOfCook R.candidate
    decides := fun x =>
      internalNTMCandidateOfCook_correctAt
        R.candidate L x (R.decides x) }

#print axioms MCore.Real.CookNormalizedNTMBridge.cookNTMOfInternal_runBranches_eq
#print axioms MCore.Real.CookNormalizedNTMBridge.internalNTM_to_cook
#print axioms MCore.Real.CookNormalizedNTMBridge.internalNTMOfCook_runBranches_eq
#print axioms MCore.Real.CookNormalizedNTMBridge.cookNTM_to_internal

end CookNormalizedNTMBridge
end Real
end MCore
