import MCore.Real.CookNormalizedMachineModel

namespace MCore
namespace Real
namespace CookNormalizedDTMBridge

open CanonicalFinalProof
open CookNormalizedMachineModel

theorem externalInputTape_eq_canonical
    (x : BitString) :
    externalInputTape x = inputTape x := by
  cases x <;> rfl

def cookDTMOfInternal
    (C : PolyDTMCandidate) : CookDTM :=
  { stateCount := C.stateCount
    initial := C.machine.initial
    transition := C.machine.transition
    halting := C.machine.halting
    accepting := C.accepting }

theorem cookDTMOfInternal_step_eq
    (C : PolyDTMCandidate)
    (config :
      Configuration (Fin (C.stateCount + 1)) (Option Bool)) :
    CookDTM.step (cookDTMOfInternal C) config =
      C.machine.step config := by
  simp [CookDTM.step, cookDTMOfInternal, TM.step, C.blank_none]

theorem cookDTMOfInternal_run_eq
    (C : PolyDTMCandidate)
    (fuel : Nat)
    (config :
      Configuration (Fin (C.stateCount + 1)) (Option Bool)) :
    CookDTM.run (cookDTMOfInternal C) fuel config =
      C.machine.run fuel config := by
  induction fuel generalizing config with
  | zero => rfl
  | succ fuel ih =>
      simp only [CookDTM.run, TM.run]
      by_cases h : C.machine.halting config.state = true
      · simp [cookDTMOfInternal, h]
      · have hf : C.machine.halting config.state = false := by
          cases hh : C.machine.halting config.state <;> simp_all
        simp only [cookDTMOfInternal, hf, Bool.false_eq_true, if_false]
        change
          CookDTM.run (cookDTMOfInternal C) fuel
              (CookDTM.step (cookDTMOfInternal C) config) =
            C.machine.run fuel (C.machine.step config)
        rw [cookDTMOfInternal_step_eq]
        exact ih (C.machine.step config)

def cookCandidateOfInternal
    (C : PolyDTMCandidate) : CookPolyDTMCandidate :=
  { machine := cookDTMOfInternal C
    timeBound := C.timeBound
    time_poly := C.time_poly }

theorem cookCandidateOfInternal_correctAt
    (C : PolyDTMCandidate)
    (L : BitLanguage)
    (x : BitString)
    (h : C.CorrectAt L x) :
    (cookCandidateOfInternal C).CorrectAt L x := by
  unfold PolyDTMCandidate.CorrectAt at h
  unfold CookPolyDTMCandidate.CorrectAt
  dsimp [cookCandidateOfInternal, initialCookDTMConfig,
    initialTMConfig]
  rw [externalInputTape_eq_canonical]
  rcases h with ⟨hhalt, hsem⟩
  constructor
  · unfold CookDTM.HaltsWithin
    unfold TM.HaltsWithin at hhalt
    rw [cookDTMOfInternal_run_eq]
    exact hhalt
  · rw [cookDTMOfInternal_run_eq]
    exact hsem

def internalDTM_to_cook
    {L : BitLanguage}
    (R : PolyDTMRealization L) :
    CookPRealization L :=
  { candidate := cookCandidateOfInternal R.candidate
    decides := fun x =>
      cookCandidateOfInternal_correctAt
        R.candidate L x (R.decides x) }

def internalTMOfCook
    (M : CookDTM) :
    TM (Fin (M.stateCount + 1)) (Option Bool) :=
  { initial := M.initial
    blank := none
    transition := M.transition
    halting := M.halting }

theorem internalTMOfCook_step_eq
    (M : CookDTM)
    (config :
      Configuration (Fin (M.stateCount + 1)) (Option Bool)) :
    (internalTMOfCook M).step config =
      CookDTM.step M config := by
  rfl

theorem internalTMOfCook_run_eq
    (M : CookDTM)
    (fuel : Nat)
    (config :
      Configuration (Fin (M.stateCount + 1)) (Option Bool)) :
    (internalTMOfCook M).run fuel config =
      CookDTM.run M fuel config := by
  induction fuel generalizing config with
  | zero => rfl
  | succ fuel ih =>
      simp only [TM.run, CookDTM.run]
      by_cases h : M.halting config.state = true
      · simp [internalTMOfCook, h]
      · have hf : M.halting config.state = false := by
          cases hh : M.halting config.state <;> simp_all
        simp only [internalTMOfCook, hf, Bool.false_eq_true, if_false]
        change
          (internalTMOfCook M).run fuel
              ((internalTMOfCook M).step config) =
            CookDTM.run M fuel (CookDTM.step M config)
        rw [internalTMOfCook_step_eq]
        exact ih (CookDTM.step M config)

def internalCandidateOfCook
    (C : CookPolyDTMCandidate) : PolyDTMCandidate :=
  { stateCount := C.machine.stateCount
    machine := internalTMOfCook C.machine
    blank_none := rfl
    accepting := C.machine.accepting
    timeBound := C.timeBound
    time_poly := C.time_poly }

theorem internalCandidateOfCook_correctAt
    (C : CookPolyDTMCandidate)
    (L : BitLanguage)
    (x : BitString)
    (h : C.CorrectAt L x) :
    (internalCandidateOfCook C).CorrectAt L x := by
  unfold CookPolyDTMCandidate.CorrectAt at h
  unfold PolyDTMCandidate.CorrectAt
  dsimp [internalCandidateOfCook, initialCookDTMConfig,
    initialTMConfig]
  rw [← externalInputTape_eq_canonical]
  rcases h with ⟨hhalt, hsem⟩
  constructor
  · unfold TM.HaltsWithin
    unfold CookDTM.HaltsWithin at hhalt
    rw [internalTMOfCook_run_eq]
    exact hhalt
  · rw [internalTMOfCook_run_eq]
    exact hsem

def cookDTM_to_internal
    {L : BitLanguage}
    (R : CookPRealization L) :
    PolyDTMRealization L :=
  { candidate := internalCandidateOfCook R.candidate
    decides := fun x =>
      internalCandidateOfCook_correctAt
        R.candidate L x (R.decides x) }

#print axioms MCore.Real.CookNormalizedDTMBridge.cookDTMOfInternal_run_eq
#print axioms MCore.Real.CookNormalizedDTMBridge.cookCandidateOfInternal_correctAt
#print axioms MCore.Real.CookNormalizedDTMBridge.internalDTM_to_cook
#print axioms MCore.Real.CookNormalizedDTMBridge.internalTMOfCook_run_eq
#print axioms MCore.Real.CookNormalizedDTMBridge.internalCandidateOfCook_correctAt
#print axioms MCore.Real.CookNormalizedDTMBridge.cookDTM_to_internal

end CookNormalizedDTMBridge
end Real
end MCore
