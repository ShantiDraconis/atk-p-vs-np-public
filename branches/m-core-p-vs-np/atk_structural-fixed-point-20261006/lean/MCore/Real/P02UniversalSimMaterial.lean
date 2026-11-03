import MCore.Real.P02FiniteMachineDescription

namespace MCore
namespace Real
namespace P02UniversalSimMaterial

open CanonicalFinalProof
open P02FiniteMachineDescription

def encodedInitialConfig
    (enc : EncodedMachine)
    (x : BitString) :
    Configuration (Fin (enc.stateCount + 1)) (Option Bool) :=
  initialTMConfig enc.toTM x

/--
Executable bounded universal simulator for an already-decoded finite machine
description.  It reports the accepting bit and the supplied fuel exactly when
the interpreted machine is halted by that fuel.
-/
def UniversalSim
    (enc : EncodedMachine)
    (x : BitString)
    (fuel : Nat) : Option (Bool × Nat) :=
  let cfg := encodedInitialConfig enc x
  let out := enc.toTM.run fuel cfg
  if enc.toTM.halting out.state then
    some (enc.accepting out.state, fuel)
  else
    none

theorem universalSim_some_iff
    (enc : EncodedMachine)
    (x : BitString)
    (fuel : Nat)
    (b : Bool)
    (k : Nat) :
    UniversalSim enc x fuel = some (b, k) ↔
      k = fuel ∧
      enc.toTM.HaltsWithin fuel (encodedInitialConfig enc x) ∧
      b = enc.accepting
        (enc.toTM.run fuel (encodedInitialConfig enc x)).state := by
  unfold UniversalSim
  unfold TM.HaltsWithin
  simp only [encodedInitialConfig]
  by_cases h :
      enc.toTM.halting
        (enc.toTM.run fuel (initialTMConfig enc.toTM x)).state = true
  · simp only [h, if_pos, Option.some.injEq, Prod.mk.injEq]
    constructor
    · rintro ⟨hb, hk⟩
      exact ⟨hk.symm, hb.symm⟩
    · rintro ⟨hk, hb⟩
      exact ⟨hb.symm, hk.symm⟩
  · have hf :
        enc.toTM.halting
          (enc.toTM.run fuel (initialTMConfig enc.toTM x)).state = false := by
      cases hh :
          enc.toTM.halting
            (enc.toTM.run fuel (initialTMConfig enc.toTM x)).state <;>
        simp_all
    simp [hf]

theorem universalSim_none_iff
    (enc : EncodedMachine)
    (x : BitString)
    (fuel : Nat) :
    UniversalSim enc x fuel = none ↔
      ¬ enc.toTM.HaltsWithin fuel (encodedInitialConfig enc x) := by
  unfold UniversalSim
  unfold TM.HaltsWithin
  simp only [encodedInitialConfig]
  by_cases h :
      enc.toTM.halting
        (enc.toTM.run fuel (initialTMConfig enc.toTM x)).state = true
  · simp [h]
  · have hf :
        enc.toTM.halting
          (enc.toTM.run fuel (initialTMConfig enc.toTM x)).state = false := by
      cases hh :
          enc.toTM.halting
            (enc.toTM.run fuel (initialTMConfig enc.toTM x)).state <;>
        simp_all
    simp [hf]

theorem universalSim_projected_correct
    (M : PolyDTMCandidate)
    (x : BitString)
    (fuel : Nat)
    (b : Bool)
    (k : Nat) :
    UniversalSim (projectFiniteMachine M) x fuel = some (b, k) ↔
      k = fuel ∧
      M.machine.HaltsWithin fuel (initialTMConfig M.machine x) ∧
      b = M.accepting
        (M.machine.run fuel (initialTMConfig M.machine x)).state := by
  rw [universalSim_some_iff]
  simp only [encodedInitialConfig]
  rw [projectFiniteMachine_toTM]
  rfl

#print axioms MCore.Real.P02UniversalSimMaterial.universalSim_some_iff
#print axioms MCore.Real.P02UniversalSimMaterial.universalSim_none_iff
#print axioms MCore.Real.P02UniversalSimMaterial.universalSim_projected_correct

end P02UniversalSimMaterial
end Real
end MCore
