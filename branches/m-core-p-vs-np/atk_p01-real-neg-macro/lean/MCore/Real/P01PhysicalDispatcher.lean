import MCore.Real.P01FullVerifierPhysicalControl
import MCore.Real.P01FullVerifierStackPrimitiveMachine
import MCore.Real.P01WitnessIndexedReadMachine
import MCore.Real.P01FullVerifierSourceRewind

namespace MCore
namespace Real
namespace P01PhysicalDispatcher

open CanonicalFinalProof
open P01FullVerifierPhysicalControl
open P01FullVerifierStackPrimitiveMachine
open P01WitnessIndexedReadMachine
open P01FullVerifierSourceRewind

/--
Fixed finite-control union of the already-certified physical verifier
submachines.

State allocation:
0..7    verifier control
8..15   stack primitive
16..21  indexed witness reader
22..24  source rewind
25      global accept
26      global reject
-/
abbrev DispatcherState := Fin 27

def controlState (q : Fin 8) : DispatcherState :=
  ⟨q.val, by omega⟩

def stackState (q : Fin 8) : DispatcherState :=
  ⟨8 + q.val, by omega⟩

def witnessReadState (q : Fin 6) : DispatcherState :=
  ⟨16 + q.val, by omega⟩

def rewindState (q : Fin 3) : DispatcherState :=
  ⟨22 + q.val, by omega⟩

def acceptState : DispatcherState := ⟨25, by decide⟩
def rejectState : DispatcherState := ⟨26, by decide⟩

def asControl (q : DispatcherState) (h : q.val < 8) : Fin 8 :=
  ⟨q.val, h⟩

def asStack
    (q : DispatcherState) (hlo : 8 ≤ q.val) (hhi : q.val < 16) : Fin 8 :=
  ⟨q.val - 8, by omega⟩

def asWitness
    (q : DispatcherState) (hlo : 16 ≤ q.val) (hhi : q.val < 22) : Fin 6 :=
  ⟨q.val - 16, by omega⟩

def asRewind
    (q : DispatcherState) (hlo : 22 ≤ q.val) (hhi : q.val < 25) : Fin 3 :=
  ⟨q.val - 22, by omega⟩

def liftControl
    (x : Fin 8 × Option Bool × Direction) :
    DispatcherState × Option Bool × Direction :=
  (controlState x.1, x.2.1, x.2.2)

def liftStack
    (x : Fin 8 × Option Bool × Direction) :
    DispatcherState × Option Bool × Direction :=
  (stackState x.1, x.2.1, x.2.2)

def liftWitness
    (x : Fin 6 × Option Bool × Direction) :
    DispatcherState × Option Bool × Direction :=
  (witnessReadState x.1, x.2.1, x.2.2)

def liftRewind
    (x : Fin 3 × Option Bool × Direction) :
    DispatcherState × Option Bool × Direction :=
  (rewindState x.1, x.2.1, x.2.2)

/--
Concrete fixed transition table containing every already-certified local
physical primitive.  Cross-phase semantic dispatch remains a separate proof
obligation; no semantic endpoint is postulated here.
-/
def physicalDispatcherMachine : TM DispatcherState (Option Bool) :=
  { initial := controlState decoderEvaluatorMachine.initial
    blank := none
    transition := fun q symbol =>
      if hc : q.val < 8 then
        liftControl
          (decoderEvaluatorMachine.transition (asControl q hc) symbol)
      else if hslo : 8 ≤ q.val then
        if hshi : q.val < 16 then
          liftStack
            (stackPrimitiveMachine.transition (asStack q hslo hshi) symbol)
        else if hwlo : 16 ≤ q.val then
          if hwhi : q.val < 22 then
            liftWitness
              (witnessIndexedReadMachine.transition
                (asWitness q hwlo hwhi) symbol)
          else if hrlo : 22 ≤ q.val then
            if hrhi : q.val < 25 then
              liftRewind
                (sourceRewindMachine.transition
                  (asRewind q hrlo hrhi) symbol)
            else
              (q, symbol, .stay)
          else
            (q, symbol, .stay)
        else
          (q, symbol, .stay)
      else
        (q, symbol, .stay)
    halting := fun q => q == acceptState || q == rejectState }

@[simp] theorem physicalDispatcherMachine_blank :
    physicalDispatcherMachine.blank = none := rfl

@[simp] theorem physicalDispatcherMachine_initial :
    physicalDispatcherMachine.initial =
      controlState decoderEvaluatorMachine.initial := rfl

theorem physicalDispatcherMachine_fixed_type :
    Nonempty (TM (Fin 27) (Option Bool)) :=
  ⟨physicalDispatcherMachine⟩

theorem controlState_injective :
    ∀ ⦃a b : Fin 8⦄, controlState a = controlState b → a = b := by
  intro a b h
  apply Fin.ext
  exact congrArg (fun z : DispatcherState => z.val) h

theorem stackState_injective :
    ∀ ⦃a b : Fin 8⦄, stackState a = stackState b → a = b := by
  intro a b h
  apply Fin.ext
  have hv := congrArg (fun z : DispatcherState => z.val) h
  simp [stackState] at hv
  omega

theorem witnessReadState_injective :
    ∀ ⦃a b : Fin 6⦄, witnessReadState a = witnessReadState b → a = b := by
  intro a b h
  apply Fin.ext
  have hv := congrArg (fun z : DispatcherState => z.val) h
  simp [witnessReadState] at hv
  omega

theorem rewindState_injective :
    ∀ ⦃a b : Fin 3⦄, rewindState a = rewindState b → a = b := by
  intro a b h
  apply Fin.ext
  have hv := congrArg (fun z : DispatcherState => z.val) h
  simp [rewindState] at hv
  omega

#print axioms MCore.Real.P01PhysicalDispatcher.physicalDispatcherMachine_blank
#print axioms MCore.Real.P01PhysicalDispatcher.physicalDispatcherMachine_fixed_type
#print axioms MCore.Real.P01PhysicalDispatcher.controlState_injective
#print axioms MCore.Real.P01PhysicalDispatcher.stackState_injective
#print axioms MCore.Real.P01PhysicalDispatcher.witnessReadState_injective
#print axioms MCore.Real.P01PhysicalDispatcher.rewindState_injective

end P01PhysicalDispatcher
end Real
end MCore
