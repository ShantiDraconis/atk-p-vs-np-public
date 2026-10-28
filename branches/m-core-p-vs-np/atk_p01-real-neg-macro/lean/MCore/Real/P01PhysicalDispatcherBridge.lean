import MCore.Real.P01PhysicalDispatcher

namespace MCore
namespace Real
namespace P01PhysicalDispatcherBridge

open P01PhysicalDispatcher
open P01FullVerifierPhysicalControl
open P01FullVerifierStackPrimitiveMachine
open P01WitnessIndexedReadMachine
open P01FullVerifierSourceRewind

theorem control_transition_lift
    (q : Fin 8) (s : Option Bool) :
    physicalDispatcherMachine.transition (controlState q) s =
      let t := decoderEvaluatorMachine.transition q s
      (controlState t.1, t.2.1, t.2.2) := by
  simp [physicalDispatcherMachine, controlState, asControl, liftControl]

theorem stack_transition_lift
    (q : Fin 8) (s : Option Bool) :
    physicalDispatcherMachine.transition (stackState q) s =
      let t := stackPrimitiveMachine.transition q s
      (stackState t.1, t.2.1, t.2.2) := by
  have hq : q.val < 8 := q.isLt
  have h0 : ¬ (8 + q.val < 8) := by omega
  have h1 : 8 ≤ 8 + q.val := by omega
  have h2 : 8 + q.val < 16 := by omega
  have hnat : 8 + q.val - 8 = q.val := by omega
  have hq' : (⟨8 + q.val - 8, by omega⟩ : Fin 8) = q := by
    apply Fin.ext
    exact hnat
  simp [physicalDispatcherMachine, stackState, asStack, liftStack,
    h0, h1, h2, hq']

theorem witness_transition_lift
    (q : Fin 6) (s : Option Bool) :
    physicalDispatcherMachine.transition (witnessReadState q) s =
      let t := witnessIndexedReadMachine.transition q s
      (witnessReadState t.1, t.2.1, t.2.2) := by
  have hq : q.val < 6 := q.isLt
  have h0 : ¬ (16 + q.val < 8) := by omega
  have h1 : 8 ≤ 16 + q.val := by omega
  have h2 : ¬ (16 + q.val < 16) := by omega
  have h3 : 16 ≤ 16 + q.val := by omega
  have h4 : 16 + q.val < 22 := by omega
  have hnat : 16 + q.val - 16 = q.val := by omega
  have hq' : (⟨16 + q.val - 16, by omega⟩ : Fin 6) = q := by
    apply Fin.ext
    exact hnat
  simp [physicalDispatcherMachine, witnessReadState, asWitness, liftWitness,
    h0, h1, h2, h3, h4, hq']

theorem rewind_transition_lift
    (q : Fin 3) (s : Option Bool) :
    physicalDispatcherMachine.transition (rewindState q) s =
      let t := sourceRewindMachine.transition q s
      (rewindState t.1, t.2.1, t.2.2) := by
  have hq : q.val < 3 := q.isLt
  have h0 : ¬ (22 + q.val < 8) := by omega
  have h1 : 8 ≤ 22 + q.val := by omega
  have h2 : ¬ (22 + q.val < 16) := by omega
  have h3 : 16 ≤ 22 + q.val := by omega
  have h4 : ¬ (22 + q.val < 22) := by omega
  have h5 : 22 ≤ 22 + q.val := by omega
  have h6 : 22 + q.val < 25 := by omega
  have hnat : 22 + q.val - 22 = q.val := by omega
  have hq' : (⟨22 + q.val - 22, by omega⟩ : Fin 3) = q := by
    apply Fin.ext
    exact hnat
  simp [physicalDispatcherMachine, rewindState, asRewind, liftRewind,
    h0, h1, h2, h3, h4, h5, h6, hq']

theorem dispatcher_accept_halts :
    physicalDispatcherMachine.halting acceptState = true := by
  simp [physicalDispatcherMachine, acceptState]

theorem dispatcher_reject_halts :
    physicalDispatcherMachine.halting rejectState = true := by
  simp [physicalDispatcherMachine, rejectState]

#print axioms MCore.Real.P01PhysicalDispatcherBridge.control_transition_lift
#print axioms MCore.Real.P01PhysicalDispatcherBridge.stack_transition_lift
#print axioms MCore.Real.P01PhysicalDispatcherBridge.witness_transition_lift
#print axioms MCore.Real.P01PhysicalDispatcherBridge.rewind_transition_lift
#print axioms MCore.Real.P01PhysicalDispatcherBridge.dispatcher_accept_halts
#print axioms MCore.Real.P01PhysicalDispatcherBridge.dispatcher_reject_halts

end P01PhysicalDispatcherBridge
end Real
end MCore
