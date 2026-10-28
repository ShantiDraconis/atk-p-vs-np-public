import MCore.Real.P01PhysicalDispatcherBridge
import MCore.Real.MachineRunLemmas

namespace MCore
namespace Real
namespace P01PhysicalEmbeddedRun

open P01PhysicalDispatcher
open P01PhysicalDispatcherBridge
open P01FullVerifierStackPrimitiveMachine
open P01WitnessIndexedReadMachine
open P01FullVerifierSourceRewind

def embedStackConfig
    (c : Configuration (Fin 8) (Option Bool)) :
    Configuration DispatcherState (Option Bool) :=
  { state := stackState c.state, tape := c.tape }

def embedWitnessConfig
    (c : Configuration (Fin 6) (Option Bool)) :
    Configuration DispatcherState (Option Bool) :=
  { state := witnessReadState c.state, tape := c.tape }

def embedRewindConfig
    (c : Configuration (Fin 3) (Option Bool)) :
    Configuration DispatcherState (Option Bool) :=
  { state := rewindState c.state, tape := c.tape }

theorem dispatcher_step_stack
    (c : Configuration (Fin 8) (Option Bool)) :
    physicalDispatcherMachine.step (embedStackConfig c) =
      embedStackConfig (stackPrimitiveMachine.step c) := by
  cases c with
  | mk q tape =>
      cases tape with
      | mk left head right =>
          simp [embedStackConfig, TM.step, stack_transition_lift, Tape.write]

theorem dispatcher_step_witness
    (c : Configuration (Fin 6) (Option Bool)) :
    physicalDispatcherMachine.step (embedWitnessConfig c) =
      embedWitnessConfig (witnessIndexedReadMachine.step c) := by
  cases c with
  | mk q tape =>
      cases tape with
      | mk left head right =>
          simp [embedWitnessConfig, TM.step, witness_transition_lift, Tape.write]

theorem dispatcher_step_rewind
    (c : Configuration (Fin 3) (Option Bool)) :
    physicalDispatcherMachine.step (embedRewindConfig c) =
      embedRewindConfig (sourceRewindMachine.step c) := by
  cases c with
  | mk q tape =>
      cases tape with
      | mk left head right =>
          simp [embedRewindConfig, TM.step, rewind_transition_lift, Tape.write]

/-- One-step embedding is exact while the local submachine has not halted.
This is the compositional kernel needed for later multi-step run proofs. -/
theorem dispatcher_run_stack_one_of_not_halt
    (c : Configuration (Fin 8) (Option Bool))
    (h : stackPrimitiveMachine.halting c.state = false) :
    physicalDispatcherMachine.run 1 (embedStackConfig c) =
      embedStackConfig (stackPrimitiveMachine.run 1 c) := by
  have hacc : stackState c.state ≠ acceptState := by
    intro he
    have hv := congrArg (fun q : DispatcherState => q.val) he
    simp [stackState, acceptState] at hv
    omega
  have hrej : stackState c.state ≠ rejectState := by
    intro he
    have hv := congrArg (fun q : DispatcherState => q.val) he
    simp [stackState, rejectState] at hv
    omega
  have hglob :
      physicalDispatcherMachine.halting (stackState c.state) = false := by
    simp [physicalDispatcherMachine, hacc, hrej]
  have hlocal :
      stackPrimitiveMachine.run 1 c = stackPrimitiveMachine.step c := by
    rw [TM.run]
    simp [h]
    rfl
  calc
    physicalDispatcherMachine.run 1 (embedStackConfig c)
        = physicalDispatcherMachine.step (embedStackConfig c) := by
            rw [TM.run]
            simp [embedStackConfig, hglob]
            rfl
    _ = embedStackConfig (stackPrimitiveMachine.step c) :=
      dispatcher_step_stack c
    _ = embedStackConfig (stackPrimitiveMachine.run 1 c) := by
      rw [hlocal]

theorem dispatcher_run_witness_one_of_not_halt
    (c : Configuration (Fin 6) (Option Bool))
    (h : witnessIndexedReadMachine.halting c.state = false) :
    physicalDispatcherMachine.run 1 (embedWitnessConfig c) =
      embedWitnessConfig (witnessIndexedReadMachine.run 1 c) := by
  have hacc : witnessReadState c.state ≠ acceptState := by
    intro he
    have hv := congrArg (fun q : DispatcherState => q.val) he
    simp [witnessReadState, acceptState] at hv
    omega
  have hrej : witnessReadState c.state ≠ rejectState := by
    intro he
    have hv := congrArg (fun q : DispatcherState => q.val) he
    simp [witnessReadState, rejectState] at hv
    omega
  have hglob :
      physicalDispatcherMachine.halting (witnessReadState c.state) = false := by
    simp [physicalDispatcherMachine, hacc, hrej]
  have hlocal :
      witnessIndexedReadMachine.run 1 c = witnessIndexedReadMachine.step c := by
    rw [TM.run]
    simp [h]
    rfl
  calc
    physicalDispatcherMachine.run 1 (embedWitnessConfig c)
        = physicalDispatcherMachine.step (embedWitnessConfig c) := by
            rw [TM.run]
            simp [embedWitnessConfig, hglob]
            rfl
    _ = embedWitnessConfig (witnessIndexedReadMachine.step c) :=
      dispatcher_step_witness c
    _ = embedWitnessConfig (witnessIndexedReadMachine.run 1 c) := by
      rw [hlocal]

theorem dispatcher_run_rewind_one_of_not_halt
    (c : Configuration (Fin 3) (Option Bool))
    (h : sourceRewindMachine.halting c.state = false) :
    physicalDispatcherMachine.run 1 (embedRewindConfig c) =
      embedRewindConfig (sourceRewindMachine.run 1 c) := by
  have hacc : rewindState c.state ≠ acceptState := by
    intro he
    have hv := congrArg (fun q : DispatcherState => q.val) he
    simp [rewindState, acceptState] at hv
    omega
  have hrej : rewindState c.state ≠ rejectState := by
    intro he
    have hv := congrArg (fun q : DispatcherState => q.val) he
    simp [rewindState, rejectState] at hv
    omega
  have hglob :
      physicalDispatcherMachine.halting (rewindState c.state) = false := by
    simp [physicalDispatcherMachine, hacc, hrej]
  have hlocal :
      sourceRewindMachine.run 1 c = sourceRewindMachine.step c := by
    rw [TM.run]
    simp [h]
    rfl
  calc
    physicalDispatcherMachine.run 1 (embedRewindConfig c)
        = physicalDispatcherMachine.step (embedRewindConfig c) := by
            rw [TM.run]
            simp [embedRewindConfig, hglob]
            rfl
    _ = embedRewindConfig (sourceRewindMachine.step c) :=
      dispatcher_step_rewind c
    _ = embedRewindConfig (sourceRewindMachine.run 1 c) := by
      rw [hlocal]

#print axioms MCore.Real.P01PhysicalEmbeddedRun.dispatcher_step_stack
#print axioms MCore.Real.P01PhysicalEmbeddedRun.dispatcher_step_witness
#print axioms MCore.Real.P01PhysicalEmbeddedRun.dispatcher_step_rewind
#print axioms MCore.Real.P01PhysicalEmbeddedRun.dispatcher_run_stack_one_of_not_halt
#print axioms MCore.Real.P01PhysicalEmbeddedRun.dispatcher_run_witness_one_of_not_halt
#print axioms MCore.Real.P01PhysicalEmbeddedRun.dispatcher_run_rewind_one_of_not_halt

end P01PhysicalEmbeddedRun
end Real
end MCore
