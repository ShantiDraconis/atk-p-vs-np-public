import MCore.Real.P01PhysicalEmbeddedRun
import MCore.Real.MachineRunLemmas

namespace MCore
namespace Real
namespace P01PhysicalEmbeddedRunMulti

open P01PhysicalDispatcher
open P01PhysicalEmbeddedRun
open P01FullVerifierStackPrimitiveMachine
open P01WitnessIndexedReadMachine
open P01FullVerifierSourceRewind

/-- Exact multi-step embedding while the local machine stays non-halting
through every strict prefix of the run. -/
def StackPrefixNonHalting
    (fuel : Nat)
    (c : Configuration (Fin 8) (Option Bool)) : Prop :=
  ∀ k, k < fuel →
    stackPrimitiveMachine.halting
      (stackPrimitiveMachine.run k c).state = false

def WitnessPrefixNonHalting
    (fuel : Nat)
    (c : Configuration (Fin 6) (Option Bool)) : Prop :=
  ∀ k, k < fuel →
    witnessIndexedReadMachine.halting
      (witnessIndexedReadMachine.run k c).state = false

def RewindPrefixNonHalting
    (fuel : Nat)
    (c : Configuration (Fin 3) (Option Bool)) : Prop :=
  ∀ k, k < fuel →
    sourceRewindMachine.halting
      (sourceRewindMachine.run k c).state = false

theorem dispatcher_run_stack_of_prefix_nonhalting
    (fuel : Nat)
    (c : Configuration (Fin 8) (Option Bool))
    (hprefix : StackPrefixNonHalting fuel c) :
    physicalDispatcherMachine.run fuel (embedStackConfig c) =
      embedStackConfig (stackPrimitiveMachine.run fuel c) := by
  induction fuel generalizing c with
  | zero =>
      rfl
  | succ n ih =>
      have h0 : stackPrimitiveMachine.halting c.state = false := by
        exact hprefix 0 (Nat.succ_pos n)
      have htail :
          StackPrefixNonHalting n (stackPrimitiveMachine.run 1 c) := by
        intro k hk
        have hlt : 1 + k < n + 1 := by omega
        have h := hprefix (1 + k) hlt
        rw [MachineRunLemmas.run_add stackPrimitiveMachine 1 k c] at h
        exact h
      calc
        physicalDispatcherMachine.run (n + 1) (embedStackConfig c)
            = physicalDispatcherMachine.run n
                (physicalDispatcherMachine.run 1 (embedStackConfig c)) := by
                rw [show n + 1 = 1 + n by omega]
                exact MachineRunLemmas.run_add
                  physicalDispatcherMachine 1 n (embedStackConfig c)
        _ = physicalDispatcherMachine.run n
              (embedStackConfig (stackPrimitiveMachine.run 1 c)) := by
              rw [dispatcher_run_stack_one_of_not_halt c h0]
        _ = embedStackConfig
              (stackPrimitiveMachine.run n (stackPrimitiveMachine.run 1 c)) := by
              exact ih (stackPrimitiveMachine.run 1 c) htail
        _ = embedStackConfig (stackPrimitiveMachine.run (n + 1) c) := by
              rw [show n + 1 = 1 + n by omega]
              rw [MachineRunLemmas.run_add stackPrimitiveMachine 1 n c]

theorem dispatcher_run_witness_of_prefix_nonhalting
    (fuel : Nat)
    (c : Configuration (Fin 6) (Option Bool))
    (hprefix : WitnessPrefixNonHalting fuel c) :
    physicalDispatcherMachine.run fuel (embedWitnessConfig c) =
      embedWitnessConfig (witnessIndexedReadMachine.run fuel c) := by
  induction fuel generalizing c with
  | zero =>
      rfl
  | succ n ih =>
      have h0 : witnessIndexedReadMachine.halting c.state = false := by
        exact hprefix 0 (Nat.succ_pos n)
      have htail :
          WitnessPrefixNonHalting n (witnessIndexedReadMachine.run 1 c) := by
        intro k hk
        have hlt : 1 + k < n + 1 := by omega
        have h := hprefix (1 + k) hlt
        rw [MachineRunLemmas.run_add witnessIndexedReadMachine 1 k c] at h
        exact h
      calc
        physicalDispatcherMachine.run (n + 1) (embedWitnessConfig c)
            = physicalDispatcherMachine.run n
                (physicalDispatcherMachine.run 1 (embedWitnessConfig c)) := by
                rw [show n + 1 = 1 + n by omega]
                exact MachineRunLemmas.run_add
                  physicalDispatcherMachine 1 n (embedWitnessConfig c)
        _ = physicalDispatcherMachine.run n
              (embedWitnessConfig (witnessIndexedReadMachine.run 1 c)) := by
              rw [dispatcher_run_witness_one_of_not_halt c h0]
        _ = embedWitnessConfig
              (witnessIndexedReadMachine.run n
                (witnessIndexedReadMachine.run 1 c)) := by
              exact ih (witnessIndexedReadMachine.run 1 c) htail
        _ = embedWitnessConfig (witnessIndexedReadMachine.run (n + 1) c) := by
              rw [show n + 1 = 1 + n by omega]
              rw [MachineRunLemmas.run_add witnessIndexedReadMachine 1 n c]

theorem dispatcher_run_rewind_of_prefix_nonhalting
    (fuel : Nat)
    (c : Configuration (Fin 3) (Option Bool))
    (hprefix : RewindPrefixNonHalting fuel c) :
    physicalDispatcherMachine.run fuel (embedRewindConfig c) =
      embedRewindConfig (sourceRewindMachine.run fuel c) := by
  induction fuel generalizing c with
  | zero =>
      rfl
  | succ n ih =>
      have h0 : sourceRewindMachine.halting c.state = false := by
        exact hprefix 0 (Nat.succ_pos n)
      have htail :
          RewindPrefixNonHalting n (sourceRewindMachine.run 1 c) := by
        intro k hk
        have hlt : 1 + k < n + 1 := by omega
        have h := hprefix (1 + k) hlt
        rw [MachineRunLemmas.run_add sourceRewindMachine 1 k c] at h
        exact h
      calc
        physicalDispatcherMachine.run (n + 1) (embedRewindConfig c)
            = physicalDispatcherMachine.run n
                (physicalDispatcherMachine.run 1 (embedRewindConfig c)) := by
                rw [show n + 1 = 1 + n by omega]
                exact MachineRunLemmas.run_add
                  physicalDispatcherMachine 1 n (embedRewindConfig c)
        _ = physicalDispatcherMachine.run n
              (embedRewindConfig (sourceRewindMachine.run 1 c)) := by
              rw [dispatcher_run_rewind_one_of_not_halt c h0]
        _ = embedRewindConfig
              (sourceRewindMachine.run n (sourceRewindMachine.run 1 c)) := by
              exact ih (sourceRewindMachine.run 1 c) htail
        _ = embedRewindConfig (sourceRewindMachine.run (n + 1) c) := by
              rw [show n + 1 = 1 + n by omega]
              rw [MachineRunLemmas.run_add sourceRewindMachine 1 n c]

#print axioms MCore.Real.P01PhysicalEmbeddedRunMulti.dispatcher_run_stack_of_prefix_nonhalting
#print axioms MCore.Real.P01PhysicalEmbeddedRunMulti.dispatcher_run_witness_of_prefix_nonhalting
#print axioms MCore.Real.P01PhysicalEmbeddedRunMulti.dispatcher_run_rewind_of_prefix_nonhalting

end P01PhysicalEmbeddedRunMulti
end Real
end MCore
