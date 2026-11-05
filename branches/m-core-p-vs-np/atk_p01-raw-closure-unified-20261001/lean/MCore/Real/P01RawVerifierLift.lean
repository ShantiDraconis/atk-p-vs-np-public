import MCore.Real.P01CheckedVerifierRun
import MCore.Real.P01RawDeadEnd

namespace MCore
namespace Real
namespace P01RawVerifierLift

open CanonicalFinalProof
open P01NTMRunLaws
open P01CheckedEvalRunLoopNTM
open P01CheckedVerifierCompositeNTM
open P01CheckedVerifierRun
open P01EvalCursorMachine
open P01WitnessPreservingPrep
open P01RawDeadEnd

abbrev EvalConfig :=
  Configuration CheckedEvalRunState (Option Bool)

abbrev VerifierConfig :=
  Configuration CheckedVerifierState (Option Bool)

/-- Any checked-evaluator reachability fact from the canonical root can be
composed with the already-certified prepared-tape scanner/entry prefix. -/
theorem prepared_nonempty_lift_eval_reach
    (witness : BitString)
    (b : Bool) (bs : BitString)
    (m1 : Nat) (target : EvalConfig)
    (hreach :
      target ∈ checkedEvalRunLoopMachine.runBranches m1
        [{ state := checkedEvalRunLoopMachine.initial,
           tape := evalCursorStackEndTape witness 0 (b :: bs) [] 0 }]) :
    ∃ m0 ≤ (b :: bs).length + 3,
      P01NTMRunLaws.liftConfig checkedEvalEmbed target ∈
        checkedVerifierMachine.runBranches (m0 + m1)
          [{ state := checkedVerifierMachine.initial,
             tape := preparedTape witness (b :: bs) }] := by
  obtain ⟨m0, hm0, h0⟩ :=
    prepared_nonempty_reaches_eval_start witness b bs

  have hLift :
      P01NTMRunLaws.liftConfig checkedEvalEmbed target ∈
        checkedVerifierMachine.runBranches m1
          [({ state := .eval checkedEvalRunLoopMachine.initial,
              tape := evalCursorStackEndTape witness 0 (b :: bs) [] 0 } :
            VerifierConfig)] := by
    exact checked_eval_mem_lift m1
      ({ state := checkedEvalRunLoopMachine.initial,
         tape := evalCursorStackEndTape witness 0 (b :: bs) [] 0 } :
        EvalConfig)
      target hreach

  have hAll :=
    mem_runBranches_trans checkedVerifierMachine
      m0 m1
      [{ state := checkedVerifierMachine.initial,
         tape := preparedTape witness (b :: bs) }]
      ({ state := .eval checkedEvalRunLoopMachine.initial,
         tape := evalCursorStackEndTape witness 0 (b :: bs) [] 0 } :
        VerifierConfig)
      (P01NTMRunLaws.liftConfig checkedEvalEmbed target)
      h0 hLift

  exact ⟨m0, hm0, hAll⟩

/-- A dead checked-evaluator state remains a dead active state after embedding
into the verifier wrapper. -/
theorem lifted_eval_dead_is_verifier_dead
    (target : EvalConfig)
    (hactive : ¬ Halted checkedEvalRunLoopMachine target)
    (hdead : checkedEvalRunLoopMachine.successors target = []) :
    let lifted := P01NTMRunLaws.liftConfig checkedEvalEmbed target
    (¬ Halted checkedVerifierMachine lifted) ∧
      checkedVerifierMachine.successors lifted = [] := by
  let lifted := P01NTMRunLaws.liftConfig checkedEvalEmbed target
  have hactV : ¬ Halted checkedVerifierMachine lifted := by
    intro hh
    have hsim := P01CheckedVerifierCompositeNTM.checkedEvalSimulation
    have hacc :
        checkedVerifierMachine.accepting lifted.state =
          checkedEvalRunLoopMachine.accepting target.state :=
      hsim.accepting target.state
    have hrej :
        checkedVerifierMachine.rejecting lifted.state =
          checkedEvalRunLoopMachine.rejecting target.state :=
      hsim.rejecting target.state
    unfold Halted at hh hactive
    rw [hacc, hrej] at hh
    exact hactive hh
  have hsucc :
      checkedVerifierMachine.successors lifted = [] := by
    have hsim := P01CheckedVerifierCompositeNTM.checkedEvalSimulation
    have hs :=
      hsim.successors target hactive
    rw [hdead] at hs
    simpa [lifted] using hs
  exact ⟨hactV, hsucc⟩

/-- Prepared nonempty sources whose evaluator path reaches a dead state are
globally fail-closed: one step after that reach the verifier frontier is empty,
hence it both HaltsWithin and cannot AcceptWithin. -/
theorem prepared_nonempty_dead_fail_closed
    (witness : BitString)
    (b : Bool) (bs : BitString)
    (m1 : Nat) (target : EvalConfig)
    (hreach :
      target ∈ checkedEvalRunLoopMachine.runBranches m1
        [{ state := checkedEvalRunLoopMachine.initial,
           tape := evalCursorStackEndTape witness 0 (b :: bs) [] 0 }])
    (hactive : ¬ Halted checkedEvalRunLoopMachine target)
    (hdead : checkedEvalRunLoopMachine.successors target = []) :
    ∃ total ≤ (b :: bs).length + 3 + m1 + 1,
      checkedVerifierMachine.HaltsWithin total
        { state := checkedVerifierMachine.initial,
          tape := preparedTape witness (b :: bs) } ∧
      ¬ checkedVerifierMachine.AcceptsWithin total
        { state := checkedVerifierMachine.initial,
          tape := preparedTape witness (b :: bs) } := by
  obtain ⟨m0, hm0, hfull⟩ :=
    prepared_nonempty_lift_eval_reach
      witness b bs m1 target hreach
  let lifted := P01NTMRunLaws.liftConfig checkedEvalEmbed target
  have hVdead := lifted_eval_dead_is_verifier_dead target hactive hdead
  let total := m0 + m1 + 1
  refine ⟨total, ?_, ?_, ?_⟩
  · dsimp [total]
    simp at hm0 ⊢
    omega
  · exact haltsWithin_succ_of_reaches_dead
      (m0 + m1)
      ({ state := checkedVerifierMachine.initial,
         tape := preparedTape witness (b :: bs) } : VerifierConfig)
      lifted
      (by simpa [lifted] using hfull)
      hVdead.1 hVdead.2
  · exact not_acceptsWithin_succ_of_reaches_dead
      (m0 + m1)
      ({ state := checkedVerifierMachine.initial,
         tape := preparedTape witness (b :: bs) } : VerifierConfig)
      lifted
      (by simpa [lifted] using hfull)
      hVdead.1 hVdead.2

#print axioms MCore.Real.P01RawVerifierLift.prepared_nonempty_lift_eval_reach
#print axioms MCore.Real.P01RawVerifierLift.lifted_eval_dead_is_verifier_dead
#print axioms MCore.Real.P01RawVerifierLift.prepared_nonempty_dead_fail_closed

end P01RawVerifierLift
end Real
end MCore
