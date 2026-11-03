import MCore.Real.P01RawVerifierLift
import MCore.Real.P01DirectVerifierInhabitant

namespace MCore
namespace Real
namespace P01RawPreparedRejectLift

open CanonicalFinalProof
open P01NTMRunLaws
open P01CheckedEvalRunLoopNTM
open P01CheckedVerifierCompositeNTM
open P01RawVerifierLift
open P01DirectVerifierInhabitant
open P01WitnessPreservingPrep

abbrev EvalConfig :=
  Configuration CheckedEvalRunState (Option Bool)

abbrev VerifierConfig :=
  Configuration CheckedVerifierState (Option Bool)

/-- Any explicit evaluator reject reached from a nonempty prepared source lifts
to exact verifier fail-closed behavior at the combined physical fuel. -/
theorem prepared_nonempty_reject_fail_closed
    (witness : BitString)
    (b : Bool) (bs : BitString)
    (m1 : Nat) (target : EvalConfig)
    (hreach :
      target ∈ checkedEvalRunLoopMachine.runBranches m1
        [{ state := checkedEvalRunLoopMachine.initial,
           tape := P01EvalCursorMachine.evalCursorStackEndTape
             witness 0 (b :: bs) [] 0 }])
    (hreject : target.state = .reject) :
    ∃ total ≤ (b :: bs).length + 3 + m1,
      checkedVerifierMachine.HaltsWithin total
        { state := checkedVerifierMachine.initial,
          tape := preparedTape witness (b :: bs) } ∧
      ¬ checkedVerifierMachine.AcceptsWithin total
        { state := checkedVerifierMachine.initial,
          tape := preparedTape witness (b :: bs) } := by
  obtain ⟨m0, hm0, hfull⟩ :=
    prepared_nonempty_lift_eval_reach
      witness b bs m1 target hreach
  let start : VerifierConfig :=
    { state := checkedVerifierMachine.initial,
      tape := preparedTape witness (b :: bs) }
  let terminal : VerifierConfig :=
    P01NTMRunLaws.liftConfig checkedEvalEmbed target
  have htermState : terminal.state = .reject := by
    simp [terminal, P01NTMRunLaws.liftConfig, checkedEvalEmbed, hreject]
  have hhalt : Halted checkedVerifierMachine terminal := by
    unfold Halted
    simp [htermState, checkedVerifierMachine]
  have hhalts :
      checkedVerifierMachine.HaltsWithin (m0 + m1) start :=
    P01CheckedVerifierDeterminism.haltsWithin_of_reaches_halted
      (m0 + m1) start terminal
      (by simpa [start, terminal] using hfull)
      hhalt
  have hnot :
      ¬ checkedVerifierMachine.AcceptsWithin (m0 + m1) start := by
    rw [acceptsWithin_iff_of_reached_terminal
      (m0 + m1) start terminal
      (by simpa [start, terminal] using hfull)]
    simp [htermState, checkedVerifierMachine]
  refine ⟨m0 + m1, ?_, ?_, ?_⟩
  · omega
  · simpa [start] using hhalts
  · simpa [start] using hnot

/-- Empty raw source rejects directly in the verifier start state transition. -/
theorem prepared_empty_reject_fail_closed
    (witness : BitString) :
    checkedVerifierMachine.HaltsWithin 1
        { state := checkedVerifierMachine.initial,
          tape := preparedTape witness [] } ∧
      ¬ checkedVerifierMachine.AcceptsWithin 1
        { state := checkedVerifierMachine.initial,
          tape := preparedTape witness [] } := by
  let start : VerifierConfig :=
    { state := checkedVerifierMachine.initial,
      tape := preparedTape witness [] }
  let terminal : VerifierConfig :=
    { state := .reject, tape := preparedTape witness [] }
  have hreach :
      terminal ∈ checkedVerifierMachine.runBranches 1 [start] := by
    simp [start, terminal, NTM.runBranches, NTM.successors,
      checkedVerifierMachine, preparedTape, NTM.stepBranch,
      Tape.write, Tape.move]
  have hhalt : Halted checkedVerifierMachine terminal := by
    simp [terminal, Halted, checkedVerifierMachine]
  have hh :=
    P01CheckedVerifierDeterminism.haltsWithin_of_reaches_halted 1 start terminal hreach hhalt
  have hn :
      ¬ checkedVerifierMachine.AcceptsWithin 1 start := by
    rw [acceptsWithin_iff_of_reached_terminal 1 start terminal hreach]
    simp [terminal, checkedVerifierMachine]
  exact ⟨by simpa [start] using hh, by simpa [start] using hn⟩

#print axioms MCore.Real.P01RawPreparedRejectLift.prepared_nonempty_reject_fail_closed
#print axioms MCore.Real.P01RawPreparedRejectLift.prepared_empty_reject_fail_closed

end P01RawPreparedRejectLift
end Real
end MCore
