import MCore.Real.P01RawVerifierLift
import MCore.Real.P01RawTotalContract
import MCore.Real.P01CheckedVerifierDeterminism

namespace MCore
namespace Real
namespace P01RawVerifierFailClosed

open CanonicalFinalProof
open P01NTMRunLaws
open P01CheckedEvalRunLoopNTM
open P01CheckedVerifierCompositeNTM
open P01CheckedVerifierDeterminism
open P01WitnessPreservingPrep
open P01RawDeadEnd
open P01RawVerifierLift
open P01RawTotalContract

abbrev EvalConfig :=
  Configuration CheckedEvalRunState (Option Bool)

abbrev VerifierConfig :=
  Configuration CheckedVerifierState (Option Bool)

/-- Explicit evaluator reject lifts to the wrapper's explicit reject state. -/
theorem lifted_explicit_reject_halted
    (cfg : EvalConfig)
    (h : cfg.state = .reject) :
    Halted checkedVerifierMachine
      (P01NTMRunLaws.liftConfig checkedEvalEmbed cfg) := by
  rcases cfg with ⟨q, tape⟩
  simp only at h
  subst q
  simp [Halted, P01NTMRunLaws.liftConfig, checkedEvalEmbed,
    checkedVerifierMachine]

theorem lifted_explicit_reject_not_accepting
    (cfg : EvalConfig)
    (h : cfg.state = .reject) :
    checkedVerifierMachine.accepting
      (P01NTMRunLaws.liftConfig checkedEvalEmbed cfg).state = false := by
  rcases cfg with ⟨q, tape⟩
  simp only at h
  subst q
  rfl

/-- Any internal checked-evaluator fail-closed outcome becomes a complete
prepared-verifier failure certificate for a nonempty source. -/
theorem prepared_nonempty_eval_fail_closed
    (witness : BitString)
    (b : Bool) (bs : BitString)
    (m1 : Nat) (target : EvalConfig)
    (hreach :
      target ∈ checkedEvalRunLoopMachine.runBranches m1
        [{ state := checkedEvalRunLoopMachine.initial,
           tape := P01EvalCursorMachine.evalCursorStackEndTape
             witness 0 (b :: bs) [] 0 }])
    (hfc : EvalFailClosed target) :
    ∃ total ≤ (b :: bs).length + 3 + m1 + 1,
      checkedVerifierMachine.HaltsWithin total
        { state := checkedVerifierMachine.initial,
          tape := preparedTape witness (b :: bs) } ∧
      ¬ checkedVerifierMachine.AcceptsWithin total
        { state := checkedVerifierMachine.initial,
          tape := preparedTape witness (b :: bs) } := by
  rcases hfc with hreject | hdead
  · obtain ⟨m0, hm0, hfull⟩ :=
      prepared_nonempty_lift_eval_reach
        witness b bs m1 target hreach
    let lifted := P01NTMRunLaws.liftConfig checkedEvalEmbed target
    have hhalt : Halted checkedVerifierMachine lifted :=
      lifted_explicit_reject_halted target hreject
    have hhaltWithin :
        checkedVerifierMachine.HaltsWithin (m0 + m1)
          ({ state := checkedVerifierMachine.initial,
             tape := preparedTape witness (b :: bs) } : VerifierConfig) :=
      haltsWithin_of_reaches_halted
        (m0 + m1)
        ({ state := checkedVerifierMachine.initial,
           tape := preparedTape witness (b :: bs) } : VerifierConfig)
        lifted
        (by simpa [lifted] using hfull)
        hhalt
    have hnot :
        ¬ checkedVerifierMachine.AcceptsWithin (m0 + m1)
          ({ state := checkedVerifierMachine.initial,
             tape := preparedTape witness (b :: bs) } : VerifierConfig) := by
      intro hacc
      rcases hacc with ⟨z, hz, hzacc⟩
      have heq :=
        runBranches_eq_singleton_of_mem
          (m0 + m1)
          ({ state := checkedVerifierMachine.initial,
             tape := preparedTape witness (b :: bs) } : VerifierConfig)
          lifted
          (by simpa [lifted] using hfull)
      rw [heq] at hz
      simp only [List.mem_singleton] at hz
      subst z
      have hnacc :=
        lifted_explicit_reject_not_accepting target hreject
      rw [hnacc] at hzacc
      contradiction
    refine ⟨m0 + m1, ?_, hhaltWithin, hnot⟩
    simp at hm0 ⊢
    omega
  · exact prepared_nonempty_dead_fail_closed
      witness b bs m1 target hreach hdead.1 hdead.2

/-- Empty prepared source rejects directly from the wrapper start state. -/
theorem prepared_empty_fail_closed
    (witness : BitString) :
    ∃ total ≤ 1,
      checkedVerifierMachine.HaltsWithin total
        { state := checkedVerifierMachine.initial,
          tape := preparedTape witness [] } ∧
      ¬ checkedVerifierMachine.AcceptsWithin total
        { state := checkedVerifierMachine.initial,
          tape := preparedTape witness [] } := by
  let start : VerifierConfig :=
    { state := checkedVerifierMachine.initial,
      tape := preparedTape witness [] }
  let terminal : VerifierConfig :=
    { state := .reject,
      tape := preparedTape witness [] }
  have hsucc :
      terminal ∈ checkedVerifierMachine.successors start := by
    dsimp [start, terminal]
    simp [checkedVerifierMachine, NTM.successors, NTM.stepBranch,
      preparedTape, Tape.write, Tape.move]
  have hone :
      terminal ∈ checkedVerifierMachine.runBranches 1 [start] := by
    have h :=
      mem_runBranches_succ_of_successor
        checkedVerifierMachine 0 [start] start terminal
        (by simp [NTM.runBranches])
        (start_not_halted (preparedTape witness [])) hsucc
    simpa using h
  have hhalt : Halted checkedVerifierMachine terminal := by
    dsimp [terminal]
    simp [Halted, checkedVerifierMachine]
  have hhalts :
      checkedVerifierMachine.HaltsWithin 1 start :=
    haltsWithin_of_reaches_halted 1 start terminal hone hhalt
  have hnot :
      ¬ checkedVerifierMachine.AcceptsWithin 1 start := by
    intro hacc
    rcases hacc with ⟨z, hz, hzacc⟩
    have heq := runBranches_eq_singleton_of_mem 1 start terminal hone
    rw [heq] at hz
    simp only [List.mem_singleton] at hz
    subst z
    simp [terminal, checkedVerifierMachine] at hzacc
  exact ⟨1, by omega, by simpa [start] using hhalts,
    by simpa [start] using hnot⟩

#print axioms MCore.Real.P01RawVerifierFailClosed.prepared_nonempty_eval_fail_closed
#print axioms MCore.Real.P01RawVerifierFailClosed.prepared_empty_fail_closed

end P01RawVerifierFailClosed
end Real
end MCore
