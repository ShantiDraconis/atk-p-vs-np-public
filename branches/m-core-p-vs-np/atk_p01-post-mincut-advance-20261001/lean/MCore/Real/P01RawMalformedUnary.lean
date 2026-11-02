import MCore.Real.P01InputIndexLookahead
import MCore.Real.P01CheckedEvalRunInputTag
import MCore.Real.P01RawDeadEnd
import MCore.Real.P01CheckedEvalRunTagPrefix
import MCore.Real.P01RawVerifierLift

namespace MCore
namespace Real
namespace P01RawMalformedUnary

open CanonicalFinalProof
open P01EvalCursorMachine
open P01WitnessIndexedReadPreserving
open P01InputReturnMode
open P01CNFMode
open P01NeedExprTagDecode
open P01NeedExprCompositeNTM
open P01CheckedVerifierCompositeNTM
open P01InputIndexLookahead
open P01InputNodeCompositeNTM
open P01InputNodeCompositeRun
open P01CheckedEvalRunLoopNTM
open P01CheckedEvalRunInputTag
open P01NTMRunLaws
open MachineRunLemmas
open P01CheckedEvalRunTagPrefix
open P01RawVerifierLift

/-- A 000 payload made only of unary true markers and followed by the physical
source separator has no terminating false marker. The real finite-control
lookahead therefore reaches its reject state after exactly k+1 steps. -/
theorem lookahead_truncated_unary_reject
    (witness frameStack : BitString)
    (consumed padding k : Nat) :
    (inputIndexLookaheadMachine.run (k + 1)
      { state := inputIndexLookaheadMachine.initial,
        tape :=
          evalCursorReadTape witness consumed
            (List.replicate k true) frameStack padding }).state =
      .reject := by
  let base : List (Option Bool) :=
    List.replicate consumed none ++ none :: witness.map some
  let suffix : List (Option Bool) :=
    none :: frameStack.reverse.map some ++
      none :: List.replicate padding none
  have hview :
      evalCursorReadTape witness consumed
          (List.replicate k true) frameStack padding =
        rightStreamTape base
          (List.replicate k (some true) ++ suffix) := by
    cases k with
    | zero =>
        simp [base, suffix, evalCursorReadTape, rightStreamTape,
          List.append_assoc]
    | succ k =>
        simp [base, suffix, evalCursorReadTape, rightStreamTape,
          List.map_replicate, List.replicate_succ,
          List.append_assoc]
  rw [hview]
  change
    (inputIndexLookaheadMachine.run (k + 1)
      { state := .scanIndex,
        tape :=
          rightStreamTape base
            (List.replicate k (some true) ++ suffix) }).state = .reject
  rw [run_add inputIndexLookaheadMachine k 1]
  rw [scanIndex_over_true k base suffix]
  simp [suffix, rightStreamTape, inputIndexLookaheadMachine,
    TM.run, TM.step, Tape.write, Tape.move]

/-- The same malformed unary payload reaches the dead lookahead-reject state
inside the actual input-node composite machine. -/
theorem inputComposite_truncated_unary_reaches_dead
    (witness frameStack : BitString)
    (consumed padding k : Nat) :
    ∃ m ≤ k + 1, ∃ tape,
      ({ state := .look .reject, tape := tape } :
        Configuration InputNodeCompositeState (Option Bool)) ∈
      inputNodeCompositeMachine.runBranches m
        [{ state := inputNodeCompositeMachine.initial,
           tape :=
             evalCursorReadTape witness consumed
               (List.replicate k true) frameStack padding }] := by
  let c0 : Configuration InputIndexLookaheadState (Option Bool) :=
    { state := inputIndexLookaheadMachine.initial,
      tape :=
        evalCursorReadTape witness consumed
          (List.replicate k true) frameStack padding }
  obtain ⟨m, hm, hmem⟩ :=
    look_run_reachable (k + 1) c0
  have hstate :
      (inputIndexLookaheadMachine.run (k + 1) c0).state = .reject := by
    simpa [c0] using
      lookahead_truncated_unary_reject
        witness frameStack consumed padding k
  cases hres :
      inputIndexLookaheadMachine.run (k + 1) c0 with
  | mk q tape =>
      have hq : q = .reject := by
        simpa [hres] using hstate
      subst q
      rw [hres] at hmem
      refine ⟨m, hm, tape, ?_⟩
      simpa [lookConfig] using hmem

/-- The malformed composite target is active but has no successors. This is a
fail-closed dead state rather than a labelled accepting/rejecting terminal. -/
theorem inputComposite_look_reject_is_dead
    (tape : Tape (Option Bool)) :
    ¬ Halted inputNodeCompositeMachine
        ({ state := .look .reject, tape := tape } :
          Configuration InputNodeCompositeState (Option Bool)) ∧
      inputNodeCompositeMachine.successors
        ({ state := .look .reject, tape := tape } :
          Configuration InputNodeCompositeState (Option Bool)) = [] := by
  constructor
  · simp [Halted, inputNodeCompositeMachine]
  · simp [inputNodeCompositeMachine, NTM.successors]


abbrev EvalConfig :=
  Configuration CheckedEvalRunState (Option Bool)

/-- Active lookahead states embed step-for-step in the checked evaluator. -/
theorem inputLook_checked_successors_active
    (mode : P01CNFMode.SyntaxMode)
    (c : Configuration InputIndexLookaheadState (Option Bool))
    (h : inputIndexLookaheadMachine.halting c.state = false) :
    checkedEvalRunLoopMachine.successors
        (inputCheckedConfig mode (lookConfig c)) =
      [inputCheckedConfig mode (lookConfig (inputIndexLookaheadMachine.step c))] := by
  have hcomp :
      ¬ Halted inputNodeCompositeMachine (lookConfig c) :=
    lookConfig_not_halted c
  rw [inputChecked_successors_active mode (lookConfig c) hcomp]
  rw [look_successors_active c h]
  simp

/-- Any finite lookahead execution lifts into the checked evaluator. -/
theorem inputLook_checked_run_reachable
    (mode : P01CNFMode.SyntaxMode) :
    ∀ (n : Nat) (c : Configuration InputIndexLookaheadState (Option Bool)),
      ∃ m ≤ n,
        inputCheckedConfig mode
            (lookConfig (inputIndexLookaheadMachine.run n c)) ∈
          checkedEvalRunLoopMachine.runBranches m
            [inputCheckedConfig mode (lookConfig c)] := by
  intro n
  induction n with
  | zero =>
      intro c
      exact ⟨0, by omega, by simp [NTM.runBranches, TM.run]⟩
  | succ n ih =>
      intro c
      cases hhalt : inputIndexLookaheadMachine.halting c.state with
      | true =>
          have hr :=
            run_halted inputIndexLookaheadMachine c hhalt (n + 1)
          refine ⟨0, by omega, ?_⟩
          rw [hr]
          simp [NTM.runBranches]
      | false =>
          obtain ⟨m, hm, hmem⟩ := ih (inputIndexLookaheadMachine.step c)
          have hact :
              ¬ Halted checkedEvalRunLoopMachine
                (inputCheckedConfig mode (lookConfig c)) := by
            apply inputChecked_active
            exact lookConfig_not_halted c
          have hsucc :
              inputCheckedConfig mode
                  (lookConfig (inputIndexLookaheadMachine.step c)) ∈
                checkedEvalRunLoopMachine.successors
                  (inputCheckedConfig mode (lookConfig c)) := by
            rw [inputLook_checked_successors_active mode c hhalt]
            simp
          have hone :
              inputCheckedConfig mode
                  (lookConfig (inputIndexLookaheadMachine.step c)) ∈
                checkedEvalRunLoopMachine.runBranches 1
                  [inputCheckedConfig mode (lookConfig c)] := by
            have h :=
              mem_runBranches_succ_of_successor
                checkedEvalRunLoopMachine 0
                [inputCheckedConfig mode (lookConfig c)]
                (inputCheckedConfig mode (lookConfig c))
                (inputCheckedConfig mode
                  (lookConfig (inputIndexLookaheadMachine.step c)))
                (by simp [NTM.runBranches]) hact hsucc
            simpa using h
          have htrans :=
            mem_runBranches_trans checkedEvalRunLoopMachine
              1 m [inputCheckedConfig mode (lookConfig c)]
              (inputCheckedConfig mode
                (lookConfig (inputIndexLookaheadMachine.step c)))
              (inputCheckedConfig mode
                (lookConfig
                  (inputIndexLookaheadMachine.run n
                    (inputIndexLookaheadMachine.step c))))
              hone hmem
          refine ⟨1 + m, by omega, ?_⟩
          simpa [TM.run, hhalt] using htrans

/-- The full checked evaluator follows an input tag with a truncated unary
payload to an active dead state. -/
theorem checked_truncated_unary_reaches_dead
    (mode : P01CNFMode.SyntaxMode)
    (witness frameStack : BitString)
    (consumed padding k : Nat) :
    ∃ m ≤
        checkedTagPrefixFuel
            (false :: false :: false :: List.replicate k true) frameStack +
          (k + 1),
      ∃ dead : EvalConfig,
        dead ∈ checkedEvalRunLoopMachine.runBranches m
          [{ state := .need mode needExprCompositeMachine.initial,
             tape :=
               evalCursorStackEndTape witness consumed
                 (false :: false :: false :: List.replicate k true)
                 frameStack padding }] ∧
        (¬ Halted checkedEvalRunLoopMachine dead) ∧
        checkedEvalRunLoopMachine.successors dead = [] := by
  obtain ⟨m0, hm0, h0⟩ :=
    checked_tag_prefix_reaches
      mode witness (List.replicate k true) frameStack
      consumed padding false false false (by
        cases mode <;> rfl)

  let cLook0 : Configuration InputIndexLookaheadState (Option Bool) :=
    { state := inputIndexLookaheadMachine.initial,
      tape :=
        evalCursorReadTape witness (consumed + 3)
          (List.replicate k true) frameStack padding }

  obtain ⟨m1, hm1, h1⟩ :=
    inputLook_checked_run_reachable mode (k + 1) cLook0

  cases hres :
      inputIndexLookaheadMachine.run (k + 1) cLook0 with
  | mk q tape =>
      have hs :
          (inputIndexLookaheadMachine.run (k + 1) cLook0).state = .reject := by
        simpa [cLook0] using
          (lookahead_truncated_unary_reject
            witness frameStack (consumed + 3) padding k)
      rw [hres] at hs
      have hq : q = .reject := hs
      subst q

      let dead : EvalConfig :=
        inputCheckedConfig mode
          (lookConfig
            ({ state := .reject, tape := tape } :
              Configuration InputIndexLookaheadState (Option Bool)))

      have h1' :
          dead ∈ checkedEvalRunLoopMachine.runBranches m1
            [inputCheckedConfig mode (lookConfig cLook0)] := by
        rw [hres] at h1
        simpa [dead] using h1

      have h0' :
          inputCheckedConfig mode (lookConfig cLook0) ∈
            checkedEvalRunLoopMachine.runBranches m0
              [{ state := .need mode needExprCompositeMachine.initial,
                 tape :=
                   evalCursorStackEndTape witness consumed
                     (false :: false :: false :: List.replicate k true)
                     frameStack padding }] := by
        simpa [postTagState, childMode, decodeTagBits,
          cLook0, inputCheckedConfig, lookConfig] using h0

      have hAll :=
        mem_runBranches_trans checkedEvalRunLoopMachine
          m0 m1
          [{ state := .need mode needExprCompositeMachine.initial,
             tape :=
               evalCursorStackEndTape witness consumed
                 (false :: false :: false :: List.replicate k true)
                 frameStack padding }]
          (inputCheckedConfig mode (lookConfig cLook0))
          dead h0' h1'

      have hcompActive :
          ¬ Halted inputNodeCompositeMachine
            (lookConfig
              ({ state := .reject, tape := tape } :
                Configuration InputIndexLookaheadState (Option Bool))) :=
        lookConfig_not_halted _

      have hactive :
          ¬ Halted checkedEvalRunLoopMachine dead := by
        exact inputChecked_active mode _ hcompActive

      have hcompDead :
          inputNodeCompositeMachine.successors
            (lookConfig
              ({ state := .reject, tape := tape } :
                Configuration InputIndexLookaheadState (Option Bool))) = [] := by
        simp [lookConfig, inputNodeCompositeMachine, NTM.successors]

      have hdead :
          checkedEvalRunLoopMachine.successors dead = [] := by
        rw [show dead =
          inputCheckedConfig mode
            (lookConfig
              ({ state := .reject, tape := tape } :
                Configuration InputIndexLookaheadState (Option Bool))) by rfl]
        rw [inputChecked_successors_active mode _ hcompActive]
        simp [hcompDead]

      refine ⟨m0 + m1, ?_, dead, hAll, hactive, hdead⟩
      omega


/-- The complete prepared verifier is fail-closed on a 000 input payload whose
unary index never terminates with false. -/
theorem prepared_truncated_unary_fail_closed
    (witness : BitString)
    (k : Nat) :
    let source : BitString :=
      false :: false :: false :: List.replicate k true
    ∃ total ≤ 3 * source.length + 10,
      checkedVerifierMachine.HaltsWithin total
        { state := checkedVerifierMachine.initial,
          tape := P01WitnessPreservingPrep.preparedTape witness source } ∧
      ¬ checkedVerifierMachine.AcceptsWithin total
        { state := checkedVerifierMachine.initial,
          tape := P01WitnessPreservingPrep.preparedTape witness source } := by
  let source : BitString :=
    false :: false :: false :: List.replicate k true
  obtain ⟨m1, hm1, dead, hreach, hactive, hdead⟩ :=
    checked_truncated_unary_reaches_dead
      .cnf witness [] 0 0 k
  have hreach' :
      dead ∈ checkedEvalRunLoopMachine.runBranches m1
        [{ state := checkedEvalRunLoopMachine.initial,
           tape := evalCursorStackEndTape witness 0 source [] 0 }] := by
    simpa [source, checkedEvalRunLoopMachine] using hreach
  obtain ⟨total, htotal, hhalt, hnot⟩ :=
    prepared_nonempty_dead_fail_closed
      witness false
      (false :: false :: List.replicate k true)
      m1 dead
      (by simpa [source] using hreach')
      hactive hdead
  refine ⟨total, ?_, ?_, ?_⟩
  · dsimp [source] at hm1 htotal ⊢
    simp [checkedTagPrefixFuel] at hm1 htotal ⊢
    omega
  · simpa [source] using hhalt
  · simpa [source] using hnot

#print axioms MCore.Real.P01RawMalformedUnary.prepared_truncated_unary_fail_closed

#print axioms MCore.Real.P01RawMalformedUnary.inputLook_checked_successors_active
#print axioms MCore.Real.P01RawMalformedUnary.inputLook_checked_run_reachable
#print axioms MCore.Real.P01RawMalformedUnary.checked_truncated_unary_reaches_dead

#print axioms MCore.Real.P01RawMalformedUnary.lookahead_truncated_unary_reject
#print axioms MCore.Real.P01RawMalformedUnary.inputComposite_truncated_unary_reaches_dead
#print axioms MCore.Real.P01RawMalformedUnary.inputComposite_look_reject_is_dead

end P01RawMalformedUnary
end Real
end MCore
