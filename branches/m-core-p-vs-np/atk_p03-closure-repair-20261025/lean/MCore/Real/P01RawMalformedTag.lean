import MCore.Real.P01CheckedEvalRunPhaseLift
import MCore.Real.P01CheckedVerifierRun
import MCore.Real.P01RawDeadEnd
import MCore.Real.P01RawVerifierLift

namespace MCore
namespace Real
namespace P01RawMalformedTag

open CanonicalFinalProof
open P01NTMRunLaws
open P01CheckedEvalRunLoopNTM
open P01CheckedEvalRunPhaseLift
open P01NeedExprCompositeNTM
open P01NeedExprTagDecode
open P01EvalCursorMachine
open P01CNFMode
open P01CheckedVerifierRun
open P01CheckedVerifierCompositeNTM
open P01RawDeadEnd
open P01RawVerifierLift
open P01WitnessPreservingPrep

abbrev EvalConfig :=
  Configuration CheckedEvalRunState (Option Bool)

/-- Fewer than three source bits cannot form a tag. The physical 3-bit
decoder reaches its reject state after exactly source.length+1 steps. -/
theorem tagDecode_short_state_reject
    (witness source frameStack : BitString)
    (consumed padding : Nat)
    (hshort : source.length < 3) :
    (tagDecodeMachine.run (source.length + 1)
      { state := tagDecodeMachine.initial,
        tape :=
          evalCursorReadTape witness consumed
            source frameStack padding }).state = .reject := by
  rcases source with _ | ⟨b0, rest⟩
  · simp [tagDecodeMachine, evalCursorReadTape,
      TM.run, TM.step, Tape.write, Tape.move]
  · rcases rest with _ | ⟨b1, rest2⟩
    · cases b0 <;>
        simp [tagDecodeMachine, evalCursorReadTape,
          TM.run, TM.step, Tape.write, Tape.move]
    · rcases rest2 with _ | ⟨b2, rest3⟩
      · cases b0 <;> cases b1 <;>
          simp [tagDecodeMachine, evalCursorReadTape,
            TM.run, TM.step, Tape.write, Tape.move]
      · simp at hshort
        omega

/-- Starting from the checked evaluator's canonical need-state, every
truncated tag reaches a dead checked-decoder state within the seek cost plus
at most three decoder steps. -/
theorem checked_truncated_tag_reaches_dead
    (mode : SyntaxMode)
    (witness source frameStack : BitString)
    (consumed padding : Nat)
    (hshort : source.length < 3) :
    ∃ m ≤ frameStack.length + source.length + 7,
      ∃ dead : EvalConfig,
        dead ∈ checkedEvalRunLoopMachine.runBranches m
          [{ state := .need mode needExprCompositeMachine.initial,
             tape :=
               evalCursorStackEndTape witness consumed
                 source frameStack padding }] ∧
        (¬ Halted checkedEvalRunLoopMachine dead) ∧
        checkedEvalRunLoopMachine.successors dead = [] := by
  let nSeek := frameStack.length + source.length + 3
  let t0 :=
    evalCursorStackEndTape witness consumed source frameStack padding
  let tRead :=
    evalCursorReadTape witness consumed source frameStack padding
  let cSeek0 : Configuration CursorSeekState (Option Bool) :=
    { state := cursorSeekMachine.initial, tape := t0 }
  let cSeekH : Configuration CursorSeekState (Option Bool) :=
    { state := .halt, tape := tRead }
  let cDec0 : Configuration TagDecodeState (Option Bool) :=
    { state := tagDecodeMachine.initial, tape := tRead }

  have hSeekExact :
      cursorSeekMachine.run nSeek cSeek0 = cSeekH := by
    dsimp [nSeek, cSeek0, cSeekH, t0, tRead]
    exact cursorSeek_run witness consumed source frameStack padding

  obtain ⟨mS, hmS, hS⟩ :=
    seek_run_reachable mode nSeek cSeek0
  have hS' :
      seekConfig mode cSeekH ∈
        checkedEvalRunLoopMachine.runBranches mS
          [seekConfig mode cSeek0] := by
    rw [hSeekExact] at hS
    exact hS

  have hSeekHandSucc :
      decodeConfig mode cDec0 ∈
        checkedEvalRunLoopMachine.successors (seekConfig mode cSeekH) := by
    dsimp [decodeConfig, seekConfig, cDec0, cSeekH]
    simp [checkedEvalRunLoopMachine, needExprCompositeMachine,
      needCheckedEmbed, NTM.successors, NTM.stepBranch,
      Tape.write, Tape.move]

  have hSeekHand :
      decodeConfig mode cDec0 ∈
        checkedEvalRunLoopMachine.runBranches 1 [seekConfig mode cSeekH] := by
    have h :=
      mem_runBranches_succ_of_successor
        checkedEvalRunLoopMachine 0 [seekConfig mode cSeekH]
        (seekConfig mode cSeekH) (decodeConfig mode cDec0)
        (by simp [NTM.runBranches])
        (seekConfig_not_halted mode cSeekH) hSeekHandSucc
    simpa using h

  have hToDec :=
    mem_runBranches_trans checkedEvalRunLoopMachine
      mS 1 [seekConfig mode cSeek0]
      (seekConfig mode cSeekH) (decodeConfig mode cDec0)
      hS' hSeekHand

  let d := source.length + 1
  obtain ⟨mD, hmD, hD⟩ :=
    decode_run_reachable mode d cDec0

  have hState :
      (tagDecodeMachine.run d cDec0).state = .reject := by
    dsimp [d, cDec0, tRead]
    exact tagDecode_short_state_reject
      witness source frameStack consumed padding hshort

  cases hres : tagDecodeMachine.run d cDec0 with
  | mk q tape =>
      have hq : q = .reject := by
        simpa [hres] using hState
      subst q
      have hD' :
          decodeConfig mode
              ({ state := .reject, tape := tape } :
                Configuration TagDecodeState (Option Bool)) ∈
            checkedEvalRunLoopMachine.runBranches mD
              [decodeConfig mode cDec0] := by
        rw [hres] at hD
        exact hD

      let dead : EvalConfig :=
        decodeConfig mode
          ({ state := .reject, tape := tape } :
            Configuration TagDecodeState (Option Bool))

      have hAll :=
        mem_runBranches_trans checkedEvalRunLoopMachine
          (mS + 1) mD [seekConfig mode cSeek0]
          (decodeConfig mode cDec0) dead
          hToDec (by simpa [dead] using hD')

      have hactive :
          ¬ Halted checkedEvalRunLoopMachine dead := by
        simp [dead, decodeConfig, Halted, checkedEvalRunLoopMachine]

      have hdead :
          checkedEvalRunLoopMachine.successors dead = [] := by
        simp [dead, decodeConfig, checkedEvalRunLoopMachine,
          needExprCompositeMachine, NTM.successors]

      refine ⟨mS + 1 + mD, ?_, dead, ?_, hactive, hdead⟩
      · dsimp [d, nSeek] at hmS hmD ⊢
        omega
      · dsimp [cSeek0, t0, seekConfig] at hAll ⊢
        simpa using hAll


/-- A nonempty source shorter than one three-bit tag is fail-closed already at
the prepared verifier level. -/
theorem prepared_truncated_tag_fail_closed
    (witness source : BitString)
    (hne : source ≠ [])
    (hshort : source.length < 3) :
    ∃ total ≤ 2 * source.length + 11,
      checkedVerifierMachine.HaltsWithin total
        { state := checkedVerifierMachine.initial,
          tape := preparedTape witness source } ∧
      ¬ checkedVerifierMachine.AcceptsWithin total
        { state := checkedVerifierMachine.initial,
          tape := preparedTape witness source } := by
  cases source with
  | nil =>
      exact False.elim (hne rfl)
  | cons b bs =>
      obtain ⟨m1, hm1, dead, hreach, hactive, hdead⟩ :=
        checked_truncated_tag_reaches_dead
          .cnf witness (b :: bs) [] 0 0 (by simpa using hshort)
      have hreach' :
          dead ∈ checkedEvalRunLoopMachine.runBranches m1
            [{ state := checkedEvalRunLoopMachine.initial,
               tape := evalCursorStackEndTape witness 0 (b :: bs) [] 0 }] := by
        simpa [checkedEvalRunLoopMachine] using hreach
      obtain ⟨total, htotal, hhalt, hnot⟩ :=
        prepared_nonempty_dead_fail_closed
          witness b bs m1 dead hreach' hactive hdead
      refine ⟨total, ?_, hhalt, hnot⟩
      simp at hm1 htotal ⊢
      omega

#print axioms MCore.Real.P01RawMalformedTag.tagDecode_short_state_reject
#print axioms MCore.Real.P01RawMalformedTag.checked_truncated_tag_reaches_dead

end P01RawMalformedTag
end Real
end MCore
