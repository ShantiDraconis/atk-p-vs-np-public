import MCore.Real.P01EvalRunLoopRun
import MCore.Real.P01EvalCursorFramePush

namespace MCore
namespace Real
namespace P01EvalRunLoopPushRun

open CanonicalFinalProof
open P01NTMRunLaws
open P01EncodedStackEvaluator
open P01EncodedFrameTape
open P01EvalCursorMachine
open P01EvalCursorRoundTrip
open P01NeedExprTagDecode
open P01NeedExprCompositeNTM
open P01NeedExprCompositeRun
open P01EvalFramePushMachine
open P01EvalCursorFramePush
open P01EvalRunLoopNTM
open P01EvalRunLoopRun

def retPushLoopConfig
    (frame : EvalFrame)
    (c : Configuration CursorReturnState (Option Bool)) : LoopConfig :=
  { state := .need (.retPush frame c.state), tape := c.tape }

def pushLoopConfig
    (frame : EvalFrame)
    (c : Configuration FramePushState (Option Bool)) : LoopConfig :=
  { state := .need (.push frame c.state), tape := c.tape }

@[simp] theorem retPushLoop_not_halted
    (frame : EvalFrame)
    (c : Configuration CursorReturnState (Option Bool)) :
    ¬ Halted evalRunLoopMachine (retPushLoopConfig frame c) := by
  simp [Halted, retPushLoopConfig, evalRunLoopMachine]

@[simp] theorem pushLoop_not_halted
    (frame : EvalFrame)
    (c : Configuration FramePushState (Option Bool)) :
    ¬ Halted evalRunLoopMachine (pushLoopConfig frame c) := by
  simp [Halted, pushLoopConfig, evalRunLoopMachine]

theorem retPushLoop_successors_active
    (frame : EvalFrame)
    (c : Configuration CursorReturnState (Option Bool))
    (h : cursorReturnMachine.halting c.state = false) :
    evalRunLoopMachine.successors (retPushLoopConfig frame c) =
      [retPushLoopConfig frame (cursorReturnMachine.step c)] := by
  rcases c with ⟨q, tape⟩
  unfold NTM.successors
  simp only [retPushLoopConfig]
  cases q <;>
    simp [evalRunLoopMachine, needExprCompositeMachine,
      needLoopEmbed, cursorReturnMachine, NTM.stepBranch, TM.step,
      Tape.write, Tape.move] at h ⊢

theorem pushLoop_successors_active
    (frame : EvalFrame)
    (c : Configuration FramePushState (Option Bool))
    (h : framePushMachine.halting c.state = false) :
    evalRunLoopMachine.successors (pushLoopConfig frame c) =
      [pushLoopConfig frame (framePushMachine.step c)] := by
  rcases c with ⟨q, tape⟩
  unfold NTM.successors
  simp only [pushLoopConfig]
  cases q <;>
    simp [evalRunLoopMachine, needExprCompositeMachine,
      needLoopEmbed, framePushMachine, NTM.stepBranch, TM.step,
      Tape.write, Tape.move] at h ⊢

private theorem tm_phase_run_reachable
    {S : Type}
    (M : TM S (Option Bool))
    (embed : Configuration S (Option Bool) → LoopConfig)
    (embed_not_halted :
      ∀ c, ¬ Halted evalRunLoopMachine (embed c))
    (step_successors :
      ∀ c, M.halting c.state = false →
        evalRunLoopMachine.successors (embed c) =
          [embed (M.step c)]) :
    ∀ (n : Nat) (c : Configuration S (Option Bool)),
      ∃ m ≤ n,
        embed (M.run n c) ∈
          evalRunLoopMachine.runBranches m [embed c] := by
  intro n
  induction n with
  | zero =>
      intro c
      refine ⟨0, by omega, ?_⟩
      change embed c ∈ [embed c]
      simp
  | succ n ih =>
      intro c
      cases hhalt : M.halting c.state with
      | true =>
          have hr := MachineRunLemmas.run_halted M c hhalt (n + 1)
          refine ⟨0, by omega, ?_⟩
          rw [hr]
          simp [NTM.runBranches]
      | false =>
          obtain ⟨m, hm, hmem⟩ := ih (M.step c)
          have hsucc :
              embed (M.step c) ∈
                evalRunLoopMachine.successors (embed c) := by
            rw [step_successors c hhalt]
            simp
          have hone :
              embed (M.step c) ∈
                evalRunLoopMachine.runBranches 1 [embed c] := by
            have h :=
              mem_runBranches_succ_of_successor
                evalRunLoopMachine 0 [embed c]
                (embed c) (embed (M.step c))
                (by simp [NTM.runBranches])
                (embed_not_halted c) hsucc
            simpa using h
          have htrans :=
            mem_runBranches_trans evalRunLoopMachine
              1 m [embed c]
              (embed (M.step c))
              (embed (M.run n (M.step c)))
              hone hmem
          refine ⟨1 + m, by omega, ?_⟩
          simpa [TM.run, hhalt] using htrans

theorem retPushLoop_run_reachable
    (frame : EvalFrame) (n : Nat)
    (c : Configuration CursorReturnState (Option Bool)) :
    ∃ m ≤ n,
      retPushLoopConfig frame (cursorReturnMachine.run n c) ∈
        evalRunLoopMachine.runBranches m [retPushLoopConfig frame c] :=
  tm_phase_run_reachable
    cursorReturnMachine (retPushLoopConfig frame)
    (retPushLoop_not_halted frame)
    (retPushLoop_successors_active frame) n c

theorem pushLoop_run_reachable
    (frame : EvalFrame) (n : Nat)
    (c : Configuration FramePushState (Option Bool)) :
    ∃ m ≤ n,
      pushLoopConfig frame (framePushMachine.run n c) ∈
        evalRunLoopMachine.runBranches m [pushLoopConfig frame c] :=
  tm_phase_run_reachable
    framePushMachine (pushLoopConfig frame)
    (pushLoop_not_halted frame)
    (pushLoop_successors_active frame) n c

private theorem one_step_of_successor
    (a b : LoopConfig)
    (ha : ¬ Halted evalRunLoopMachine a)
    (hs : b ∈ evalRunLoopMachine.successors a) :
    b ∈ evalRunLoopMachine.runBranches 1 [a] := by
  have h :=
    mem_runBranches_succ_of_successor
      evalRunLoopMachine 0 [a] a b
      (by simp [NTM.runBranches]) ha hs
  simpa using h

/-- Complete structural-tag step inside the physical evaluator loop. -/
theorem pushTag_loop_reaches_need
    (witness rest frameStack : BitString)
    (consumed padding : Nat)
    (b0 b1 b2 : Bool)
    (tag : NeedExprTag)
    (frame : EvalFrame)
    (hdecode : decodeTagBits b0 b1 b2 = tag)
    (hhandoff :
      ∀ tape : Tape (Option Bool),
        needExprCompositeMachine.successors
          { state := .decode (.halt tag), tape := tape } =
          [{ state := .retPush frame .scanUnread, tape := tape }]) :
    ∃ m ≤ pushTagCompositeFuel frameStack rest,
      ({ state := .need needExprCompositeMachine.initial,
         tape :=
           evalCursorStackEndTape witness (consumed + 3) rest
             (encodeEvalFrame frame ++ frameStack)
             (((padding - 1) - 1) - 1) } : LoopConfig) ∈
        evalRunLoopMachine.runBranches m
          [{ state := .need needExprCompositeMachine.initial,
             tape :=
               evalCursorStackEndTape witness consumed
                 (b0 :: b1 :: b2 :: rest)
                 frameStack padding }] := by
  let nSeek := frameStack.length + (rest.length + 3) + 3
  let nRet := rest.length + frameStack.length + 2
  let t0 :=
    evalCursorStackEndTape witness consumed
      (b0 :: b1 :: b2 :: rest) frameStack padding
  let tRead :=
    evalCursorReadTape witness consumed
      (b0 :: b1 :: b2 :: rest) frameStack padding
  let tAfterTag :=
    evalCursorReadTape witness (consumed + 3)
      rest frameStack padding
  let tDone :=
    evalCursorStackEndTape witness (consumed + 3)
      rest frameStack padding
  let tPushed :=
    evalCursorStackEndTape witness (consumed + 3) rest
      (encodeEvalFrame frame ++ frameStack)
      (((padding - 1) - 1) - 1)

  let cSeek0 : Configuration CursorSeekState (Option Bool) :=
    { state := cursorSeekMachine.initial, tape := t0 }
  let cSeekH : Configuration CursorSeekState (Option Bool) :=
    { state := .halt, tape := tRead }
  let cDec0 : Configuration TagDecodeState (Option Bool) :=
    { state := tagDecodeMachine.initial, tape := tRead }
  let cDecH : Configuration TagDecodeState (Option Bool) :=
    { state := .halt tag, tape := tAfterTag }
  let cRet0 : Configuration CursorReturnState (Option Bool) :=
    { state := .scanUnread, tape := tAfterTag }
  let cRetH : Configuration CursorReturnState (Option Bool) :=
    { state := .halt, tape := tDone }
  let cPush0 : Configuration FramePushState (Option Bool) :=
    { state := .start frame, tape := tDone }
  let cPushH : Configuration FramePushState (Option Bool) :=
    { state := .halt, tape := tPushed }

  have hSeekExact :
      cursorSeekMachine.run nSeek cSeek0 = cSeekH := by
    dsimp [nSeek, cSeek0, cSeekH, t0, tRead]
    simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
      cursorSeek_run witness consumed
        (b0 :: b1 :: b2 :: rest) frameStack padding
  obtain ⟨mS, hmS, hS⟩ := seekLoop_run_reachable nSeek cSeek0
  have hS' :
      seekLoopConfig cSeekH ∈
        evalRunLoopMachine.runBranches mS [seekLoopConfig cSeek0] := by
    rw [hSeekExact] at hS
    exact hS

  have hSeekHandSucc :
      decodeLoopConfig cDec0 ∈
        evalRunLoopMachine.successors (seekLoopConfig cSeekH) := by
    dsimp [seekLoopConfig, decodeLoopConfig, cSeekH, cDec0]
    simp [evalRunLoopMachine, needExprCompositeMachine, needLoopEmbed,
      NTM.successors, NTM.stepBranch, Tape.write, Tape.move]
  have hSeekHand :
      decodeLoopConfig cDec0 ∈
        evalRunLoopMachine.runBranches 1 [seekLoopConfig cSeekH] :=
    one_step_of_successor
      (seekLoopConfig cSeekH) (decodeLoopConfig cDec0)
      (seekLoop_not_halted cSeekH) hSeekHandSucc
  have hToDec :=
    mem_runBranches_trans evalRunLoopMachine
      mS 1 [seekLoopConfig cSeek0]
      (seekLoopConfig cSeekH) (decodeLoopConfig cDec0)
      hS' hSeekHand

  have hDecExact :
      tagDecodeMachine.run 3 cDec0 = cDecH := by
    dsimp [cDec0, cDecH, tRead, tAfterTag]
    simpa [hdecode] using
      tagDecode_run_three witness rest frameStack consumed padding
        b0 b1 b2
  obtain ⟨mD, hmD, hD⟩ := decodeLoop_run_reachable 3 cDec0
  have hD' :
      decodeLoopConfig cDecH ∈
        evalRunLoopMachine.runBranches mD [decodeLoopConfig cDec0] := by
    rw [hDecExact] at hD
    exact hD
  have hThroughDec :=
    mem_runBranches_trans evalRunLoopMachine
      (mS + 1) mD [seekLoopConfig cSeek0]
      (decodeLoopConfig cDec0) (decodeLoopConfig cDecH)
      hToDec hD'

  have hDecHandSucc :
      retPushLoopConfig frame cRet0 ∈
        evalRunLoopMachine.successors (decodeLoopConfig cDecH) := by
    change
      ({ state := .need (.retPush frame .scanUnread), tape := tAfterTag } :
        LoopConfig) ∈
      evalRunLoopMachine.successors
        ({ state := .need (.decode (.halt tag)), tape := tAfterTag } :
          LoopConfig)
    have hsrc := hhandoff tAfterTag
    rw [show evalRunLoopMachine.successors
        ({ state := .need (.decode (.halt tag)), tape := tAfterTag } :
          LoopConfig) =
      (needExprCompositeMachine.successors
        ({ state := .decode (.halt tag), tape := tAfterTag } :
          Configuration NeedExprCompositeState (Option Bool))).map
        (fun d => ({ state := needLoopEmbed d.state, tape := d.tape } :
          LoopConfig)) by
        simp [evalRunLoopMachine, needExprCompositeMachine,
          NTM.successors, NTM.stepBranch, needLoopEmbed,
          Tape.write, Tape.move]]
    rw [hsrc]
    simp [needLoopEmbed]
  have hDecHand :
      retPushLoopConfig frame cRet0 ∈
        evalRunLoopMachine.runBranches 1 [decodeLoopConfig cDecH] :=
    one_step_of_successor
      (decodeLoopConfig cDecH) (retPushLoopConfig frame cRet0)
      (decodeLoop_not_halted cDecH) hDecHandSucc
  have hToRet :=
    mem_runBranches_trans evalRunLoopMachine
      ((mS + 1) + mD) 1 [seekLoopConfig cSeek0]
      (decodeLoopConfig cDecH) (retPushLoopConfig frame cRet0)
      hThroughDec hDecHand

  have hRetExact :
      cursorReturnMachine.run nRet cRet0 = cRetH := by
    dsimp [nRet, cRet0, cRetH, tAfterTag, tDone]
    exact cursorReturn_preserve_run
      witness (consumed + 3) rest frameStack padding
  obtain ⟨mR, hmR, hR⟩ :=
    retPushLoop_run_reachable frame nRet cRet0
  have hR' :
      retPushLoopConfig frame cRetH ∈
        evalRunLoopMachine.runBranches mR
          [retPushLoopConfig frame cRet0] := by
    rw [hRetExact] at hR
    exact hR
  have hThroughRet :=
    mem_runBranches_trans evalRunLoopMachine
      (((mS + 1) + mD) + 1) mR [seekLoopConfig cSeek0]
      (retPushLoopConfig frame cRet0)
      (retPushLoopConfig frame cRetH)
      hToRet hR'

  have hRetHandSucc :
      pushLoopConfig frame cPush0 ∈
        evalRunLoopMachine.successors
          (retPushLoopConfig frame cRetH) := by
    change
      ({ state := .need (.push frame (.start frame)), tape := tDone } :
        LoopConfig) ∈
      evalRunLoopMachine.successors
        ({ state := .need (.retPush frame .halt), tape := tDone } :
          LoopConfig)
    rw [show evalRunLoopMachine.successors
        ({ state := .need (.retPush frame .halt), tape := tDone } :
          LoopConfig) =
      (needExprCompositeMachine.successors
        ({ state := .retPush frame .halt, tape := tDone } :
          Configuration NeedExprCompositeState (Option Bool))).map
        (fun d => ({ state := needLoopEmbed d.state, tape := d.tape } :
          LoopConfig)) by
        simp [evalRunLoopMachine, needExprCompositeMachine,
          NTM.successors, NTM.stepBranch, needLoopEmbed,
          Tape.write, Tape.move]]
    rw [retPush_handoff_successors frame tDone]
    simp [needLoopEmbed]
  have hRetHand :
      pushLoopConfig frame cPush0 ∈
        evalRunLoopMachine.runBranches 1
          [retPushLoopConfig frame cRetH] :=
    one_step_of_successor
      (retPushLoopConfig frame cRetH) (pushLoopConfig frame cPush0)
      (retPushLoop_not_halted frame cRetH) hRetHandSucc
  have hToPush :=
    mem_runBranches_trans evalRunLoopMachine
      ((((mS + 1) + mD) + 1) + mR) 1 [seekLoopConfig cSeek0]
      (retPushLoopConfig frame cRetH) (pushLoopConfig frame cPush0)
      hThroughRet hRetHand

  have hPushExact :
      framePushMachine.run 3 cPush0 = cPushH := by
    dsimp [cPush0, cPushH, tDone, tPushed]
    exact framePush_run_three_cursor_exact
      witness rest frameStack (consumed + 3) padding frame
  obtain ⟨mP, hmP, hP⟩ :=
    pushLoop_run_reachable frame 3 cPush0
  have hP' :
      pushLoopConfig frame cPushH ∈
        evalRunLoopMachine.runBranches mP [pushLoopConfig frame cPush0] := by
    rw [hPushExact] at hP
    exact hP
  have hThroughPush :=
    mem_runBranches_trans evalRunLoopMachine
      (((((mS + 1) + mD) + 1) + mR) + 1) mP
      [seekLoopConfig cSeek0]
      (pushLoopConfig frame cPush0) (pushLoopConfig frame cPushH)
      hToPush hP'

  let cNeed : LoopConfig :=
    { state := .need needExprCompositeMachine.initial, tape := tPushed }
  have hFinalSucc :
      cNeed ∈
        evalRunLoopMachine.successors (pushLoopConfig frame cPushH) := by
    change
      ({ state := .need needExprCompositeMachine.initial, tape := tPushed } :
        LoopConfig) ∈
      evalRunLoopMachine.successors
        ({ state := .need (.push frame .halt), tape := tPushed } :
          LoopConfig)
    rw [show evalRunLoopMachine.successors
        ({ state := .need (.push frame .halt), tape := tPushed } :
          LoopConfig) =
      (needExprCompositeMachine.successors
        ({ state := .push frame .halt, tape := tPushed } :
          Configuration NeedExprCompositeState (Option Bool))).map
        (fun d => ({ state := needLoopEmbed d.state, tape := d.tape } :
          LoopConfig)) by
        simp [evalRunLoopMachine, needExprCompositeMachine,
          NTM.successors, NTM.stepBranch, needLoopEmbed,
          Tape.write, Tape.move]]
    rw [push_handoff_successors frame tPushed]
    simp [needLoopEmbed]
  have hFinal :
      cNeed ∈
        evalRunLoopMachine.runBranches 1 [pushLoopConfig frame cPushH] :=
    one_step_of_successor
      (pushLoopConfig frame cPushH) cNeed
      (pushLoop_not_halted frame cPushH) hFinalSucc

  have hAll :=
    mem_runBranches_trans evalRunLoopMachine
      ((((((mS + 1) + mD) + 1) + mR) + 1) + mP) 1
      [seekLoopConfig cSeek0]
      (pushLoopConfig frame cPushH) cNeed
      hThroughPush hFinal

  refine ⟨((((((mS + 1) + mD) + 1) + mR) + 1) + mP) + 1, ?_, ?_⟩
  · dsimp [pushTagCompositeFuel, nSeek, nRet] at *
    omega
  · dsimp [cNeed, tPushed, cSeek0, t0] at hAll ⊢
    simpa [seekLoopConfig, needExprCompositeMachine] using hAll

theorem neg_loop_reaches_need
    (witness rest frameStack : BitString)
    (consumed padding : Nat) :
    ∃ m ≤ pushTagCompositeFuel frameStack rest,
      ({ state := .need needExprCompositeMachine.initial,
         tape :=
           evalCursorStackEndTape witness (consumed + 3) rest
             (encodeEvalFrame .neg ++ frameStack)
             (((padding - 1) - 1) - 1) } : LoopConfig) ∈
        evalRunLoopMachine.runBranches m
          [{ state := .need needExprCompositeMachine.initial,
             tape := evalCursorStackEndTape witness consumed
               (false :: true :: true :: rest) frameStack padding }] := by
  apply pushTag_loop_reaches_need witness rest frameStack consumed padding
    false true true .neg .neg
  · rfl
  · exact neg_handoff_successors

theorem and_loop_reaches_need
    (witness rest frameStack : BitString)
    (consumed padding : Nat) :
    ∃ m ≤ pushTagCompositeFuel frameStack rest,
      ({ state := .need needExprCompositeMachine.initial,
         tape :=
           evalCursorStackEndTape witness (consumed + 3) rest
             (encodeEvalFrame .andLeft ++ frameStack)
             (((padding - 1) - 1) - 1) } : LoopConfig) ∈
        evalRunLoopMachine.runBranches m
          [{ state := .need needExprCompositeMachine.initial,
             tape := evalCursorStackEndTape witness consumed
               (true :: false :: false :: rest) frameStack padding }] := by
  apply pushTag_loop_reaches_need witness rest frameStack consumed padding
    true false false .and .andLeft
  · rfl
  · exact and_handoff_successors

theorem or_loop_reaches_need
    (witness rest frameStack : BitString)
    (consumed padding : Nat) :
    ∃ m ≤ pushTagCompositeFuel frameStack rest,
      ({ state := .need needExprCompositeMachine.initial,
         tape :=
           evalCursorStackEndTape witness (consumed + 3) rest
             (encodeEvalFrame .orLeft ++ frameStack)
             (((padding - 1) - 1) - 1) } : LoopConfig) ∈
        evalRunLoopMachine.runBranches m
          [{ state := .need needExprCompositeMachine.initial,
             tape := evalCursorStackEndTape witness consumed
               (true :: false :: true :: rest) frameStack padding }] := by
  apply pushTag_loop_reaches_need witness rest frameStack consumed padding
    true false true .or .orLeft
  · rfl
  · exact or_handoff_successors

#print axioms MCore.Real.P01EvalRunLoopPushRun.pushTag_loop_reaches_need
#print axioms MCore.Real.P01EvalRunLoopPushRun.neg_loop_reaches_need
#print axioms MCore.Real.P01EvalRunLoopPushRun.and_loop_reaches_need
#print axioms MCore.Real.P01EvalRunLoopPushRun.or_loop_reaches_need

end P01EvalRunLoopPushRun
end Real
end MCore
