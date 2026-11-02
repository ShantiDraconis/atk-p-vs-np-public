import MCore.Real.P01CheckedEvalRunHaveValue

namespace MCore
namespace Real
namespace P01CheckedEvalRunNeedTags

open CanonicalFinalProof
open P01NTMRunLaws
open P01EncodedStackEvaluator
open P01EncodedFrameTape
open P01EvalCursorMachine
open P01EvalCursorRoundTrip
open P01EvalFramePushMachine
open P01EvalCursorFramePush
open P01NeedExprCompositeNTM
open P01NeedExprTagDecode
open P01CheckedEvalRunLoopNTM
open P01CheckedEvalRunPhaseLift
open P01CheckedEvalRunTagPrefix
open P01CNFMode

abbrev CheckedConfig :=
  Configuration CheckedEvalRunState (Option Bool)

def checkedPushTagFuel
    (source frameStack : BitString) : Nat :=
  checkedTagPrefixFuel source frameStack +
    (source.drop 3).length + frameStack.length + 2 +
    1 + 3 + 1

private theorem one_step_of_successor
    (a b : CheckedConfig)
    (ha : ¬ Halted checkedEvalRunLoopMachine a)
    (hs : b ∈ checkedEvalRunLoopMachine.successors a) :
    b ∈ checkedEvalRunLoopMachine.runBranches 1 [a] := by
  have h :=
    mem_runBranches_succ_of_successor
      checkedEvalRunLoopMachine 0 [a] a b
      (by simp [NTM.runBranches]) ha hs
  simpa using h

/-- Generic checked route for the three continuation-producing tags.
The common prefix performs seek/decode/admission and lands directly in the
mode-aware retPush state; only physical return/push remain. -/
theorem pushTag_checked_reaches_need
    (mode : SyntaxMode)
    (witness rest frameStack : BitString)
    (consumed padding : Nat)
    (b0 b1 b2 : Bool)
    (tag : NeedExprTag)
    (frame : EvalFrame)
    (hTag : decodeTagBits b0 b1 b2 = tag)
    (hAllowed : tagAllowed mode tag = true)
    (hPost :
      postTagState mode tag =
        .need (childMode mode tag) (.retPush frame .scanUnread)) :
    ∃ m ≤
        checkedTagPrefixFuel (b0 :: b1 :: b2 :: rest) frameStack +
          (rest.length + frameStack.length + 2) + 1 + 3 + 1,
      ({ state := .need (childMode mode tag)
           needExprCompositeMachine.initial,
         tape :=
           evalCursorStackEndTape witness (consumed + 3)
             rest (encodeEvalFrame frame ++ frameStack)
             (((padding - 1) - 1) - 1) } : CheckedConfig) ∈
        checkedEvalRunLoopMachine.runBranches m
          [{ state := .need mode needExprCompositeMachine.initial,
             tape :=
               evalCursorStackEndTape witness consumed
                 (b0 :: b1 :: b2 :: rest) frameStack padding }] := by
  let nextMode := childMode mode tag
  let tAfter :=
    evalCursorReadTape witness (consumed + 3)
      rest frameStack padding
  let tStack :=
    evalCursorStackEndTape witness (consumed + 3)
      rest frameStack padding
  let tPushed :=
    evalCursorStackEndTape witness (consumed + 3)
      rest (encodeEvalFrame frame ++ frameStack)
      (((padding - 1) - 1) - 1)
  let nRet := rest.length + frameStack.length + 2

  let cRet0 : Configuration CursorReturnState (Option Bool) :=
    { state := .scanUnread, tape := tAfter }
  let cRetH : Configuration CursorReturnState (Option Bool) :=
    { state := .halt, tape := tStack }
  let cPush0 : Configuration FramePushState (Option Bool) :=
    framePushConfig frame tStack
  let cPushH : Configuration FramePushState (Option Bool) :=
    { state := .halt, tape := tPushed }

  obtain ⟨m0, hm0, h0⟩ :=
    checked_tag_prefix_reaches
      mode witness rest frameStack consumed padding
      b0 b1 b2 (by simpa [hTag] using hAllowed)

  have hPrefix :
      retPushConfig nextMode frame cRet0 ∈
        checkedEvalRunLoopMachine.runBranches m0
          [{ state := .need mode needExprCompositeMachine.initial,
             tape :=
               evalCursorStackEndTape witness consumed
                 (b0 :: b1 :: b2 :: rest) frameStack padding }] := by
    simpa [retPushConfig, nextMode, tAfter, hTag, hPost] using h0

  have hRetExact :
      cursorReturnMachine.run nRet cRet0 = cRetH := by
    dsimp [nRet, cRet0, cRetH, tAfter, tStack]
    exact cursorReturn_preserve_run
      witness (consumed + 3) rest frameStack padding

  obtain ⟨mR, hmR, hR⟩ :=
    retPush_run_reachable nextMode frame nRet cRet0
  have hR' :
      retPushConfig nextMode frame cRetH ∈
        checkedEvalRunLoopMachine.runBranches mR
          [retPushConfig nextMode frame cRet0] := by
    rw [hRetExact] at hR
    exact hR

  have hThroughRet :=
    mem_runBranches_trans checkedEvalRunLoopMachine
      m0 mR
      [{ state := .need mode needExprCompositeMachine.initial,
         tape :=
           evalCursorStackEndTape witness consumed
             (b0 :: b1 :: b2 :: rest) frameStack padding }]
      (retPushConfig nextMode frame cRet0)
      (retPushConfig nextMode frame cRetH)
      hPrefix hR'

  have hRetHandSucc :
      pushConfig nextMode frame cPush0 ∈
        checkedEvalRunLoopMachine.successors
          (retPushConfig nextMode frame cRetH) := by
    dsimp [retPushConfig, pushConfig, cRetH, cPush0]
    simp [checkedEvalRunLoopMachine, needExprCompositeMachine,
      needCheckedEmbed, framePushConfig,
      NTM.successors, NTM.stepBranch, Tape.write, Tape.move]

  have hRetHand :
      pushConfig nextMode frame cPush0 ∈
        checkedEvalRunLoopMachine.runBranches 1
          [retPushConfig nextMode frame cRetH] :=
    one_step_of_successor
      (retPushConfig nextMode frame cRetH)
      (pushConfig nextMode frame cPush0)
      (retPushConfig_not_halted nextMode frame cRetH)
      hRetHandSucc

  have hToPush :=
    mem_runBranches_trans checkedEvalRunLoopMachine
      (m0 + mR) 1
      [{ state := .need mode needExprCompositeMachine.initial,
         tape :=
           evalCursorStackEndTape witness consumed
             (b0 :: b1 :: b2 :: rest) frameStack padding }]
      (retPushConfig nextMode frame cRetH)
      (pushConfig nextMode frame cPush0)
      hThroughRet hRetHand

  have hPushExact :
      framePushMachine.run 3 cPush0 = cPushH := by
    dsimp [cPush0, cPushH, tStack, tPushed]
    exact framePush_run_three_cursor_exact
      witness rest frameStack (consumed + 3) padding frame

  obtain ⟨mP, hmP, hP⟩ :=
    push_run_reachable nextMode frame 3 cPush0
  have hP' :
      pushConfig nextMode frame cPushH ∈
        checkedEvalRunLoopMachine.runBranches mP
          [pushConfig nextMode frame cPush0] := by
    rw [hPushExact] at hP
    exact hP

  have hThroughPush :=
    mem_runBranches_trans checkedEvalRunLoopMachine
      ((m0 + mR) + 1) mP
      [{ state := .need mode needExprCompositeMachine.initial,
         tape :=
           evalCursorStackEndTape witness consumed
             (b0 :: b1 :: b2 :: rest) frameStack padding }]
      (pushConfig nextMode frame cPush0)
      (pushConfig nextMode frame cPushH)
      hToPush hP'

  let cNeed : CheckedConfig :=
    { state := .need nextMode needExprCompositeMachine.initial,
      tape := tPushed }

  have hFinalSucc :
      cNeed ∈ checkedEvalRunLoopMachine.successors
        (pushConfig nextMode frame cPushH) := by
    dsimp [cNeed, pushConfig, cPushH]
    simp [checkedEvalRunLoopMachine, needExprCompositeMachine,
      needCheckedEmbed, NTM.successors, NTM.stepBranch,
      Tape.write, Tape.move]

  have hFinal :
      cNeed ∈ checkedEvalRunLoopMachine.runBranches 1
        [pushConfig nextMode frame cPushH] :=
    one_step_of_successor
      (pushConfig nextMode frame cPushH) cNeed
      (pushConfig_not_halted nextMode frame cPushH)
      hFinalSucc

  have hAll :=
    mem_runBranches_trans checkedEvalRunLoopMachine
      (((m0 + mR) + 1) + mP) 1
      [{ state := .need mode needExprCompositeMachine.initial,
         tape :=
           evalCursorStackEndTape witness consumed
             (b0 :: b1 :: b2 :: rest) frameStack padding }]
      (pushConfig nextMode frame cPushH) cNeed
      hThroughPush hFinal

  refine ⟨(((m0 + mR) + 1) + mP) + 1, ?_, ?_⟩
  · omega
  · dsimp [cNeed, nextMode, tPushed] at hAll ⊢
    simpa using hAll

theorem neg_checked_reaches_need
    (mode : SyntaxMode)
    (witness rest frameStack : BitString)
    (consumed padding : Nat)
    (hAllowed : tagAllowed mode .neg = true) :
    ∃ m,
      ({ state := .need .mustInput needExprCompositeMachine.initial,
         tape :=
           evalCursorStackEndTape witness (consumed + 3)
             rest (encodeEvalFrame .neg ++ frameStack)
             (((padding - 1) - 1) - 1) } : CheckedConfig) ∈
        checkedEvalRunLoopMachine.runBranches m
          [{ state := .need mode needExprCompositeMachine.initial,
             tape :=
               evalCursorStackEndTape witness consumed
                 (false :: true :: true :: rest) frameStack padding }] := by
  obtain ⟨m, hm, h⟩ :=
    pushTag_checked_reaches_need
      mode witness rest frameStack consumed padding
      false true true .neg .neg rfl hAllowed (by
        simp [postTagState, childMode])
  exact ⟨m, by simpa [childMode] using h⟩

theorem and_checked_reaches_need
    (mode : SyntaxMode)
    (witness rest frameStack : BitString)
    (consumed padding : Nat)
    (hAllowed : tagAllowed mode .and = true) :
    ∃ m,
      ({ state := .need (childMode mode .and)
           needExprCompositeMachine.initial,
         tape :=
           evalCursorStackEndTape witness (consumed + 3)
             rest (encodeEvalFrame .andLeft ++ frameStack)
             (((padding - 1) - 1) - 1) } : CheckedConfig) ∈
        checkedEvalRunLoopMachine.runBranches m
          [{ state := .need mode needExprCompositeMachine.initial,
             tape :=
               evalCursorStackEndTape witness consumed
                 (true :: false :: false :: rest) frameStack padding }] := by
  obtain ⟨m, hm, h⟩ :=
    pushTag_checked_reaches_need
      mode witness rest frameStack consumed padding
      true false false .and .andLeft rfl hAllowed (by
        simp [postTagState, childMode])
  exact ⟨m, h⟩

theorem or_checked_reaches_need
    (mode : SyntaxMode)
    (witness rest frameStack : BitString)
    (consumed padding : Nat)
    (hAllowed : tagAllowed mode .or = true) :
    ∃ m,
      ({ state := .need .clause
           needExprCompositeMachine.initial,
         tape :=
           evalCursorStackEndTape witness (consumed + 3)
             rest (encodeEvalFrame .orLeft ++ frameStack)
             (((padding - 1) - 1) - 1) } : CheckedConfig) ∈
        checkedEvalRunLoopMachine.runBranches m
          [{ state := .need mode needExprCompositeMachine.initial,
             tape :=
               evalCursorStackEndTape witness consumed
                 (true :: false :: true :: rest) frameStack padding }] := by
  obtain ⟨m, hm, h⟩ :=
    pushTag_checked_reaches_need
      mode witness rest frameStack consumed padding
      true false true .or .orLeft rfl hAllowed (by
        simp [postTagState, childMode])
  exact ⟨m, by simpa [childMode] using h⟩

#print axioms MCore.Real.P01CheckedEvalRunNeedTags.pushTag_checked_reaches_need
#print axioms MCore.Real.P01CheckedEvalRunNeedTags.neg_checked_reaches_need
#print axioms MCore.Real.P01CheckedEvalRunNeedTags.and_checked_reaches_need
#print axioms MCore.Real.P01CheckedEvalRunNeedTags.or_checked_reaches_need

end P01CheckedEvalRunNeedTags
end Real
end MCore
