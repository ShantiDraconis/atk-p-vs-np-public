import MCore.Real.P01CheckedEvalRunPhaseLift

namespace MCore
namespace Real
namespace P01CheckedEvalRunTagPrefix

open CanonicalFinalProof
open P01NTMRunLaws
open P01CheckedEvalRunLoopNTM
open P01CheckedEvalRunPhaseLift
open P01NeedExprCompositeNTM
open P01NeedExprTagDecode
open P01EvalCursorMachine
open P01CNFMode

abbrev CheckedConfig :=
  Configuration CheckedEvalRunState (Option Bool)

/-- Checked control immediately after a physically decoded, admitted tag. -/
def postTagState
    (mode : SyntaxMode) (tag : NeedExprTag) :
    CheckedEvalRunState :=
  let nextMode := childMode mode tag
  match tag with
  | .input =>
      .need nextMode (.input P01InputNodeCompositeNTM.inputNodeCompositeMachine.initial)
  | .constFalse =>
      .need nextMode (.retValue false .scanUnread)
  | .constTrue =>
      .need nextMode (.retValue true .scanUnread)
  | .neg =>
      .need nextMode (.retPush .neg .scanUnread)
  | .and =>
      .need nextMode (.retPush .andLeft .scanUnread)
  | .or =>
      .need nextMode (.retPush .orLeft .scanUnread)
  | .invalid110 => .reject
  | .invalid111 => .reject

/-- Once the 3-bit decoder has halted on an admitted tag, the checked wrapper
performs exactly one deterministic handoff to the tag's physical continuation. -/
theorem allowed_decode_handoff
    (mode : SyntaxMode)
    (tag : NeedExprTag)
    (tape : Tape (Option Bool))
    (hallowed : tagAllowed mode tag = true) :
    checkedEvalRunLoopMachine.successors
      ({ state := .need mode (.decode (.halt tag)), tape := tape } :
        CheckedConfig) =
      [{ state := postTagState mode tag, tape := tape }] := by
  cases mode <;> cases tag <;>
    simp [checkedEvalRunLoopMachine, postTagState, childMode, tagAllowed,
      needExprCompositeMachine, needCheckedEmbed,
      NTM.successors, NTM.stepBranch, Tape.write, Tape.move] at hallowed ⊢

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

def checkedTagPrefixFuel
    (source frameStack : BitString) : Nat :=
  frameStack.length + source.length + 3 + 1 + 3 + 1

/-- Common physical prefix for every admitted evaluator tag.

Starting at the canonical stack-end layout, this theorem:
1. seeks to the first unread source bit,
2. physically erases/decodes three tag bits,
3. checks the finite CNF syntax mode,
4. hands off to the already-certified tag continuation.

No semantic circuit theorem is used here. -/
theorem checked_tag_prefix_reaches
    (mode : SyntaxMode)
    (witness rest frameStack : BitString)
    (consumed padding : Nat)
    (b0 b1 b2 : Bool)
    (hallowed :
      tagAllowed mode (decodeTagBits b0 b1 b2) = true) :
    ∃ m ≤ checkedTagPrefixFuel
          (b0 :: b1 :: b2 :: rest) frameStack,
      ({ state := postTagState mode (decodeTagBits b0 b1 b2),
         tape :=
           evalCursorReadTape witness (consumed + 3)
             rest frameStack padding } : CheckedConfig) ∈
        checkedEvalRunLoopMachine.runBranches m
          [{ state := .need mode needExprCompositeMachine.initial,
             tape :=
               evalCursorStackEndTape witness consumed
                 (b0 :: b1 :: b2 :: rest)
                 frameStack padding }] := by
  let source := b0 :: b1 :: b2 :: rest
  let nSeek := frameStack.length + source.length + 3
  let t0 :=
    evalCursorStackEndTape witness consumed source frameStack padding
  let tRead :=
    evalCursorReadTape witness consumed source frameStack padding
  let tAfter :=
    evalCursorReadTape witness (consumed + 3) rest frameStack padding

  let cSeek0 : Configuration CursorSeekState (Option Bool) :=
    { state := cursorSeekMachine.initial, tape := t0 }
  let cSeekH : Configuration CursorSeekState (Option Bool) :=
    { state := .halt, tape := tRead }
  let cDec0 : Configuration P01NeedExprTagDecode.TagDecodeState (Option Bool) :=
    { state := P01NeedExprTagDecode.tagDecodeMachine.initial, tape := tRead }
  let cDecH : Configuration P01NeedExprTagDecode.TagDecodeState (Option Bool) :=
    { state := .halt (decodeTagBits b0 b1 b2), tape := tAfter }

  have hSeekExact :
      cursorSeekMachine.run nSeek cSeek0 = cSeekH := by
    dsimp [nSeek, cSeek0, cSeekH, t0, tRead, source]
    exact cursorSeek_run witness consumed
      (b0 :: b1 :: b2 :: rest) frameStack padding

  obtain ⟨mS, hmS, hS⟩ :=
    seek_run_reachable mode nSeek cSeek0
  have hS' :
      seekConfig mode cSeekH ∈
        checkedEvalRunLoopMachine.runBranches mS [seekConfig mode cSeek0] := by
    rw [hSeekExact] at hS
    exact hS

  let cCheckedDec0 : CheckedConfig := decodeConfig mode cDec0
  have hSeekHandSucc :
      cCheckedDec0 ∈
        checkedEvalRunLoopMachine.successors (seekConfig mode cSeekH) := by
    dsimp [cCheckedDec0, seekConfig, decodeConfig, cSeekH, cDec0]
    simp [checkedEvalRunLoopMachine, needExprCompositeMachine,
      needCheckedEmbed, NTM.successors, NTM.stepBranch,
      Tape.write, Tape.move]
  have hSeekHand :
      cCheckedDec0 ∈
        checkedEvalRunLoopMachine.runBranches 1 [seekConfig mode cSeekH] :=
    one_step_of_successor
      (seekConfig mode cSeekH) cCheckedDec0
      (seekConfig_not_halted mode cSeekH) hSeekHandSucc

  have hToDec :=
    mem_runBranches_trans checkedEvalRunLoopMachine
      mS 1 [seekConfig mode cSeek0]
      (seekConfig mode cSeekH) cCheckedDec0
      hS' hSeekHand

  have hDecExact :
      P01NeedExprTagDecode.tagDecodeMachine.run 3 cDec0 = cDecH := by
    dsimp [cDec0, cDecH, tRead, tAfter, source]
    exact tagDecode_run_three witness rest frameStack
      consumed padding b0 b1 b2

  obtain ⟨mD, hmD, hD⟩ :=
    decode_run_reachable mode 3 cDec0
  have hD' :
      decodeConfig mode cDecH ∈
        checkedEvalRunLoopMachine.runBranches mD [cCheckedDec0] := by
    rw [hDecExact] at hD
    simpa [cCheckedDec0] using hD

  have hThroughDec :=
    mem_runBranches_trans checkedEvalRunLoopMachine
      (mS + 1) mD [seekConfig mode cSeek0]
      cCheckedDec0 (decodeConfig mode cDecH)
      hToDec hD'

  let cPost : CheckedConfig :=
    { state := postTagState mode (decodeTagBits b0 b1 b2),
      tape := tAfter }

  have hPostSucc :
      cPost ∈
        checkedEvalRunLoopMachine.successors (decodeConfig mode cDecH) := by
    dsimp [cPost, decodeConfig, cDecH]
    rw [allowed_decode_handoff mode
      (decodeTagBits b0 b1 b2) tAfter hallowed]
    simp
  have hPost :
      cPost ∈
        checkedEvalRunLoopMachine.runBranches 1 [decodeConfig mode cDecH] :=
    one_step_of_successor
      (decodeConfig mode cDecH) cPost
      (decodeConfig_not_halted mode cDecH) hPostSucc

  have hAll :=
    mem_runBranches_trans checkedEvalRunLoopMachine
      ((mS + 1) + mD) 1 [seekConfig mode cSeek0]
      (decodeConfig mode cDecH) cPost
      hThroughDec hPost

  refine ⟨((mS + 1) + mD) + 1, ?_, ?_⟩
  · dsimp [checkedTagPrefixFuel, nSeek, source] at *
    omega
  · dsimp [cPost, tAfter, cSeek0, t0, source] at hAll ⊢
    simpa [seekConfig] using hAll

/-- Common physical rejection prefix for a syntactically forbidden tag.

Starting from the canonical stack-end layout, the machine seeks to the unread
source, physically decodes the three tag bits, and then takes the checked
wrapper's certified one-step rejection branch. -/
theorem disallowed_tag_prefix_reaches_reject
    (mode : SyntaxMode)
    (witness rest frameStack : BitString)
    (consumed padding : Nat)
    (b0 b1 b2 : Bool)
    (hdisallowed :
      tagAllowed mode (decodeTagBits b0 b1 b2) = false) :
    ∃ m ≤ checkedTagPrefixFuel
          (b0 :: b1 :: b2 :: rest) frameStack,
      ({ state := .reject,
         tape :=
           evalCursorReadTape witness (consumed + 3)
             rest frameStack padding } : CheckedConfig) ∈
        checkedEvalRunLoopMachine.runBranches m
          [{ state := .need mode needExprCompositeMachine.initial,
             tape :=
               evalCursorStackEndTape witness consumed
                 (b0 :: b1 :: b2 :: rest)
                 frameStack padding }] := by
  let source := b0 :: b1 :: b2 :: rest
  let nSeek := frameStack.length + source.length + 3
  let t0 :=
    evalCursorStackEndTape witness consumed source frameStack padding
  let tRead :=
    evalCursorReadTape witness consumed source frameStack padding
  let tAfter :=
    evalCursorReadTape witness (consumed + 3) rest frameStack padding

  let cSeek0 : Configuration CursorSeekState (Option Bool) :=
    { state := cursorSeekMachine.initial, tape := t0 }
  let cSeekH : Configuration CursorSeekState (Option Bool) :=
    { state := .halt, tape := tRead }
  let cDec0 : Configuration P01NeedExprTagDecode.TagDecodeState (Option Bool) :=
    { state := P01NeedExprTagDecode.tagDecodeMachine.initial, tape := tRead }
  let cDecH : Configuration P01NeedExprTagDecode.TagDecodeState (Option Bool) :=
    { state := .halt (decodeTagBits b0 b1 b2), tape := tAfter }

  have hSeekExact :
      cursorSeekMachine.run nSeek cSeek0 = cSeekH := by
    dsimp [nSeek, cSeek0, cSeekH, t0, tRead, source]
    exact cursorSeek_run witness consumed
      (b0 :: b1 :: b2 :: rest) frameStack padding

  obtain ⟨mS, hmS, hS⟩ :=
    seek_run_reachable mode nSeek cSeek0
  have hS' :
      seekConfig mode cSeekH ∈
        checkedEvalRunLoopMachine.runBranches mS [seekConfig mode cSeek0] := by
    rw [hSeekExact] at hS
    exact hS

  let cCheckedDec0 : CheckedConfig := decodeConfig mode cDec0
  have hSeekHandSucc :
      cCheckedDec0 ∈
        checkedEvalRunLoopMachine.successors (seekConfig mode cSeekH) := by
    dsimp [cCheckedDec0, seekConfig, decodeConfig, cSeekH, cDec0]
    simp [checkedEvalRunLoopMachine, needExprCompositeMachine,
      needCheckedEmbed, NTM.successors, NTM.stepBranch,
      Tape.write, Tape.move]
  have hSeekHand :
      cCheckedDec0 ∈
        checkedEvalRunLoopMachine.runBranches 1 [seekConfig mode cSeekH] :=
    one_step_of_successor
      (seekConfig mode cSeekH) cCheckedDec0
      (seekConfig_not_halted mode cSeekH) hSeekHandSucc

  have hToDec :=
    mem_runBranches_trans checkedEvalRunLoopMachine
      mS 1 [seekConfig mode cSeek0]
      (seekConfig mode cSeekH) cCheckedDec0
      hS' hSeekHand

  have hDecExact :
      P01NeedExprTagDecode.tagDecodeMachine.run 3 cDec0 = cDecH := by
    dsimp [cDec0, cDecH, tRead, tAfter, source]
    exact tagDecode_run_three witness rest frameStack
      consumed padding b0 b1 b2

  obtain ⟨mD, hmD, hD⟩ :=
    decode_run_reachable mode 3 cDec0
  have hD' :
      decodeConfig mode cDecH ∈
        checkedEvalRunLoopMachine.runBranches mD [cCheckedDec0] := by
    rw [hDecExact] at hD
    simpa [cCheckedDec0] using hD

  have hThroughDec :=
    mem_runBranches_trans checkedEvalRunLoopMachine
      (mS + 1) mD [seekConfig mode cSeek0]
      cCheckedDec0 (decodeConfig mode cDecH)
      hToDec hD'

  let cReject : CheckedConfig :=
    { state := .reject, tape := tAfter }

  have hRejectSucc :
      cReject ∈
        checkedEvalRunLoopMachine.successors (decodeConfig mode cDecH) := by
    dsimp [cReject, decodeConfig, cDecH]
    rw [disallowed_tag_successors mode
      (decodeTagBits b0 b1 b2) tAfter hdisallowed]
    simp

  have hReject :
      cReject ∈
        checkedEvalRunLoopMachine.runBranches 1 [decodeConfig mode cDecH] :=
    one_step_of_successor
      (decodeConfig mode cDecH) cReject
      (decodeConfig_not_halted mode cDecH) hRejectSucc

  have hAll :=
    mem_runBranches_trans checkedEvalRunLoopMachine
      ((mS + 1) + mD) 1 [seekConfig mode cSeek0]
      (decodeConfig mode cDecH) cReject
      hThroughDec hReject

  refine ⟨((mS + 1) + mD) + 1, ?_, ?_⟩
  · dsimp [checkedTagPrefixFuel, nSeek, source] at *
    omega
  · dsimp [cReject, tAfter, cSeek0, t0, source] at hAll ⊢
    simpa [seekConfig] using hAll

#print axioms MCore.Real.P01CheckedEvalRunTagPrefix.disallowed_tag_prefix_reaches_reject

#print axioms MCore.Real.P01CheckedEvalRunTagPrefix.allowed_decode_handoff
#print axioms MCore.Real.P01CheckedEvalRunTagPrefix.checked_tag_prefix_reaches

end P01CheckedEvalRunTagPrefix
end Real
end MCore
