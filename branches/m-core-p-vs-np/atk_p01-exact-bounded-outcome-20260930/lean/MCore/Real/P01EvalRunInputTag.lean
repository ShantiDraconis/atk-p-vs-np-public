import MCore.Real.P01EvalRunLoopRun

namespace MCore
namespace Real
namespace P01EvalRunInputTag

open CanonicalFinalProof
open CanonicalCircuitBits
open P01NTMRunLaws
open P01EncodedStackEvaluator
open P01EvalCursorMachine
open P01NeedExprTagDecode
open P01NeedExprCompositeNTM
open P01InputNodeCompositeNTM
open P01InputNodeCompositeRun
open P01InputNodeRoundTrip
open P01EvalRunLoopNTM
open P01EvalRunLoopRun

/-- Uniform physical majorant for the complete 000 input-tag route in the
repeated evaluator loop. -/
def inputTagLoopFuel
    (consumed i : Nat) (tail frameStack : BitString) : Nat :=
  (frameStack.length +
      (false :: false :: false :: (encodeNat i ++ tail)).length + 3) +
    1 + 3 + 1 +
    inputNodeCompositeFuel (consumed + 3) i tail frameStack

/-- Complete physical 000 route in the repeated evaluator.

The input-node submachine retains the return mode all the way to its done
terminal. inputLoopEmbed then chooses the correct global continuation:
final selected iff there is no source tail and no frame stack; otherwise
have/start selected. -/
theorem inputTag_loop_reaches_mode
    (witness tail frameStack : BitString)
    (consumed padding i : Nat)
    (hi : i < witness.length) :
    ∃ m ≤ inputTagLoopFuel consumed i tail frameStack,
      inputLoopConfig
        ({ state :=
             .done (witness.getD i false)
               (inputNodeFinalMode tail frameStack),
           tape :=
             (inputAfterReadTarget witness
               (consumedAfterInputIndex (consumed + 3) i)
               tail frameStack padding).tape } :
          Configuration InputNodeCompositeState (Option Bool)) ∈
        evalRunLoopMachine.runBranches m
          [{ state := .need needExprCompositeMachine.initial,
             tape :=
               evalCursorStackEndTape witness consumed
                 (false :: false :: false :: (encodeNat i ++ tail))
                 frameStack padding }] := by
  let source :=
    false :: false :: false :: (encodeNat i ++ tail)
  let nSeek := frameStack.length + source.length + 3
  let t0 :=
    evalCursorStackEndTape witness consumed source frameStack padding
  let tRead :=
    evalCursorReadTape witness consumed source frameStack padding
  let tAfterTag :=
    evalCursorReadTape witness (consumed + 3)
      (encodeNat i ++ tail) frameStack padding

  let cSeek0 : Configuration CursorSeekState (Option Bool) :=
    { state := cursorSeekMachine.initial, tape := t0 }
  let cSeekH : Configuration CursorSeekState (Option Bool) :=
    { state := .halt, tape := tRead }
  let cDec0 : Configuration TagDecodeState (Option Bool) :=
    { state := tagDecodeMachine.initial, tape := tRead }
  let cDecH : Configuration TagDecodeState (Option Bool) :=
    { state := .halt .input, tape := tAfterTag }
  let cInput0 : Configuration InputNodeCompositeState (Option Bool) :=
    { state := inputNodeCompositeMachine.initial, tape := tAfterTag }

  have hSeekExact :
      cursorSeekMachine.run nSeek cSeek0 = cSeekH := by
    dsimp [nSeek, cSeek0, cSeekH, t0, tRead, source]
    exact cursorSeek_run witness consumed
      (false :: false :: false :: (encodeNat i ++ tail))
      frameStack padding

  obtain ⟨mS, hmS, hS⟩ :=
    seekLoop_run_reachable nSeek cSeek0
  have hS' :
      seekLoopConfig cSeekH ∈
        evalRunLoopMachine.runBranches mS [seekLoopConfig cSeek0] := by
    rw [hSeekExact] at hS
    exact hS

  have hSeekSucc :
      decodeLoopConfig cDec0 ∈
        evalRunLoopMachine.successors (seekLoopConfig cSeekH) := by
    dsimp [seekLoopConfig, decodeLoopConfig, cSeekH, cDec0]
    simp [evalRunLoopMachine, needExprCompositeMachine, needLoopEmbed,
      NTM.successors, NTM.stepBranch, Tape.write, Tape.move]

  have hSeekStep :
      decodeLoopConfig cDec0 ∈
        evalRunLoopMachine.runBranches 1 [seekLoopConfig cSeekH] := by
    have h :=
      mem_runBranches_succ_of_successor
        evalRunLoopMachine 0 [seekLoopConfig cSeekH]
        (seekLoopConfig cSeekH) (decodeLoopConfig cDec0)
        (by simp [NTM.runBranches])
        (seekLoop_not_halted cSeekH) hSeekSucc
    simpa using h

  have hToDec :=
    mem_runBranches_trans evalRunLoopMachine
      mS 1 [seekLoopConfig cSeek0]
      (seekLoopConfig cSeekH) (decodeLoopConfig cDec0)
      hS' hSeekStep

  have hDecExact :
      tagDecodeMachine.run 3 cDec0 = cDecH := by
    dsimp [cDec0, cDecH, tRead, tAfterTag, source]
    simpa [decodeTagBits] using
      tagDecode_run_three witness (encodeNat i ++ tail)
        frameStack consumed padding false false false

  obtain ⟨mD, hmD, hD⟩ :=
    decodeLoop_run_reachable 3 cDec0
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

  have hInputSucc :
      inputLoopConfig cInput0 ∈
        evalRunLoopMachine.successors (decodeLoopConfig cDecH) := by
    change
      ({ state := .need (.input inputNodeCompositeMachine.initial),
         tape := tAfterTag } : P01EvalRunLoopRun.LoopConfig) ∈
      evalRunLoopMachine.successors
        ({ state := .need (.decode (.halt .input)),
           tape := tAfterTag } : P01EvalRunLoopRun.LoopConfig)
    rw [show evalRunLoopMachine.successors
        ({ state := .need (.decode (.halt .input)),
           tape := tAfterTag } : P01EvalRunLoopRun.LoopConfig) =
      (needExprCompositeMachine.successors
        ({ state := .decode (.halt .input), tape := tAfterTag } :
          Configuration NeedExprCompositeState (Option Bool))).map
        (fun d =>
          ({ state := needLoopEmbed d.state, tape := d.tape } :
            P01EvalRunLoopRun.LoopConfig)) by
        simp [evalRunLoopMachine, needExprCompositeMachine,
          NTM.successors, NTM.stepBranch, needLoopEmbed,
          Tape.write, Tape.move]]
    rw [input_tag_handoff_successors tAfterTag]
    simp [inputLoopConfig, inputLoopEmbed, needLoopEmbed]

  have hInputStep :
      inputLoopConfig cInput0 ∈
        evalRunLoopMachine.runBranches 1 [decodeLoopConfig cDecH] := by
    have h :=
      mem_runBranches_succ_of_successor
        evalRunLoopMachine 0 [decodeLoopConfig cDecH]
        (decodeLoopConfig cDecH) (inputLoopConfig cInput0)
        (by simp [NTM.runBranches])
        (decodeLoop_not_halted cDecH) hInputSucc
    simpa using h

  have hToInput :=
    mem_runBranches_trans evalRunLoopMachine
      ((mS + 1) + mD) 1 [seekLoopConfig cSeek0]
      (decodeLoopConfig cDecH) (inputLoopConfig cInput0)
      hThroughDec hInputStep

  obtain ⟨mI, hmI, hI⟩ :=
    inputNode_loop_from_read
      witness tail frameStack (consumed + 3) padding i hi

  have hI' :
      inputLoopConfig
        ({ state :=
             .done (witness.getD i false)
               (inputNodeFinalMode tail frameStack),
           tape :=
             (inputAfterReadTarget witness
               (consumedAfterInputIndex (consumed + 3) i)
               tail frameStack padding).tape } :
          Configuration InputNodeCompositeState (Option Bool)) ∈
        evalRunLoopMachine.runBranches mI [inputLoopConfig cInput0] := by
    simpa [cInput0, tAfterTag] using hI

  have hAll :=
    mem_runBranches_trans evalRunLoopMachine
      (((mS + 1) + mD) + 1) mI
      [seekLoopConfig cSeek0]
      (inputLoopConfig cInput0)
      (inputLoopConfig
        ({ state :=
             .done (witness.getD i false)
               (inputNodeFinalMode tail frameStack),
           tape :=
             (inputAfterReadTarget witness
               (consumedAfterInputIndex (consumed + 3) i)
               tail frameStack padding).tape } :
          Configuration InputNodeCompositeState (Option Bool)))
      hToInput hI'

  refine ⟨(((mS + 1) + mD) + 1) + mI, ?_, ?_⟩
  · dsimp [inputTagLoopFuel, nSeek, source] at *
    omega
  · dsimp [cSeek0, t0, source] at hAll ⊢
    simpa [seekLoopConfig, needExprCompositeMachine] using hAll

/-- Fully evaluated input with no continuation stack reaches the real final
loop state, not an intermediate value terminal. -/
theorem inputTag_empty_reaches_final
    (witness : BitString)
    (consumed padding i : Nat)
    (hi : i < witness.length) :
    ∃ m ≤ inputTagLoopFuel consumed i [] [],
      ({ state := .final (witness.getD i false),
         tape :=
           (inputAfterReadTarget witness
             (consumedAfterInputIndex (consumed + 3) i)
             [] [] padding).tape } :
        P01EvalRunLoopRun.LoopConfig) ∈
      evalRunLoopMachine.runBranches m
        [{ state := .need needExprCompositeMachine.initial,
           tape :=
             evalCursorStackEndTape witness consumed
               (false :: false :: false :: encodeNat i)
               [] padding }] := by
  simpa [inputLoopConfig, inputLoopEmbed, inputNodeFinalMode] using
    inputTag_loop_reaches_mode
      witness [] [] consumed padding i hi

/-- An input whose source tail is nonempty restarts in haveValue mode. -/
theorem inputTag_tail_reaches_have
    (witness : BitString)
    (b : Bool) (tail frameStack : BitString)
    (consumed padding i : Nat)
    (hi : i < witness.length) :
    ∃ m ≤ inputTagLoopFuel consumed i (b :: tail) frameStack,
      ({ state := .have (.start (witness.getD i false)),
         tape :=
           (inputAfterReadTarget witness
             (consumedAfterInputIndex (consumed + 3) i)
             (b :: tail) frameStack padding).tape } :
        P01EvalRunLoopRun.LoopConfig) ∈
      evalRunLoopMachine.runBranches m
        [{ state := .need needExprCompositeMachine.initial,
           tape :=
             evalCursorStackEndTape witness consumed
               (false :: false :: false ::
                 (encodeNat i ++ (b :: tail)))
               frameStack padding }] := by
  simpa [inputLoopConfig, inputLoopEmbed, inputNodeFinalMode] using
    inputTag_loop_reaches_mode
      witness (b :: tail) frameStack consumed padding i hi

/-- Empty source tail with a nonempty continuation stack also restarts in
haveValue mode. -/
theorem inputTag_frames_reaches_have
    (witness : BitString)
    (f : Bool) (frameTail : BitString)
    (consumed padding i : Nat)
    (hi : i < witness.length) :
    ∃ m ≤ inputTagLoopFuel consumed i [] (f :: frameTail),
      ({ state := .have (.start (witness.getD i false)),
         tape :=
           (inputAfterReadTarget witness
             (consumedAfterInputIndex (consumed + 3) i)
             [] (f :: frameTail) padding).tape } :
        P01EvalRunLoopRun.LoopConfig) ∈
      evalRunLoopMachine.runBranches m
        [{ state := .need needExprCompositeMachine.initial,
           tape :=
             evalCursorStackEndTape witness consumed
               (false :: false :: false :: encodeNat i)
               (f :: frameTail) padding }] := by
  simpa [inputLoopConfig, inputLoopEmbed, inputNodeFinalMode] using
    inputTag_loop_reaches_mode
      witness [] (f :: frameTail) consumed padding i hi

#print axioms MCore.Real.P01EvalRunInputTag.inputTag_loop_reaches_mode
#print axioms MCore.Real.P01EvalRunInputTag.inputTag_empty_reaches_final
#print axioms MCore.Real.P01EvalRunInputTag.inputTag_tail_reaches_have
#print axioms MCore.Real.P01EvalRunInputTag.inputTag_frames_reaches_have

end P01EvalRunInputTag
end Real
end MCore
