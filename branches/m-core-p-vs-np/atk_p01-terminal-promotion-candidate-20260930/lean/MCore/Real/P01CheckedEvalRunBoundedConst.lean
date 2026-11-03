import MCore.Real.P01CheckedEvalRunBaseCases
import MCore.Real.P01CheckedVerifierInvariant
import MCore.Real.P01CheckedVerifierGlobalBudget

namespace MCore
namespace Real
namespace P01CheckedEvalRunBoundedConst

open CanonicalFinalProof
open CanonicalCircuitBits
open P01EncodedStackEvaluator
open P01EncodedFrameTape
open P01EvalCursorMachine
open P01EvalCursorRoundTrip
open P01NeedExprCompositeNTM
open P01NeedExprTagDecode
open P01CheckedEvalRunLoopNTM
open P01CheckedEvalRunBaseCases
open P01CheckedEvalRunPhaseLift
open P01CheckedEvalRunTagPrefix
open P01CheckedVerifierBudget
open P01CheckedVerifierGlobalBudget
open P01CheckedVerifierInvariant
open P01CNFMode
open P01NTMRunLaws

abbrev CheckedConfig :=
  Configuration CheckedEvalRunState (Option Bool)

private theorem linear_tail_fits_half_loop
    (n tailLen frameLen : Nat)
    (ht : tailLen ≤ n)
    (hf : frameLen ≤ n) :
    tailLen + frameLen + 2 + 1 + 3 ≤
      128 * (n + 1) ^ 2 := by
  have h1 : n + 1 ≤ (n + 1) * (n + 1) := by
    exact Nat.le_mul_of_pos_right (n + 1) (by omega)
  have hlin :
      tailLen + frameLen + 2 + 1 + 3 ≤ 8 * (n + 1) := by
    omega
  have hquad :
      8 * (n + 1) ≤ 8 * ((n + 1) * (n + 1)) :=
    Nat.mul_le_mul_left 8 h1
  have hcoef :
      8 * ((n + 1) * (n + 1)) ≤
        128 * ((n + 1) * (n + 1)) :=
    Nat.mul_le_mul_right ((n + 1) * (n + 1)) (by omega)
  simpa [Nat.pow_two] using
    Nat.le_trans hlin (Nat.le_trans hquad hcoef)

/-- A checked constant circuit reaches its exact checked-loop outcome within
one uniform checked-loop step envelope, under the global layout invariant. -/
theorem const_checked_run_within_loopEnvelope
    (n : Nat)
    (sigma : Assignment)
    (witness tail : BitString)
    (frames : List EvalFrame)
    (mode : SyntaxMode)
    (consumed padding : Nat)
    (v : Bool)
    (hmode : modeCheck mode (.const v) = true)
    (hLayout :
      CheckedLayoutBound n consumed
        (encodeCircuit (.const v) ++ tail)
        (encodeEvalFrames frames)) :
    ∃ m ≤ checkedLoopStepEnvelope n, ∃ cfg,
      cfg ∈
        checkedEvalRunLoopMachine.runBranches m
          [{ state := .need mode needExprCompositeMachine.initial,
             tape :=
               evalCursorStackEndTape witness consumed
                 (encodeCircuit (.const v) ++ tail)
                 (encodeEvalFrames frames) padding }] ∧
      CheckedLoopOutcome witness (exitMode mode (.const v))
        v tail frames cfg := by
  let b0 := false
  let b1 := v
  let b2 := !v
  have htag :
      decodeTagBits b0 b1 b2 =
        (if v then NeedExprTag.constTrue else NeedExprTag.constFalse) := by
    cases v <;> rfl
  have hallowed :
      tagAllowed mode
        (if v then NeedExprTag.constTrue else NeedExprTag.constFalse) = true := by
    cases v <;> simpa using hmode

  obtain ⟨m0, hm0, h0⟩ :=
    checked_tag_prefix_reaches
      mode witness tail (encodeEvalFrames frames)
      consumed padding b0 b1 b2
      (by simpa [htag] using hallowed)

  let tAfter :=
    evalCursorReadTape witness (consumed + 3)
      tail (encodeEvalFrames frames) padding
  let tDone :=
    evalCursorStackEndTape witness (consumed + 3)
      tail (encodeEvalFrames frames) padding
  let nRet := tail.length + (encodeEvalFrames frames).length + 2
  let cRet0 : Configuration CursorReturnState (Option Bool) :=
    { state := .scanUnread, tape := tAfter }
  let cRetH : Configuration CursorReturnState (Option Bool) :=
    { state := .halt, tape := tDone }
  let cCheckedRet0 : CheckedConfig :=
    { state := .need mode (.retValue v .scanUnread), tape := tAfter }
  let cCheckedRetH : CheckedConfig :=
    { state := .need mode (.retValue v .halt), tape := tDone }
  let cHave : CheckedConfig :=
    { state := .have mode (.start v), tape := tDone }

  have hPrefix :
      cCheckedRet0 ∈
        checkedEvalRunLoopMachine.runBranches m0
          [{ state := .need mode needExprCompositeMachine.initial,
             tape :=
               evalCursorStackEndTape witness consumed
                 (encodeCircuit (.const v) ++ tail)
                 (encodeEvalFrames frames) padding }] := by
    cases v <;>
      simpa [cCheckedRet0, tAfter, postTagState,
        childMode, circuitTag, encodeCircuit, b0, b1, b2,
        decodeTagBits] using h0

  have hRetExact :
      cursorReturnMachine.run nRet cRet0 = cRetH := by
    dsimp [nRet, cRet0, cRetH, tAfter, tDone]
    exact cursorReturn_preserve_run
      witness (consumed + 3) tail
        (encodeEvalFrames frames) padding

  obtain ⟨mR, hmR, hR⟩ :=
    retValue_run_reachable mode v nRet cRet0
  have hR' :
      cCheckedRetH ∈
        checkedEvalRunLoopMachine.runBranches mR [cCheckedRet0] := by
    rw [hRetExact] at hR
    simpa [cCheckedRet0, cCheckedRetH,
      retValueConfig, cRet0, cRetH] using hR

  have hThroughRet :=
    mem_runBranches_trans checkedEvalRunLoopMachine
      m0 mR
      [{ state := .need mode needExprCompositeMachine.initial,
         tape :=
           evalCursorStackEndTape witness consumed
             (encodeCircuit (.const v) ++ tail)
             (encodeEvalFrames frames) padding }]
      cCheckedRet0 cCheckedRetH hPrefix hR'

  have hHandSucc :
      cHave ∈ checkedEvalRunLoopMachine.successors cCheckedRetH := by
    dsimp [cHave, cCheckedRetH, tDone]
    simp [checkedEvalRunLoopMachine, needExprCompositeMachine,
      needCheckedEmbed, NTM.successors, NTM.stepBranch,
      Tape.write, Tape.move]

  have hHand :
      cHave ∈
        checkedEvalRunLoopMachine.runBranches 1 [cCheckedRetH] := by
    have hactive : ¬ Halted checkedEvalRunLoopMachine cCheckedRetH := by
      dsimp [cCheckedRetH]
      simp [Halted, checkedEvalRunLoopMachine]
    have h :=
      mem_runBranches_succ_of_successor
        checkedEvalRunLoopMachine 0 [cCheckedRetH]
        cCheckedRetH cHave (by simp [NTM.runBranches]) hactive hHandSucc
    simpa using h

  have hToHave :=
    mem_runBranches_trans checkedEvalRunLoopMachine
      (m0 + mR) 1
      [{ state := .need mode needExprCompositeMachine.initial,
         tape :=
           evalCursorStackEndTape witness consumed
             (encodeCircuit (.const v) ++ tail)
             (encodeEvalFrames frames) padding }]
      cCheckedRetH cHave hThroughRet hHand

  have hsource :
      (encodeCircuit (.const v) ++ tail).length ≤ n :=
    hLayout.source_le
  have hframes :
      (encodeEvalFrames frames).length ≤ n :=
    hLayout.frames_le
  have htail : tail.length ≤ n := by
    cases v <;> simp [encodeCircuit] at hsource ⊢ <;> omega

  have hprefixFuel :
      checkedTagPrefixFuel
          (b0 :: b1 :: b2 :: tail) (encodeEvalFrames frames) ≤
        checkedStepEnvelope n := by
    apply checkedTagPrefixFuel_le_envelope
    · cases v <;>
        simpa [b0, b1, b2, encodeCircuit] using hsource
    · exact hframes
  have hm0' : m0 ≤ checkedStepEnvelope n :=
    Nat.le_trans hm0 hprefixFuel

  have hrest :
      mR + 1 + 3 ≤ 128 * (n + 1) ^ 2 := by
    have hlin :=
      linear_tail_fits_half_loop n tail.length
        (encodeEvalFrames frames).length htail hframes
    dsimp [nRet] at hmR
    omega

  have hm0Half :
      m0 ≤ 128 * (n + 1) ^ 2 := by
    simpa [P01CheckedVerifierBudget.checkedStepEnvelope] using hm0'
  have htotal :
      m0 + mR + 1 + 3 ≤ checkedLoopStepEnvelope n := by
    change m0 + mR + 1 + 3 ≤ 256 * (n + 1) ^ 2
    omega

  cases tail with
  | cons x xs =>
      refine ⟨m0 + mR + 1, ?_, cHave, hToHave, ?_⟩
      · omega
      · change CheckedLoopOutcome witness (exitMode mode (.const v))
          v (x :: xs) frames cHave
        refine ⟨consumed + 3, padding, ?_⟩
        cases v <;> cases mode <;>
          simp [CheckedLoopOutcome, exitMode, circuitTag, childMode,
            cHave, tDone, modeCheck] at hmode ⊢
  | nil =>
      cases frames with
      | cons f fs =>
          refine ⟨m0 + mR + 1, ?_, cHave, hToHave, ?_⟩
          · omega
          · change CheckedLoopOutcome witness (exitMode mode (.const v))
              v [] (f :: fs) cHave
            refine ⟨consumed + 3, padding, ?_⟩
            cases v <;> cases mode <;>
              simp [CheckedLoopOutcome, exitMode, circuitTag, childMode,
                cHave, tDone, modeCheck] at hmode ⊢
      | nil =>
          obtain ⟨mF, hmF, hF⟩ :=
            checked_empty_frames_reaches_final
              mode witness (consumed + 3) padding v
          let cFinal : CheckedConfig :=
            { state := .final v,
              tape :=
                Tape.move none .left
                  (Tape.move none .left
                    (evalCursorStackEndTape witness (consumed + 3)
                      [] [] padding)) }
          have hToHaveNil :
              cHave ∈
                checkedEvalRunLoopMachine.runBranches (m0 + mR + 1)
                  [{ state := .need mode needExprCompositeMachine.initial,
                     tape :=
                       evalCursorStackEndTape witness consumed
                         (encodeCircuit (.const v))
                         (encodeEvalFrames []) padding }] := by
            simpa using hToHave
          have hAll :=
            mem_runBranches_trans checkedEvalRunLoopMachine
              (m0 + mR + 1) mF
              [{ state := .need mode needExprCompositeMachine.initial,
                 tape :=
                   evalCursorStackEndTape witness consumed
                     (encodeCircuit (.const v))
                     (encodeEvalFrames []) padding }]
              cHave cFinal hToHaveNil
              (by simpa [cFinal] using hF)
          refine ⟨m0 + mR + 1 + mF, ?_, cFinal, ?_, ?_⟩
          · omega
          · simpa using hAll
          · exact ⟨cFinal.tape, rfl⟩


/-- Exact pre-normalization form of the bounded constant producer.
It exposes the physical have-state at source cursor `consumed + 3`, so the
result can be composed with a following circuit without recovering cursor
information from an existential outcome. -/
theorem const_checked_reaches_have_within_loopEnvelope
    (n : Nat)
    (sigma : Assignment)
    (witness tail : BitString)
    (frames : List EvalFrame)
    (mode : SyntaxMode)
    (consumed padding : Nat)
    (v : Bool)
    (hmode : modeCheck mode (.const v) = true)
    (hLayout :
      CheckedLayoutBound n consumed
        (encodeCircuit (.const v) ++ tail)
        (encodeEvalFrames frames)) :
    ∃ m ≤ checkedLoopStepEnvelope n,
      ({ state := .have mode (.start v),
         tape :=
           evalCursorStackEndTape witness (consumed + 3)
             tail (encodeEvalFrames frames) padding } : CheckedConfig) ∈
        checkedEvalRunLoopMachine.runBranches m
          [{ state := .need mode needExprCompositeMachine.initial,
             tape :=
               evalCursorStackEndTape witness consumed
                 (encodeCircuit (.const v) ++ tail)
                 (encodeEvalFrames frames) padding }] := by
  let b0 := false
  let b1 := v
  let b2 := !v
  have htag :
      decodeTagBits b0 b1 b2 =
        (if v then NeedExprTag.constTrue else NeedExprTag.constFalse) := by
    cases v <;> rfl
  have hallowed :
      tagAllowed mode
        (if v then NeedExprTag.constTrue else NeedExprTag.constFalse) = true := by
    cases v <;> simpa using hmode

  obtain ⟨m0, hm0, h0⟩ :=
    checked_tag_prefix_reaches
      mode witness tail (encodeEvalFrames frames)
      consumed padding b0 b1 b2
      (by simpa [htag] using hallowed)

  let tAfter :=
    evalCursorReadTape witness (consumed + 3)
      tail (encodeEvalFrames frames) padding
  let tDone :=
    evalCursorStackEndTape witness (consumed + 3)
      tail (encodeEvalFrames frames) padding
  let nRet := tail.length + (encodeEvalFrames frames).length + 2
  let cRet0 : Configuration CursorReturnState (Option Bool) :=
    { state := .scanUnread, tape := tAfter }
  let cRetH : Configuration CursorReturnState (Option Bool) :=
    { state := .halt, tape := tDone }
  let cCheckedRet0 : CheckedConfig :=
    { state := .need mode (.retValue v .scanUnread), tape := tAfter }
  let cCheckedRetH : CheckedConfig :=
    { state := .need mode (.retValue v .halt), tape := tDone }
  let cHave : CheckedConfig :=
    { state := .have mode (.start v), tape := tDone }

  have hPrefix :
      cCheckedRet0 ∈
        checkedEvalRunLoopMachine.runBranches m0
          [{ state := .need mode needExprCompositeMachine.initial,
             tape :=
               evalCursorStackEndTape witness consumed
                 (encodeCircuit (.const v) ++ tail)
                 (encodeEvalFrames frames) padding }] := by
    cases v <;>
      simpa [cCheckedRet0, tAfter, postTagState,
        childMode, circuitTag, encodeCircuit, b0, b1, b2,
        decodeTagBits] using h0

  have hRetExact :
      cursorReturnMachine.run nRet cRet0 = cRetH := by
    dsimp [nRet, cRet0, cRetH, tAfter, tDone]
    exact cursorReturn_preserve_run
      witness (consumed + 3) tail
        (encodeEvalFrames frames) padding

  obtain ⟨mR, hmR, hR⟩ :=
    retValue_run_reachable mode v nRet cRet0
  have hR' :
      cCheckedRetH ∈
        checkedEvalRunLoopMachine.runBranches mR [cCheckedRet0] := by
    rw [hRetExact] at hR
    simpa [cCheckedRet0, cCheckedRetH,
      retValueConfig, cRet0, cRetH] using hR

  have hThroughRet :=
    mem_runBranches_trans checkedEvalRunLoopMachine
      m0 mR
      [{ state := .need mode needExprCompositeMachine.initial,
         tape :=
           evalCursorStackEndTape witness consumed
             (encodeCircuit (.const v) ++ tail)
             (encodeEvalFrames frames) padding }]
      cCheckedRet0 cCheckedRetH hPrefix hR'

  have hHandSucc :
      cHave ∈ checkedEvalRunLoopMachine.successors cCheckedRetH := by
    dsimp [cHave, cCheckedRetH, tDone]
    simp [checkedEvalRunLoopMachine, needExprCompositeMachine,
      needCheckedEmbed, NTM.successors, NTM.stepBranch,
      Tape.write, Tape.move]

  have hHand :
      cHave ∈
        checkedEvalRunLoopMachine.runBranches 1 [cCheckedRetH] := by
    have hactive : ¬ Halted checkedEvalRunLoopMachine cCheckedRetH := by
      dsimp [cCheckedRetH]
      simp [Halted, checkedEvalRunLoopMachine]
    have h :=
      mem_runBranches_succ_of_successor
        checkedEvalRunLoopMachine 0 [cCheckedRetH]
        cCheckedRetH cHave (by simp [NTM.runBranches]) hactive hHandSucc
    simpa using h

  have hToHave :=
    mem_runBranches_trans checkedEvalRunLoopMachine
      (m0 + mR) 1
      [{ state := .need mode needExprCompositeMachine.initial,
         tape :=
           evalCursorStackEndTape witness consumed
             (encodeCircuit (.const v) ++ tail)
             (encodeEvalFrames frames) padding }]
      cCheckedRetH cHave hThroughRet hHand

  have hsource :
      (encodeCircuit (.const v) ++ tail).length ≤ n :=
    hLayout.source_le
  have hframes :
      (encodeEvalFrames frames).length ≤ n :=
    hLayout.frames_le
  have htail : tail.length ≤ n := by
    cases v <;> simp [encodeCircuit] at hsource ⊢ <;> omega

  have hprefixFuel :
      checkedTagPrefixFuel
          (b0 :: b1 :: b2 :: tail) (encodeEvalFrames frames) ≤
        checkedStepEnvelope n := by
    apply checkedTagPrefixFuel_le_envelope
    · cases v <;>
        simpa [b0, b1, b2, encodeCircuit] using hsource
    · exact hframes
  have hm0' : m0 ≤ checkedStepEnvelope n :=
    Nat.le_trans hm0 hprefixFuel

  have hrest :
      mR + 1 + 3 ≤ 128 * (n + 1) ^ 2 := by
    have hlin :=
      linear_tail_fits_half_loop n tail.length
        (encodeEvalFrames frames).length htail hframes
    dsimp [nRet] at hmR
    omega

  have hm0Half :
      m0 ≤ 128 * (n + 1) ^ 2 := by
    simpa [P01CheckedVerifierBudget.checkedStepEnvelope] using hm0'
  have htotal :
      m0 + mR + 1 ≤ checkedLoopStepEnvelope n := by
    change m0 + mR + 1 ≤ 256 * (n + 1) ^ 2
    omega

  refine ⟨m0 + mR + 1, htotal, ?_⟩
  simpa [cHave, tDone] using hToHave

#print axioms MCore.Real.P01CheckedEvalRunBoundedConst.const_checked_run_within_loopEnvelope
#print axioms MCore.Real.P01CheckedEvalRunBoundedConst.const_checked_reaches_have_within_loopEnvelope

end P01CheckedEvalRunBoundedConst
end Real
end MCore
