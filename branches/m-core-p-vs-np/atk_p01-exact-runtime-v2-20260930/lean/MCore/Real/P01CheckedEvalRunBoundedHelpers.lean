import MCore.Real.P01CheckedVerifierBudget
import MCore.Real.P01CheckedVerifierGlobalBudget
import MCore.Real.P01CheckedEvalRunBaseCases
import MCore.Real.P01CheckedEvalRunNeedTags
import MCore.Real.P01CheckedEvalRunHaveValue
import MCore.Real.P01CheckedEvalRunInputTag

namespace MCore
namespace Real
namespace P01CheckedEvalRunBoundedHelpers

open CanonicalFinalProof
open CanonicalCircuitBits
open P01EncodedStackEvaluator
open P01EncodedFrameTape
open P01EvalCursorMachine
open P01CheckedEvalRunLoopNTM
open P01CheckedEvalRunBaseCases
open P01CheckedEvalRunNeedTags
open P01CheckedEvalRunHaveValue
open P01CheckedEvalRunInputTag
open P01CheckedVerifierBudget
open P01CheckedVerifierGlobalBudget

abbrev CheckedConfig :=
  Configuration CheckedEvalRunState (Option Bool)

private theorem small_const_le_stepEnvelope
    (n k : Nat) (hk : k ≤ 13) :
    k ≤ checkedLoopStepEnvelope n := by
  unfold checkedLoopStepEnvelope
  have h1 : 1 ≤ n + 1 := by omega
  have hsq : 1 ≤ (n + 1) ^ 2 := by
    have hmul : 1 * 1 ≤ (n + 1) * (n + 1) :=
      Nat.mul_le_mul h1 h1
    simpa [Nat.pow_two] using hmul
  have h256 : 256 ≤ 256 * (n + 1) ^ 2 := by
    simpa using Nat.mul_le_mul_left 256 hsq
  omega

/-- The checked 000 route fits the common one-step physical envelope. -/
theorem inputTag_checked_reaches_mode_within_envelope
    (n : Nat)
    (mode : P01CNFMode.SyntaxMode)
    (witness tail frameStack : BitString)
    (consumed padding i : Nat)
    (hi : i < witness.length)
    (hsource :
      (false :: false :: false :: (encodeNat i ++ tail)).length ≤ n)
    (hc3 : consumed + 3 ≤ n)
    (hindex : i ≤ n)
    (htail : tail.length ≤ n)
    (hframes : frameStack.length ≤ n) :
    ∃ m ≤ checkedLoopStepEnvelope n,
      inputCheckedConfig mode
        ({ state :=
             .done (witness.getD i false)
               (P01InputNodeCompositeRun.inputNodeFinalMode tail frameStack),
           tape :=
             (P01InputNodeRoundTrip.inputAfterReadTarget witness
               (P01InputNodeRoundTrip.consumedAfterInputIndex
                 (consumed + 3) i)
               tail frameStack padding).tape } :
          Configuration P01InputNodeCompositeNTM.InputNodeCompositeState
            (Option Bool)) ∈
        checkedEvalRunLoopMachine.runBranches m
          [{ state := .need mode P01NeedExprCompositeNTM.needExprCompositeMachine.initial,
             tape :=
               evalCursorStackEndTape witness consumed
                 (false :: false :: false :: (encodeNat i ++ tail))
                 frameStack padding }] := by
  obtain ⟨m, hm, hrun⟩ :=
    inputTag_checked_reaches_mode
      mode witness tail frameStack consumed padding i hi
  refine ⟨m, Nat.le_trans hm ?_, hrun⟩
  have h :=
    checkedInputTagFuel_le
      n consumed i tail frameStack
      hsource hc3 hindex htail hframes
  exact Nat.le_trans h (checkedStepEnvelope_le_loopEnvelope n)

/-- Generic continuation-producing checked tag under the common envelope. -/
theorem pushTag_checked_reaches_need_within_envelope
    (n : Nat)
    (mode : P01CNFMode.SyntaxMode)
    (witness rest frameStack : BitString)
    (consumed padding : Nat)
    (b0 b1 b2 : Bool)
    (tag : P01NeedExprTagDecode.NeedExprTag)
    (frame : EvalFrame)
    (hTag :
      P01NeedExprTagDecode.decodeTagBits b0 b1 b2 = tag)
    (hAllowed :
      P01CNFMode.tagAllowed mode tag = true)
    (hPost :
      P01CheckedEvalRunTagPrefix.postTagState mode tag =
        .need (P01CNFMode.childMode mode tag) (.retPush frame .scanUnread))
    (hsource : (b0 :: b1 :: b2 :: rest).length ≤ n)
    (hframes : frameStack.length ≤ n) :
    ∃ m ≤ checkedLoopStepEnvelope n,
      ({ state := .need (P01CNFMode.childMode mode tag)
           P01NeedExprCompositeNTM.needExprCompositeMachine.initial,
         tape :=
           evalCursorStackEndTape witness (consumed + 3)
             rest (encodeEvalFrame frame ++ frameStack)
             (((padding - 1) - 1) - 1) } : CheckedConfig) ∈
        checkedEvalRunLoopMachine.runBranches m
          [{ state := .need mode P01NeedExprCompositeNTM.needExprCompositeMachine.initial,
             tape :=
               evalCursorStackEndTape witness consumed
                 (b0 :: b1 :: b2 :: rest) frameStack padding }] := by
  obtain ⟨m, hm, hrun⟩ :=
    pushTag_checked_reaches_need
      mode witness rest frameStack consumed padding
      b0 b1 b2 tag frame hTag hAllowed hPost
  refine ⟨m, Nat.le_trans hm ?_, hrun⟩
  have hfuel :
      checkedPushTagFuel (b0 :: b1 :: b2 :: rest) frameStack ≤
        checkedStepEnvelope n :=
    checkedPushTagFuel_le_envelope
      n (b0 :: b1 :: b2 :: rest) frameStack hsource hframes
  have heq :
      P01CheckedEvalRunTagPrefix.checkedTagPrefixFuel
          (b0 :: b1 :: b2 :: rest) frameStack +
          (rest.length + frameStack.length + 2) + 1 + 3 + 1 =
        checkedPushTagFuel (b0 :: b1 :: b2 :: rest) frameStack := by
    unfold checkedPushTagFuel
    simp
    omega
  rw [heq]
  exact Nat.le_trans hfuel (checkedStepEnvelope_le_loopEnvelope n)

/-- Normalizing an already-produced value to the external checked outcome costs
at most one common step envelope. -/
theorem have_reaches_outcome_within_envelope
    (n : Nat)
    (mode : P01CNFMode.SyntaxMode)
    (witness : BitString)
    (value : Bool)
    (tail : BitString)
    (frames : List EvalFrame)
    (consumed padding : Nat) :
    ∃ m ≤ checkedLoopStepEnvelope n, ∃ cfg,
      cfg ∈
        checkedEvalRunLoopMachine.runBranches m
          [{ state := .have mode (.start value),
             tape :=
               evalCursorStackEndTape witness consumed tail
                 (encodeEvalFrames frames) padding }] ∧
      CheckedLoopOutcome witness mode value tail frames cfg := by
  cases tail with
  | cons b bs =>
      let cfg : CheckedConfig :=
        { state := .have mode (.start value),
          tape :=
            evalCursorStackEndTape witness consumed (b :: bs)
              (encodeEvalFrames frames) padding }
      refine ⟨0, ?_, cfg, ?_, ?_⟩
      · exact Nat.zero_le _
      · simp [cfg, NTM.runBranches]
      · exact ⟨consumed, padding, rfl⟩
  | nil =>
      cases frames with
      | cons f fs =>
          let cfg : CheckedConfig :=
            { state := .have mode (.start value),
              tape :=
                evalCursorStackEndTape witness consumed []
                  (encodeEvalFrames (f :: fs)) padding }
          refine ⟨0, ?_, cfg, ?_, ?_⟩
          · exact Nat.zero_le _
          · simp [cfg, NTM.runBranches]
          · exact ⟨consumed, padding, rfl⟩
      | nil =>
          obtain ⟨m, hm, hrun⟩ :=
            checked_empty_frames_reaches_final
              mode witness consumed padding value
          let cfg : CheckedConfig :=
            { state := .final value,
              tape :=
                Tape.move none .left
                  (Tape.move none .left
                    (evalCursorStackEndTape witness consumed [] [] padding)) }
          refine ⟨m, Nat.le_trans hm
              (small_const_le_stepEnvelope n 3 (by omega)),
            cfg, ?_, ?_⟩
          · simpa [cfg] using hrun
          · exact ⟨cfg.tape, rfl⟩

theorem nine_le_stepEnvelope (n : Nat) :
    9 ≤ checkedLoopStepEnvelope n :=
  small_const_le_stepEnvelope n 9 (by omega)

theorem thirteen_le_stepEnvelope (n : Nat) :
    13 ≤ checkedLoopStepEnvelope n :=
  small_const_le_stepEnvelope n 13 (by omega)

#print axioms MCore.Real.P01CheckedEvalRunBoundedHelpers.inputTag_checked_reaches_mode_within_envelope
#print axioms MCore.Real.P01CheckedEvalRunBoundedHelpers.pushTag_checked_reaches_need_within_envelope
#print axioms MCore.Real.P01CheckedEvalRunBoundedHelpers.have_reaches_outcome_within_envelope
#print axioms MCore.Real.P01CheckedEvalRunBoundedHelpers.nine_le_stepEnvelope
#print axioms MCore.Real.P01CheckedEvalRunBoundedHelpers.thirteen_le_stepEnvelope

end P01CheckedEvalRunBoundedHelpers
end Real
end MCore
