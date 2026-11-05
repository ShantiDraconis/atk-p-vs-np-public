import MCore.Real.P01CheckedEvalRunInputTag
import MCore.Real.P01CheckedVerifierInvariant
import MCore.Real.P01CheckedVerifierGlobalBudget

namespace MCore
namespace Real
namespace P01CheckedEvalRunBoundedInput

open CanonicalFinalProof
open CanonicalCircuitBits
open P01EncodedStackEvaluator
open P01EncodedFrameTape
open P01EvalCursorMachine
open P01InputNodeCompositeNTM
open P01InputNodeRoundTrip
open P01NeedExprCompositeNTM
open P01CheckedEvalRunLoopNTM
open P01CheckedEvalRunInputTag
open P01CheckedVerifierBudget
open P01CheckedVerifierGlobalBudget
open P01CheckedVerifierInvariant

abbrev CheckedConfig :=
  Configuration CheckedEvalRunState (Option Bool)

/-- The complete checked 000 route fits the uniform checked-loop envelope
whenever the current physical layout satisfies the global source/stack budget.

This is the first runtime-producing bridge from the layout invariant to a
concrete checked-machine execution bound. -/
theorem inputTag_checked_reaches_within_loopEnvelope
    (n : Nat)
    (mode : P01CNFMode.SyntaxMode)
    (witness tail frameStack : BitString)
    (consumed padding i : Nat)
    (hi : i < witness.length)
    (hLayout :
      CheckedLayoutBound n consumed
        (false :: false :: false :: (encodeNat i ++ tail))
        frameStack) :
    ∃ m ≤ checkedLoopStepEnvelope n,
      inputCheckedConfig mode
        ({ state :=
             .done (witness.getD i false)
               (P01InputNodeCompositeRun.inputNodeFinalMode tail frameStack),
           tape :=
             (inputAfterReadTarget witness
               (consumedAfterInputIndex (consumed + 3) i)
               tail frameStack padding).tape } :
          Configuration InputNodeCompositeState (Option Bool)) ∈
        checkedEvalRunLoopMachine.runBranches m
          [{ state := .need mode needExprCompositeMachine.initial,
             tape :=
               evalCursorStackEndTape witness consumed
                 (false :: false :: false :: (encodeNat i ++ tail))
                 frameStack padding }] := by
  obtain ⟨m, hm, hrun⟩ :=
    inputTag_checked_reaches_mode
      mode witness tail frameStack consumed padding i hi
  have hsource :
      (false :: false :: false :: (encodeNat i ++ tail)).length ≤ n :=
    hLayout.source_le
  have hc3 : consumed + 3 ≤ n :=
    consumed_add_three_le n consumed false false false
      (encodeNat i ++ tail) frameStack hLayout
  have hindex : i ≤ n :=
    input_index_le n consumed i tail frameStack hLayout
  have htail : tail.length ≤ n := by
    have hs := hLayout.source_budget
    simp [List.length_append,
      P01CheckedVerifierBudget.encodeNat_length] at hs
    omega
  have hframes : frameStack.length ≤ n :=
    hLayout.frames_le
  have h :=
      checkedInputTagFuel_le
        n consumed i tail frameStack
        hsource hc3 hindex htail hframes
  have hstep :
      checkedStepEnvelope n ≤ checkedLoopStepEnvelope n :=
    checkedStepEnvelope_le_loopEnvelope n
  have hfuel :
      checkedInputTagFuel consumed i tail frameStack ≤
        checkedLoopStepEnvelope n :=
    Nat.le_trans h hstep
  exact ⟨m, Nat.le_trans hm hfuel, hrun⟩

/-- The input route also fits any larger accumulated budget. -/
theorem inputTag_checked_reaches_within_accumulated
    (n total : Nat)
    (mode : P01CNFMode.SyntaxMode)
    (witness tail frameStack : BitString)
    (consumed padding i : Nat)
    (hi : i < witness.length)
    (hLayout :
      CheckedLayoutBound n consumed
        (false :: false :: false :: (encodeNat i ++ tail))
        frameStack)
    (hstep : checkedLoopStepEnvelope n ≤ total) :
    ∃ m ≤ total,
      inputCheckedConfig mode
        ({ state :=
             .done (witness.getD i false)
               (P01InputNodeCompositeRun.inputNodeFinalMode tail frameStack),
           tape :=
             (inputAfterReadTarget witness
               (consumedAfterInputIndex (consumed + 3) i)
               tail frameStack padding).tape } :
          Configuration InputNodeCompositeState (Option Bool)) ∈
        checkedEvalRunLoopMachine.runBranches m
          [{ state := .need mode needExprCompositeMachine.initial,
             tape :=
               evalCursorStackEndTape witness consumed
                 (false :: false :: false :: (encodeNat i ++ tail))
                 frameStack padding }] := by
  obtain ⟨m, hm, hrun⟩ :=
    inputTag_checked_reaches_within_loopEnvelope
      n mode witness tail frameStack consumed padding i hi hLayout
  exact ⟨m, Nat.le_trans hm hstep, hrun⟩

#print axioms MCore.Real.P01CheckedEvalRunBoundedInput.inputTag_checked_reaches_within_loopEnvelope
#print axioms MCore.Real.P01CheckedEvalRunBoundedInput.inputTag_checked_reaches_within_accumulated

end P01CheckedEvalRunBoundedInput
end Real
end MCore
