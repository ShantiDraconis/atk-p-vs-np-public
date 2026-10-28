import MCore.Real.P01EvalStepSemanticRefinement
import MCore.Real.P01CheckedVerifierBudget

namespace MCore
namespace Real
namespace P01EvalStepEnvelope

open CanonicalFinalProof
open CanonicalCircuitBits
open P01EncodedStackEvaluator
open P01EncodedFrameTape
open P01EvalCursorMachine
open P01EvalStepCompositeNTM
open P01EvalStepCompositeRun
open P01EvalStepSemanticRefinement
open P01CheckedVerifierBudget

private theorem small_const_le_envelope (n k : Nat) (hk : k ≤ 13) :
    k ≤ checkedStepEnvelope n := by
  unfold checkedStepEnvelope
  have hbase : 13 ≤ 128 * (n + 1) ^ 2 := by
    have h1 : 1 ≤ n + 1 := by omega
    have hpos : 1 ≤ (n + 1) ^ 2 := by
      have hmul : 1 * 1 ≤ (n + 1) * (n + 1) :=
        Nat.mul_le_mul h1 h1
      simpa [Nat.pow_two] using hmul
    have h128 : 128 ≤ 128 * (n + 1) ^ 2 := by
      simpa using Nat.mul_le_mul_left 128 hpos
    omega
  omega

theorem constFalse_refines_within_envelope
    (n : Nat)
    (sigma : Assignment)
    (witness rest : BitString)
    (frames : List EvalFrame)
    (consumed padding : Nat)
    (hrest : rest.length ≤ n)
    (hframes : (encodeEvalFrames frames).length ≤ n) :
    evalStep sigma
      (needExpr (false :: false :: true :: rest) frames) =
        some (haveValue false rest frames) ∧
    ∃ m ≤ checkedStepEnvelope n,
      ({ state := .doneValue false,
         tape :=
           evalCursorStackEndTape witness (consumed + 3)
             rest (encodeEvalFrames frames) padding } :
        EvalStepConfig) ∈
        evalStepCompositeMachine.runBranches m
          [needStart witness consumed
            (false :: false :: true :: rest) frames padding] := by
  obtain ⟨hsem, m, hm, hrun⟩ :=
    constFalse_refines_evalStep
      sigma witness rest frames consumed padding
  refine ⟨hsem, m, ?_, hrun⟩
  exact Nat.le_trans hm
    (constTagCompositeFuel_le_envelope
      n (encodeEvalFrames frames) rest hframes hrest)

theorem constTrue_refines_within_envelope
    (n : Nat)
    (sigma : Assignment)
    (witness rest : BitString)
    (frames : List EvalFrame)
    (consumed padding : Nat)
    (hrest : rest.length ≤ n)
    (hframes : (encodeEvalFrames frames).length ≤ n) :
    evalStep sigma
      (needExpr (false :: true :: false :: rest) frames) =
        some (haveValue true rest frames) ∧
    ∃ m ≤ checkedStepEnvelope n,
      ({ state := .doneValue true,
         tape :=
           evalCursorStackEndTape witness (consumed + 3)
             rest (encodeEvalFrames frames) padding } :
        EvalStepConfig) ∈
        evalStepCompositeMachine.runBranches m
          [needStart witness consumed
            (false :: true :: false :: rest) frames padding] := by
  obtain ⟨hsem, m, hm, hrun⟩ :=
    constTrue_refines_evalStep
      sigma witness rest frames consumed padding
  refine ⟨hsem, m, ?_, hrun⟩
  exact Nat.le_trans hm
    (constTagCompositeFuel_le_envelope
      n (encodeEvalFrames frames) rest hframes hrest)

theorem negTag_refines_within_envelope
    (n : Nat)
    (sigma : Assignment)
    (witness rest : BitString)
    (frames : List EvalFrame)
    (consumed padding : Nat)
    (hrest : rest.length ≤ n)
    (hframes : (encodeEvalFrames frames).length ≤ n) :
    evalStep sigma
      (needExpr (false :: true :: true :: rest) frames) =
        some (needExpr rest (.neg :: frames)) ∧
    ∃ m ≤ checkedStepEnvelope n,
      ({ state := .doneNeed,
         tape :=
           evalCursorStackEndTape witness (consumed + 3) rest
             (encodeEvalFrames (.neg :: frames))
             (((padding - 1) - 1) - 1) } :
        EvalStepConfig) ∈
        evalStepCompositeMachine.runBranches m
          [needStart witness consumed
            (false :: true :: true :: rest) frames padding] := by
  obtain ⟨hsem, m, hm, hrun⟩ :=
    negTag_refines_evalStep
      sigma witness rest frames consumed padding
  refine ⟨hsem, m, ?_, hrun⟩
  exact Nat.le_trans hm
    (pushTagCompositeFuel_le_envelope
      n (encodeEvalFrames frames) rest hframes hrest)

theorem andTag_refines_within_envelope
    (n : Nat)
    (sigma : Assignment)
    (witness rest : BitString)
    (frames : List EvalFrame)
    (consumed padding : Nat)
    (hrest : rest.length ≤ n)
    (hframes : (encodeEvalFrames frames).length ≤ n) :
    evalStep sigma
      (needExpr (true :: false :: false :: rest) frames) =
        some (needExpr rest (.andLeft :: frames)) ∧
    ∃ m ≤ checkedStepEnvelope n,
      ({ state := .doneNeed,
         tape :=
           evalCursorStackEndTape witness (consumed + 3) rest
             (encodeEvalFrames (.andLeft :: frames))
             (((padding - 1) - 1) - 1) } :
        EvalStepConfig) ∈
        evalStepCompositeMachine.runBranches m
          [needStart witness consumed
            (true :: false :: false :: rest) frames padding] := by
  obtain ⟨hsem, m, hm, hrun⟩ :=
    andTag_refines_evalStep
      sigma witness rest frames consumed padding
  refine ⟨hsem, m, ?_, hrun⟩
  exact Nat.le_trans hm
    (pushTagCompositeFuel_le_envelope
      n (encodeEvalFrames frames) rest hframes hrest)

theorem orTag_refines_within_envelope
    (n : Nat)
    (sigma : Assignment)
    (witness rest : BitString)
    (frames : List EvalFrame)
    (consumed padding : Nat)
    (hrest : rest.length ≤ n)
    (hframes : (encodeEvalFrames frames).length ≤ n) :
    evalStep sigma
      (needExpr (true :: false :: true :: rest) frames) =
        some (needExpr rest (.orLeft :: frames)) ∧
    ∃ m ≤ checkedStepEnvelope n,
      ({ state := .doneNeed,
         tape :=
           evalCursorStackEndTape witness (consumed + 3) rest
             (encodeEvalFrames (.orLeft :: frames))
             (((padding - 1) - 1) - 1) } :
        EvalStepConfig) ∈
        evalStepCompositeMachine.runBranches m
          [needStart witness consumed
            (true :: false :: true :: rest) frames padding] := by
  obtain ⟨hsem, m, hm, hrun⟩ :=
    orTag_refines_evalStep
      sigma witness rest frames consumed padding
  refine ⟨hsem, m, ?_, hrun⟩
  exact Nat.le_trans hm
    (pushTagCompositeFuel_le_envelope
      n (encodeEvalFrames frames) rest hframes hrest)

theorem inputTag_refines_within_envelope
    (n : Nat)
    (sigma : Assignment)
    (witness tail : BitString)
    (frames : List EvalFrame)
    (consumed padding i : Nat)
    (hi : i < witness.length)
    (hread : witness.getD i false = sigma i)
    (hconsumed : consumed + 3 ≤ n)
    (hindex : i ≤ n)
    (htail : tail.length ≤ n)
    (hframes : (encodeEvalFrames frames).length ≤ n) :
    evalStep sigma
      (needExpr
        (false :: false :: false :: (CanonicalCircuitBits.encodeNat i ++ tail))
        frames) =
      some (haveValue (sigma i) tail frames) ∧
    ∃ m ≤ checkedStepEnvelope n,
      ({ state := .doneValue (sigma i),
         tape :=
           (P01InputNodeRoundTrip.inputAfterReadTarget witness
             (P01InputNodeRoundTrip.consumedAfterInputIndex
               (consumed + 3) i)
             tail (encodeEvalFrames frames) padding).tape } :
        EvalStepConfig) ∈
      evalStepCompositeMachine.runBranches m
        [needStart witness consumed
          (false :: false :: false :: (CanonicalCircuitBits.encodeNat i ++ tail))
          frames padding] := by
  obtain ⟨hsem, m, hm, hrun⟩ :=
    inputTag_refines_evalStep
      sigma witness tail frames consumed padding i hi hread
  refine ⟨hsem, m, ?_, hrun⟩
  exact Nat.le_trans hm
    (inputTagCompositeFuel_le_envelope
      n consumed i tail (encodeEvalFrames frames)
      hconsumed hindex htail hframes)

theorem emptyFrames_refines_within_envelope
    (n : Nat)
    (sigma : Assignment)
    (witness bits : BitString)
    (consumed padding : Nat)
    (v : Bool) :
    evalStep sigma (haveValue v bits []) = none ∧
    ∃ m ≤ checkedStepEnvelope n,
      ({ state := .doneValue v,
         tape :=
           evalCursorStackEndTape witness consumed bits [] padding } :
        EvalStepConfig) ∈
        evalStepCompositeMachine.runBranches m
          [haveStart witness consumed v bits [] padding] := by
  obtain ⟨hsem, m, hm, hrun⟩ :=
    emptyFrames_refines_halt sigma witness bits consumed padding v
  refine ⟨hsem, m, ?_, hrun⟩
  exact Nat.le_trans hm (small_const_le_envelope n 2 (by omega))

theorem negReturn_refines_within_envelope
    (n : Nat)
    (sigma : Assignment)
    (witness bits : BitString)
    (frames : List EvalFrame)
    (consumed padding : Nat)
    (v : Bool) :
    evalStep sigma (haveValue v bits (.neg :: frames)) =
      some (haveValue (!v) bits frames) ∧
    ∃ m ≤ checkedStepEnvelope n,
      ({ state := .doneValue (!v),
         tape :=
           evalCursorStackEndTape witness consumed bits
             (encodeEvalFrames frames) (padding + 3) } :
        EvalStepConfig) ∈
        evalStepCompositeMachine.runBranches m
          [haveStart witness consumed v bits (.neg :: frames) padding] := by
  obtain ⟨hsem, m, hm, hrun⟩ :=
    negReturn_refines_evalStep
      sigma witness bits frames consumed padding v
  refine ⟨hsem, m, ?_, hrun⟩
  exact Nat.le_trans hm (small_const_le_envelope n 9 (by omega))

theorem andRightReturn_refines_within_envelope
    (n : Nat)
    (sigma : Assignment)
    (witness bits : BitString)
    (frames : List EvalFrame)
    (consumed padding : Nat)
    (l v : Bool) :
    evalStep sigma (haveValue v bits (.andRight l :: frames)) =
      some (haveValue (Bool.and l v) bits frames) ∧
    ∃ m ≤ checkedStepEnvelope n,
      ({ state := .doneValue (Bool.and l v),
         tape :=
           evalCursorStackEndTape witness consumed bits
             (encodeEvalFrames frames) (padding + 3) } :
        EvalStepConfig) ∈
        evalStepCompositeMachine.runBranches m
          [haveStart witness consumed v bits (.andRight l :: frames) padding] := by
  obtain ⟨hsem, m, hm, hrun⟩ :=
    andRightReturn_refines_evalStep
      sigma witness bits frames consumed padding l v
  refine ⟨hsem, m, ?_, hrun⟩
  exact Nat.le_trans hm (small_const_le_envelope n 9 (by omega))

theorem orRightReturn_refines_within_envelope
    (n : Nat)
    (sigma : Assignment)
    (witness bits : BitString)
    (frames : List EvalFrame)
    (consumed padding : Nat)
    (l v : Bool) :
    evalStep sigma (haveValue v bits (.orRight l :: frames)) =
      some (haveValue (Bool.or l v) bits frames) ∧
    ∃ m ≤ checkedStepEnvelope n,
      ({ state := .doneValue (Bool.or l v),
         tape :=
           evalCursorStackEndTape witness consumed bits
             (encodeEvalFrames frames) (padding + 3) } :
        EvalStepConfig) ∈
        evalStepCompositeMachine.runBranches m
          [haveStart witness consumed v bits (.orRight l :: frames) padding] := by
  obtain ⟨hsem, m, hm, hrun⟩ :=
    orRightReturn_refines_evalStep
      sigma witness bits frames consumed padding l v
  refine ⟨hsem, m, ?_, hrun⟩
  exact Nat.le_trans hm (small_const_le_envelope n 9 (by omega))

theorem andLeftReturn_refines_within_envelope
    (n : Nat)
    (sigma : Assignment)
    (witness bits : BitString)
    (frames : List EvalFrame)
    (consumed padding : Nat)
    (v : Bool) :
    evalStep sigma (haveValue v bits (.andLeft :: frames)) =
      some (needExpr bits (.andRight v :: frames)) ∧
    ∃ m ≤ checkedStepEnvelope n,
      ({ state := .doneNeed,
         tape :=
           evalCursorStackEndTape witness consumed bits
             (encodeEvalFrames (.andRight v :: frames))
             ((((padding + 3) - 1) - 1) - 1) } :
        EvalStepConfig) ∈
        evalStepCompositeMachine.runBranches m
          [haveStart witness consumed v bits (.andLeft :: frames) padding] := by
  obtain ⟨hsem, m, hm, hrun⟩ :=
    andLeftReturn_refines_evalStep
      sigma witness bits frames consumed padding v
  refine ⟨hsem, m, ?_, hrun⟩
  exact Nat.le_trans hm (small_const_le_envelope n 13 (by omega))

theorem orLeftReturn_refines_within_envelope
    (n : Nat)
    (sigma : Assignment)
    (witness bits : BitString)
    (frames : List EvalFrame)
    (consumed padding : Nat)
    (v : Bool) :
    evalStep sigma (haveValue v bits (.orLeft :: frames)) =
      some (needExpr bits (.orRight v :: frames)) ∧
    ∃ m ≤ checkedStepEnvelope n,
      ({ state := .doneNeed,
         tape :=
           evalCursorStackEndTape witness consumed bits
             (encodeEvalFrames (.orRight v :: frames))
             ((((padding + 3) - 1) - 1) - 1) } :
        EvalStepConfig) ∈
        evalStepCompositeMachine.runBranches m
          [haveStart witness consumed v bits (.orLeft :: frames) padding] := by
  obtain ⟨hsem, m, hm, hrun⟩ :=
    orLeftReturn_refines_evalStep
      sigma witness bits frames consumed padding v
  refine ⟨hsem, m, ?_, hrun⟩
  exact Nat.le_trans hm (small_const_le_envelope n 13 (by omega))

#print axioms MCore.Real.P01EvalStepEnvelope.constFalse_refines_within_envelope
#print axioms MCore.Real.P01EvalStepEnvelope.constTrue_refines_within_envelope
#print axioms MCore.Real.P01EvalStepEnvelope.negTag_refines_within_envelope
#print axioms MCore.Real.P01EvalStepEnvelope.andTag_refines_within_envelope
#print axioms MCore.Real.P01EvalStepEnvelope.orTag_refines_within_envelope
#print axioms MCore.Real.P01EvalStepEnvelope.inputTag_refines_within_envelope
#print axioms MCore.Real.P01EvalStepEnvelope.emptyFrames_refines_within_envelope
#print axioms MCore.Real.P01EvalStepEnvelope.negReturn_refines_within_envelope
#print axioms MCore.Real.P01EvalStepEnvelope.andRightReturn_refines_within_envelope
#print axioms MCore.Real.P01EvalStepEnvelope.orRightReturn_refines_within_envelope
#print axioms MCore.Real.P01EvalStepEnvelope.andLeftReturn_refines_within_envelope
#print axioms MCore.Real.P01EvalStepEnvelope.orLeftReturn_refines_within_envelope

end P01EvalStepEnvelope
end Real
end MCore
