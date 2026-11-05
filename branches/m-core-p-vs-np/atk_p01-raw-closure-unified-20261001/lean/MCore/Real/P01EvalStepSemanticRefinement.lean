import MCore.Real.P01EvalStepCompositeRun
import MCore.Real.P01EncodedFrameTape

namespace MCore
namespace Real
namespace P01EvalStepSemanticRefinement

open CanonicalFinalProof
open CanonicalCircuitBits
open P01EncodedStackEvaluator
open P01EncodedFrameTape
open P01EvalCursorMachine
open P01NeedExprCompositeNTM
open P01InputNodeRoundTrip
open P01NeedExprCompositeRun
open P01HaveValueCompositeNTM
open P01HaveValueCompositeRun
open P01EvalStepCompositeNTM
open P01EvalStepCompositeRun

/-- Physical start configuration for the semantic `needExpr` arm. -/
def needStart
    (witness : BitString) (consumed : Nat)
    (bits : BitString) (frames : List EvalFrame)
    (padding : Nat) : EvalStepConfig :=
  { state := .need needExprCompositeMachine.initial,
    tape :=
      evalCursorStackEndTape witness consumed bits
        (encodeEvalFrames frames) padding }

/-- Physical start configuration for the semantic `haveValue` arm. -/
def haveStart
    (witness : BitString) (consumed : Nat)
    (v : Bool) (bits : BitString) (frames : List EvalFrame)
    (padding : Nat) : EvalStepConfig :=
  { state := .have (.start v),
    tape :=
      evalCursorStackEndTape witness consumed bits
        (encodeEvalFrames frames) padding }

theorem constFalse_refines_evalStep
    (sigma : Assignment)
    (witness rest : BitString)
    (frames : List EvalFrame)
    (consumed padding : Nat) :
    evalStep sigma
      (needExpr (false :: false :: true :: rest) frames) =
        some (haveValue false rest frames) ∧
    ∃ m ≤ constTagCompositeFuel (encodeEvalFrames frames) rest,
      ({ state := .doneValue false,
         tape :=
           evalCursorStackEndTape witness (consumed + 3)
             rest (encodeEvalFrames frames) padding } : EvalStepConfig) ∈
        evalStepCompositeMachine.runBranches m
          [needStart witness consumed
            (false :: false :: true :: rest) frames padding] := by
  constructor
  · simp [evalStep, needExpr, haveValue]
  · obtain ⟨m, hm, h⟩ :=
      constFalse_reaches_done
        witness rest (encodeEvalFrames frames) consumed padding
    refine ⟨m, hm, ?_⟩
    have hl := need_mem_lift m
      ({ state := needExprCompositeMachine.initial,
         tape :=
           evalCursorStackEndTape witness consumed
             (false :: false :: true :: rest)
             (encodeEvalFrames frames) padding } :
        Configuration NeedExprCompositeState (Option Bool))
      ({ state := .doneValue false,
         tape :=
           evalCursorStackEndTape witness (consumed + 3)
             rest (encodeEvalFrames frames) padding } :
        Configuration NeedExprCompositeState (Option Bool))
      h
    simpa [needStart, liftNeedConfig, needStateEmbed] using hl

theorem constTrue_refines_evalStep
    (sigma : Assignment)
    (witness rest : BitString)
    (frames : List EvalFrame)
    (consumed padding : Nat) :
    evalStep sigma
      (needExpr (false :: true :: false :: rest) frames) =
        some (haveValue true rest frames) ∧
    ∃ m ≤ constTagCompositeFuel (encodeEvalFrames frames) rest,
      ({ state := .doneValue true,
         tape :=
           evalCursorStackEndTape witness (consumed + 3)
             rest (encodeEvalFrames frames) padding } : EvalStepConfig) ∈
        evalStepCompositeMachine.runBranches m
          [needStart witness consumed
            (false :: true :: false :: rest) frames padding] := by
  constructor
  · simp [evalStep, needExpr, haveValue]
  · obtain ⟨m, hm, h⟩ :=
      constTrue_reaches_done
        witness rest (encodeEvalFrames frames) consumed padding
    refine ⟨m, hm, ?_⟩
    have hl := need_mem_lift m
      ({ state := needExprCompositeMachine.initial,
         tape :=
           evalCursorStackEndTape witness consumed
             (false :: true :: false :: rest)
             (encodeEvalFrames frames) padding } :
        Configuration NeedExprCompositeState (Option Bool))
      ({ state := .doneValue true,
         tape :=
           evalCursorStackEndTape witness (consumed + 3)
             rest (encodeEvalFrames frames) padding } :
        Configuration NeedExprCompositeState (Option Bool))
      h
    simpa [needStart, liftNeedConfig, needStateEmbed] using hl

theorem negTag_refines_evalStep
    (sigma : Assignment)
    (witness rest : BitString)
    (frames : List EvalFrame)
    (consumed padding : Nat) :
    evalStep sigma
      (needExpr (false :: true :: true :: rest) frames) =
        some (needExpr rest (.neg :: frames)) ∧
    ∃ m ≤ pushTagCompositeFuel (encodeEvalFrames frames) rest,
      ({ state := .doneNeed,
         tape :=
           evalCursorStackEndTape witness (consumed + 3) rest
             (encodeEvalFrames (.neg :: frames))
             (((padding - 1) - 1) - 1) } : EvalStepConfig) ∈
        evalStepCompositeMachine.runBranches m
          [needStart witness consumed
            (false :: true :: true :: rest) frames padding] := by
  constructor
  · simp [evalStep, needExpr, haveValue]
  · obtain ⟨m, hm, h⟩ :=
      neg_reaches_done
        witness rest (encodeEvalFrames frames) consumed padding
    refine ⟨m, hm, ?_⟩
    have hl := need_mem_lift m
      ({ state := needExprCompositeMachine.initial,
         tape :=
           evalCursorStackEndTape witness consumed
             (false :: true :: true :: rest)
             (encodeEvalFrames frames) padding } :
        Configuration NeedExprCompositeState (Option Bool))
      ({ state := .doneNeed,
         tape :=
           evalCursorStackEndTape witness (consumed + 3) rest
             (encodeEvalFrame .neg ++ encodeEvalFrames frames)
             (((padding - 1) - 1) - 1) } :
        Configuration NeedExprCompositeState (Option Bool))
      h
    simpa [needStart, liftNeedConfig, needStateEmbed,
      encodeEvalFrames] using hl

theorem andTag_refines_evalStep
    (sigma : Assignment)
    (witness rest : BitString)
    (frames : List EvalFrame)
    (consumed padding : Nat) :
    evalStep sigma
      (needExpr (true :: false :: false :: rest) frames) =
        some (needExpr rest (.andLeft :: frames)) ∧
    ∃ m ≤ pushTagCompositeFuel (encodeEvalFrames frames) rest,
      ({ state := .doneNeed,
         tape :=
           evalCursorStackEndTape witness (consumed + 3) rest
             (encodeEvalFrames (.andLeft :: frames))
             (((padding - 1) - 1) - 1) } : EvalStepConfig) ∈
        evalStepCompositeMachine.runBranches m
          [needStart witness consumed
            (true :: false :: false :: rest) frames padding] := by
  constructor
  · simp [evalStep, needExpr, haveValue]
  · obtain ⟨m, hm, h⟩ :=
      and_reaches_done
        witness rest (encodeEvalFrames frames) consumed padding
    refine ⟨m, hm, ?_⟩
    have hl := need_mem_lift m
      ({ state := needExprCompositeMachine.initial,
         tape :=
           evalCursorStackEndTape witness consumed
             (true :: false :: false :: rest)
             (encodeEvalFrames frames) padding } :
        Configuration NeedExprCompositeState (Option Bool))
      ({ state := .doneNeed,
         tape :=
           evalCursorStackEndTape witness (consumed + 3) rest
             (encodeEvalFrame .andLeft ++ encodeEvalFrames frames)
             (((padding - 1) - 1) - 1) } :
        Configuration NeedExprCompositeState (Option Bool))
      h
    simpa [needStart, liftNeedConfig, needStateEmbed,
      encodeEvalFrames] using hl

theorem orTag_refines_evalStep
    (sigma : Assignment)
    (witness rest : BitString)
    (frames : List EvalFrame)
    (consumed padding : Nat) :
    evalStep sigma
      (needExpr (true :: false :: true :: rest) frames) =
        some (needExpr rest (.orLeft :: frames)) ∧
    ∃ m ≤ pushTagCompositeFuel (encodeEvalFrames frames) rest,
      ({ state := .doneNeed,
         tape :=
           evalCursorStackEndTape witness (consumed + 3) rest
             (encodeEvalFrames (.orLeft :: frames))
             (((padding - 1) - 1) - 1) } : EvalStepConfig) ∈
        evalStepCompositeMachine.runBranches m
          [needStart witness consumed
            (true :: false :: true :: rest) frames padding] := by
  constructor
  · simp [evalStep, needExpr, haveValue]
  · obtain ⟨m, hm, h⟩ :=
      or_reaches_done
        witness rest (encodeEvalFrames frames) consumed padding
    refine ⟨m, hm, ?_⟩
    have hl := need_mem_lift m
      ({ state := needExprCompositeMachine.initial,
         tape :=
           evalCursorStackEndTape witness consumed
             (true :: false :: true :: rest)
             (encodeEvalFrames frames) padding } :
        Configuration NeedExprCompositeState (Option Bool))
      ({ state := .doneNeed,
         tape :=
           evalCursorStackEndTape witness (consumed + 3) rest
             (encodeEvalFrame .orLeft ++ encodeEvalFrames frames)
             (((padding - 1) - 1) - 1) } :
        Configuration NeedExprCompositeState (Option Bool))
      h
    simpa [needStart, liftNeedConfig, needStateEmbed,
      encodeEvalFrames] using hl

theorem emptyFrames_refines_halt
    (sigma : Assignment)
    (witness bits : BitString)
    (consumed padding : Nat)
    (v : Bool) :
    evalStep sigma (haveValue v bits []) = none ∧
    ∃ m ≤ 2,
      ({ state := .doneValue v,
         tape :=
           evalCursorStackEndTape witness consumed bits [] padding } :
        EvalStepConfig) ∈
        evalStepCompositeMachine.runBranches m
          [haveStart witness consumed v bits [] padding] := by
  constructor
  · rfl
  · obtain ⟨m, hm, h⟩ :=
      empty_frames_reaches_doneValue
        witness bits consumed padding v
    refine ⟨m, hm, ?_⟩
    have hl := have_mem_lift m
      ({ state := .start v,
         tape :=
           evalCursorStackEndTape witness consumed bits [] padding } :
        Configuration HaveValueCompositeState (Option Bool))
      ({ state := .doneValue v,
         tape :=
           evalCursorStackEndTape witness consumed bits [] padding } :
        Configuration HaveValueCompositeState (Option Bool))
      h
    simpa [haveStart, liftHaveConfig, haveStateEmbed] using hl

theorem negReturn_refines_evalStep
    (sigma : Assignment)
    (witness bits : BitString)
    (frames : List EvalFrame)
    (consumed padding : Nat)
    (v : Bool) :
    evalStep sigma (haveValue v bits (.neg :: frames)) =
      some (haveValue (!v) bits frames) ∧
    ∃ m ≤ 9,
      ({ state := .doneValue (!v),
         tape :=
           evalCursorStackEndTape witness consumed bits
             (encodeEvalFrames frames) (padding + 3) } :
        EvalStepConfig) ∈
        evalStepCompositeMachine.runBranches m
          [haveStart witness consumed v bits (.neg :: frames) padding] := by
  constructor
  · rfl
  · obtain ⟨m, hm, h⟩ :=
      neg_reaches_doneValue
        witness bits (encodeEvalFrames frames)
        consumed padding v
    refine ⟨m, hm, ?_⟩
    have hl := have_mem_lift m
      ({ state := .start v,
         tape :=
           evalCursorStackEndTape witness consumed bits
             (encodeEvalFrame .neg ++ encodeEvalFrames frames) padding } :
        Configuration HaveValueCompositeState (Option Bool))
      ({ state := .doneValue (!v),
         tape :=
           evalCursorStackEndTape witness consumed bits
             (encodeEvalFrames frames) (padding + 3) } :
        Configuration HaveValueCompositeState (Option Bool))
      h
    simpa [haveStart, liftHaveConfig, haveStateEmbed,
      encodeEvalFrames] using hl

theorem andRightReturn_refines_evalStep
    (sigma : Assignment)
    (witness bits : BitString)
    (frames : List EvalFrame)
    (consumed padding : Nat)
    (l v : Bool) :
    evalStep sigma (haveValue v bits (.andRight l :: frames)) =
      some (haveValue (Bool.and l v) bits frames) ∧
    ∃ m ≤ 9,
      ({ state := .doneValue (Bool.and l v),
         tape :=
           evalCursorStackEndTape witness consumed bits
             (encodeEvalFrames frames) (padding + 3) } :
        EvalStepConfig) ∈
        evalStepCompositeMachine.runBranches m
          [haveStart witness consumed v bits (.andRight l :: frames) padding] := by
  constructor
  · rfl
  · obtain ⟨m, hm, h⟩ :=
      andRight_reaches_doneValue
        witness bits (encodeEvalFrames frames)
        consumed padding l v
    refine ⟨m, hm, ?_⟩
    have hl := have_mem_lift m
      ({ state := .start v,
         tape :=
           evalCursorStackEndTape witness consumed bits
             (encodeEvalFrame (.andRight l) ++ encodeEvalFrames frames)
             padding } :
        Configuration HaveValueCompositeState (Option Bool))
      ({ state := .doneValue (Bool.and l v),
         tape :=
           evalCursorStackEndTape witness consumed bits
             (encodeEvalFrames frames) (padding + 3) } :
        Configuration HaveValueCompositeState (Option Bool))
      h
    simpa [haveStart, liftHaveConfig, haveStateEmbed,
      encodeEvalFrames] using hl

theorem orRightReturn_refines_evalStep
    (sigma : Assignment)
    (witness bits : BitString)
    (frames : List EvalFrame)
    (consumed padding : Nat)
    (l v : Bool) :
    evalStep sigma (haveValue v bits (.orRight l :: frames)) =
      some (haveValue (Bool.or l v) bits frames) ∧
    ∃ m ≤ 9,
      ({ state := .doneValue (Bool.or l v),
         tape :=
           evalCursorStackEndTape witness consumed bits
             (encodeEvalFrames frames) (padding + 3) } :
        EvalStepConfig) ∈
        evalStepCompositeMachine.runBranches m
          [haveStart witness consumed v bits (.orRight l :: frames) padding] := by
  constructor
  · rfl
  · obtain ⟨m, hm, h⟩ :=
      orRight_reaches_doneValue
        witness bits (encodeEvalFrames frames)
        consumed padding l v
    refine ⟨m, hm, ?_⟩
    have hl := have_mem_lift m
      ({ state := .start v,
         tape :=
           evalCursorStackEndTape witness consumed bits
             (encodeEvalFrame (.orRight l) ++ encodeEvalFrames frames)
             padding } :
        Configuration HaveValueCompositeState (Option Bool))
      ({ state := .doneValue (Bool.or l v),
         tape :=
           evalCursorStackEndTape witness consumed bits
             (encodeEvalFrames frames) (padding + 3) } :
        Configuration HaveValueCompositeState (Option Bool))
      h
    simpa [haveStart, liftHaveConfig, haveStateEmbed,
      encodeEvalFrames] using hl

theorem andLeftReturn_refines_evalStep
    (sigma : Assignment)
    (witness bits : BitString)
    (frames : List EvalFrame)
    (consumed padding : Nat)
    (v : Bool) :
    evalStep sigma (haveValue v bits (.andLeft :: frames)) =
      some (needExpr bits (.andRight v :: frames)) ∧
    ∃ m ≤ 13,
      ({ state := .doneNeed,
         tape :=
           evalCursorStackEndTape witness consumed bits
             (encodeEvalFrames (.andRight v :: frames))
             ((((padding + 3) - 1) - 1) - 1) } :
        EvalStepConfig) ∈
        evalStepCompositeMachine.runBranches m
          [haveStart witness consumed v bits (.andLeft :: frames) padding] := by
  constructor
  · rfl
  · obtain ⟨m, hm, h⟩ :=
      andLeft_reaches_doneNeed
        witness bits (encodeEvalFrames frames)
        consumed padding v
    refine ⟨m, hm, ?_⟩
    have hl := have_mem_lift m
      ({ state := .start v,
         tape :=
           evalCursorStackEndTape witness consumed bits
             (encodeEvalFrame .andLeft ++ encodeEvalFrames frames)
             padding } :
        Configuration HaveValueCompositeState (Option Bool))
      ({ state := .doneNeed,
         tape :=
           evalCursorStackEndTape witness consumed bits
             (encodeEvalFrame (.andRight v) ++ encodeEvalFrames frames)
             ((((padding + 3) - 1) - 1) - 1) } :
        Configuration HaveValueCompositeState (Option Bool))
      h
    simpa [haveStart, liftHaveConfig, haveStateEmbed,
      encodeEvalFrames] using hl

theorem orLeftReturn_refines_evalStep
    (sigma : Assignment)
    (witness bits : BitString)
    (frames : List EvalFrame)
    (consumed padding : Nat)
    (v : Bool) :
    evalStep sigma (haveValue v bits (.orLeft :: frames)) =
      some (needExpr bits (.orRight v :: frames)) ∧
    ∃ m ≤ 13,
      ({ state := .doneNeed,
         tape :=
           evalCursorStackEndTape witness consumed bits
             (encodeEvalFrames (.orRight v :: frames))
             ((((padding + 3) - 1) - 1) - 1) } :
        EvalStepConfig) ∈
        evalStepCompositeMachine.runBranches m
          [haveStart witness consumed v bits (.orLeft :: frames) padding] := by
  constructor
  · rfl
  · obtain ⟨m, hm, h⟩ :=
      orLeft_reaches_doneNeed
        witness bits (encodeEvalFrames frames)
        consumed padding v
    refine ⟨m, hm, ?_⟩
    have hl := have_mem_lift m
      ({ state := .start v,
         tape :=
           evalCursorStackEndTape witness consumed bits
             (encodeEvalFrame .orLeft ++ encodeEvalFrames frames)
             padding } :
        Configuration HaveValueCompositeState (Option Bool))
      ({ state := .doneNeed,
         tape :=
           evalCursorStackEndTape witness consumed bits
             (encodeEvalFrame (.orRight v) ++ encodeEvalFrames frames)
             ((((padding + 3) - 1) - 1) - 1) } :
        Configuration HaveValueCompositeState (Option Bool))
      h
    simpa [haveStart, liftHaveConfig, haveStateEmbed,
      encodeEvalFrames] using hl

/-- The remaining physical 000 case.

The premise `hread` is not a computational assumption: it is exactly the
representation relation saying that the physical witness bit at index `i`
encodes the semantic assignment value `sigma i`. -/
theorem inputTag_refines_evalStep
    (sigma : Assignment)
    (witness tail : BitString)
    (frames : List EvalFrame)
    (consumed padding i : Nat)
    (hi : i < witness.length)
    (hread : witness.getD i false = sigma i) :
    evalStep sigma
      (needExpr
        (false :: false :: false :: (encodeNat i ++ tail))
        frames) =
      some (haveValue (sigma i) tail frames) ∧
    ∃ m ≤ inputTagCompositeFuel consumed i tail
        (encodeEvalFrames frames),
      ({ state := .doneValue (sigma i),
         tape :=
           (inputAfterReadTarget witness
             (consumedAfterInputIndex (consumed + 3) i)
             tail (encodeEvalFrames frames) padding).tape } :
        EvalStepConfig) ∈
      evalStepCompositeMachine.runBranches m
        [needStart witness consumed
          (false :: false :: false :: (encodeNat i ++ tail))
          frames padding] := by
  constructor
  · simp [evalStep, needExpr, haveValue,
      decodeNat_encodeNat_append]
  · obtain ⟨m, hm, h⟩ :=
      input_reaches_done
        witness tail (encodeEvalFrames frames)
        consumed padding i hi
    refine ⟨m, hm, ?_⟩
    have hl := need_mem_lift m
      ({ state := needExprCompositeMachine.initial,
         tape :=
           evalCursorStackEndTape witness consumed
             (false :: false :: false :: (encodeNat i ++ tail))
             (encodeEvalFrames frames) padding } :
        Configuration NeedExprCompositeState (Option Bool))
      ({ state := .doneValue (witness.getD i false),
         tape :=
           (inputAfterReadTarget witness
             (consumedAfterInputIndex (consumed + 3) i)
             tail (encodeEvalFrames frames) padding).tape } :
        Configuration NeedExprCompositeState (Option Bool))
      h
    rw [hread] at hl
    simpa [needStart, liftNeedConfig, needStateEmbed] using hl

#print axioms MCore.Real.P01EvalStepSemanticRefinement.inputTag_refines_evalStep

#print axioms MCore.Real.P01EvalStepSemanticRefinement.constFalse_refines_evalStep
#print axioms MCore.Real.P01EvalStepSemanticRefinement.constTrue_refines_evalStep
#print axioms MCore.Real.P01EvalStepSemanticRefinement.negTag_refines_evalStep
#print axioms MCore.Real.P01EvalStepSemanticRefinement.andTag_refines_evalStep
#print axioms MCore.Real.P01EvalStepSemanticRefinement.orTag_refines_evalStep
#print axioms MCore.Real.P01EvalStepSemanticRefinement.emptyFrames_refines_halt
#print axioms MCore.Real.P01EvalStepSemanticRefinement.negReturn_refines_evalStep
#print axioms MCore.Real.P01EvalStepSemanticRefinement.andRightReturn_refines_evalStep
#print axioms MCore.Real.P01EvalStepSemanticRefinement.orRightReturn_refines_evalStep
#print axioms MCore.Real.P01EvalStepSemanticRefinement.andLeftReturn_refines_evalStep
#print axioms MCore.Real.P01EvalStepSemanticRefinement.orLeftReturn_refines_evalStep

end P01EvalStepSemanticRefinement
end Real
end MCore
