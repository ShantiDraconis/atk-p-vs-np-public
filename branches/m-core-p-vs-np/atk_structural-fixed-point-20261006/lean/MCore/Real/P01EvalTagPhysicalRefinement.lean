import MCore.Real.P01EvalCursorConsume
import MCore.Real.P01EvalCursorFramePush
import MCore.Real.P01EncodedStackEvaluator

namespace MCore
namespace Real
namespace P01EvalTagPhysicalRefinement

open CanonicalFinalProof
open P01EncodedStackEvaluator
open P01EncodedFrameTape
open P01EvalCursorMachine
open P01EvalCursorConsume
open P01EvalCursorFramePush
open P01EvalFramePushMachine

/-- Three physical source-bit consumptions followed by one certified frame push.
This is the common physical action for NOT/AND/OR prefix tags. -/
theorem consumeThree_then_push_frame
    (witness : BitString)
    (consumed : Nat)
    (b0 b1 b2 : Bool)
    (rest : BitString)
    (frames : List EvalFrame)
    (padding : Nat)
    (f : EvalFrame) :
    let consumedTape :=
      consumeThreeTape witness consumed
        (b0 :: b1 :: b2 :: rest)
        (encodeEvalFrames frames) padding
    let final :=
      framePushMachine.run 3
        (framePushConfig f consumedTape)
    final.state = .halt ∧
      final.tape =
        evalCursorStackEndTape witness (consumed + 3) rest
          (encodeEvalFrame f ++ encodeEvalFrames frames)
          (((padding - 1) - 1) - 1) := by
  dsimp
  rw [consumeThreeTape_correct]
  exact
    framePush_run_three_cursor
      witness rest (encodeEvalFrames frames)
      (consumed + 3) padding f

/-- Constant false: semantic evalStep and concrete physical tag consumption
agree exactly.  No frame mutation is required. -/
theorem evalStep_const_false_cursor_refined
    (sigma : Assignment)
    (witness : BitString)
    (consumed : Nat)
    (rest : BitString)
    (frames : List EvalFrame)
    (padding : Nat) :
    evalStep sigma
      (needExpr (false :: false :: true :: rest) frames) =
        some (haveValue false rest frames) ∧
    consumeThreeTape witness consumed
      (false :: false :: true :: rest)
      (encodeEvalFrames frames) padding =
        evalCursorStackEndTape witness (consumed + 3) rest
          (encodeEvalFrames frames) padding := by
  constructor
  · simp [evalStep, needExpr, haveValue]
  · exact
      consumeThreeTape_correct witness consumed
        false false true rest (encodeEvalFrames frames) padding

/-- Constant true: semantic evalStep and concrete physical tag consumption
agree exactly. -/
theorem evalStep_const_true_cursor_refined
    (sigma : Assignment)
    (witness : BitString)
    (consumed : Nat)
    (rest : BitString)
    (frames : List EvalFrame)
    (padding : Nat) :
    evalStep sigma
      (needExpr (false :: true :: false :: rest) frames) =
        some (haveValue true rest frames) ∧
    consumeThreeTape witness consumed
      (false :: true :: false :: rest)
      (encodeEvalFrames frames) padding =
        evalCursorStackEndTape witness (consumed + 3) rest
          (encodeEvalFrames frames) padding := by
  constructor
  · simp [evalStep, needExpr, haveValue]
  · exact
      consumeThreeTape_correct witness consumed
        false true false rest (encodeEvalFrames frames) padding

/-- NOT prefix tag: consume exactly three source bits and push exactly the
canonical negation continuation frame. -/
theorem evalStep_not_tag_cursor_refined
    (sigma : Assignment)
    (witness : BitString)
    (consumed : Nat)
    (rest : BitString)
    (frames : List EvalFrame)
    (padding : Nat) :
    evalStep sigma
      (needExpr (false :: true :: true :: rest) frames) =
        some (needExpr rest (.neg :: frames)) ∧
    let consumedTape :=
      consumeThreeTape witness consumed
        (false :: true :: true :: rest)
        (encodeEvalFrames frames) padding
    let final :=
      framePushMachine.run 3
        (framePushConfig .neg consumedTape)
    final.state = .halt ∧
      final.tape =
        evalCursorStackEndTape witness (consumed + 3) rest
          (encodeEvalFrame .neg ++ encodeEvalFrames frames)
          (((padding - 1) - 1) - 1) := by
  constructor
  · simp [evalStep, needExpr, haveValue]
  · exact
      consumeThree_then_push_frame
        witness consumed false true true rest frames padding .neg

/-- AND prefix tag: consume exactly three source bits and push the left-operand
continuation frame. -/
theorem evalStep_and_tag_cursor_refined
    (sigma : Assignment)
    (witness : BitString)
    (consumed : Nat)
    (rest : BitString)
    (frames : List EvalFrame)
    (padding : Nat) :
    evalStep sigma
      (needExpr (true :: false :: false :: rest) frames) =
        some (needExpr rest (.andLeft :: frames)) ∧
    let consumedTape :=
      consumeThreeTape witness consumed
        (true :: false :: false :: rest)
        (encodeEvalFrames frames) padding
    let final :=
      framePushMachine.run 3
        (framePushConfig .andLeft consumedTape)
    final.state = .halt ∧
      final.tape =
        evalCursorStackEndTape witness (consumed + 3) rest
          (encodeEvalFrame .andLeft ++ encodeEvalFrames frames)
          (((padding - 1) - 1) - 1) := by
  constructor
  · simp [evalStep, needExpr, haveValue]
  · exact
      consumeThree_then_push_frame
        witness consumed true false false rest frames padding .andLeft

/-- OR prefix tag: consume exactly three source bits and push the left-operand
continuation frame. -/
theorem evalStep_or_tag_cursor_refined
    (sigma : Assignment)
    (witness : BitString)
    (consumed : Nat)
    (rest : BitString)
    (frames : List EvalFrame)
    (padding : Nat) :
    evalStep sigma
      (needExpr (true :: false :: true :: rest) frames) =
        some (needExpr rest (.orLeft :: frames)) ∧
    let consumedTape :=
      consumeThreeTape witness consumed
        (true :: false :: true :: rest)
        (encodeEvalFrames frames) padding
    let final :=
      framePushMachine.run 3
        (framePushConfig .orLeft consumedTape)
    final.state = .halt ∧
      final.tape =
        evalCursorStackEndTape witness (consumed + 3) rest
          (encodeEvalFrame .orLeft ++ encodeEvalFrames frames)
          (((padding - 1) - 1) - 1) := by
  constructor
  · simp [evalStep, needExpr, haveValue]
  · exact
      consumeThree_then_push_frame
        witness consumed true false true rest frames padding .orLeft

#print axioms MCore.Real.P01EvalTagPhysicalRefinement.consumeThree_then_push_frame
#print axioms MCore.Real.P01EvalTagPhysicalRefinement.evalStep_const_false_cursor_refined
#print axioms MCore.Real.P01EvalTagPhysicalRefinement.evalStep_const_true_cursor_refined
#print axioms MCore.Real.P01EvalTagPhysicalRefinement.evalStep_not_tag_cursor_refined
#print axioms MCore.Real.P01EvalTagPhysicalRefinement.evalStep_and_tag_cursor_refined
#print axioms MCore.Real.P01EvalTagPhysicalRefinement.evalStep_or_tag_cursor_refined

end P01EvalTagPhysicalRefinement
end Real
end MCore
