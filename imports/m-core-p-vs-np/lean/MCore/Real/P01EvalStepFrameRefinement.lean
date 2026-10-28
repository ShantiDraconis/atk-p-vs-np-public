import MCore.Real.P01EvalFramePushMachine
import MCore.Real.P01EvalFramePopMachine

namespace MCore
namespace Real
namespace P01EvalStepFrameRefinement

open CanonicalFinalProof
open P01EncodedStackEvaluator
open P01EncodedFrameTape
open P01FullVerifierPhysicalStackV2
open P01EvalFramePushMachine
open P01EvalFramePopMachine

/-- Exact physical refinement of semantic frame-stack push: three TM steps
prepend precisely the canonical three-bit code of the new EvalFrame. -/
theorem push_refines_frame_cons
    (witness source : BitString)
    (frames : List EvalFrame)
    (padding : Nat)
    (f : EvalFrame) :
    let final :=
      framePushMachine.run 3
        (framePushConfig f
          (physicalStackV2Tape witness source
            (encodeEvalFrames frames) padding))
    final.state = .halt ∧
      final.tape =
        physicalStackV2Tape witness source
          (encodeEvalFrames (f :: frames))
          (((padding - 1) - 1) - 1) := by
  dsimp
  simpa [encodeEvalFrames] using
    framePush_run_three witness source (encodeEvalFrames frames) padding f

/-- Exact physical refinement of semantic frame-stack pop/read: four TM steps
decode the head frame, erase exactly its three-bit code, and restore the
canonical physical representation of the tail frame stack. -/
theorem pop_refines_frame_tail
    (witness source : BitString)
    (frames : List EvalFrame)
    (padding : Nat)
    (f : EvalFrame) :
    let final :=
      framePopMachine.run 4
        (framePopConfig
          (physicalStackV2Tape witness source
            (encodeEvalFrames (f :: frames)) padding))
    final.state = .halt f ∧
      final.tape =
        physicalStackV2Tape witness source
          (encodeEvalFrames frames) (padding + 3) := by
  dsimp
  simpa [encodeEvalFrames] using
    framePop_run_four witness source (encodeEvalFrames frames) padding f

/-- The semantic NOT-tag transition and its physical frame-stack action agree:
the logical step pushes .neg and the fixed physical machine pushes exactly the
canonical .neg frame code. -/
theorem evalStep_not_tag_refined
    (sigma : Assignment)
    (rest witness source : BitString)
    (frames : List EvalFrame)
    (padding : Nat) :
    evalStep sigma
      (needExpr (false :: true :: true :: rest) frames) =
        some (needExpr rest (.neg :: frames)) ∧
    let final :=
      framePushMachine.run 3
        (framePushConfig .neg
          (physicalStackV2Tape witness source
            (encodeEvalFrames frames) padding))
    final.state = .halt ∧
      final.tape =
        physicalStackV2Tape witness source
          (encodeEvalFrames (.neg :: frames))
          (((padding - 1) - 1) - 1) := by
  constructor
  · simp [evalStep, needExpr]
  · exact push_refines_frame_cons witness source frames padding .neg

/-- The semantic AND-tag transition and its physical frame-stack action agree. -/
theorem evalStep_and_tag_refined
    (sigma : Assignment)
    (rest witness source : BitString)
    (frames : List EvalFrame)
    (padding : Nat) :
    evalStep sigma
      (needExpr (true :: false :: false :: rest) frames) =
        some (needExpr rest (.andLeft :: frames)) ∧
    let final :=
      framePushMachine.run 3
        (framePushConfig .andLeft
          (physicalStackV2Tape witness source
            (encodeEvalFrames frames) padding))
    final.state = .halt ∧
      final.tape =
        physicalStackV2Tape witness source
          (encodeEvalFrames (.andLeft :: frames))
          (((padding - 1) - 1) - 1) := by
  constructor
  · simp [evalStep, needExpr]
  · exact push_refines_frame_cons witness source frames padding .andLeft

/-- The semantic OR-tag transition and its physical frame-stack action agree. -/
theorem evalStep_or_tag_refined
    (sigma : Assignment)
    (rest witness source : BitString)
    (frames : List EvalFrame)
    (padding : Nat) :
    evalStep sigma
      (needExpr (true :: false :: true :: rest) frames) =
        some (needExpr rest (.orLeft :: frames)) ∧
    let final :=
      framePushMachine.run 3
        (framePushConfig .orLeft
          (physicalStackV2Tape witness source
            (encodeEvalFrames frames) padding))
    final.state = .halt ∧
      final.tape =
        physicalStackV2Tape witness source
          (encodeEvalFrames (.orLeft :: frames))
          (((padding - 1) - 1) - 1) := by
  constructor
  · simp [evalStep, needExpr]
  · exact push_refines_frame_cons witness source frames padding .orLeft

/-- Returning through a semantic frame is physically readable/removable with
the already-certified fixed pop machine.  This theorem covers every EvalFrame
constructor and is the common first half of neg/and/or return refinement. -/
theorem evalStep_return_frame_physically_decodable
    (witness source : BitString)
    (frames : List EvalFrame)
    (padding : Nat)
    (f : EvalFrame) :
    let final :=
      framePopMachine.run 4
        (framePopConfig
          (physicalStackV2Tape witness source
            (encodeEvalFrames (f :: frames)) padding))
    final.state = .halt f ∧
      PhysicalStackRepV2 final.tape witness source
        (encodeEvalFrames frames) := by
  dsimp
  have h :=
    framePop_run_four_rep witness source
      (encodeEvalFrames frames) padding f
  simpa [encodeEvalFrames] using h

#print axioms MCore.Real.P01EvalStepFrameRefinement.push_refines_frame_cons
#print axioms MCore.Real.P01EvalStepFrameRefinement.pop_refines_frame_tail
#print axioms MCore.Real.P01EvalStepFrameRefinement.evalStep_not_tag_refined
#print axioms MCore.Real.P01EvalStepFrameRefinement.evalStep_and_tag_refined
#print axioms MCore.Real.P01EvalStepFrameRefinement.evalStep_or_tag_refined
#print axioms MCore.Real.P01EvalStepFrameRefinement.evalStep_return_frame_physically_decodable


/-- Returning through negation: the semantic transition only updates the
finite-control Boolean value; the physical tape action is exactly one frame
pop. -/
theorem evalStep_neg_return_refined
    (sigma : Assignment)
    (v : Bool)
    (bits witness source : BitString)
    (frames : List EvalFrame)
    (padding : Nat) :
    evalStep sigma
      (haveValue v bits (.neg :: frames)) =
        some (haveValue (!v) bits frames) ∧
    let final :=
      framePopMachine.run 4
        (framePopConfig
          (physicalStackV2Tape witness source
            (encodeEvalFrames (.neg :: frames)) padding))
    final.state = .halt .neg ∧
      final.tape =
        physicalStackV2Tape witness source
          (encodeEvalFrames frames) (padding + 3) := by
  constructor
  · rfl
  · exact pop_refines_frame_tail witness source frames padding .neg

/-- Returning from the left operand of AND: semantic control replaces
.andLeft by .andRight l; physically this is one certified pop followed by one
certified push of the finite frame carrying l. -/
theorem evalStep_andLeft_return_refined
    (sigma : Assignment)
    (l : Bool)
    (bits witness source : BitString)
    (frames : List EvalFrame)
    (padding : Nat) :
    evalStep sigma
      (haveValue l bits (.andLeft :: frames)) =
        some (needExpr bits (.andRight l :: frames)) ∧
    let popped :=
      framePopMachine.run 4
        (framePopConfig
          (physicalStackV2Tape witness source
            (encodeEvalFrames (.andLeft :: frames)) padding))
    let pushed :=
      framePushMachine.run 3
        (framePushConfig (.andRight l) popped.tape)
    popped.state = .halt .andLeft ∧
      pushed.state = .halt ∧
      pushed.tape =
        physicalStackV2Tape witness source
          (encodeEvalFrames (.andRight l :: frames))
          ((((padding + 3) - 1) - 1) - 1) := by
  constructor
  · rfl
  · dsimp
    have hp := pop_refines_frame_tail witness source frames padding .andLeft
    rcases hp with ⟨hps, hpt⟩
    have hpt' :
        (framePopMachine.run 4
          (framePopConfig
            (physicalStackV2Tape witness source
              (encodeEvalFrame .andLeft ++ encodeEvalFrames frames) padding))).tape =
          physicalStackV2Tape witness source
            (encodeEvalFrames frames) (padding + 3) := by
      simpa [encodeEvalFrames] using hpt
    rw [hpt']
    have hq :=
      push_refines_frame_cons witness source frames (padding + 3) (.andRight l)
    exact ⟨by simpa [encodeEvalFrames] using hps, hq.1, by simpa using hq.2⟩

/-- Returning from the left operand of OR: identical physical pop/push pattern
with the .orRight l continuation frame. -/
theorem evalStep_orLeft_return_refined
    (sigma : Assignment)
    (l : Bool)
    (bits witness source : BitString)
    (frames : List EvalFrame)
    (padding : Nat) :
    evalStep sigma
      (haveValue l bits (.orLeft :: frames)) =
        some (needExpr bits (.orRight l :: frames)) ∧
    let popped :=
      framePopMachine.run 4
        (framePopConfig
          (physicalStackV2Tape witness source
            (encodeEvalFrames (.orLeft :: frames)) padding))
    let pushed :=
      framePushMachine.run 3
        (framePushConfig (.orRight l) popped.tape)
    popped.state = .halt .orLeft ∧
      pushed.state = .halt ∧
      pushed.tape =
        physicalStackV2Tape witness source
          (encodeEvalFrames (.orRight l :: frames))
          ((((padding + 3) - 1) - 1) - 1) := by
  constructor
  · rfl
  · dsimp
    have hp := pop_refines_frame_tail witness source frames padding .orLeft
    rcases hp with ⟨hps, hpt⟩
    have hpt' :
        (framePopMachine.run 4
          (framePopConfig
            (physicalStackV2Tape witness source
              (encodeEvalFrame .orLeft ++ encodeEvalFrames frames) padding))).tape =
          physicalStackV2Tape witness source
            (encodeEvalFrames frames) (padding + 3) := by
      simpa [encodeEvalFrames] using hpt
    rw [hpt']
    have hq :=
      push_refines_frame_cons witness source frames (padding + 3) (.orRight l)
    exact ⟨by simpa [encodeEvalFrames] using hps, hq.1, by simpa using hq.2⟩

/-- Returning from the right operand of AND: the stored left bit is already
finite-control data in the frame; after physical pop, the Boolean result is a
finite-control computation and no further tape mutation is required. -/
theorem evalStep_andRight_return_refined
    (sigma : Assignment)
    (l r : Bool)
    (bits witness source : BitString)
    (frames : List EvalFrame)
    (padding : Nat) :
    evalStep sigma
      (haveValue r bits (.andRight l :: frames)) =
        some (haveValue (Bool.and l r) bits frames) ∧
    let final :=
      framePopMachine.run 4
        (framePopConfig
          (physicalStackV2Tape witness source
            (encodeEvalFrames (.andRight l :: frames)) padding))
    final.state = .halt (.andRight l) ∧
      final.tape =
        physicalStackV2Tape witness source
          (encodeEvalFrames frames) (padding + 3) := by
  constructor
  · rfl
  · exact pop_refines_frame_tail witness source frames padding (.andRight l)

/-- Returning from the right operand of OR. -/
theorem evalStep_orRight_return_refined
    (sigma : Assignment)
    (l r : Bool)
    (bits witness source : BitString)
    (frames : List EvalFrame)
    (padding : Nat) :
    evalStep sigma
      (haveValue r bits (.orRight l :: frames)) =
        some (haveValue (Bool.or l r) bits frames) ∧
    let final :=
      framePopMachine.run 4
        (framePopConfig
          (physicalStackV2Tape witness source
            (encodeEvalFrames (.orRight l :: frames)) padding))
    final.state = .halt (.orRight l) ∧
      final.tape =
        physicalStackV2Tape witness source
          (encodeEvalFrames frames) (padding + 3) := by
  constructor
  · rfl
  · exact pop_refines_frame_tail witness source frames padding (.orRight l)

#print axioms MCore.Real.P01EvalStepFrameRefinement.evalStep_neg_return_refined
#print axioms MCore.Real.P01EvalStepFrameRefinement.evalStep_andLeft_return_refined
#print axioms MCore.Real.P01EvalStepFrameRefinement.evalStep_orLeft_return_refined
#print axioms MCore.Real.P01EvalStepFrameRefinement.evalStep_andRight_return_refined
#print axioms MCore.Real.P01EvalStepFrameRefinement.evalStep_orRight_return_refined

end P01EvalStepFrameRefinement
end Real
end MCore
