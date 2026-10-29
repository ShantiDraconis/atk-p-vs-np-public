import MCore.Real.P01EvalCursorMachine
import MCore.Real.P01EvalFramePopMachineV2

namespace MCore
namespace Real
namespace P01EvalCursorFramePop

open CanonicalFinalProof
open P01EncodedStackEvaluator
open P01EncodedFrameTape
open P01EvalCursorMachine
open P01EvalFramePopMachineV2
open P01EvalFramePushMachine
open P01FullVerifierPhysicalStackV2
open MachineRunLemmas

/-- Entering one stack cell from the cursor-aware stack-end layout exposes the
top encoded frame bit without touching witness/source/cursor data. -/
theorem popEnter_head_cursor
    (witness unread : BitString)
    (consumed : Nat)
    (v : Bool) (stack : List Bool)
    (padding : Nat) :
    (popEnter
      (evalCursorStackEndTape witness consumed unread
        (v :: stack) padding)).head = some v := by
  simp [popEnter, evalCursorStackEndTape, Tape.move]

/-- Erasing one exposed stack bit restores the canonical cursor-aware stack-end
layout with the same witness, consumed count and unread source. -/
theorem popErase_correct_cursor
    (witness unread : BitString)
    (consumed : Nat)
    (v : Bool) (stack : List Bool)
    (padding : Nat) :
    popErase
      (popEnter
        (evalCursorStackEndTape witness consumed unread
          (v :: stack) padding)) =
      evalCursorStackEndTape witness consumed unread
        stack (padding + 1) := by
  simp [popErase, popEnter, evalCursorStackEndTape, Tape.write, Tape.move,
    List.map_cons, List.append_assoc, List.replicate_succ, Nat.add_comm]

theorem framePop_first_two_cursor
    (witness unread : BitString)
    (consumed : Nat)
    (rest : List Bool) (padding : Nat)
    (b0 : Bool) :
    framePopMachine.run 2
      (framePopConfig
        (evalCursorStackEndTape witness consumed unread
          (b0 :: rest) padding)) =
      { state := FramePopState.gap1 b0,
        tape := evalCursorStackEndTape witness consumed unread
          rest (padding + 1) } := by
  unfold framePopConfig
  rw [show 2 = 1 + 1 by decide, MachineRunLemmas.run_add]
  rw [framePop_start_one _ rfl]
  rw [framePop_read0_one b0 _
    (popEnter_head_cursor witness unread consumed b0 rest padding)]
  rw [popErase_correct_cursor]

theorem framePop_second_two_cursor
    (witness unread : BitString)
    (consumed : Nat)
    (rest : List Bool) (padding : Nat)
    (b0 b1 : Bool) :
    framePopMachine.run 2
      { state := FramePopState.gap1 b0,
        tape := evalCursorStackEndTape witness consumed unread
          (b1 :: rest) padding } =
      { state := FramePopState.gap2 b0 b1,
        tape := evalCursorStackEndTape witness consumed unread
          rest (padding + 1) } := by
  rw [show 2 = 1 + 1 by decide, MachineRunLemmas.run_add]
  rw [framePop_gap1_one b0 _ rfl]
  rw [framePop_read1_one b0 b1 _
    (popEnter_head_cursor witness unread consumed b1 rest padding)]
  rw [popErase_correct_cursor]

theorem framePop_third_two_cursor
    (witness unread : BitString)
    (consumed : Nat)
    (rest : List Bool) (padding : Nat)
    (b0 b1 b2 : Bool) (f : EvalFrame)
    (hdecode : decodeEvalFrame [b0,b1,b2] = some f) :
    framePopMachine.run 2
      { state := FramePopState.gap2 b0 b1,
        tape := evalCursorStackEndTape witness consumed unread
          (b2 :: rest) padding } =
      { state := FramePopState.halt f,
        tape := evalCursorStackEndTape witness consumed unread
          rest (padding + 1) } := by
  rw [show 2 = 1 + 1 by decide, MachineRunLemmas.run_add]
  rw [framePop_gap2_one b0 b1 _ rfl]
  rw [framePop_read2_one b0 b1 b2 f _
    (popEnter_head_cursor witness unread consumed b2 rest padding) hdecode]
  rw [popErase_correct_cursor]

/-- Exact six-step cursor-aware frame pop. -/
theorem framePop_run_six_cursor
    (witness unread : BitString)
    (consumed : Nat)
    (stack : List Bool)
    (padding : Nat)
    (f : EvalFrame) :
    framePopMachine.run 6
      (framePopConfig
        (evalCursorStackEndTape witness consumed unread
          (encodeEvalFrame f ++ stack) padding)) =
      { state := FramePopState.halt f,
        tape := evalCursorStackEndTape witness consumed unread
          stack (padding + 3) } := by
  rw [encodeEvalFrame_eq_bits]
  simp only [List.cons_append, List.nil_append]
  have hdecode :
      decodeEvalFrame [frameBit0 f, frameBit1 f, frameBit2 f] = some f := by
    rw [← encodeEvalFrame_eq_bits]
    exact decodeEvalFrame_encodeEvalFrame f
  rw [show 6 = 2 + (2 + 2) by decide, MachineRunLemmas.run_add]
  rw [framePop_first_two_cursor witness unread consumed
    (frameBit1 f :: frameBit2 f :: stack) padding (frameBit0 f)]
  rw [MachineRunLemmas.run_add]
  rw [framePop_second_two_cursor witness unread consumed
    (frameBit2 f :: stack) (padding + 1) (frameBit0 f) (frameBit1 f)]
  rw [framePop_third_two_cursor witness unread consumed
    stack (padding + 1 + 1)
    (frameBit0 f) (frameBit1 f) (frameBit2 f) f hdecode]

#print axioms MCore.Real.P01EvalCursorFramePop.popErase_correct_cursor
#print axioms MCore.Real.P01EvalCursorFramePop.framePop_run_six_cursor

end P01EvalCursorFramePop
end Real
end MCore
