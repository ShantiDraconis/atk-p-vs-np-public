import MCore.Real.P01EvalCursorMachine
import MCore.Real.P01EvalFramePushMachine

namespace MCore
namespace Real
namespace P01EvalCursorFramePush

open CanonicalFinalProof
open P01EncodedStackEvaluator
open P01EncodedFrameTape
open P01EvalCursorMachine
open P01EvalFramePushMachine
open P01FullVerifierPhysicalStackV2
open MachineRunLemmas

/-- One Boolean stack push preserves the entire cursor representation:
only the finite frame-stack prefix and right blank padding change. -/
theorem pushStep_evalCursorStackEndTape
    (witness unread frameStack : BitString)
    (consumed padding : Nat) (b : Bool) :
    pushStep b
      (evalCursorStackEndTape
        witness consumed unread frameStack padding) =
      evalCursorStackEndTape
        witness consumed unread (b :: frameStack) (padding - 1) := by
  cases padding with
  | zero =>
      simp [pushStep, evalCursorStackEndTape, Tape.write, Tape.move,
        List.append_assoc]
  | succ n =>
      simp [pushStep, evalCursorStackEndTape, Tape.write, Tape.move,
        List.replicate_succ, Nat.succ_sub_one, List.append_assoc]

/-- The already-certified fixed three-step frame writer works unchanged on the
cursor-aware stack-end representation.  It preserves witness, consumed count,
and unread source exactly. -/
theorem framePush_run_three_cursor
    (witness unread frameStack : BitString)
    (consumed padding : Nat)
    (f : EvalFrame) :
    let final :=
      framePushMachine.run 3
        (framePushConfig f
          (evalCursorStackEndTape
            witness consumed unread frameStack padding))
    final.state = .halt ∧
      final.tape =
        evalCursorStackEndTape
          witness consumed unread
          (encodeEvalFrame f ++ frameStack)
          (((padding - 1) - 1) - 1) := by
  dsimp
  unfold framePushConfig
  have h1 := framePush_start_one f
    (evalCursorStackEndTape witness consumed unread frameStack padding) rfl
  have hp1 :=
    pushStep_evalCursorStackEndTape
      witness unread frameStack consumed padding (frameBit2 f)
  have h2 := framePush_after1_one f
    (evalCursorStackEndTape witness consumed unread
      (frameBit2 f :: frameStack) (padding - 1)) rfl
  have hp2 :=
    pushStep_evalCursorStackEndTape
      witness unread (frameBit2 f :: frameStack)
      consumed (padding - 1) (frameBit1 f)
  have h3 := framePush_after2_one f
    (evalCursorStackEndTape witness consumed unread
      (frameBit1 f :: frameBit2 f :: frameStack)
      ((padding - 1) - 1)) rfl
  have hp3 :=
    pushStep_evalCursorStackEndTape
      witness unread
      (frameBit1 f :: frameBit2 f :: frameStack)
      consumed ((padding - 1) - 1) (frameBit0 f)
  rw [show 3 = 1 + 2 by decide, MachineRunLemmas.run_add]
  rw [h1, hp1]
  rw [show 2 = 1 + 1 by decide, MachineRunLemmas.run_add]
  rw [h2, hp2]
  rw [h3, hp3]
  constructor
  · rfl
  · rw [encodeEvalFrame_eq_bits]
    rfl

#print axioms MCore.Real.P01EvalCursorFramePush.pushStep_evalCursorStackEndTape
#print axioms MCore.Real.P01EvalCursorFramePush.framePush_run_three_cursor

end P01EvalCursorFramePush
end Real
end MCore
