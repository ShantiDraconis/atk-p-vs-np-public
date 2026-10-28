import MCore.Real.P01EvalCursorRoundTrip
import MCore.Real.MachineRunLemmas

namespace MCore
namespace Real
namespace P01EvalCursorReturnNoErase

open CanonicalFinalProof
open P01EvalCursorMachine
open P01EvalCursorRoundTrip
open MachineRunLemmas

/-- Enter the existing return machine directly in its unread-scan phase,
without erasing the source cell currently under the head.  This is the return
needed after a three-bit tag has already been physically consumed. -/
theorem cursorReturn_noErase_run
    (witness tail frameStack : BitString)
    (consumed padding : Nat) :
    cursorReturnMachine.run
      (tail.length + frameStack.length + 2)
      { state := .scanUnread,
        tape :=
          evalCursorReadTape witness consumed
            tail frameStack padding } =
      { state := .halt,
        tape :=
          evalCursorStackEndTape witness consumed
            tail frameStack padding } := by
  let left0 : List (Option Bool) :=
    List.replicate consumed none ++ none :: witness.map some

  have hstart :
      ({ state := CursorReturnState.scanUnread,
         tape :=
           evalCursorReadTape witness consumed tail frameStack padding } :
        Configuration CursorReturnState (Option Bool)) =
      unreadReturnConfig left0 tail frameStack padding := by
    cases tail <;>
      rfl

  rw [hstart]
  rw [show tail.length + frameStack.length + 2 =
      tail.length + (1 + (frameStack.length + 1)) by omega]
  rw [run_add]
  rw [unreadReturn_run]
  rw [run_add]
  rw [sourceSeparator_to_frames]
  rw [show frameStack.length = frameStack.reverse.length by simp]
  rw [run_add]
  rw [frameReturn_run]
  rw [frameReturn_halt]
  simp [left0, evalCursorStackEndTape,
    List.reverse_reverse, List.map_append, List.append_assoc]

theorem cursorReturn_noErase_halts
    (witness tail frameStack : BitString)
    (consumed padding : Nat) :
    cursorReturnMachine.HaltsWithin
      (tail.length + frameStack.length + 2)
      { state := .scanUnread,
        tape :=
          evalCursorReadTape witness consumed
            tail frameStack padding } := by
  unfold TM.HaltsWithin
  rw [cursorReturn_noErase_run]
  rfl

#print axioms MCore.Real.P01EvalCursorReturnNoErase.cursorReturn_noErase_run
#print axioms MCore.Real.P01EvalCursorReturnNoErase.cursorReturn_noErase_halts

end P01EvalCursorReturnNoErase
end Real
end MCore
