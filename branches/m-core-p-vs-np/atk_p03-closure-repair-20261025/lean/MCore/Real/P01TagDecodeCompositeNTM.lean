import MCore.Real.P01InputTagDecodeMachine
import MCore.Real.P01NTMRunLaws

namespace MCore
namespace Real
namespace P01TagDecodeCompositeNTM

open P01EvalCursorMachine
open P01InputTagDecodeMachine

inductive TagDecodeCompositeState where
  | seek : CursorSeekState → TagDecodeCompositeState
  | decode : TagDecodeState → TagDecodeCompositeState
  | done : Bool → Bool → Bool → TagDecodeCompositeState
  | reject
  deriving DecidableEq, Repr

def tagDecodeCompositeMachine :
    NTM TagDecodeCompositeState (Option Bool) where
  initial := .seek cursorSeekMachine.initial
  blank := none
  transition := fun q symbol =>
    match q with
    | .seek qs =>
        match qs with
        | .halt =>
            [(.decode tagDecodeMachine.initial, symbol, .stay)]
        | .reject => []
        | _ =>
            let t := cursorSeekMachine.transition qs symbol
            [(.seek t.1, t.2.1, t.2.2)]
    | .decode qd =>
        match qd with
        | .halt b0 b1 b2 =>
            [(.done b0 b1 b2, symbol, .stay)]
        | .reject => []
        | _ =>
            let t := tagDecodeMachine.transition qd symbol
            [(.decode t.1, t.2.1, t.2.2)]
    | .done _ _ _ => []
    | .reject => []
  accepting := fun q =>
    match q with
    | .done _ _ _ => true
    | _ => false
  rejecting := fun q =>
    match q with
    | .reject => true
    | _ => false

@[simp] theorem tagDecodeCompositeMachine_initial :
    tagDecodeCompositeMachine.initial =
      .seek cursorSeekMachine.initial := rfl

@[simp] theorem tagDecodeCompositeMachine_blank :
    tagDecodeCompositeMachine.blank = none := rfl

@[simp] theorem tagDecodeCompositeMachine_accepting_done
    (b0 b1 b2 : Bool) :
    tagDecodeCompositeMachine.accepting (.done b0 b1 b2) = true := rfl

theorem seek_handoff_successors
    (tape : Tape (Option Bool)) :
    tagDecodeCompositeMachine.successors
      { state := .seek .halt, tape := tape } =
      [{ state := .decode tagDecodeMachine.initial, tape := tape }] := by
  simp [tagDecodeCompositeMachine, NTM.successors, NTM.stepBranch,
    Tape.write, Tape.move]

theorem decode_handoff_successors
    (b0 b1 b2 : Bool)
    (tape : Tape (Option Bool)) :
    tagDecodeCompositeMachine.successors
      { state := .decode (.halt b0 b1 b2), tape := tape } =
      [{ state := .done b0 b1 b2, tape := tape }] := by
  simp [tagDecodeCompositeMachine, NTM.successors, NTM.stepBranch,
    Tape.write, Tape.move]

theorem seek_transition_active
    (q : CursorSeekState) (symbol : Option Bool)
    (h : cursorSeekMachine.halting q = false) :
    tagDecodeCompositeMachine.transition (.seek q) symbol =
      let t := cursorSeekMachine.transition q symbol
      [(.seek t.1, t.2.1, t.2.2)] := by
  cases q <;>
    simp [cursorSeekMachine, tagDecodeCompositeMachine] at h ⊢

theorem decode_transition_active
    (q : TagDecodeState) (symbol : Option Bool)
    (h : tagDecodeMachine.halting q = false) :
    tagDecodeCompositeMachine.transition (.decode q) symbol =
      let t := tagDecodeMachine.transition q symbol
      [(.decode t.1, t.2.1, t.2.2)] := by
  cases q <;>
    simp [tagDecodeMachine, tagDecodeCompositeMachine] at h ⊢

theorem tagDecodeComposite_successors_length_le_one
    (c : Configuration TagDecodeCompositeState (Option Bool)) :
    (tagDecodeCompositeMachine.successors c).length ≤ 1 := by
  unfold NTM.successors
  cases c.state with
  | seek q =>
      cases q <;>
        simp [tagDecodeCompositeMachine, NTM.stepBranch]
  | decode q =>
      cases q <;>
        simp [tagDecodeCompositeMachine, NTM.stepBranch]
  | done b0 b1 b2 =>
      simp [tagDecodeCompositeMachine, NTM.stepBranch]
  | reject =>
      simp [tagDecodeCompositeMachine, NTM.stepBranch]

#print axioms MCore.Real.P01TagDecodeCompositeNTM.seek_handoff_successors
#print axioms MCore.Real.P01TagDecodeCompositeNTM.decode_handoff_successors
#print axioms MCore.Real.P01TagDecodeCompositeNTM.seek_transition_active
#print axioms MCore.Real.P01TagDecodeCompositeNTM.decode_transition_active
#print axioms MCore.Real.P01TagDecodeCompositeNTM.tagDecodeComposite_successors_length_le_one

end P01TagDecodeCompositeNTM
end Real
end MCore
