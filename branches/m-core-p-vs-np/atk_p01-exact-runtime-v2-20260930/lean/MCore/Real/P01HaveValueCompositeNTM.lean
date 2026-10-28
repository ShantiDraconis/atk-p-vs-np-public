import MCore.Real.P01EvalCursorFramePop
import MCore.Real.P01EvalCursorFramePush
import MCore.Real.P01NTMRunLaws

namespace MCore
namespace Real
namespace P01HaveValueCompositeNTM

open CanonicalFinalProof
open P01EncodedStackEvaluator
open P01EvalFramePopMachineV2
open P01EvalFramePushMachine
open P01EvalCursorFramePop
open P01EvalCursorFramePush

/-- Finite control for one physical evaluator step starting from a semantic
`haveValue v bits frames` state.

The Boolean value and decoded continuation frame live only in finite control;
witness/source/frame data remain on tape. -/
inductive HaveValueCompositeState where
  | start : Bool → HaveValueCompositeState
  | peek : Bool → HaveValueCompositeState
  | pop : Bool → FramePopState → HaveValueCompositeState
  | push : EvalFrame → FramePushState → HaveValueCompositeState
  | doneValue : Bool → HaveValueCompositeState
  | doneNeed
  | reject
  deriving DecidableEq, Repr

/-- One fixed NTM for the full physical `haveValue` arm of `evalStep`.
Every active state has at most one successor. -/
def haveValueCompositeMachine :
    NTM HaveValueCompositeState (Option Bool) where
  initial := .start false
  blank := none
  transition := fun q symbol =>
    match q with
    | .start v =>
        match symbol with
        | none => [(.peek v, none, .left)]
        | some b => [(.reject, some b, .stay)]
    | .peek v =>
        match symbol with
        | none => [(.doneValue v, none, .right)]
        | some b => [(.pop v framePopMachine.initial, some b, .right)]
    | .pop v qp =>
        match qp with
        | .halt frame =>
            match frame with
            | .neg =>
                [(.doneValue (!v), symbol, .stay)]
            | .andLeft =>
                let f := EvalFrame.andRight v
                [(.push f (.start f), symbol, .stay)]
            | .andRight l =>
                [(.doneValue (Bool.and l v), symbol, .stay)]
            | .orLeft =>
                let f := EvalFrame.orRight v
                [(.push f (.start f), symbol, .stay)]
            | .orRight l =>
                [(.doneValue (Bool.or l v), symbol, .stay)]
        | .reject => [(.reject, symbol, .stay)]
        | _ =>
            let t := framePopMachine.transition qp symbol
            [(.pop v t.1, t.2.1, t.2.2)]
    | .push frame qp =>
        match qp with
        | .halt => [(.doneNeed, symbol, .stay)]
        | .reject => [(.reject, symbol, .stay)]
        | _ =>
            let t := framePushMachine.transition qp symbol
            [(.push frame t.1, t.2.1, t.2.2)]
    | .doneValue _ => []
    | .doneNeed => []
    | .reject => []
  accepting := fun q =>
    match q with
    | .doneValue _ => true
    | .doneNeed => true
    | _ => false
  rejecting := fun q =>
    match q with
    | .reject => true
    | _ => false

@[simp] theorem haveValueCompositeMachine_blank :
    haveValueCompositeMachine.blank = none := rfl

@[simp] theorem accepting_doneValue (v : Bool) :
    haveValueCompositeMachine.accepting (.doneValue v) = true := rfl

@[simp] theorem accepting_doneNeed :
    haveValueCompositeMachine.accepting .doneNeed = true := rfl

/-- Rewriting the current head symbol is physically inert. -/
@[simp] theorem tape_write_head_self
    (tape : Tape (Option Bool)) :
    Tape.write tape tape.head = tape := by
  cases tape
  rfl

theorem start_successors
    (v : Bool) (tape : Tape (Option Bool))
    (hblank : tape.head = none) :
    haveValueCompositeMachine.successors
      { state := .start v, tape := tape } =
      [{ state := .peek v, tape := Tape.move none .left tape }] := by
  have hwrite : Tape.write tape none = tape := by
    rw [← hblank]
    exact tape_write_head_self tape
  simp [haveValueCompositeMachine, NTM.successors, NTM.stepBranch,
    hblank, hwrite]

/-- If the cell left of the stack-end boundary is blank, there is no encoded
continuation frame; the machine restores the stack-end head and preserves the
current value. -/
theorem empty_handoff_successors
    (v : Bool) (tape : Tape (Option Bool))
    (hblank : tape.head = none) :
    haveValueCompositeMachine.successors
      { state := .peek v, tape := tape } =
      [{ state := .doneValue v,
         tape := Tape.move none .right tape }] := by
  have hwrite : Tape.write tape none = tape := by
    rw [← hblank]
    exact tape_write_head_self tape
  simp [haveValueCompositeMachine, NTM.successors, NTM.stepBranch,
    hblank, hwrite]

/-- A nonblank top-frame bit returns the head to the stack-end boundary and
enters the certified six-step frame-pop machine. -/
theorem nonempty_handoff_successors
    (v b : Bool) (tape : Tape (Option Bool))
    (hhead : tape.head = some b) :
    haveValueCompositeMachine.successors
      { state := .peek v, tape := tape } =
      [{ state := .pop v framePopMachine.initial,
         tape := Tape.move none .right tape }] := by
  have hwrite : Tape.write tape (some b) = tape := by
    rw [← hhead]
    exact tape_write_head_self tape
  simp [haveValueCompositeMachine, NTM.successors, NTM.stepBranch,
    hhead, hwrite]

theorem pop_transition_active
    (v : Bool) (q : FramePopState) (symbol : Option Bool)
    (h : framePopMachine.halting q = false) :
    haveValueCompositeMachine.transition (.pop v q) symbol =
      let t := framePopMachine.transition q symbol
      [(.pop v t.1, t.2.1, t.2.2)] := by
  cases q <;>
    simp [framePopMachine, haveValueCompositeMachine] at h ⊢

theorem push_transition_active
    (frame : EvalFrame) (q : FramePushState) (symbol : Option Bool)
    (h : framePushMachine.halting q = false) :
    haveValueCompositeMachine.transition (.push frame q) symbol =
      let t := framePushMachine.transition q symbol
      [(.push frame t.1, t.2.1, t.2.2)] := by
  cases q <;>
    simp [framePushMachine, haveValueCompositeMachine] at h ⊢

theorem pop_neg_handoff_successors
    (v : Bool) (tape : Tape (Option Bool)) :
    haveValueCompositeMachine.successors
      { state := .pop v (.halt .neg), tape := tape } =
      [{ state := .doneValue (!v), tape := tape }] := by
  simp [haveValueCompositeMachine, NTM.successors, NTM.stepBranch,
    Tape.write, Tape.move]

theorem pop_andLeft_handoff_successors
    (v : Bool) (tape : Tape (Option Bool)) :
    haveValueCompositeMachine.successors
      { state := .pop v (.halt .andLeft), tape := tape } =
      [{ state := .push (.andRight v) (.start (.andRight v)),
         tape := tape }] := by
  simp [haveValueCompositeMachine, NTM.successors, NTM.stepBranch,
    Tape.write, Tape.move]

theorem pop_andRight_handoff_successors
    (l v : Bool) (tape : Tape (Option Bool)) :
    haveValueCompositeMachine.successors
      { state := .pop v (.halt (.andRight l)), tape := tape } =
      [{ state := .doneValue (Bool.and l v), tape := tape }] := by
  simp [haveValueCompositeMachine, NTM.successors, NTM.stepBranch,
    Tape.write, Tape.move]

theorem pop_orLeft_handoff_successors
    (v : Bool) (tape : Tape (Option Bool)) :
    haveValueCompositeMachine.successors
      { state := .pop v (.halt .orLeft), tape := tape } =
      [{ state := .push (.orRight v) (.start (.orRight v)),
         tape := tape }] := by
  simp [haveValueCompositeMachine, NTM.successors, NTM.stepBranch,
    Tape.write, Tape.move]

theorem pop_orRight_handoff_successors
    (l v : Bool) (tape : Tape (Option Bool)) :
    haveValueCompositeMachine.successors
      { state := .pop v (.halt (.orRight l)), tape := tape } =
      [{ state := .doneValue (Bool.or l v), tape := tape }] := by
  simp [haveValueCompositeMachine, NTM.successors, NTM.stepBranch,
    Tape.write, Tape.move]

theorem push_handoff_successors
    (frame : EvalFrame) (tape : Tape (Option Bool)) :
    haveValueCompositeMachine.successors
      { state := .push frame .halt, tape := tape } =
      [{ state := .doneNeed, tape := tape }] := by
  simp [haveValueCompositeMachine, NTM.successors, NTM.stepBranch,
    Tape.write, Tape.move]

theorem haveValueComposite_successors_length_le_one
    (c : Configuration HaveValueCompositeState (Option Bool)) :
    (haveValueCompositeMachine.successors c).length ≤ 1 := by
  have hlen :
      (haveValueCompositeMachine.successors c).length =
        (haveValueCompositeMachine.transition c.state c.tape.head).length := by
    simp [NTM.successors]
  rw [hlen]
  cases c.state with
  | start v =>
      cases c.tape.head <;>
        simp [haveValueCompositeMachine]
  | peek v =>
      cases c.tape.head <;>
        simp [haveValueCompositeMachine]
  | pop v q =>
      cases q with
      | halt f =>
          cases f <;>
            simp [haveValueCompositeMachine]
      | _ =>
          simp [haveValueCompositeMachine]
  | push frame q =>
      cases q <;>
        simp [haveValueCompositeMachine]
  | doneValue v =>
      simp [haveValueCompositeMachine]
  | doneNeed =>
      simp [haveValueCompositeMachine]
  | reject =>
      simp [haveValueCompositeMachine]

#print axioms MCore.Real.P01HaveValueCompositeNTM.start_successors
#print axioms MCore.Real.P01HaveValueCompositeNTM.pop_transition_active
#print axioms MCore.Real.P01HaveValueCompositeNTM.push_transition_active
#print axioms MCore.Real.P01HaveValueCompositeNTM.haveValueComposite_successors_length_le_one

end P01HaveValueCompositeNTM
end Real
end MCore
