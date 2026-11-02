import MCore.Real.P01EvalCursorMachine
import MCore.Real.P01EvalCursorRoundTrip
import MCore.Real.P01EvalFramePushMachine
import MCore.Real.P01NeedExprTagDecode
import MCore.Real.P01InputNodeCompositeNTM

namespace MCore
namespace Real
namespace P01NeedExprCompositeNTM

open CanonicalFinalProof
open P01EncodedStackEvaluator
open P01EvalCursorMachine
open P01EvalCursorRoundTrip
open P01EvalFramePushMachine
open P01NeedExprTagDecode
open P01InputNodeCompositeNTM

/-- Finite control for one complete physical `needExpr` evaluator step.

The six valid prefix tags share the same physical seek and 3-bit decoder.
After decoding:
* 000 enters the already-certified indexed-input composite;
* 001/010 preserve-return and finish with a Boolean value;
* 011/100/101 preserve-return, push one continuation frame, and finish in
  `needExpr` mode;
* 110/111 reject.

All dynamic source/witness/frame data remains on tape; finite control carries
only finite tags, frames, Booleans, and submachine states. -/
inductive NeedExprCompositeState where
  | seek : CursorSeekState → NeedExprCompositeState
  | decode : TagDecodeState → NeedExprCompositeState
  | input : InputNodeCompositeState → NeedExprCompositeState
  | retValue : Bool → CursorReturnState → NeedExprCompositeState
  | retPush : EvalFrame → CursorReturnState → NeedExprCompositeState
  | push : EvalFrame → FramePushState → NeedExprCompositeState
  | doneValue : Bool → NeedExprCompositeState
  | doneNeed
  | reject
  deriving DecidableEq, Repr

/-- Terminal-preserving embedding of the indexed-input primitive into the
global needExpr control.  Internal input states stay under `.input`; the
input primitive's accepting/rejecting terminals become the corresponding
global terminals immediately. -/
def inputStateEmbed : InputNodeCompositeState → NeedExprCompositeState
  | .done selected _mode => .doneValue selected
  | .reject => .reject
  | q => .input q

/-- One fixed NTM implementing all six valid `needExpr` tag cases. -/
def needExprCompositeMachine :
    NTM NeedExprCompositeState (Option Bool) where
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
        | .halt tag =>
            match tag with
            | .input =>
                [(.input inputNodeCompositeMachine.initial, symbol, .stay)]
            | .constFalse =>
                [(.retValue false .scanUnread, symbol, .stay)]
            | .constTrue =>
                [(.retValue true .scanUnread, symbol, .stay)]
            | .neg =>
                [(.retPush .neg .scanUnread, symbol, .stay)]
            | .and =>
                [(.retPush .andLeft .scanUnread, symbol, .stay)]
            | .or =>
                [(.retPush .orLeft .scanUnread, symbol, .stay)]
            | .invalid110 => []
            | .invalid111 => []
        | .reject => []
        | _ =>
            let t := tagDecodeMachine.transition qd symbol
            [(.decode t.1, t.2.1, t.2.2)]
    | .input qi =>
        match qi with
        | .done selected _mode =>
            [(.doneValue selected, symbol, .stay)]
        | .reject => []
        | _ =>
            (inputNodeCompositeMachine.transition qi symbol).map
              (fun t => (inputStateEmbed t.1, t.2.1, t.2.2))
    | .retValue value qr =>
        match qr with
        | .halt =>
            [(.doneValue value, symbol, .stay)]
        | .reject => []
        | _ =>
            let t := cursorReturnMachine.transition qr symbol
            [(.retValue value t.1, t.2.1, t.2.2)]
    | .retPush frame qr =>
        match qr with
        | .halt =>
            [(.push frame (.start frame), symbol, .stay)]
        | .reject => []
        | _ =>
            let t := cursorReturnMachine.transition qr symbol
            [(.retPush frame t.1, t.2.1, t.2.2)]
    | .push frame qp =>
        match qp with
        | .halt =>
            [(.doneNeed, symbol, .stay)]
        | .reject => []
        | _ =>
            let t := framePushMachine.transition qp symbol
            [(.push frame t.1, t.2.1, t.2.2)]
    | .doneValue _ => []
    | .doneNeed => []
    | .reject => []
  accepting := fun q =>
    match q with
    | .input (.done _ _) => true
    | .doneValue _ => true
    | .doneNeed => true
    | _ => false
  rejecting := fun q =>
    match q with
    | .input .reject => true
    | .reject => true
    | _ => false

@[simp] theorem needExprCompositeMachine_initial :
    needExprCompositeMachine.initial =
      .seek cursorSeekMachine.initial := rfl

@[simp] theorem needExprCompositeMachine_blank :
    needExprCompositeMachine.blank = none := rfl

@[simp] theorem needExprCompositeMachine_accepting_input_done
    (selected : Bool) (mode : P01InputReturnMode.InputReturnMode) :
    needExprCompositeMachine.accepting
      (.input (.done selected mode)) = true := rfl

@[simp] theorem needExprCompositeMachine_rejecting_input_reject :
    needExprCompositeMachine.rejecting (.input .reject) = true := rfl

@[simp] theorem needExprCompositeMachine_accepting_value (b : Bool) :
    needExprCompositeMachine.accepting (.doneValue b) = true := rfl

@[simp] theorem needExprCompositeMachine_accepting_need :
    needExprCompositeMachine.accepting .doneNeed = true := rfl

/-- Cursor-seek completion hands the unchanged tape to the tag decoder. -/
theorem seek_handoff_successors
    (tape : Tape (Option Bool)) :
    needExprCompositeMachine.successors
      { state := .seek .halt, tape := tape } =
      [{ state := .decode tagDecodeMachine.initial, tape := tape }] := by
  simp [needExprCompositeMachine, NTM.successors, NTM.stepBranch,
    Tape.write, Tape.move]

/-- The physical input tag dispatches to the already-certified input-node
composite without changing the tape. -/
theorem input_tag_handoff_successors
    (tape : Tape (Option Bool)) :
    needExprCompositeMachine.successors
      { state := .decode (.halt .input), tape := tape } =
      [{ state := .input inputNodeCompositeMachine.initial, tape := tape }] := by
  simp [needExprCompositeMachine, NTM.successors, NTM.stepBranch,
    Tape.write, Tape.move]

theorem constFalse_handoff_successors
    (tape : Tape (Option Bool)) :
    needExprCompositeMachine.successors
      { state := .decode (.halt .constFalse), tape := tape } =
      [{ state := .retValue false .scanUnread, tape := tape }] := by
  simp [needExprCompositeMachine, NTM.successors, NTM.stepBranch,
    Tape.write, Tape.move]

theorem constTrue_handoff_successors
    (tape : Tape (Option Bool)) :
    needExprCompositeMachine.successors
      { state := .decode (.halt .constTrue), tape := tape } =
      [{ state := .retValue true .scanUnread, tape := tape }] := by
  simp [needExprCompositeMachine, NTM.successors, NTM.stepBranch,
    Tape.write, Tape.move]

theorem neg_handoff_successors
    (tape : Tape (Option Bool)) :
    needExprCompositeMachine.successors
      { state := .decode (.halt .neg), tape := tape } =
      [{ state := .retPush .neg .scanUnread, tape := tape }] := by
  simp [needExprCompositeMachine, NTM.successors, NTM.stepBranch,
    Tape.write, Tape.move]

theorem and_handoff_successors
    (tape : Tape (Option Bool)) :
    needExprCompositeMachine.successors
      { state := .decode (.halt .and), tape := tape } =
      [{ state := .retPush .andLeft .scanUnread, tape := tape }] := by
  simp [needExprCompositeMachine, NTM.successors, NTM.stepBranch,
    Tape.write, Tape.move]

theorem or_handoff_successors
    (tape : Tape (Option Bool)) :
    needExprCompositeMachine.successors
      { state := .decode (.halt .or), tape := tape } =
      [{ state := .retPush .orLeft .scanUnread, tape := tape }] := by
  simp [needExprCompositeMachine, NTM.successors, NTM.stepBranch,
    Tape.write, Tape.move]

/-- Active seek states reproduce exactly the deterministic cursor-seek
transition with only the composite-state injection. -/
theorem seek_transition_active
    (q : CursorSeekState) (symbol : Option Bool)
    (h : cursorSeekMachine.halting q = false) :
    needExprCompositeMachine.transition (.seek q) symbol =
      let t := cursorSeekMachine.transition q symbol
      [(.seek t.1, t.2.1, t.2.2)] := by
  cases q <;>
    simp [cursorSeekMachine, needExprCompositeMachine] at h ⊢

/-- Active tag-decoder states reproduce the deterministic decoder step. -/
theorem decode_transition_active
    (q : TagDecodeState) (symbol : Option Bool)
    (h : tagDecodeMachine.halting q = false) :
    needExprCompositeMachine.transition (.decode q) symbol =
      let t := tagDecodeMachine.transition q symbol
      [(.decode t.1, t.2.1, t.2.2)] := by
  cases q <;>
    simp [tagDecodeMachine, needExprCompositeMachine] at h ⊢

theorem retValue_transition_active
    (value : Bool) (q : CursorReturnState) (symbol : Option Bool)
    (h : cursorReturnMachine.halting q = false) :
    needExprCompositeMachine.transition (.retValue value q) symbol =
      let t := cursorReturnMachine.transition q symbol
      [(.retValue value t.1, t.2.1, t.2.2)] := by
  cases q <;>
    simp [cursorReturnMachine, needExprCompositeMachine] at h ⊢

theorem retPush_transition_active
    (frame : P01EncodedStackEvaluator.EvalFrame)
    (q : CursorReturnState) (symbol : Option Bool)
    (h : cursorReturnMachine.halting q = false) :
    needExprCompositeMachine.transition (.retPush frame q) symbol =
      let t := cursorReturnMachine.transition q symbol
      [(.retPush frame t.1, t.2.1, t.2.2)] := by
  cases q <;>
    simp [cursorReturnMachine, needExprCompositeMachine] at h ⊢

theorem push_transition_active
    (frame : P01EncodedStackEvaluator.EvalFrame)
    (q : FramePushState) (symbol : Option Bool)
    (h : framePushMachine.halting q = false) :
    needExprCompositeMachine.transition (.push frame q) symbol =
      let t := framePushMachine.transition q symbol
      [(.push frame t.1, t.2.1, t.2.2)] := by
  cases q <;>
    simp [framePushMachine, needExprCompositeMachine] at h ⊢

theorem retValue_handoff_successors
    (value : Bool) (tape : Tape (Option Bool)) :
    needExprCompositeMachine.successors
      { state := .retValue value .halt, tape := tape } =
      [{ state := .doneValue value, tape := tape }] := by
  simp [needExprCompositeMachine, NTM.successors, NTM.stepBranch,
    Tape.write, Tape.move]

theorem retPush_handoff_successors
    (frame : P01EncodedStackEvaluator.EvalFrame)
    (tape : Tape (Option Bool)) :
    needExprCompositeMachine.successors
      { state := .retPush frame .halt, tape := tape } =
      [{ state := .push frame (.start frame), tape := tape }] := by
  simp [needExprCompositeMachine, NTM.successors, NTM.stepBranch,
    Tape.write, Tape.move]

theorem push_handoff_successors
    (frame : P01EncodedStackEvaluator.EvalFrame)
    (tape : Tape (Option Bool)) :
    needExprCompositeMachine.successors
      { state := .push frame .halt, tape := tape } =
      [{ state := .doneNeed, tape := tape }] := by
  simp [needExprCompositeMachine, NTM.successors, NTM.stepBranch,
    Tape.write, Tape.move]

/-- Completed input-node evaluation hands the selected Boolean to the
global needExpr value state without changing the tape. -/
theorem input_done_handoff_successors
    (selected : Bool) (mode : P01InputReturnMode.InputReturnMode)
    (tape : Tape (Option Bool)) :
    needExprCompositeMachine.successors
      { state := .input (.done selected mode), tape := tape } =
      [{ state := .doneValue selected, tape := tape }] := by
  simp [needExprCompositeMachine, NTM.successors, NTM.stepBranch,
    Tape.write, Tape.move]

/-- Invalid tag patterns have no successor. -/
theorem invalid110_rejects
    (tape : Tape (Option Bool)) :
    needExprCompositeMachine.successors
      { state := .decode (.halt .invalid110), tape := tape } = [] := by
  simp [needExprCompositeMachine, NTM.successors]

theorem invalid111_rejects
    (tape : Tape (Option Bool)) :
    needExprCompositeMachine.successors
      { state := .decode (.halt .invalid111), tape := tape } = [] := by
  simp [needExprCompositeMachine, NTM.successors]


/-- The fused need-expression machine is operationally deterministic: every
configuration has at most one successor. -/
theorem needExprComposite_successors_length_le_one
    (c : Configuration NeedExprCompositeState (Option Bool)) :
    (needExprCompositeMachine.successors c).length ≤ 1 := by
  have hlen :
      (needExprCompositeMachine.successors c).length =
        (needExprCompositeMachine.transition c.state c.tape.head).length := by
    simp [NTM.successors]
  rw [hlen]
  cases c.state with
  | seek q =>
      cases q <;>
        simp [needExprCompositeMachine]
  | decode q =>
      cases q with
      | halt tag =>
          cases tag <;>
            simp [needExprCompositeMachine]
      | _ =>
          simp [needExprCompositeMachine]
  | input qi =>
      cases qi with
      | look q =>
          have h :=
            P01InputNodeCompositeNTM.inputNodeComposite_successors_length_le_one
              ({ state := P01InputNodeCompositeNTM.InputNodeCompositeState.look q,
                 tape := c.tape } :
                Configuration P01InputNodeCompositeNTM.InputNodeCompositeState
                  (Option Bool))
          simpa [NTM.successors, needExprCompositeMachine] using h
      | read mode q =>
          have h :=
            P01InputNodeCompositeNTM.inputNodeComposite_successors_length_le_one
              ({ state := P01InputNodeCompositeNTM.InputNodeCompositeState.read mode q,
                 tape := c.tape } :
                Configuration P01InputNodeCompositeNTM.InputNodeCompositeState
                  (Option Bool))
          simpa [NTM.successors, needExprCompositeMachine] using h
      | ret mode selected q =>
          have h :=
            P01InputNodeCompositeNTM.inputNodeComposite_successors_length_le_one
              ({ state := P01InputNodeCompositeNTM.InputNodeCompositeState.ret mode selected q,
                 tape := c.tape } :
                Configuration P01InputNodeCompositeNTM.InputNodeCompositeState
                  (Option Bool))
          simpa [NTM.successors, needExprCompositeMachine] using h
      | done selected mode =>
          simp [needExprCompositeMachine]
      | reject =>
          simp [needExprCompositeMachine]
  | retValue value q =>
      cases q <;>
        simp [needExprCompositeMachine]
  | retPush frame q =>
      cases q <;>
        simp [needExprCompositeMachine]
  | push frame q =>
      cases q <;>
        simp [needExprCompositeMachine]
  | doneValue v =>
      simp [needExprCompositeMachine]
  | doneNeed =>
      simp [needExprCompositeMachine]
  | reject =>
      simp [needExprCompositeMachine]

#print axioms MCore.Real.P01NeedExprCompositeNTM.needExprComposite_successors_length_le_one

#print axioms MCore.Real.P01NeedExprCompositeNTM.seek_handoff_successors
#print axioms MCore.Real.P01NeedExprCompositeNTM.input_tag_handoff_successors
#print axioms MCore.Real.P01NeedExprCompositeNTM.constFalse_handoff_successors
#print axioms MCore.Real.P01NeedExprCompositeNTM.neg_handoff_successors
#print axioms MCore.Real.P01NeedExprCompositeNTM.input_done_handoff_successors
#print axioms MCore.Real.P01NeedExprCompositeNTM.retValue_handoff_successors
#print axioms MCore.Real.P01NeedExprCompositeNTM.retPush_handoff_successors
#print axioms MCore.Real.P01NeedExprCompositeNTM.push_handoff_successors
#print axioms MCore.Real.P01NeedExprCompositeNTM.invalid110_rejects

end P01NeedExprCompositeNTM
end Real
end MCore
