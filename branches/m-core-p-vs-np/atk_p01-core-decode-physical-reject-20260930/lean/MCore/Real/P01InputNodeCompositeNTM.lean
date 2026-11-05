import MCore.Real.P01InputNodeRoundTrip
import MCore.Real.P01NTMRunLaws

namespace MCore
namespace Real
namespace P01InputNodeCompositeNTM

open CanonicalFinalProof
open P01InputReturnMode
open P01InputIndexLookahead
open P01InputAfterReadReturn
open P01WitnessIndexedReadPreserving

/-- Finite control for the full physical input-node primitive.

The lookahead result `InputReturnMode` is carried through the preserving read,
and the selected witness bit is carried through the return phase.  No dynamic
information is discarded at phase boundaries. -/
inductive InputNodeCompositeState where
  | look : InputIndexLookaheadState → InputNodeCompositeState
  | read : InputReturnMode → PreservingReadState → InputNodeCompositeState
  | ret : InputReturnMode → Bool → InputAfterReadReturnState →
      InputNodeCompositeState
  | done : Bool → InputReturnMode → InputNodeCompositeState
  | reject
  deriving DecidableEq, Repr

/-- One fixed nondeterministic machine for the input node.  Every active state
has exactly one successor, so the machine is operationally deterministic; NTM
is used because this is the state type required by the final verifier phase.

Phase handoffs are stationary and preserve the entire physical tape. -/
def inputNodeCompositeMachine :
    NTM InputNodeCompositeState (Option Bool) where
  initial := .look inputIndexLookaheadMachine.initial
  blank := none
  transition := fun q symbol =>
    match q with
    | .look ql =>
        match ql with
        | .halt mode =>
            [(.read mode preservingReadMachine.initial, symbol, .stay)]
        | .reject => [(.reject, symbol, .stay)]
        | _ =>
            let t := inputIndexLookaheadMachine.transition ql symbol
            [(.look t.1, t.2.1, t.2.2)]
    | .read mode qr =>
        match qr with
        | .halt selected =>
            [(.ret mode selected (.start mode), symbol, .stay)]
        | .reject => [(.reject, symbol, .stay)]
        | _ =>
            let t := preservingReadMachine.transition qr symbol
            [(.read mode t.1, t.2.1, t.2.2)]
    | .ret mode selected qt =>
        match qt with
        | .halt finalMode =>
            [(.done selected finalMode, symbol, .stay)]
        | .reject => [(.reject, symbol, .stay)]
        | _ =>
            let t := inputAfterReadReturnMachine.transition qt symbol
            [(.ret mode selected t.1, t.2.1, t.2.2)]
    | .done _ _ => []
    | .reject => []
  accepting := fun q =>
    match q with
    | .done _ _ => true
    | _ => false
  rejecting := fun q =>
    match q with
    | .reject => true
    | _ => false

@[simp] theorem inputNodeCompositeMachine_initial :
    inputNodeCompositeMachine.initial =
      .look inputIndexLookaheadMachine.initial := rfl

@[simp] theorem inputNodeCompositeMachine_blank :
    inputNodeCompositeMachine.blank = none := rfl

@[simp] theorem inputNodeCompositeMachine_accepting_done
    (selected : Bool) (mode : InputReturnMode) :
    inputNodeCompositeMachine.accepting (.done selected mode) = true := rfl

@[simp] theorem inputNodeCompositeMachine_rejecting_reject :
    inputNodeCompositeMachine.rejecting .reject = true := rfl

/-- Nested failures from lookahead/read/return are fail-closed: one additional
composite step promotes them to the unique rejecting terminal. -/
theorem nested_input_reject_successors
    (mode : InputReturnMode) (selected : Bool)
    (tape : Tape (Option Bool)) :
    inputNodeCompositeMachine.successors
        { state := .look .reject, tape := tape } =
          [{ state := .reject, tape := tape }] ∧
    inputNodeCompositeMachine.successors
        { state := .read mode .reject, tape := tape } =
          [{ state := .reject, tape := tape }] ∧
    inputNodeCompositeMachine.successors
        { state := .ret mode selected .reject, tape := tape } =
          [{ state := .reject, tape := tape }] := by
  simp [inputNodeCompositeMachine, NTM.successors,
    NTM.stepBranch, Tape.write, Tape.move]

#print axioms MCore.Real.P01InputNodeCompositeNTM.nested_input_reject_successors


/-- Lookahead handoff preserves the entire tape and stores the classified mode
in finite control. -/
theorem look_handoff_successors
    (mode : InputReturnMode)
    (tape : Tape (Option Bool)) :
    inputNodeCompositeMachine.successors
      { state := .look (.halt mode), tape := tape } =
      [{ state := .read mode preservingReadMachine.initial, tape := tape }] := by
  simp [inputNodeCompositeMachine, NTM.successors, NTM.stepBranch,
    Tape.write, Tape.move]

/-- Reader handoff preserves the tape, carries the mode, and captures the
selected witness bit in finite control. -/
theorem read_handoff_successors
    (mode : InputReturnMode) (selected : Bool)
    (tape : Tape (Option Bool)) :
    inputNodeCompositeMachine.successors
      { state := .read mode (.halt selected), tape := tape } =
      [{ state := .ret mode selected (.start mode), tape := tape }] := by
  simp [inputNodeCompositeMachine, NTM.successors, NTM.stepBranch,
    Tape.write, Tape.move]

/-- Return handoff records successful completion without changing the tape. -/
theorem return_handoff_successors
    (mode finalMode : InputReturnMode) (selected : Bool)
    (tape : Tape (Option Bool)) :
    inputNodeCompositeMachine.successors
      { state := .ret mode selected (.halt finalMode), tape := tape } =
      [{ state := .done selected finalMode, tape := tape }] := by
  simp [inputNodeCompositeMachine, NTM.successors, NTM.stepBranch,
    Tape.write, Tape.move]

/-- On every active lookahead state, the composite transition is exactly the
lookahead TM transition with only a control-state injection. -/
theorem look_transition_active
    (q : InputIndexLookaheadState) (symbol : Option Bool)
    (h : inputIndexLookaheadMachine.halting q = false) :
    inputNodeCompositeMachine.transition (.look q) symbol =
      let t := inputIndexLookaheadMachine.transition q symbol
      [(.look t.1, t.2.1, t.2.2)] := by
  cases q <;> simp [inputIndexLookaheadMachine, inputNodeCompositeMachine] at h ⊢

/-- On every active preserving-reader state, the transition table is inherited
exactly from the already-certified preserving reader. -/
theorem read_transition_active
    (mode : InputReturnMode)
    (q : PreservingReadState) (symbol : Option Bool)
    (h : preservingReadMachine.halting q = false) :
    inputNodeCompositeMachine.transition (.read mode q) symbol =
      let t := preservingReadMachine.transition q symbol
      [(.read mode t.1, t.2.1, t.2.2)] := by
  cases q <;>
    simp [preservingReadMachine, inputNodeCompositeMachine] at h ⊢

/-- On every active return state, the transition table is inherited exactly
from the already-certified mode-aware return machine. -/
theorem return_transition_active
    (mode : InputReturnMode) (selected : Bool)
    (q : InputAfterReadReturnState) (symbol : Option Bool)
    (h : inputAfterReadReturnMachine.halting q = false) :
    inputNodeCompositeMachine.transition (.ret mode selected q) symbol =
      let t := inputAfterReadReturnMachine.transition q symbol
      [(.ret mode selected t.1, t.2.1, t.2.2)] := by
  cases q <;>
    simp [inputAfterReadReturnMachine, inputNodeCompositeMachine] at h ⊢

/-- Every configuration of the fused input-node NTM has at most one
successor.  This is the structural determinism fact needed to turn existential
accepting reachability into universal `HaltsWithin`. -/
theorem inputNodeComposite_successors_length_le_one
    (c : Configuration InputNodeCompositeState (Option Bool)) :
    (inputNodeCompositeMachine.successors c).length ≤ 1 := by
  unfold NTM.successors
  cases c.state with
  | look q =>
      cases q <;>
        simp [inputNodeCompositeMachine, NTM.stepBranch]
  | read mode q =>
      cases q <;>
        simp [inputNodeCompositeMachine, NTM.stepBranch]
  | ret mode selected q =>
      cases q <;>
        simp [inputNodeCompositeMachine, NTM.stepBranch]
  | done selected mode =>
      simp [inputNodeCompositeMachine, NTM.stepBranch]
  | reject =>
      simp [inputNodeCompositeMachine, NTM.stepBranch]

#print axioms MCore.Real.P01InputNodeCompositeNTM.inputNodeComposite_successors_length_le_one

#print axioms MCore.Real.P01InputNodeCompositeNTM.look_handoff_successors
#print axioms MCore.Real.P01InputNodeCompositeNTM.read_handoff_successors
#print axioms MCore.Real.P01InputNodeCompositeNTM.return_handoff_successors
#print axioms MCore.Real.P01InputNodeCompositeNTM.look_transition_active
#print axioms MCore.Real.P01InputNodeCompositeNTM.read_transition_active
#print axioms MCore.Real.P01InputNodeCompositeNTM.return_transition_active

end P01InputNodeCompositeNTM
end Real
end MCore
