import MCore.Real.P01EvalStepSemanticRefinement

namespace MCore
namespace Real
namespace P01EvalRunLoopNTM

open CanonicalFinalProof
open P01InputReturnMode
open P01InputNodeCompositeNTM
open P01NeedExprCompositeNTM
open P01HaveValueCompositeNTM
open P01EvalFramePopMachineV2
open P01EvalFramePushMachine

/-- Finite control for repeatedly executing the already-certified physical
`evalStep` arms.

The loop deliberately retains the raw input-node terminal long enough to keep
`InputReturnMode.done` distinct from the nonfinal `frameStack` mode. -/
inductive EvalRunLoopState where
  | need : NeedExprCompositeState → EvalRunLoopState
  | have : HaveValueCompositeState → EvalRunLoopState
  | final : Bool → EvalRunLoopState
  | reject
  deriving DecidableEq, Repr

/-- Terminal-aware embedding of the indexed-input submachine. -/
def inputLoopEmbed : InputNodeCompositeState → EvalRunLoopState
  | .done selected .done => .final selected
  | .done selected _ => .have (.start selected)
  | .reject => .reject
  | q => .need (.input q)

/-- Handoff used for all non-input `needExpr` terminals. -/
def needLoopEmbed : NeedExprCompositeState → EvalRunLoopState
  | .input (.done selected .done) => .final selected
  | .input (.done selected _) => .have (.start selected)
  | .input .reject => .reject
  | .doneValue v => .have (.start v)
  | .doneNeed => .need needExprCompositeMachine.initial
  | .reject => .reject
  | q => .need q

/-- Handoff used after a nonfinal `haveValue` continuation. -/
def haveLoopEmbed : HaveValueCompositeState → EvalRunLoopState
  | .doneValue v => .have (.start v)
  | .doneNeed => .need needExprCompositeMachine.initial
  | .reject => .reject
  | q => .have q

/-- One fixed NTM for repeated physical evaluator steps.

Two cases are intentionally intercepted instead of blindly delegating:
* `need (.input qi)` delegates directly to the input-node NTM, so its return
  mode is still available when the indexed read finishes;
* `have (.peek v)` sends an empty continuation stack directly to `final v`,
  while a nonempty stack continues into the certified frame-pop machine. -/
def evalRunLoopMachine :
    NTM EvalRunLoopState (Option Bool) where
  initial := .need needExprCompositeMachine.initial
  blank := none
  transition := fun q symbol =>
    match q with
    | .need (.input qi) =>
        match qi with
        | .done selected .done =>
            [(.final selected, symbol, .stay)]
        | .done selected _ =>
            [(.have (.start selected), symbol, .stay)]
        | .reject =>
            [(.reject, symbol, .stay)]
        | _ =>
            (inputNodeCompositeMachine.transition qi symbol).map
              (fun t => (inputLoopEmbed t.1, t.2.1, t.2.2))
    | .need qn =>
        match qn with
        | .doneValue v =>
            [(.have (.start v), symbol, .stay)]
        | .doneNeed =>
            [(.need needExprCompositeMachine.initial, symbol, .stay)]
        | .reject =>
            [(.reject, symbol, .stay)]
        | _ =>
            (needExprCompositeMachine.transition qn symbol).map
              (fun t => (needLoopEmbed t.1, t.2.1, t.2.2))
    | .have (.peek v) =>
        match symbol with
        | none =>
            [(.final v, none, .right)]
        | some b =>
            [(.have (.pop v framePopMachine.initial), some b, .right)]
    | .have qh =>
        match qh with
        | .doneValue v =>
            [(.have (.start v), symbol, .stay)]
        | .doneNeed =>
            [(.need needExprCompositeMachine.initial, symbol, .stay)]
        | .reject =>
            [(.reject, symbol, .stay)]
        | _ =>
            (haveValueCompositeMachine.transition qh symbol).map
              (fun t => (haveLoopEmbed t.1, t.2.1, t.2.2))
    | .final _ => []
    | .reject => []
  accepting := fun q =>
    match q with
    | .final true => true
    | _ => false
  rejecting := fun q =>
    match q with
    | .final false => true
    | .reject => true
    | _ => false

@[simp] theorem evalRunLoopMachine_blank :
    evalRunLoopMachine.blank = none := rfl

@[simp] theorem accepting_final (v : Bool) :
    evalRunLoopMachine.accepting (.final v) = v := by
  cases v <;> rfl

@[simp] theorem rejecting_final (v : Bool) :
    evalRunLoopMachine.rejecting (.final v) = !v := by
  cases v <;> rfl

@[simp] theorem rejecting_reject :
    evalRunLoopMachine.rejecting .reject = true := rfl

theorem input_done_final_successors
    (selected : Bool)
    (tape : Tape (Option Bool)) :
    evalRunLoopMachine.successors
      { state := .need (.input (.done selected .done)), tape := tape } =
      [{ state := .final selected, tape := tape }] := by
  simp [evalRunLoopMachine, NTM.successors, NTM.stepBranch,
    Tape.write, Tape.move]

theorem input_done_frameStack_successors
    (selected : Bool)
    (tape : Tape (Option Bool)) :
    evalRunLoopMachine.successors
      { state := .need (.input (.done selected .frameStack)), tape := tape } =
      [{ state := .have (.start selected), tape := tape }] := by
  simp [evalRunLoopMachine, NTM.successors, NTM.stepBranch,
    Tape.write, Tape.move]

theorem input_done_sourceTail_successors
    (selected : Bool)
    (tape : Tape (Option Bool)) :
    evalRunLoopMachine.successors
      { state := .need (.input (.done selected .sourceTail)), tape := tape } =
      [{ state := .have (.start selected), tape := tape }] := by
  simp [evalRunLoopMachine, NTM.successors, NTM.stepBranch,
    Tape.write, Tape.move]

theorem need_doneValue_restart_successors
    (v : Bool) (tape : Tape (Option Bool)) :
    evalRunLoopMachine.successors
      { state := .need (.doneValue v), tape := tape } =
      [{ state := .have (.start v), tape := tape }] := by
  simp [evalRunLoopMachine, NTM.successors, NTM.stepBranch,
    Tape.write, Tape.move]

theorem need_doneNeed_restart_successors
    (tape : Tape (Option Bool)) :
    evalRunLoopMachine.successors
      { state := .need .doneNeed, tape := tape } =
      [{ state := .need needExprCompositeMachine.initial, tape := tape }] := by
  simp [evalRunLoopMachine, NTM.successors, NTM.stepBranch,
    Tape.write, Tape.move]

/-- This is the physical halting test for a semantic `haveValue v _ []` state:
the stack-end blank is inspected and the head is restored in the same step. -/
theorem have_empty_final_successors
    (v : Bool)
    (tape : Tape (Option Bool))
    (hblank : tape.head = none) :
    evalRunLoopMachine.successors
      { state := .have (.peek v), tape := tape } =
      [{ state := .final v, tape := Tape.move none .right tape }] := by
  cases tape with
  | mk left head right =>
      simp_all [evalRunLoopMachine, NTM.successors, NTM.stepBranch,
        Tape.write, Tape.move]

theorem have_nonempty_pop_successors
    (v b : Bool)
    (tape : Tape (Option Bool))
    (hhead : tape.head = some b) :
    evalRunLoopMachine.successors
      { state := .have (.peek v), tape := tape } =
      [{ state := .have (.pop v framePopMachine.initial),
         tape := Tape.move none .right tape }] := by
  cases tape with
  | mk left head right =>
      simp_all [evalRunLoopMachine, NTM.successors, NTM.stepBranch,
        Tape.write, Tape.move]

theorem have_doneValue_restart_successors
    (v : Bool) (tape : Tape (Option Bool)) :
    evalRunLoopMachine.successors
      { state := .have (.doneValue v), tape := tape } =
      [{ state := .have (.start v), tape := tape }] := by
  simp [evalRunLoopMachine, NTM.successors, NTM.stepBranch,
    Tape.write, Tape.move]

theorem have_doneNeed_restart_successors
    (tape : Tape (Option Bool)) :
    evalRunLoopMachine.successors
      { state := .have .doneNeed, tape := tape } =
      [{ state := .need needExprCompositeMachine.initial, tape := tape }] := by
  simp [evalRunLoopMachine, NTM.successors, NTM.stepBranch,
    Tape.write, Tape.move]

#print axioms MCore.Real.P01EvalRunLoopNTM.input_done_final_successors
#print axioms MCore.Real.P01EvalRunLoopNTM.need_doneValue_restart_successors
#print axioms MCore.Real.P01EvalRunLoopNTM.need_doneNeed_restart_successors
#print axioms MCore.Real.P01EvalRunLoopNTM.have_empty_final_successors

end P01EvalRunLoopNTM
end Real
end MCore
