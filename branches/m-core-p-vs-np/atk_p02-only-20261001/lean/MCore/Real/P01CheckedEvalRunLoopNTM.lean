import MCore.Real.P01EvalRunLoopNTM
import MCore.Real.P01CNFMode

namespace MCore
namespace Real
namespace P01CheckedEvalRunLoopNTM

open CanonicalFinalProof
open P01InputReturnMode
open P01InputNodeCompositeNTM
open P01NeedExprTagDecode
open P01NeedExprCompositeNTM
open P01HaveValueCompositeNTM
open P01EvalFramePopMachineV2
open P01EvalFramePushMachine
open P01CNFMode

/-- The physical evaluator enriched only with a finite CNF syntax obligation.

The mode is control data, not tape data.  It is needed only while entering a
new expression:
* root / AND children use `cnf`;
* OR children use `clause`;
* the child of NOT uses `mustInput`.
-/
inductive CheckedEvalRunState where
  | need : SyntaxMode → NeedExprCompositeState → CheckedEvalRunState
  | have : SyntaxMode → HaveValueCompositeState → CheckedEvalRunState
  | checkSource : Bool → CheckedEvalRunState
  | final : Bool → CheckedEvalRunState
  | reject
  deriving DecidableEq, Repr

/-- Mode carried after a continuation frame has been popped.

Only left binary frames lead to a new right-hand expression. -/
def modeAfterFrame (current : SyntaxMode) :
    P01EncodedStackEvaluator.EvalFrame → SyntaxMode
  | .andLeft => .cnf
  | .andRight _ => .cnf
  | .orLeft => .clause
  | .orRight _ => .clause
  | .neg => current

def inputCheckedEmbed
    (mode : SyntaxMode) :
    InputNodeCompositeState → CheckedEvalRunState
  | .done selected .done => .final selected
  | .done selected _ => .have mode (.start selected)
  | .reject => .reject
  | q => .need mode (.input q)

def needCheckedEmbed
    (mode : SyntaxMode) :
    NeedExprCompositeState → CheckedEvalRunState
  | .input (.done selected .done) => .final selected
  | .input (.done selected _) => .have mode (.start selected)
  | .input .reject => .reject
  | .doneValue v => .have mode (.start v)
  | .doneNeed => .need mode needExprCompositeMachine.initial
  | .reject => .reject
  | q => .need mode q

def haveCheckedEmbed
    (mode : SyntaxMode) :
    HaveValueCompositeState → CheckedEvalRunState
  | .doneValue v => .have mode (.start v)
  | .doneNeed => .need mode needExprCompositeMachine.initial
  | .reject => .reject
  | q => .have mode q

/-- Fixed physical evaluator with the CNF grammar firewall fused into finite
control.  The underlying evaluator transitions are reused verbatim.

No extra tape symbol, oracle, endpoint proposition, or unbounded control data is
introduced. -/
def checkedEvalRunLoopMachine :
    NTM CheckedEvalRunState (Option Bool) where
  initial := .need .cnf needExprCompositeMachine.initial
  blank := none
  transition := fun q symbol =>
    match q with
    | .need mode (.input qi) =>
        match qi with
        | .done selected .done =>
            [(.final selected, symbol, .stay)]
        | .done selected _ =>
            [(.have mode (.start selected), symbol, .stay)]
        | .reject =>
            [(.reject, symbol, .stay)]
        | _ =>
            (inputNodeCompositeMachine.transition qi symbol).map
              (fun t => (inputCheckedEmbed mode t.1, t.2.1, t.2.2))
    | .need mode (.decode (.halt tag)) =>
        if tagAllowed mode tag then
          let nextMode := childMode mode tag
          (needExprCompositeMachine.transition (.decode (.halt tag)) symbol).map
            (fun t => (needCheckedEmbed nextMode t.1, t.2.1, t.2.2))
        else
          [(.reject, symbol, .stay)]
    | .need mode qn =>
        match qn with
        | .doneValue v =>
            [(.have mode (.start v), symbol, .stay)]
        | .doneNeed =>
            [(.need mode needExprCompositeMachine.initial, symbol, .stay)]
        | .reject =>
            [(.reject, symbol, .stay)]
        | _ =>
            (needExprCompositeMachine.transition qn symbol).map
              (fun t => (needCheckedEmbed mode t.1, t.2.1, t.2.2))
    | .have mode (.peek v) =>
        match symbol with
        | none =>
            [(.checkSource v, none, .left)]
        | some b =>
            [(.have mode (.pop v framePopMachine.initial), some b, .right)]
    | .checkSource v =>
        match symbol with
        | none => [(.final v, none, .stay)]
        | some b => [(.reject, some b, .stay)]
    | .have mode (.pop v (.halt frame)) =>
        let nextMode := modeAfterFrame mode frame
        (haveValueCompositeMachine.transition (.pop v (.halt frame)) symbol).map
          (fun t => (haveCheckedEmbed nextMode t.1, t.2.1, t.2.2))
    | .have mode qh =>
        match qh with
        | .doneValue v =>
            [(.have mode (.start v), symbol, .stay)]
        | .doneNeed =>
            [(.need mode needExprCompositeMachine.initial, symbol, .stay)]
        | .reject =>
            [(.reject, symbol, .stay)]
        | _ =>
            (haveValueCompositeMachine.transition qh symbol).map
              (fun t => (haveCheckedEmbed mode t.1, t.2.1, t.2.2))
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

@[simp] theorem checkedEvalRunLoopMachine_blank :
    checkedEvalRunLoopMachine.blank = none := rfl

@[simp] theorem accepting_final (v : Bool) :
    checkedEvalRunLoopMachine.accepting (.final v) = v := by
  cases v <;> rfl

@[simp] theorem rejecting_final (v : Bool) :
    checkedEvalRunLoopMachine.rejecting (.final v) = !v := by
  cases v <;> rfl

@[simp] theorem rejecting_reject :
    checkedEvalRunLoopMachine.rejecting .reject = true := rfl

def needCheckedLift
    (mode : SyntaxMode)
    (c : Configuration NeedExprCompositeState (Option Bool)) :
    Configuration CheckedEvalRunState (Option Bool) :=
  { state := needCheckedEmbed mode c.state
    tape := c.tape }

/-- For an admitted root tag the checked wrapper performs exactly the already
certified physical decoder handoff, changing only the finite syntax mode for
the child expression. -/
theorem allowed_tag_successors
    (mode : SyntaxMode)
    (tag : NeedExprTag)
    (tape : Tape (Option Bool))
    (h : tagAllowed mode tag = true) :
    checkedEvalRunLoopMachine.successors
      { state := .need mode (.decode (.halt tag)), tape := tape } =
    (needExprCompositeMachine.successors
      { state := .decode (.halt tag), tape := tape }).map
        (needCheckedLift (childMode mode tag)) := by
  cases tape with
  | mk left head right =>
      cases mode <;> cases tag <;>
        simp [checkedEvalRunLoopMachine, needExprCompositeMachine,
          needCheckedLift, needCheckedEmbed, NTM.successors, NTM.stepBranch,
          tagAllowed, childMode, Tape.write, Tape.move] at h ⊢

/-- Any syntactically forbidden decoded tag is rejected in one physical step. -/
theorem disallowed_tag_successors
    (mode : SyntaxMode)
    (tag : NeedExprTag)
    (tape : Tape (Option Bool))
    (h : tagAllowed mode tag = false) :
    checkedEvalRunLoopMachine.successors
      { state := .need mode (.decode (.halt tag)), tape := tape } =
      [{ state := .reject, tape := tape }] := by
  cases tape with
  | mk left head right =>
      simp [checkedEvalRunLoopMachine, NTM.successors, h,
        NTM.stepBranch, Tape.write, Tape.move]

/-- A conjunction tag is forbidden while checking a clause. -/
theorem clause_and_rejects
    (tape : Tape (Option Bool)) :
    checkedEvalRunLoopMachine.successors
      { state := .need .clause (.decode (.halt .and)), tape := tape } =
      [{ state := .reject, tape := tape }] := by
  exact disallowed_tag_successors .clause .and tape rfl

/-- Once NOT has demanded an input literal, any constant tag is rejected. -/
theorem mustInput_constFalse_rejects
    (tape : Tape (Option Bool)) :
    checkedEvalRunLoopMachine.successors
      { state := .need .mustInput (.decode (.halt .constFalse)), tape := tape } =
      [{ state := .reject, tape := tape }] := by
  exact disallowed_tag_successors .mustInput .constFalse tape rfl

#print axioms MCore.Real.P01CheckedEvalRunLoopNTM.allowed_tag_successors
#print axioms MCore.Real.P01CheckedEvalRunLoopNTM.disallowed_tag_successors
#print axioms MCore.Real.P01CheckedEvalRunLoopNTM.clause_and_rejects
#print axioms MCore.Real.P01CheckedEvalRunLoopNTM.mustInput_constFalse_rejects

end P01CheckedEvalRunLoopNTM
end Real
end MCore
