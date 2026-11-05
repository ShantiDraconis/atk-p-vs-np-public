import MCore.Real.P01NeedExprCompositeRun
import MCore.Real.P01HaveValueCompositeRun
import MCore.Real.P01NTMRunLaws

namespace MCore
namespace Real
namespace P01EvalStepCompositeNTM

open CanonicalFinalProof
open P01NTMRunLaws
open P01NeedExprCompositeNTM
open P01NeedExprCompositeRun
open P01HaveValueCompositeNTM
open P01HaveValueCompositeRun

/-- One finite-control state space for one complete physical evaluator step.

Active states remain tagged by the already-certified `needExpr` or
`haveValue` submachine.  Their accepting/rejecting terminals are promoted
immediately to global terminals so no fake extra phase is inserted. -/
inductive EvalStepCompositeState where
  | need : NeedExprCompositeState → EvalStepCompositeState
  | have : HaveValueCompositeState → EvalStepCompositeState
  | doneNeed
  | doneValue : Bool → EvalStepCompositeState
  | reject
  deriving DecidableEq, Repr

def needStateEmbed : NeedExprCompositeState → EvalStepCompositeState
  | .input (.done selected _mode) => .doneValue selected
  | .input .reject => .reject
  | .doneNeed => .doneNeed
  | .doneValue v => .doneValue v
  | .reject => .reject
  | q => .need q

def haveStateEmbed : HaveValueCompositeState → EvalStepCompositeState
  | .doneNeed => .doneNeed
  | .doneValue v => .doneValue v
  | .reject => .reject
  | q => .have q

/-- One fixed NTM containing both physical arms of `evalStep`. -/
def evalStepCompositeMachine :
    NTM EvalStepCompositeState (Option Bool) where
  initial := .need needExprCompositeMachine.initial
  blank := none
  transition := fun q symbol =>
    match q with
    | .need qn =>
        (needExprCompositeMachine.transition qn symbol).map
          (fun t => (needStateEmbed t.1, t.2.1, t.2.2))
    | .have qh =>
        (haveValueCompositeMachine.transition qh symbol).map
          (fun t => (haveStateEmbed t.1, t.2.1, t.2.2))
    | .doneNeed => []
    | .doneValue _ => []
    | .reject => []
  accepting := fun q =>
    match q with
    | .doneNeed => true
    | .doneValue _ => true
    | _ => false
  rejecting := fun q =>
    match q with
    | .reject => true
    | _ => false

@[simp] theorem evalStepCompositeMachine_blank :
    evalStepCompositeMachine.blank = none := rfl

@[simp] theorem accepting_doneNeed :
    evalStepCompositeMachine.accepting .doneNeed = true := rfl

@[simp] theorem accepting_doneValue (v : Bool) :
    evalStepCompositeMachine.accepting (.doneValue v) = true := rfl

@[simp] theorem rejecting_reject :
    evalStepCompositeMachine.rejecting .reject = true := rfl

/-- Exact terminal-preserving simulation of the six-case `needExpr` NTM. -/
def needSimulation :
    P01NTMRunLaws.Simulation
      needExprCompositeMachine evalStepCompositeMachine needStateEmbed where
  accepting := by
    intro q
    cases q <;> try rfl
    case input qi =>
      cases qi <;> rfl
  rejecting := by
    intro q
    cases q <;> try rfl
    case input qi =>
      cases qi <;> rfl
  successors := by
    intro c hactive
    rcases c with ⟨q, tape⟩
    cases q <;>
      simp [Halted, needStateEmbed,
        evalStepCompositeMachine, needExprCompositeMachine,
        P01NTMRunLaws.liftConfig, NTM.successors, NTM.stepBranch,
        List.map_map, Function.comp_def, Tape.write, Tape.move] at hactive ⊢
    case input qi =>
      cases qi <;>
        simp [Halted, needStateEmbed,
          evalStepCompositeMachine, needExprCompositeMachine,
          inputStateEmbed, P01InputNodeCompositeNTM.inputNodeCompositeMachine,
          P01NTMRunLaws.liftConfig, NTM.successors, NTM.stepBranch,
          List.map_map, Function.comp_def, Tape.write, Tape.move] at hactive ⊢

/-- Exact terminal-preserving simulation of the complete `haveValue` NTM. -/
def haveSimulation :
    P01NTMRunLaws.Simulation
      haveValueCompositeMachine evalStepCompositeMachine haveStateEmbed where
  accepting := by
    intro q
    cases q <;> rfl
  rejecting := by
    intro q
    cases q <;> rfl
  successors := by
    intro c hactive
    rcases c with ⟨q, tape⟩
    cases q <;>
      simp [Halted, haveStateEmbed,
        evalStepCompositeMachine, haveValueCompositeMachine,
        P01NTMRunLaws.liftConfig, NTM.successors, NTM.stepBranch,
        List.map_map, Function.comp_def, Tape.write, Tape.move] at hactive ⊢

/-- Run transport for the `needExpr` arm. -/
theorem need_runBranches_map
    (n : Nat)
    (xs : List (Configuration NeedExprCompositeState (Option Bool))) :
    evalStepCompositeMachine.runBranches n
      (xs.map (P01NTMRunLaws.liftConfig needStateEmbed)) =
    (needExprCompositeMachine.runBranches n xs).map
      (P01NTMRunLaws.liftConfig needStateEmbed) :=
  P01NTMRunLaws.runBranches_map
    needExprCompositeMachine evalStepCompositeMachine
      needStateEmbed needSimulation n xs

/-- Run transport for the `haveValue` arm. -/
theorem have_runBranches_map
    (n : Nat)
    (xs : List (Configuration HaveValueCompositeState (Option Bool))) :
    evalStepCompositeMachine.runBranches n
      (xs.map (P01NTMRunLaws.liftConfig haveStateEmbed)) =
    (haveValueCompositeMachine.runBranches n xs).map
      (P01NTMRunLaws.liftConfig haveStateEmbed) :=
  P01NTMRunLaws.runBranches_map
    haveValueCompositeMachine evalStepCompositeMachine
      haveStateEmbed haveSimulation n xs

#print axioms MCore.Real.P01EvalStepCompositeNTM.needSimulation
#print axioms MCore.Real.P01EvalStepCompositeNTM.haveSimulation
#print axioms MCore.Real.P01EvalStepCompositeNTM.need_runBranches_map
#print axioms MCore.Real.P01EvalStepCompositeNTM.have_runBranches_map

end P01EvalStepCompositeNTM
end Real
end MCore
