import MCore.Real.P01EvalStepCompositeNTM

namespace MCore
namespace Real
namespace P01EvalStepCompositeRun

open P01NTMRunLaws
open P01NeedExprCompositeNTM
open P01NeedExprCompositeRun
open P01HaveValueCompositeNTM
open P01HaveValueCompositeRun
open P01EvalStepCompositeNTM

abbrev EvalStepConfig :=
  Configuration EvalStepCompositeState (Option Bool)

def liftNeedConfig
    (c : Configuration NeedExprCompositeState (Option Bool)) :
    EvalStepConfig :=
  P01NTMRunLaws.liftConfig needStateEmbed c

def liftHaveConfig
    (c : Configuration HaveValueCompositeState (Option Bool)) :
    EvalStepConfig :=
  P01NTMRunLaws.liftConfig haveStateEmbed c

/-- Membership transport from the certified needExpr submachine into the
single evalStep NTM, with exactly the same fuel. -/
theorem need_mem_lift
    (n : Nat)
    (a b : Configuration NeedExprCompositeState (Option Bool))
    (h :
      b ∈ needExprCompositeMachine.runBranches n [a]) :
    liftNeedConfig b ∈
      evalStepCompositeMachine.runBranches n [liftNeedConfig a] := by
  rw [show [liftNeedConfig a] =
      [a].map (P01NTMRunLaws.liftConfig needStateEmbed) by rfl]
  rw [need_runBranches_map]
  exact List.mem_map.mpr ⟨b, h, rfl⟩

/-- Membership transport from the certified haveValue submachine into the
single evalStep NTM, with exactly the same fuel. -/
theorem have_mem_lift
    (n : Nat)
    (a b : Configuration HaveValueCompositeState (Option Bool))
    (h :
      b ∈ haveValueCompositeMachine.runBranches n [a]) :
    liftHaveConfig b ∈
      evalStepCompositeMachine.runBranches n [liftHaveConfig a] := by
  rw [show [liftHaveConfig a] =
      [a].map (P01NTMRunLaws.liftConfig haveStateEmbed) by rfl]
  rw [have_runBranches_map]
  exact List.mem_map.mpr ⟨b, h, rfl⟩

@[simp] theorem liftNeed_doneNeed
    (tape : Tape (Option Bool)) :
    liftNeedConfig
      ({ state := NeedExprCompositeState.doneNeed, tape := tape } :
        Configuration NeedExprCompositeState (Option Bool)) =
      ({ state := EvalStepCompositeState.doneNeed, tape := tape } :
        EvalStepConfig) := rfl

@[simp] theorem liftNeed_doneValue
    (v : Bool) (tape : Tape (Option Bool)) :
    liftNeedConfig
      ({ state := NeedExprCompositeState.doneValue v, tape := tape } :
        Configuration NeedExprCompositeState (Option Bool)) =
      ({ state := EvalStepCompositeState.doneValue v, tape := tape } :
        EvalStepConfig) := rfl

@[simp] theorem liftHave_doneNeed
    (tape : Tape (Option Bool)) :
    liftHaveConfig
      ({ state := HaveValueCompositeState.doneNeed, tape := tape } :
        Configuration HaveValueCompositeState (Option Bool)) =
      ({ state := EvalStepCompositeState.doneNeed, tape := tape } :
        EvalStepConfig) := rfl

@[simp] theorem liftHave_doneValue
    (v : Bool) (tape : Tape (Option Bool)) :
    liftHaveConfig
      ({ state := HaveValueCompositeState.doneValue v, tape := tape } :
        Configuration HaveValueCompositeState (Option Bool)) =
      ({ state := EvalStepCompositeState.doneValue v, tape := tape } :
        EvalStepConfig) := rfl

#print axioms MCore.Real.P01EvalStepCompositeRun.need_mem_lift
#print axioms MCore.Real.P01EvalStepCompositeRun.have_mem_lift

end P01EvalStepCompositeRun
end Real
end MCore
