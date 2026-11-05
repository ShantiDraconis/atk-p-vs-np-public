import MCore.Real.P01CheckedVerifierCompositeNTM
import MCore.Real.P01IntegratedAssembly

namespace MCore
namespace Real
namespace P01CheckedVerifierFiniteState

open P01IntegratedAssembly
open P01CheckedVerifierCompositeNTM

deriving instance Fintype for P01EncodedStackEvaluator.EvalFrame
deriving instance Fintype for P01InputReturnMode.InputReturnMode
deriving instance Fintype for P01InputReturnMode.InputReturnClassifyState
deriving instance Fintype for P01InputIndexLookahead.InputIndexLookaheadState
deriving instance Fintype for P01WitnessIndexedReadPreserving.PreservingReadState
deriving instance Fintype for P01InputAfterReadReturn.InputAfterReadReturnState
deriving instance Fintype for P01InputNodeCompositeNTM.InputNodeCompositeState
deriving instance Fintype for P01EvalCursorMachine.CursorSeekState
deriving instance Fintype for P01EvalCursorRoundTrip.CursorReturnState
deriving instance Fintype for P01NeedExprTagDecode.NeedExprTag
deriving instance Fintype for P01NeedExprTagDecode.TagDecodeState
deriving instance Fintype for P01EvalFramePushMachine.FramePushState
deriving instance Fintype for P01EvalFramePopMachineV2.FramePopState
deriving instance Fintype for P01NeedExprCompositeNTM.NeedExprCompositeState
deriving instance Fintype for P01HaveValueCompositeNTM.HaveValueCompositeState
deriving instance Fintype for P01CNFMode.SyntaxMode
deriving instance Fintype for P01CheckedEvalRunLoopNTM.CheckedEvalRunState
deriving instance Fintype for CheckedVerifierState

/-- One spare code is intentionally left unreachable, exactly as in the
previous verifier relabelling. -/
def checkedVerifierStateCount : Nat :=
  Fintype.card CheckedVerifierState

noncomputable def checkedVerifierStateEquiv :
    CheckedVerifierState ≃ Fin (Fintype.card CheckedVerifierState) :=
  Fintype.equivFin CheckedVerifierState

noncomputable def checkedVerifierStateEncode
    (q : CheckedVerifierState) :
    Fin (checkedVerifierStateCount + 1) :=
  ⟨(checkedVerifierStateEquiv q).val,
    Nat.lt_succ_of_lt (checkedVerifierStateEquiv q).isLt⟩

noncomputable def checkedVerifierStateDecode
    (q : Fin (checkedVerifierStateCount + 1)) :
    CheckedVerifierState :=
  if h : q.val < Fintype.card CheckedVerifierState then
    checkedVerifierStateEquiv.symm ⟨q.val, h⟩
  else
    checkedVerifierMachine.initial

theorem checkedVerifierStateDecode_encode
    (q : CheckedVerifierState) :
    checkedVerifierStateDecode (checkedVerifierStateEncode q) = q := by
  unfold checkedVerifierStateDecode checkedVerifierStateEncode
    checkedVerifierStateCount
  simp [checkedVerifierStateEquiv]

/-- Concrete Fin-indexed checked verifier, obtained only by control-state
relabeling. No transition or tape behavior is changed. -/
noncomputable def checkedVerifierFinMachine :
    NTM (Fin (checkedVerifierStateCount + 1)) (Option Bool) :=
  P01IntegratedAssembly.relabel
    checkedVerifierMachine
    checkedVerifierStateEncode
    checkedVerifierStateDecode

@[simp] theorem checkedVerifierFinMachine_blank :
    checkedVerifierFinMachine.blank = none := rfl

theorem checkedVerifierFinMachine_haltsWithin_iff
    (n : Nat)
    (c : Configuration CheckedVerifierState (Option Bool)) :
    checkedVerifierFinMachine.HaltsWithin n
        (P01NTMRunLaws.liftConfig checkedVerifierStateEncode c) ↔
      checkedVerifierMachine.HaltsWithin n c := by
  exact P01IntegratedAssembly.relabel_haltsWithin_iff
    checkedVerifierMachine
    checkedVerifierStateEncode
    checkedVerifierStateDecode
    checkedVerifierStateDecode_encode
    n c

theorem checkedVerifierFinMachine_acceptsWithin_iff
    (n : Nat)
    (c : Configuration CheckedVerifierState (Option Bool)) :
    checkedVerifierFinMachine.AcceptsWithin n
        (P01NTMRunLaws.liftConfig checkedVerifierStateEncode c) ↔
      checkedVerifierMachine.AcceptsWithin n c := by
  exact P01IntegratedAssembly.relabel_acceptsWithin_iff
    checkedVerifierMachine
    checkedVerifierStateEncode
    checkedVerifierStateDecode
    checkedVerifierStateDecode_encode
    n c

#print axioms MCore.Real.P01CheckedVerifierFiniteState.checkedVerifierStateDecode_encode
#print axioms MCore.Real.P01CheckedVerifierFiniteState.checkedVerifierFinMachine_haltsWithin_iff
#print axioms MCore.Real.P01CheckedVerifierFiniteState.checkedVerifierFinMachine_acceptsWithin_iff

end P01CheckedVerifierFiniteState
end Real
end MCore
