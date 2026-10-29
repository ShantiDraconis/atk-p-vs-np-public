import MCore.Real.P01CheckedEvalRunLoopNTM
import MCore.Real.P01NTMRunLaws
import MCore.Real.MachineRunLemmas

namespace MCore
namespace Real
namespace P01CheckedEvalRunPhaseLift

open CanonicalFinalProof
open P01NTMRunLaws
open P01CheckedEvalRunLoopNTM
open P01NeedExprCompositeNTM
open P01NeedExprTagDecode
open P01EvalCursorMachine
open P01EvalCursorRoundTrip
open P01EvalFramePushMachine
open P01CNFMode
open MachineRunLemmas

abbrev CheckedConfig :=
  Configuration CheckedEvalRunState (Option Bool)

def seekConfig
    (mode : SyntaxMode)
    (c : Configuration CursorSeekState (Option Bool)) :
    CheckedConfig :=
  { state := .need mode (.seek c.state), tape := c.tape }

def decodeConfig
    (mode : SyntaxMode)
    (c : Configuration P01NeedExprTagDecode.TagDecodeState (Option Bool)) :
    CheckedConfig :=
  { state := .need mode (.decode c.state), tape := c.tape }

def retValueConfig
    (mode : SyntaxMode) (value : Bool)
    (c : Configuration CursorReturnState (Option Bool)) :
    CheckedConfig :=
  { state := .need mode (.retValue value c.state), tape := c.tape }

def retPushConfig
    (mode : SyntaxMode) (frame : P01EncodedStackEvaluator.EvalFrame)
    (c : Configuration CursorReturnState (Option Bool)) :
    CheckedConfig :=
  { state := .need mode (.retPush frame c.state), tape := c.tape }

def pushConfig
    (mode : SyntaxMode) (frame : P01EncodedStackEvaluator.EvalFrame)
    (c : Configuration FramePushState (Option Bool)) :
    CheckedConfig :=
  { state := .need mode (.push frame c.state), tape := c.tape }

@[simp] theorem seekConfig_not_halted
    (mode : SyntaxMode)
    (c : Configuration CursorSeekState (Option Bool)) :
    ¬ Halted checkedEvalRunLoopMachine (seekConfig mode c) := by
  simp [Halted, seekConfig, checkedEvalRunLoopMachine]

@[simp] theorem decodeConfig_not_halted
    (mode : SyntaxMode)
    (c : Configuration P01NeedExprTagDecode.TagDecodeState (Option Bool)) :
    ¬ Halted checkedEvalRunLoopMachine (decodeConfig mode c) := by
  simp [Halted, decodeConfig, checkedEvalRunLoopMachine]

@[simp] theorem retValueConfig_not_halted
    (mode : SyntaxMode) (value : Bool)
    (c : Configuration CursorReturnState (Option Bool)) :
    ¬ Halted checkedEvalRunLoopMachine (retValueConfig mode value c) := by
  simp [Halted, retValueConfig, checkedEvalRunLoopMachine]

@[simp] theorem retPushConfig_not_halted
    (mode : SyntaxMode)
    (frame : P01EncodedStackEvaluator.EvalFrame)
    (c : Configuration CursorReturnState (Option Bool)) :
    ¬ Halted checkedEvalRunLoopMachine (retPushConfig mode frame c) := by
  simp [Halted, retPushConfig, checkedEvalRunLoopMachine]

@[simp] theorem pushConfig_not_halted
    (mode : SyntaxMode)
    (frame : P01EncodedStackEvaluator.EvalFrame)
    (c : Configuration FramePushState (Option Bool)) :
    ¬ Halted checkedEvalRunLoopMachine (pushConfig mode frame c) := by
  simp [Halted, pushConfig, checkedEvalRunLoopMachine]

theorem seek_successors_active
    (mode : SyntaxMode)
    (c : Configuration CursorSeekState (Option Bool))
    (h : cursorSeekMachine.halting c.state = false) :
    checkedEvalRunLoopMachine.successors (seekConfig mode c) =
      [seekConfig mode (cursorSeekMachine.step c)] := by
  rcases c with ⟨q, tape⟩
  cases q <;>
    simp [seekConfig, checkedEvalRunLoopMachine,
      P01NeedExprCompositeNTM.needExprCompositeMachine, needCheckedEmbed,
      NTM.successors, NTM.stepBranch, TM.step,
      cursorSeekMachine, Tape.write, Tape.move] at h ⊢

theorem decode_successors_active
    (mode : SyntaxMode)
    (c : Configuration P01NeedExprTagDecode.TagDecodeState (Option Bool))
    (h : P01NeedExprTagDecode.tagDecodeMachine.halting c.state = false) :
    checkedEvalRunLoopMachine.successors (decodeConfig mode c) =
      [decodeConfig mode (P01NeedExprTagDecode.tagDecodeMachine.step c)] := by
  rcases c with ⟨q, tape⟩
  cases q <;>
    simp [decodeConfig, checkedEvalRunLoopMachine,
      P01NeedExprCompositeNTM.needExprCompositeMachine, needCheckedEmbed,
      NTM.successors, NTM.stepBranch, TM.step,
      P01NeedExprTagDecode.tagDecodeMachine, Tape.write, Tape.move] at h ⊢

theorem retValue_successors_active
    (mode : SyntaxMode) (value : Bool)
    (c : Configuration CursorReturnState (Option Bool))
    (h : cursorReturnMachine.halting c.state = false) :
    checkedEvalRunLoopMachine.successors (retValueConfig mode value c) =
      [retValueConfig mode value (cursorReturnMachine.step c)] := by
  rcases c with ⟨q, tape⟩
  cases q <;>
    simp [retValueConfig, checkedEvalRunLoopMachine,
      P01NeedExprCompositeNTM.needExprCompositeMachine,
      needCheckedEmbed, NTM.successors, NTM.stepBranch,
      TM.step, cursorReturnMachine, Tape.write, Tape.move] at h ⊢

theorem retPush_successors_active
    (mode : SyntaxMode)
    (frame : P01EncodedStackEvaluator.EvalFrame)
    (c : Configuration CursorReturnState (Option Bool))
    (h : cursorReturnMachine.halting c.state = false) :
    checkedEvalRunLoopMachine.successors (retPushConfig mode frame c) =
      [retPushConfig mode frame (cursorReturnMachine.step c)] := by
  rcases c with ⟨q, tape⟩
  cases q <;>
    simp [retPushConfig, checkedEvalRunLoopMachine,
      P01NeedExprCompositeNTM.needExprCompositeMachine,
      needCheckedEmbed, NTM.successors, NTM.stepBranch,
      TM.step, cursorReturnMachine, Tape.write, Tape.move] at h ⊢

theorem push_successors_active
    (mode : SyntaxMode)
    (frame : P01EncodedStackEvaluator.EvalFrame)
    (c : Configuration FramePushState (Option Bool))
    (h : framePushMachine.halting c.state = false) :
    checkedEvalRunLoopMachine.successors (pushConfig mode frame c) =
      [pushConfig mode frame (framePushMachine.step c)] := by
  rcases c with ⟨q, tape⟩
  cases q <;>
    simp [pushConfig, checkedEvalRunLoopMachine,
      P01NeedExprCompositeNTM.needExprCompositeMachine,
      needCheckedEmbed, NTM.successors, NTM.stepBranch,
      TM.step, framePushMachine, Tape.write, Tape.move] at h ⊢

private theorem tm_phase_run_reachable
    {S : Type}
    (M : TM S (Option Bool))
    (embed : Configuration S (Option Bool) → CheckedConfig)
    (embed_not_halted :
      ∀ c, ¬ Halted checkedEvalRunLoopMachine (embed c))
    (step_successors :
      ∀ c, M.halting c.state = false →
        checkedEvalRunLoopMachine.successors (embed c) =
          [embed (M.step c)]) :
    ∀ (n : Nat) (c : Configuration S (Option Bool)),
      ∃ m ≤ n,
        embed (M.run n c) ∈
          checkedEvalRunLoopMachine.runBranches m [embed c] := by
  intro n
  induction n with
  | zero =>
      intro c
      refine ⟨0, by omega, ?_⟩
      change embed c ∈ [embed c]
      simp
  | succ n ih =>
      intro c
      cases hhalt : M.halting c.state with
      | true =>
          have hr := run_halted M c hhalt (n + 1)
          refine ⟨0, by omega, ?_⟩
          rw [hr]
          simp [NTM.runBranches]
      | false =>
          obtain ⟨m, hm, hmem⟩ := ih (M.step c)
          have hsucc :
              embed (M.step c) ∈
                checkedEvalRunLoopMachine.successors (embed c) := by
            rw [step_successors c hhalt]
            simp
          have hone :
              embed (M.step c) ∈
                checkedEvalRunLoopMachine.runBranches 1 [embed c] := by
            have h :=
              mem_runBranches_succ_of_successor
                checkedEvalRunLoopMachine 0 [embed c]
                (embed c) (embed (M.step c))
                (by simp [NTM.runBranches])
                (embed_not_halted c) hsucc
            simpa using h
          have htrans :=
            mem_runBranches_trans checkedEvalRunLoopMachine
              1 m [embed c]
              (embed (M.step c))
              (embed (M.run n (M.step c)))
              hone hmem
          refine ⟨1 + m, by omega, ?_⟩
          simpa [TM.run, hhalt] using htrans

theorem seek_run_reachable
    (mode : SyntaxMode) (n : Nat)
    (c : Configuration CursorSeekState (Option Bool)) :
    ∃ m ≤ n,
      seekConfig mode (cursorSeekMachine.run n c) ∈
        checkedEvalRunLoopMachine.runBranches m [seekConfig mode c] :=
  tm_phase_run_reachable cursorSeekMachine (seekConfig mode)
    (seekConfig_not_halted mode) (seek_successors_active mode) n c

theorem decode_run_reachable
    (mode : SyntaxMode) (n : Nat)
    (c : Configuration P01NeedExprTagDecode.TagDecodeState (Option Bool)) :
    ∃ m ≤ n,
      decodeConfig mode (P01NeedExprTagDecode.tagDecodeMachine.run n c) ∈
        checkedEvalRunLoopMachine.runBranches m [decodeConfig mode c] :=
  tm_phase_run_reachable P01NeedExprTagDecode.tagDecodeMachine (decodeConfig mode)
    (decodeConfig_not_halted mode) (decode_successors_active mode) n c

theorem retValue_run_reachable
    (mode : SyntaxMode) (value : Bool) (n : Nat)
    (c : Configuration CursorReturnState (Option Bool)) :
    ∃ m ≤ n,
      retValueConfig mode value (cursorReturnMachine.run n c) ∈
        checkedEvalRunLoopMachine.runBranches m [retValueConfig mode value c] :=
  tm_phase_run_reachable cursorReturnMachine (retValueConfig mode value)
    (retValueConfig_not_halted mode value)
    (retValue_successors_active mode value) n c

theorem retPush_run_reachable
    (mode : SyntaxMode)
    (frame : P01EncodedStackEvaluator.EvalFrame)
    (n : Nat)
    (c : Configuration CursorReturnState (Option Bool)) :
    ∃ m ≤ n,
      retPushConfig mode frame (cursorReturnMachine.run n c) ∈
        checkedEvalRunLoopMachine.runBranches m [retPushConfig mode frame c] :=
  tm_phase_run_reachable cursorReturnMachine (retPushConfig mode frame)
    (retPushConfig_not_halted mode frame)
    (retPush_successors_active mode frame) n c

theorem push_run_reachable
    (mode : SyntaxMode)
    (frame : P01EncodedStackEvaluator.EvalFrame)
    (n : Nat)
    (c : Configuration FramePushState (Option Bool)) :
    ∃ m ≤ n,
      pushConfig mode frame (framePushMachine.run n c) ∈
        checkedEvalRunLoopMachine.runBranches m [pushConfig mode frame c] :=
  tm_phase_run_reachable framePushMachine (pushConfig mode frame)
    (pushConfig_not_halted mode frame)
    (push_successors_active mode frame) n c

#print axioms MCore.Real.P01CheckedEvalRunPhaseLift.seek_run_reachable
#print axioms MCore.Real.P01CheckedEvalRunPhaseLift.decode_run_reachable
#print axioms MCore.Real.P01CheckedEvalRunPhaseLift.retValue_run_reachable
#print axioms MCore.Real.P01CheckedEvalRunPhaseLift.retPush_run_reachable
#print axioms MCore.Real.P01CheckedEvalRunPhaseLift.push_run_reachable

end P01CheckedEvalRunPhaseLift
end Real
end MCore
