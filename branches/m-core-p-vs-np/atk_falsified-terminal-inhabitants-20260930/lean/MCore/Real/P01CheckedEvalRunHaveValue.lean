import MCore.Real.P01CheckedEvalRunInputTag
import MCore.Real.P01EvalCursorFramePop
import MCore.Real.P01EvalCursorFramePush
import MCore.Real.MachineRunLemmas

namespace MCore
namespace Real
namespace P01CheckedEvalRunHaveValue

open CanonicalFinalProof
open P01NTMRunLaws
open P01EncodedStackEvaluator
open P01EncodedFrameTape
open P01EvalCursorMachine
open P01EvalFramePopMachineV2
open P01EvalCursorFramePop
open P01EvalFramePushMachine
open P01EvalCursorFramePush
open P01HaveValueCompositeNTM
open P01NeedExprCompositeNTM
open P01CheckedEvalRunLoopNTM
open P01CNFMode
open MachineRunLemmas

abbrev CheckedConfig :=
  Configuration CheckedEvalRunState (Option Bool)

def havePopCheckedConfig
    (mode : SyntaxMode)
    (v : Bool)
    (c : Configuration FramePopState (Option Bool)) :
    CheckedConfig :=
  { state := .have mode (.pop v c.state), tape := c.tape }

def havePushCheckedConfig
    (mode : SyntaxMode)
    (frame : EvalFrame)
    (c : Configuration FramePushState (Option Bool)) :
    CheckedConfig :=
  { state := .have mode (.push frame c.state), tape := c.tape }

@[simp] theorem haveStart_not_halted
    (mode : SyntaxMode)
    (v : Bool) (tape : Tape (Option Bool)) :
    ¬ Halted checkedEvalRunLoopMachine
      ({ state := .have mode (.start v), tape := tape } : CheckedConfig) := by
  simp [Halted, checkedEvalRunLoopMachine]

@[simp] theorem havePeek_not_halted
    (mode : SyntaxMode)
    (v : Bool) (tape : Tape (Option Bool)) :
    ¬ Halted checkedEvalRunLoopMachine
      ({ state := .have mode (.peek v), tape := tape } : CheckedConfig) := by
  simp [Halted, checkedEvalRunLoopMachine]

@[simp] theorem havePopChecked_not_halted
    (mode : SyntaxMode)
    (v : Bool)
    (c : Configuration FramePopState (Option Bool)) :
    ¬ Halted checkedEvalRunLoopMachine (havePopCheckedConfig mode v c) := by
  simp [Halted, havePopCheckedConfig, checkedEvalRunLoopMachine]

@[simp] theorem havePushChecked_not_halted
    (mode : SyntaxMode)
    (frame : EvalFrame)
    (c : Configuration FramePushState (Option Bool)) :
    ¬ Halted checkedEvalRunLoopMachine (havePushCheckedConfig mode frame c) := by
  simp [Halted, havePushCheckedConfig, checkedEvalRunLoopMachine]

theorem havePopChecked_successors_active
    (mode : SyntaxMode)
    (v : Bool)
    (c : Configuration FramePopState (Option Bool))
    (h : framePopMachine.halting c.state = false) :
    checkedEvalRunLoopMachine.successors (havePopCheckedConfig mode v c) =
      [havePopCheckedConfig mode v (framePopMachine.step c)] := by
  rcases c with ⟨q, tape⟩
  unfold NTM.successors
  simp only [havePopCheckedConfig]
  cases q <;>
    simp [checkedEvalRunLoopMachine, haveValueCompositeMachine,
      haveCheckedEmbed, framePopMachine, modeAfterFrame,
      NTM.stepBranch, TM.step, Tape.write, Tape.move] at h ⊢

theorem havePushChecked_successors_active
    (mode : SyntaxMode)
    (frame : EvalFrame)
    (c : Configuration FramePushState (Option Bool))
    (h : framePushMachine.halting c.state = false) :
    checkedEvalRunLoopMachine.successors (havePushCheckedConfig mode frame c) =
      [havePushCheckedConfig mode frame (framePushMachine.step c)] := by
  rcases c with ⟨q, tape⟩
  unfold NTM.successors
  simp only [havePushCheckedConfig]
  cases q <;>
    simp [checkedEvalRunLoopMachine, haveValueCompositeMachine,
      haveCheckedEmbed, framePushMachine,
      NTM.stepBranch, TM.step, Tape.write, Tape.move] at h ⊢

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

theorem havePopChecked_run_reachable
    (mode : SyntaxMode)
    (v : Bool) (n : Nat)
    (c : Configuration FramePopState (Option Bool)) :
    ∃ m ≤ n,
      havePopCheckedConfig mode v (framePopMachine.run n c) ∈
        checkedEvalRunLoopMachine.runBranches m
          [havePopCheckedConfig mode v c] :=
  tm_phase_run_reachable framePopMachine (havePopCheckedConfig mode v)
    (havePopChecked_not_halted mode v)
    (havePopChecked_successors_active mode v) n c

theorem havePushChecked_run_reachable
    (mode : SyntaxMode)
    (frame : EvalFrame) (n : Nat)
    (c : Configuration FramePushState (Option Bool)) :
    ∃ m ≤ n,
      havePushCheckedConfig mode frame (framePushMachine.run n c) ∈
        checkedEvalRunLoopMachine.runBranches m
          [havePushCheckedConfig mode frame c] :=
  tm_phase_run_reachable framePushMachine (havePushCheckedConfig mode frame)
    (havePushChecked_not_halted mode frame)
    (havePushChecked_successors_active mode frame) n c

private theorem one_step_of_successor
    (a b : CheckedConfig)
    (ha : ¬ Halted checkedEvalRunLoopMachine a)
    (hs : b ∈ checkedEvalRunLoopMachine.successors a) :
    b ∈ checkedEvalRunLoopMachine.runBranches 1 [a] := by
  have h :=
    mem_runBranches_succ_of_successor
      checkedEvalRunLoopMachine 0 [a] a b
      (by simp [NTM.runBranches]) ha hs
  simpa using h

/-- Common nonempty-frame prefix in the checked loop. -/
theorem frame_checked_reaches_popped
    (mode : SyntaxMode)
    (witness unread frameStack : BitString)
    (consumed padding : Nat)
    (v : Bool) (frame : EvalFrame) :
    ∃ m ≤ 8,
      havePopCheckedConfig mode v
        { state := .halt frame,
          tape :=
            evalCursorStackEndTape witness consumed unread
              frameStack (padding + 3) } ∈
        checkedEvalRunLoopMachine.runBranches m
          [{ state := .have mode (.start v),
             tape :=
               evalCursorStackEndTape witness consumed unread
                 (encodeEvalFrame frame ++ frameStack) padding }] := by
  let t0 :=
    evalCursorStackEndTape witness consumed unread
      (encodeEvalFrame frame ++ frameStack) padding
  let tPeek := Tape.move none .left t0
  let c0 : CheckedConfig :=
    { state := .have mode (.start v), tape := t0 }
  let cPeek : CheckedConfig :=
    { state := .have mode (.peek v), tape := tPeek }
  let cPop0 : Configuration FramePopState (Option Bool) :=
    framePopConfig t0
  let cPopH : Configuration FramePopState (Option Bool) :=
    { state := .halt frame,
      tape :=
        evalCursorStackEndTape witness consumed unread
          frameStack (padding + 3) }

  have h0blank : t0.head = none := by
    dsimp [t0]
    simp [evalCursorStackEndTape]

  have hStartSucc :
      cPeek ∈ checkedEvalRunLoopMachine.successors c0 := by
    change
      cPeek ∈
        (haveValueCompositeMachine.successors
          ({ state := .start v, tape := t0 } :
            Configuration HaveValueCompositeState (Option Bool))).map
          (fun d =>
            ({ state := haveCheckedEmbed mode d.state, tape := d.tape } :
              CheckedConfig))
    rw [start_successors v t0 h0blank]
    simp [cPeek, tPeek, haveCheckedEmbed]
  have hStart :
      cPeek ∈ checkedEvalRunLoopMachine.runBranches 1 [c0] :=
    one_step_of_successor c0 cPeek
      (haveStart_not_halted mode v t0) hStartSucc

  have hPeekHead : tPeek.head = some (frameBit0 frame) := by
    dsimp [tPeek, t0]
    rw [encodeEvalFrame_eq_bits]
    simp [evalCursorStackEndTape, Tape.move]

  have hPeekSucc :
      havePopCheckedConfig mode v cPop0 ∈
        checkedEvalRunLoopMachine.successors cPeek := by
    dsimp [cPeek, cPop0, havePopCheckedConfig]
    cases frame <;>
      simp [checkedEvalRunLoopMachine, framePopConfig, framePopMachine,
        hPeekHead, tPeek, t0, encodeEvalFrame_eq_bits,
        evalCursorStackEndTape, NTM.successors, NTM.stepBranch,
        Tape.write, Tape.move, List.append_assoc]

  have hPeek :
      havePopCheckedConfig mode v cPop0 ∈
        checkedEvalRunLoopMachine.runBranches 1 [cPeek] :=
    one_step_of_successor cPeek (havePopCheckedConfig mode v cPop0)
      (havePeek_not_halted mode v tPeek) hPeekSucc

  have hToPop :=
    mem_runBranches_trans checkedEvalRunLoopMachine
      1 1 [c0] cPeek (havePopCheckedConfig mode v cPop0)
      hStart hPeek

  have hPopExact :
      framePopMachine.run 6 cPop0 = cPopH := by
    dsimp [cPop0, cPopH, t0]
    exact framePop_run_six_cursor
      witness unread consumed frameStack padding frame

  obtain ⟨mP, hmP, hP⟩ :=
    havePopChecked_run_reachable mode v 6 cPop0
  have hP' :
      havePopCheckedConfig mode v cPopH ∈
        checkedEvalRunLoopMachine.runBranches mP
          [havePopCheckedConfig mode v cPop0] := by
    rw [hPopExact] at hP
    exact hP

  have hAll :=
    mem_runBranches_trans checkedEvalRunLoopMachine
      2 mP [c0] (havePopCheckedConfig mode v cPop0)
      (havePopCheckedConfig mode v cPopH) hToPop hP'
  refine ⟨2 + mP, by omega, ?_⟩
  dsimp [c0, cPopH, t0] at hAll ⊢
  simpa [havePopCheckedConfig] using hAll

/-- A popped frame whose submachine produces a value restarts haveValue under
the finite mode selected by `modeAfterFrame`. -/
theorem valueFrame_checked_reaches_have
    (mode : SyntaxMode)
    (witness unread frameStack : BitString)
    (consumed padding : Nat)
    (v : Bool) (frame : EvalFrame) (result : Bool)
    (hhandoff :
      ∀ tape : Tape (Option Bool),
        haveValueCompositeMachine.successors
          { state := .pop v (.halt frame), tape := tape } =
          [{ state := .doneValue result, tape := tape }]) :
    ∃ m ≤ 9,
      ({ state := .have (modeAfterFrame mode frame) (.start result),
         tape :=
           evalCursorStackEndTape witness consumed unread
             frameStack (padding + 3) } : CheckedConfig) ∈
        checkedEvalRunLoopMachine.runBranches m
          [{ state := .have mode (.start v),
             tape :=
               evalCursorStackEndTape witness consumed unread
                 (encodeEvalFrame frame ++ frameStack) padding }] := by
  obtain ⟨m, hm, hPop⟩ :=
    frame_checked_reaches_popped
      mode witness unread frameStack consumed padding v frame

  let nextMode := modeAfterFrame mode frame
  let tRest :=
    evalCursorStackEndTape witness consumed unread
      frameStack (padding + 3)
  let cPop : CheckedConfig :=
    { state := .have mode (.pop v (.halt frame)), tape := tRest }
  let cHave : CheckedConfig :=
    { state := .have nextMode (.start result), tape := tRest }

  have hSucc :
      cHave ∈ checkedEvalRunLoopMachine.successors cPop := by
    change
      ({ state := .have nextMode (.start result), tape := tRest } :
        CheckedConfig) ∈
      checkedEvalRunLoopMachine.successors
        ({ state := .have mode (.pop v (.halt frame)), tape := tRest } :
          CheckedConfig)
    rw [show checkedEvalRunLoopMachine.successors
        ({ state := .have mode (.pop v (.halt frame)), tape := tRest } :
          CheckedConfig) =
      (haveValueCompositeMachine.successors
        ({ state := .pop v (.halt frame), tape := tRest } :
          Configuration HaveValueCompositeState (Option Bool))).map
        (fun d =>
          ({ state := haveCheckedEmbed nextMode d.state, tape := d.tape } :
            CheckedConfig)) by
        simp [checkedEvalRunLoopMachine, nextMode, modeAfterFrame,
          NTM.successors, NTM.stepBranch, Tape.write, Tape.move]]
    rw [hhandoff tRest]
    simp [haveCheckedEmbed, nextMode]

  have hOne :
      cHave ∈ checkedEvalRunLoopMachine.runBranches 1 [cPop] :=
    one_step_of_successor cPop cHave
      (havePopChecked_not_halted mode v
        { state := .halt frame, tape := tRest }) hSucc

  have hAll :=
    mem_runBranches_trans checkedEvalRunLoopMachine
      m 1
      [{ state := .have mode (.start v),
         tape :=
           evalCursorStackEndTape witness consumed unread
             (encodeEvalFrame frame ++ frameStack) padding }]
      cPop cHave hPop hOne

  refine ⟨m + 1, by omega, ?_⟩
  dsimp [cPop, cHave, tRest, nextMode] at hAll ⊢
  simpa using hAll

theorem negReturn_checked_reaches_have
    (mode : SyntaxMode)
    (witness unread frameStack : BitString)
    (consumed padding : Nat)
    (v : Bool) :
    ∃ m ≤ 9,
      ({ state := .have mode (.start (!v)),
         tape :=
           evalCursorStackEndTape witness consumed unread
             frameStack (padding + 3) } : CheckedConfig) ∈
        checkedEvalRunLoopMachine.runBranches m
          [{ state := .have mode (.start v),
             tape :=
               evalCursorStackEndTape witness consumed unread
                 (encodeEvalFrame .neg ++ frameStack) padding }] := by
  simpa [modeAfterFrame] using
    valueFrame_checked_reaches_have
      mode witness unread frameStack consumed padding
      v .neg (!v) (pop_neg_handoff_successors v)

theorem andRightReturn_checked_reaches_have
    (mode : SyntaxMode)
    (witness unread frameStack : BitString)
    (consumed padding : Nat)
    (l v : Bool) :
    ∃ m ≤ 9,
      ({ state := .have .cnf (.start (Bool.and l v)),
         tape :=
           evalCursorStackEndTape witness consumed unread
             frameStack (padding + 3) } : CheckedConfig) ∈
        checkedEvalRunLoopMachine.runBranches m
          [{ state := .have mode (.start v),
             tape :=
               evalCursorStackEndTape witness consumed unread
                 (encodeEvalFrame (.andRight l) ++ frameStack) padding }] := by
  simpa [modeAfterFrame] using
    valueFrame_checked_reaches_have
      mode witness unread frameStack consumed padding
      v (.andRight l) (Bool.and l v)
      (pop_andRight_handoff_successors l v)

theorem orRightReturn_checked_reaches_have
    (mode : SyntaxMode)
    (witness unread frameStack : BitString)
    (consumed padding : Nat)
    (l v : Bool) :
    ∃ m ≤ 9,
      ({ state := .have .clause (.start (Bool.or l v)),
         tape :=
           evalCursorStackEndTape witness consumed unread
             frameStack (padding + 3) } : CheckedConfig) ∈
        checkedEvalRunLoopMachine.runBranches m
          [{ state := .have mode (.start v),
             tape :=
               evalCursorStackEndTape witness consumed unread
                 (encodeEvalFrame (.orRight l) ++ frameStack) padding }] := by
  simpa [modeAfterFrame] using
    valueFrame_checked_reaches_have
      mode witness unread frameStack consumed padding
      v (.orRight l) (Bool.or l v)
      (pop_orRight_handoff_successors l v)

/-- A popped left binary frame changes the finite syntax mode, pushes the
matching right frame, and restarts needExpr under that mode. -/
theorem leftFrame_checked_reaches_need
    (mode : SyntaxMode)
    (witness unread frameStack : BitString)
    (consumed padding : Nat)
    (v : Bool)
    (oldFrame newFrame : EvalFrame)
    (hhandoff :
      ∀ tape : Tape (Option Bool),
        haveValueCompositeMachine.successors
          { state := .pop v (.halt oldFrame), tape := tape } =
          [{ state := .push newFrame (.start newFrame), tape := tape }]) :
    ∃ m ≤ 13,
      ({ state := .need (modeAfterFrame mode oldFrame)
           needExprCompositeMachine.initial,
         tape :=
           evalCursorStackEndTape witness consumed unread
             (encodeEvalFrame newFrame ++ frameStack)
             ((((padding + 3) - 1) - 1) - 1) } : CheckedConfig) ∈
        checkedEvalRunLoopMachine.runBranches m
          [{ state := .have mode (.start v),
             tape :=
               evalCursorStackEndTape witness consumed unread
                 (encodeEvalFrame oldFrame ++ frameStack) padding }] := by
  obtain ⟨m0, hm0, h0⟩ :=
    frame_checked_reaches_popped
      mode witness unread frameStack consumed padding v oldFrame

  let nextMode := modeAfterFrame mode oldFrame
  let tRest :=
    evalCursorStackEndTape witness consumed unread
      frameStack (padding + 3)
  let tPushed :=
    evalCursorStackEndTape witness consumed unread
      (encodeEvalFrame newFrame ++ frameStack)
      ((((padding + 3) - 1) - 1) - 1)
  let cPop : CheckedConfig :=
    { state := .have mode (.pop v (.halt oldFrame)), tape := tRest }
  let cPush0 : Configuration FramePushState (Option Bool) :=
    framePushConfig newFrame tRest
  let cPushH : Configuration FramePushState (Option Bool) :=
    { state := .halt, tape := tPushed }
  let cDone : CheckedConfig :=
    { state := .need nextMode needExprCompositeMachine.initial, tape := tPushed }

  have hHandSucc :
      havePushCheckedConfig nextMode newFrame cPush0 ∈
        checkedEvalRunLoopMachine.successors cPop := by
    change
      ({ state := .have nextMode (.push newFrame (.start newFrame)),
         tape := tRest } : CheckedConfig) ∈
      checkedEvalRunLoopMachine.successors
        ({ state := .have mode (.pop v (.halt oldFrame)),
           tape := tRest } : CheckedConfig)
    rw [show checkedEvalRunLoopMachine.successors
        ({ state := .have mode (.pop v (.halt oldFrame)),
           tape := tRest } : CheckedConfig) =
      (haveValueCompositeMachine.successors
        ({ state := .pop v (.halt oldFrame), tape := tRest } :
          Configuration HaveValueCompositeState (Option Bool))).map
        (fun d =>
          ({ state := haveCheckedEmbed nextMode d.state, tape := d.tape } :
            CheckedConfig)) by
        simp [checkedEvalRunLoopMachine, nextMode, modeAfterFrame,
          NTM.successors, NTM.stepBranch, Tape.write, Tape.move]]
    rw [hhandoff tRest]
    simp [havePushCheckedConfig, framePushConfig, haveCheckedEmbed, nextMode]

  have hHand :
      havePushCheckedConfig nextMode newFrame cPush0 ∈
        checkedEvalRunLoopMachine.runBranches 1 [cPop] :=
    one_step_of_successor cPop
      (havePushCheckedConfig nextMode newFrame cPush0)
      (havePopChecked_not_halted mode v
        { state := .halt oldFrame, tape := tRest }) hHandSucc

  have hToPush :=
    mem_runBranches_trans checkedEvalRunLoopMachine
      m0 1
      [{ state := .have mode (.start v),
         tape :=
           evalCursorStackEndTape witness consumed unread
             (encodeEvalFrame oldFrame ++ frameStack) padding }]
      cPop (havePushCheckedConfig nextMode newFrame cPush0) h0 hHand

  have hPushExact :
      framePushMachine.run 3 cPush0 = cPushH := by
    dsimp [cPush0, cPushH, tRest, tPushed]
    exact framePush_run_three_cursor_exact
      witness unread frameStack consumed (padding + 3) newFrame

  obtain ⟨mP, hmP, hP⟩ :=
    havePushChecked_run_reachable nextMode newFrame 3 cPush0
  have hP' :
      havePushCheckedConfig nextMode newFrame cPushH ∈
        checkedEvalRunLoopMachine.runBranches mP
          [havePushCheckedConfig nextMode newFrame cPush0] := by
    rw [hPushExact] at hP
    exact hP

  have hThroughPush :=
    mem_runBranches_trans checkedEvalRunLoopMachine
      (m0 + 1) mP
      [{ state := .have mode (.start v),
         tape :=
           evalCursorStackEndTape witness consumed unread
             (encodeEvalFrame oldFrame ++ frameStack) padding }]
      (havePushCheckedConfig nextMode newFrame cPush0)
      (havePushCheckedConfig nextMode newFrame cPushH)
      hToPush hP'

  have hFinalSucc :
      cDone ∈ checkedEvalRunLoopMachine.successors
        (havePushCheckedConfig nextMode newFrame cPushH) := by
    change
      ({ state := .need nextMode needExprCompositeMachine.initial,
         tape := tPushed } : CheckedConfig) ∈
      checkedEvalRunLoopMachine.successors
        ({ state := .have nextMode (.push newFrame .halt),
           tape := tPushed } : CheckedConfig)
    simp [checkedEvalRunLoopMachine, haveValueCompositeMachine,
      haveCheckedEmbed, NTM.successors, NTM.stepBranch,
      Tape.write, Tape.move]

  have hFinal :
      cDone ∈ checkedEvalRunLoopMachine.runBranches 1
        [havePushCheckedConfig nextMode newFrame cPushH] :=
    one_step_of_successor
      (havePushCheckedConfig nextMode newFrame cPushH) cDone
      (havePushChecked_not_halted nextMode newFrame cPushH) hFinalSucc

  have hAll :=
    mem_runBranches_trans checkedEvalRunLoopMachine
      ((m0 + 1) + mP) 1
      [{ state := .have mode (.start v),
         tape :=
           evalCursorStackEndTape witness consumed unread
             (encodeEvalFrame oldFrame ++ frameStack) padding }]
      (havePushCheckedConfig nextMode newFrame cPushH) cDone
      hThroughPush hFinal

  refine ⟨((m0 + 1) + mP) + 1, by omega, ?_⟩
  dsimp [cDone, tPushed, nextMode] at hAll ⊢
  simpa using hAll

theorem andLeftReturn_checked_reaches_need
    (mode : SyntaxMode)
    (witness unread frameStack : BitString)
    (consumed padding : Nat)
    (v : Bool) :
    ∃ m ≤ 13,
      ({ state := .need .cnf needExprCompositeMachine.initial,
         tape :=
           evalCursorStackEndTape witness consumed unread
             (encodeEvalFrame (.andRight v) ++ frameStack)
             ((((padding + 3) - 1) - 1) - 1) } : CheckedConfig) ∈
        checkedEvalRunLoopMachine.runBranches m
          [{ state := .have mode (.start v),
             tape :=
               evalCursorStackEndTape witness consumed unread
                 (encodeEvalFrame .andLeft ++ frameStack) padding }] := by
  simpa [modeAfterFrame] using
    leftFrame_checked_reaches_need
      mode witness unread frameStack consumed padding v
      .andLeft (.andRight v) (pop_andLeft_handoff_successors v)

theorem orLeftReturn_checked_reaches_need
    (mode : SyntaxMode)
    (witness unread frameStack : BitString)
    (consumed padding : Nat)
    (v : Bool) :
    ∃ m ≤ 13,
      ({ state := .need .clause needExprCompositeMachine.initial,
         tape :=
           evalCursorStackEndTape witness consumed unread
             (encodeEvalFrame (.orRight v) ++ frameStack)
             ((((padding + 3) - 1) - 1) - 1) } : CheckedConfig) ∈
        checkedEvalRunLoopMachine.runBranches m
          [{ state := .have mode (.start v),
             tape :=
               evalCursorStackEndTape witness consumed unread
                 (encodeEvalFrame .orLeft ++ frameStack) padding }] := by
  simpa [modeAfterFrame] using
    leftFrame_checked_reaches_need
      mode witness unread frameStack consumed padding v
      .orLeft (.orRight v) (pop_orLeft_handoff_successors v)

#print axioms MCore.Real.P01CheckedEvalRunHaveValue.frame_checked_reaches_popped
#print axioms MCore.Real.P01CheckedEvalRunHaveValue.valueFrame_checked_reaches_have
#print axioms MCore.Real.P01CheckedEvalRunHaveValue.negReturn_checked_reaches_have
#print axioms MCore.Real.P01CheckedEvalRunHaveValue.andRightReturn_checked_reaches_have
#print axioms MCore.Real.P01CheckedEvalRunHaveValue.orRightReturn_checked_reaches_have
#print axioms MCore.Real.P01CheckedEvalRunHaveValue.leftFrame_checked_reaches_need
#print axioms MCore.Real.P01CheckedEvalRunHaveValue.andLeftReturn_checked_reaches_need
#print axioms MCore.Real.P01CheckedEvalRunHaveValue.orLeftReturn_checked_reaches_need

end P01CheckedEvalRunHaveValue
end Real
end MCore
