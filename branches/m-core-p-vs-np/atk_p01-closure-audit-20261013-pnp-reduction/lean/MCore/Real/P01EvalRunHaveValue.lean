import MCore.Real.P01EvalRunInputTag
import MCore.Real.P01HaveValueCompositeRun

namespace MCore
namespace Real
namespace P01EvalRunHaveValue

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
open P01EvalRunLoopNTM
open P01EvalRunLoopRun

abbrev LoopConfig :=
  Configuration EvalRunLoopState (Option Bool)

def havePopLoopConfig
    (v : Bool)
    (c : Configuration FramePopState (Option Bool)) :
    LoopConfig :=
  { state := .have (.pop v c.state), tape := c.tape }

def havePushLoopConfig
    (frame : EvalFrame)
    (c : Configuration FramePushState (Option Bool)) :
    LoopConfig :=
  { state := .have (.push frame c.state), tape := c.tape }

@[simp] theorem haveStart_not_halted
    (v : Bool) (tape : Tape (Option Bool)) :
    ¬ Halted evalRunLoopMachine
      ({ state := .have (.start v), tape := tape } : LoopConfig) := by
  simp [Halted, evalRunLoopMachine]

@[simp] theorem havePeek_not_halted
    (v : Bool) (tape : Tape (Option Bool)) :
    ¬ Halted evalRunLoopMachine
      ({ state := .have (.peek v), tape := tape } : LoopConfig) := by
  simp [Halted, evalRunLoopMachine]

@[simp] theorem havePopLoop_not_halted
    (v : Bool)
    (c : Configuration FramePopState (Option Bool)) :
    ¬ Halted evalRunLoopMachine (havePopLoopConfig v c) := by
  simp [Halted, havePopLoopConfig, evalRunLoopMachine]

@[simp] theorem havePushLoop_not_halted
    (frame : EvalFrame)
    (c : Configuration FramePushState (Option Bool)) :
    ¬ Halted evalRunLoopMachine (havePushLoopConfig frame c) := by
  simp [Halted, havePushLoopConfig, evalRunLoopMachine]

theorem havePopLoop_successors_active
    (v : Bool)
    (c : Configuration FramePopState (Option Bool))
    (h : framePopMachine.halting c.state = false) :
    evalRunLoopMachine.successors (havePopLoopConfig v c) =
      [havePopLoopConfig v (framePopMachine.step c)] := by
  rcases c with ⟨q, tape⟩
  unfold NTM.successors
  simp only [havePopLoopConfig]
  cases q <;>
    simp [evalRunLoopMachine, haveValueCompositeMachine,
      haveLoopEmbed, framePopMachine, NTM.stepBranch, TM.step,
      Tape.write, Tape.move] at h ⊢

theorem havePushLoop_successors_active
    (frame : EvalFrame)
    (c : Configuration FramePushState (Option Bool))
    (h : framePushMachine.halting c.state = false) :
    evalRunLoopMachine.successors (havePushLoopConfig frame c) =
      [havePushLoopConfig frame (framePushMachine.step c)] := by
  rcases c with ⟨q, tape⟩
  unfold NTM.successors
  simp only [havePushLoopConfig]
  cases q <;>
    simp [evalRunLoopMachine, haveValueCompositeMachine,
      haveLoopEmbed, framePushMachine, NTM.stepBranch, TM.step,
      Tape.write, Tape.move] at h ⊢

private theorem tm_phase_run_reachable
    {S : Type}
    (M : TM S (Option Bool))
    (embed : Configuration S (Option Bool) → LoopConfig)
    (embed_not_halted :
      ∀ c, ¬ Halted evalRunLoopMachine (embed c))
    (step_successors :
      ∀ c, M.halting c.state = false →
        evalRunLoopMachine.successors (embed c) =
          [embed (M.step c)]) :
    ∀ (n : Nat) (c : Configuration S (Option Bool)),
      ∃ m ≤ n,
        embed (M.run n c) ∈
          evalRunLoopMachine.runBranches m [embed c] := by
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
          have hr := MachineRunLemmas.run_halted M c hhalt (n + 1)
          refine ⟨0, by omega, ?_⟩
          rw [hr]
          simp [NTM.runBranches]
      | false =>
          obtain ⟨m, hm, hmem⟩ := ih (M.step c)
          have hsucc :
              embed (M.step c) ∈
                evalRunLoopMachine.successors (embed c) := by
            rw [step_successors c hhalt]
            simp
          have hone :
              embed (M.step c) ∈
                evalRunLoopMachine.runBranches 1 [embed c] := by
            have h :=
              mem_runBranches_succ_of_successor
                evalRunLoopMachine 0 [embed c]
                (embed c) (embed (M.step c))
                (by simp [NTM.runBranches])
                (embed_not_halted c) hsucc
            simpa using h
          have htrans :=
            mem_runBranches_trans evalRunLoopMachine
              1 m [embed c]
              (embed (M.step c))
              (embed (M.run n (M.step c)))
              hone hmem
          refine ⟨1 + m, by omega, ?_⟩
          simpa [TM.run, hhalt] using htrans

theorem havePopLoop_run_reachable
    (v : Bool) (n : Nat)
    (c : Configuration FramePopState (Option Bool)) :
    ∃ m ≤ n,
      havePopLoopConfig v (framePopMachine.run n c) ∈
        evalRunLoopMachine.runBranches m [havePopLoopConfig v c] :=
  tm_phase_run_reachable
    framePopMachine (havePopLoopConfig v)
    (havePopLoop_not_halted v)
    (havePopLoop_successors_active v) n c

theorem havePushLoop_run_reachable
    (frame : EvalFrame) (n : Nat)
    (c : Configuration FramePushState (Option Bool)) :
    ∃ m ≤ n,
      havePushLoopConfig frame (framePushMachine.run n c) ∈
        evalRunLoopMachine.runBranches m [havePushLoopConfig frame c] :=
  tm_phase_run_reachable
    framePushMachine (havePushLoopConfig frame)
    (havePushLoop_not_halted frame)
    (havePushLoop_successors_active frame) n c

private theorem one_step_of_successor
    (a b : LoopConfig)
    (ha : ¬ Halted evalRunLoopMachine a)
    (hs : b ∈ evalRunLoopMachine.successors a) :
    b ∈ evalRunLoopMachine.runBranches 1 [a] := by
  have h :=
    mem_runBranches_succ_of_successor
      evalRunLoopMachine 0 [a] a b
      (by simp [NTM.runBranches]) ha hs
  simpa using h

/-- Empty continuation stack terminates the repeated evaluator physically. -/
theorem emptyFrames_loop_reaches_final
    (witness unread : BitString)
    (consumed padding : Nat)
    (v : Bool) :
    ∃ m ≤ 2,
      ({ state := .final v,
         tape :=
           evalCursorStackEndTape witness consumed unread [] padding } :
        LoopConfig) ∈
      evalRunLoopMachine.runBranches m
        [{ state := .have (.start v),
           tape :=
             evalCursorStackEndTape witness consumed unread [] padding }] := by
  let t0 := evalCursorStackEndTape witness consumed unread [] padding
  let tPeek := Tape.move none .left t0
  let c0 : LoopConfig := { state := .have (.start v), tape := t0 }
  let cPeek : LoopConfig := { state := .have (.peek v), tape := tPeek }
  let cFinal : LoopConfig := { state := .final v, tape := t0 }

  have h0blank : t0.head = none := by
    dsimp [t0]
    simp [evalCursorStackEndTape]
  have hStartSucc :
      cPeek ∈ evalRunLoopMachine.successors c0 := by
    change
      cPeek ∈
        (haveValueCompositeMachine.successors
          ({ state := .start v, tape := t0 } :
            Configuration HaveValueCompositeState (Option Bool))).map
          (fun d => ({ state := haveLoopEmbed d.state, tape := d.tape } :
            LoopConfig))
    rw [start_successors v t0 h0blank]
    simp [cPeek, tPeek, haveLoopEmbed]

  have hStart :
      cPeek ∈ evalRunLoopMachine.runBranches 1 [c0] :=
    one_step_of_successor c0 cPeek
      (haveStart_not_halted v t0) hStartSucc

  have hBlank : tPeek.head = none := by
    dsimp [tPeek, t0]
    simp [evalCursorStackEndTape, Tape.move]

  have hPeekSucc :
      cFinal ∈ evalRunLoopMachine.successors cPeek := by
    dsimp [cPeek, cFinal]
    rw [have_empty_final_successors v tPeek hBlank]
    simp [tPeek, t0, evalCursorStackEndTape, Tape.move]

  have hPeek :
      cFinal ∈ evalRunLoopMachine.runBranches 1 [cPeek] :=
    one_step_of_successor cPeek cFinal
      (havePeek_not_halted v tPeek) hPeekSucc

  have hAll :=
    mem_runBranches_trans evalRunLoopMachine
      1 1 [c0] cPeek cFinal hStart hPeek
  refine ⟨2, by omega, ?_⟩
  dsimp [c0, cFinal, t0] at hAll ⊢
  simpa using hAll

/-- Common nonempty-frame prefix: start, inspect, and physically pop one frame. -/
theorem frame_loop_reaches_popped
    (witness unread frameStack : BitString)
    (consumed padding : Nat)
    (v : Bool) (frame : EvalFrame) :
    ∃ m ≤ 8,
      havePopLoopConfig v
        { state := .halt frame,
          tape :=
            evalCursorStackEndTape witness consumed unread
              frameStack (padding + 3) } ∈
        evalRunLoopMachine.runBranches m
          [{ state := .have (.start v),
             tape :=
               evalCursorStackEndTape witness consumed unread
                 (encodeEvalFrame frame ++ frameStack) padding }] := by
  let t0 :=
    evalCursorStackEndTape witness consumed unread
      (encodeEvalFrame frame ++ frameStack) padding
  let tPeek := Tape.move none .left t0
  let c0 : LoopConfig := { state := .have (.start v), tape := t0 }
  let cPeek : LoopConfig := { state := .have (.peek v), tape := tPeek }
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
      cPeek ∈ evalRunLoopMachine.successors c0 := by
    change
      cPeek ∈
        (haveValueCompositeMachine.successors
          ({ state := .start v, tape := t0 } :
            Configuration HaveValueCompositeState (Option Bool))).map
          (fun d => ({ state := haveLoopEmbed d.state, tape := d.tape } :
            LoopConfig))
    rw [start_successors v t0 h0blank]
    simp [cPeek, tPeek, haveLoopEmbed]
  have hStart :
      cPeek ∈ evalRunLoopMachine.runBranches 1 [c0] :=
    one_step_of_successor c0 cPeek
      (haveStart_not_halted v t0) hStartSucc

  have hPeekHead : tPeek.head = some (frameBit0 frame) := by
    dsimp [tPeek, t0]
    rw [encodeEvalFrame_eq_bits]
    simp [evalCursorStackEndTape, Tape.move]

  have hPeekSucc :
      havePopLoopConfig v cPop0 ∈
        evalRunLoopMachine.successors cPeek := by
    dsimp [cPeek, cPop0, havePopLoopConfig]
    rw [have_nonempty_pop_successors v (frameBit0 frame) tPeek hPeekHead]
    simp [havePopLoopConfig, framePopConfig, framePopMachine,
      tPeek, t0, encodeEvalFrame_eq_bits,
      evalCursorStackEndTape, Tape.move, List.append_assoc]

  have hPeek :
      havePopLoopConfig v cPop0 ∈
        evalRunLoopMachine.runBranches 1 [cPeek] :=
    one_step_of_successor cPeek (havePopLoopConfig v cPop0)
      (havePeek_not_halted v tPeek) hPeekSucc

  have hToPop :=
    mem_runBranches_trans evalRunLoopMachine
      1 1 [c0] cPeek (havePopLoopConfig v cPop0)
      hStart hPeek

  have hPopExact :
      framePopMachine.run 6 cPop0 = cPopH := by
    dsimp [cPop0, cPopH, t0]
    exact framePop_run_six_cursor
      witness unread consumed frameStack padding frame

  obtain ⟨mP, hmP, hP⟩ :=
    havePopLoop_run_reachable v 6 cPop0
  have hP' :
      havePopLoopConfig v cPopH ∈
        evalRunLoopMachine.runBranches mP [havePopLoopConfig v cPop0] := by
    rw [hPopExact] at hP
    exact hP

  have hAll :=
    mem_runBranches_trans evalRunLoopMachine
      2 mP [c0] (havePopLoopConfig v cPop0)
      (havePopLoopConfig v cPopH) hToPop hP'
  refine ⟨2 + mP, by omega, ?_⟩
  dsimp [c0, cPopH, t0] at hAll ⊢
  simpa [havePopLoopConfig] using hAll

/-- Unary/binary right-result frame: one pop handoff immediately restarts haveValue. -/
theorem valueFrame_loop_reaches_have
    (witness unread frameStack : BitString)
    (consumed padding : Nat)
    (v : Bool) (frame : EvalFrame) (result : Bool)
    (hhandoff :
      ∀ tape : Tape (Option Bool),
        haveValueCompositeMachine.successors
          { state := .pop v (.halt frame), tape := tape } =
          [{ state := .doneValue result, tape := tape }]) :
    ∃ m ≤ 9,
      ({ state := .have (.start result),
         tape :=
           evalCursorStackEndTape witness consumed unread
             frameStack (padding + 3) } : LoopConfig) ∈
        evalRunLoopMachine.runBranches m
          [{ state := .have (.start v),
             tape :=
               evalCursorStackEndTape witness consumed unread
                 (encodeEvalFrame frame ++ frameStack) padding }] := by
  obtain ⟨m, hm, hPop⟩ :=
    frame_loop_reaches_popped
      witness unread frameStack consumed padding v frame

  let tRest :=
    evalCursorStackEndTape witness consumed unread
      frameStack (padding + 3)
  let cPop : LoopConfig :=
    { state := .have (.pop v (.halt frame)), tape := tRest }
  let cHave : LoopConfig :=
    { state := .have (.start result), tape := tRest }

  have hSucc :
      cHave ∈ evalRunLoopMachine.successors cPop := by
    change
      ({ state := .have (.start result), tape := tRest } : LoopConfig) ∈
      evalRunLoopMachine.successors
        ({ state := .have (.pop v (.halt frame)), tape := tRest } : LoopConfig)
    rw [show evalRunLoopMachine.successors
        ({ state := .have (.pop v (.halt frame)), tape := tRest } : LoopConfig) =
      (haveValueCompositeMachine.successors
        ({ state := .pop v (.halt frame), tape := tRest } :
          Configuration HaveValueCompositeState (Option Bool))).map
        (fun d => ({ state := haveLoopEmbed d.state, tape := d.tape } :
          LoopConfig)) by
        simp [evalRunLoopMachine, haveValueCompositeMachine,
          NTM.successors, NTM.stepBranch, haveLoopEmbed,
          Tape.write, Tape.move]]
    rw [hhandoff tRest]
    simp [haveLoopEmbed]

  have hOne :
      cHave ∈ evalRunLoopMachine.runBranches 1 [cPop] :=
    one_step_of_successor cPop cHave
      (havePopLoop_not_halted v
        { state := .halt frame, tape := tRest }) hSucc

  have hAll :=
    mem_runBranches_trans evalRunLoopMachine
      m 1
      [{ state := .have (.start v),
         tape :=
           evalCursorStackEndTape witness consumed unread
             (encodeEvalFrame frame ++ frameStack) padding }]
      cPop cHave hPop hOne

  refine ⟨m + 1, by omega, ?_⟩
  dsimp [cPop, cHave, tRest] at hAll ⊢
  simpa using hAll

theorem negReturn_loop_reaches_have
    (witness unread frameStack : BitString)
    (consumed padding : Nat)
    (v : Bool) :
    ∃ m ≤ 9,
      ({ state := .have (.start (!v)),
         tape :=
           evalCursorStackEndTape witness consumed unread
             frameStack (padding + 3) } : LoopConfig) ∈
        evalRunLoopMachine.runBranches m
          [{ state := .have (.start v),
             tape :=
               evalCursorStackEndTape witness consumed unread
                 (encodeEvalFrame .neg ++ frameStack) padding }] := by
  apply valueFrame_loop_reaches_have
    witness unread frameStack consumed padding v .neg (!v)
  exact pop_neg_handoff_successors v

theorem andRightReturn_loop_reaches_have
    (witness unread frameStack : BitString)
    (consumed padding : Nat)
    (l v : Bool) :
    ∃ m ≤ 9,
      ({ state := .have (.start (Bool.and l v)),
         tape :=
           evalCursorStackEndTape witness consumed unread
             frameStack (padding + 3) } : LoopConfig) ∈
        evalRunLoopMachine.runBranches m
          [{ state := .have (.start v),
             tape :=
               evalCursorStackEndTape witness consumed unread
                 (encodeEvalFrame (.andRight l) ++ frameStack) padding }] := by
  apply valueFrame_loop_reaches_have
    witness unread frameStack consumed padding v (.andRight l) (Bool.and l v)
  exact pop_andRight_handoff_successors l v

theorem orRightReturn_loop_reaches_have
    (witness unread frameStack : BitString)
    (consumed padding : Nat)
    (l v : Bool) :
    ∃ m ≤ 9,
      ({ state := .have (.start (Bool.or l v)),
         tape :=
           evalCursorStackEndTape witness consumed unread
             frameStack (padding + 3) } : LoopConfig) ∈
        evalRunLoopMachine.runBranches m
          [{ state := .have (.start v),
             tape :=
               evalCursorStackEndTape witness consumed unread
                 (encodeEvalFrame (.orRight l) ++ frameStack) padding }] := by
  apply valueFrame_loop_reaches_have
    witness unread frameStack consumed padding v (.orRight l) (Bool.or l v)
  exact pop_orRight_handoff_successors l v

/-- Left binary frame: pop the old frame, push the right-continuation frame,
then restart needExpr in the repeated loop. -/
theorem leftFrame_loop_reaches_need
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
      ({ state := .need needExprCompositeMachine.initial,
         tape :=
           evalCursorStackEndTape witness consumed unread
             (encodeEvalFrame newFrame ++ frameStack)
             ((((padding + 3) - 1) - 1) - 1) } : LoopConfig) ∈
        evalRunLoopMachine.runBranches m
          [{ state := .have (.start v),
             tape :=
               evalCursorStackEndTape witness consumed unread
                 (encodeEvalFrame oldFrame ++ frameStack) padding }] := by
  obtain ⟨m0, hm0, h0⟩ :=
    frame_loop_reaches_popped
      witness unread frameStack consumed padding v oldFrame

  let tRest :=
    evalCursorStackEndTape witness consumed unread
      frameStack (padding + 3)
  let tPushed :=
    evalCursorStackEndTape witness consumed unread
      (encodeEvalFrame newFrame ++ frameStack)
      ((((padding + 3) - 1) - 1) - 1)
  let cPop : LoopConfig :=
    { state := .have (.pop v (.halt oldFrame)), tape := tRest }
  let cPush0 : Configuration FramePushState (Option Bool) :=
    framePushConfig newFrame tRest
  let cPushH : Configuration FramePushState (Option Bool) :=
    { state := .halt, tape := tPushed }
  let cNeed : LoopConfig :=
    { state := .need needExprCompositeMachine.initial, tape := tPushed }

  have hHandSucc :
      havePushLoopConfig newFrame cPush0 ∈
        evalRunLoopMachine.successors cPop := by
    change
      ({ state := .have (.push newFrame (.start newFrame)), tape := tRest } :
        LoopConfig) ∈
      evalRunLoopMachine.successors
        ({ state := .have (.pop v (.halt oldFrame)), tape := tRest } :
          LoopConfig)
    rw [show evalRunLoopMachine.successors
        ({ state := .have (.pop v (.halt oldFrame)), tape := tRest } :
          LoopConfig) =
      (haveValueCompositeMachine.successors
        ({ state := .pop v (.halt oldFrame), tape := tRest } :
          Configuration HaveValueCompositeState (Option Bool))).map
        (fun d => ({ state := haveLoopEmbed d.state, tape := d.tape } :
          LoopConfig)) by
        simp [evalRunLoopMachine, haveValueCompositeMachine,
          NTM.successors, NTM.stepBranch, haveLoopEmbed,
          Tape.write, Tape.move]]
    rw [hhandoff tRest]
    simp [havePushLoopConfig, framePushConfig, haveLoopEmbed]

  have hHand :
      havePushLoopConfig newFrame cPush0 ∈
        evalRunLoopMachine.runBranches 1 [cPop] :=
    one_step_of_successor cPop (havePushLoopConfig newFrame cPush0)
      (havePopLoop_not_halted v
        { state := .halt oldFrame, tape := tRest }) hHandSucc

  have hToPush :=
    mem_runBranches_trans evalRunLoopMachine
      m0 1
      [{ state := .have (.start v),
         tape :=
           evalCursorStackEndTape witness consumed unread
             (encodeEvalFrame oldFrame ++ frameStack) padding }]
      cPop (havePushLoopConfig newFrame cPush0) h0 hHand

  have hPushExact :
      framePushMachine.run 3 cPush0 = cPushH := by
    dsimp [cPush0, cPushH, tRest, tPushed]
    exact framePush_run_three_cursor_exact
      witness unread frameStack consumed (padding + 3) newFrame

  obtain ⟨mP, hmP, hP⟩ :=
    havePushLoop_run_reachable newFrame 3 cPush0
  have hP' :
      havePushLoopConfig newFrame cPushH ∈
        evalRunLoopMachine.runBranches mP [havePushLoopConfig newFrame cPush0] := by
    rw [hPushExact] at hP
    exact hP

  have hThroughPush :=
    mem_runBranches_trans evalRunLoopMachine
      (m0 + 1) mP
      [{ state := .have (.start v),
         tape :=
           evalCursorStackEndTape witness consumed unread
             (encodeEvalFrame oldFrame ++ frameStack) padding }]
      (havePushLoopConfig newFrame cPush0)
      (havePushLoopConfig newFrame cPushH)
      hToPush hP'

  have hFinalSucc :
      cNeed ∈
        evalRunLoopMachine.successors (havePushLoopConfig newFrame cPushH) := by
    dsimp [cNeed, havePushLoopConfig, cPushH]
    simp [evalRunLoopMachine, haveValueCompositeMachine, haveLoopEmbed,
      NTM.successors, NTM.stepBranch, Tape.write, Tape.move]

  have hFinal :
      cNeed ∈
        evalRunLoopMachine.runBranches 1 [havePushLoopConfig newFrame cPushH] :=
    one_step_of_successor
      (havePushLoopConfig newFrame cPushH) cNeed
      (havePushLoop_not_halted newFrame cPushH) hFinalSucc

  have hAll :=
    mem_runBranches_trans evalRunLoopMachine
      ((m0 + 1) + mP) 1
      [{ state := .have (.start v),
         tape :=
           evalCursorStackEndTape witness consumed unread
             (encodeEvalFrame oldFrame ++ frameStack) padding }]
      (havePushLoopConfig newFrame cPushH) cNeed
      hThroughPush hFinal

  refine ⟨((m0 + 1) + mP) + 1, by omega, ?_⟩
  dsimp [cNeed, tPushed] at hAll ⊢
  simpa using hAll

theorem andLeftReturn_loop_reaches_need
    (witness unread frameStack : BitString)
    (consumed padding : Nat)
    (v : Bool) :
    ∃ m ≤ 13,
      ({ state := .need needExprCompositeMachine.initial,
         tape :=
           evalCursorStackEndTape witness consumed unread
             (encodeEvalFrame (.andRight v) ++ frameStack)
             ((((padding + 3) - 1) - 1) - 1) } : LoopConfig) ∈
        evalRunLoopMachine.runBranches m
          [{ state := .have (.start v),
             tape :=
               evalCursorStackEndTape witness consumed unread
                 (encodeEvalFrame .andLeft ++ frameStack) padding }] := by
  apply leftFrame_loop_reaches_need
    witness unread frameStack consumed padding v
      .andLeft (.andRight v)
  exact pop_andLeft_handoff_successors v

theorem orLeftReturn_loop_reaches_need
    (witness unread frameStack : BitString)
    (consumed padding : Nat)
    (v : Bool) :
    ∃ m ≤ 13,
      ({ state := .need needExprCompositeMachine.initial,
         tape :=
           evalCursorStackEndTape witness consumed unread
             (encodeEvalFrame (.orRight v) ++ frameStack)
             ((((padding + 3) - 1) - 1) - 1) } : LoopConfig) ∈
        evalRunLoopMachine.runBranches m
          [{ state := .have (.start v),
             tape :=
               evalCursorStackEndTape witness consumed unread
                 (encodeEvalFrame .orLeft ++ frameStack) padding }] := by
  apply leftFrame_loop_reaches_need
    witness unread frameStack consumed padding v
      .orLeft (.orRight v)
  exact pop_orLeft_handoff_successors v

#print axioms MCore.Real.P01EvalRunHaveValue.emptyFrames_loop_reaches_final
#print axioms MCore.Real.P01EvalRunHaveValue.frame_loop_reaches_popped
#print axioms MCore.Real.P01EvalRunHaveValue.valueFrame_loop_reaches_have
#print axioms MCore.Real.P01EvalRunHaveValue.negReturn_loop_reaches_have
#print axioms MCore.Real.P01EvalRunHaveValue.andRightReturn_loop_reaches_have
#print axioms MCore.Real.P01EvalRunHaveValue.orRightReturn_loop_reaches_have
#print axioms MCore.Real.P01EvalRunHaveValue.leftFrame_loop_reaches_need
#print axioms MCore.Real.P01EvalRunHaveValue.andLeftReturn_loop_reaches_need
#print axioms MCore.Real.P01EvalRunHaveValue.orLeftReturn_loop_reaches_need

end P01EvalRunHaveValue
end Real
end MCore
