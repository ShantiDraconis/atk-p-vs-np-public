import MCore.Real.P01HaveValueCompositeNTM
import MCore.Real.P01NTMRunLaws

namespace MCore
namespace Real
namespace P01HaveValueCompositeRun

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

abbrev HaveValueConfig :=
  Configuration HaveValueCompositeState (Option Bool)

def popConfig
    (v : Bool)
    (c : Configuration FramePopState (Option Bool)) :
    HaveValueConfig :=
  { state := .pop v c.state, tape := c.tape }

def pushConfig
    (frame : EvalFrame)
    (c : Configuration FramePushState (Option Bool)) :
    HaveValueConfig :=
  { state := .push frame c.state, tape := c.tape }

@[simp] theorem start_not_halted
    (v : Bool) (tape : Tape (Option Bool)) :
    ¬ Halted haveValueCompositeMachine
      ({ state := .start v, tape := tape } : HaveValueConfig) := by
  simp [Halted, haveValueCompositeMachine]

@[simp] theorem peek_not_halted
    (v : Bool) (tape : Tape (Option Bool)) :
    ¬ Halted haveValueCompositeMachine
      ({ state := .peek v, tape := tape } : HaveValueConfig) := by
  simp [Halted, haveValueCompositeMachine]

@[simp] theorem popConfig_not_halted
    (v : Bool)
    (c : Configuration FramePopState (Option Bool)) :
    ¬ Halted haveValueCompositeMachine (popConfig v c) := by
  simp [Halted, popConfig, haveValueCompositeMachine]

@[simp] theorem pushConfig_not_halted
    (frame : EvalFrame)
    (c : Configuration FramePushState (Option Bool)) :
    ¬ Halted haveValueCompositeMachine (pushConfig frame c) := by
  simp [Halted, pushConfig, haveValueCompositeMachine]

theorem pop_successors_active
    (v : Bool)
    (c : Configuration FramePopState (Option Bool))
    (h : framePopMachine.halting c.state = false) :
    haveValueCompositeMachine.successors (popConfig v c) =
      [popConfig v (framePopMachine.step c)] := by
  unfold NTM.successors
  simp only [popConfig]
  rw [pop_transition_active v c.state c.tape.head h]
  simp [popConfig, NTM.stepBranch, TM.step,
    framePopMachine, haveValueCompositeMachine,
    Tape.write, Tape.move]

theorem push_successors_active
    (frame : EvalFrame)
    (c : Configuration FramePushState (Option Bool))
    (h : framePushMachine.halting c.state = false) :
    haveValueCompositeMachine.successors (pushConfig frame c) =
      [pushConfig frame (framePushMachine.step c)] := by
  unfold NTM.successors
  simp only [pushConfig]
  rw [push_transition_active frame c.state c.tape.head h]
  simp [pushConfig, NTM.stepBranch, TM.step,
    framePushMachine, haveValueCompositeMachine,
    Tape.write, Tape.move]

private theorem tm_phase_run_reachable
    {S : Type}
    (M : TM S (Option Bool))
    (embed : Configuration S (Option Bool) → HaveValueConfig)
    (embed_not_halted :
      ∀ c, ¬ Halted haveValueCompositeMachine (embed c))
    (step_successors :
      ∀ c, M.halting c.state = false →
        haveValueCompositeMachine.successors (embed c) =
          [embed (M.step c)]) :
    ∀ (n : Nat) (c : Configuration S (Option Bool)),
      ∃ m ≤ n,
        embed (M.run n c) ∈
          haveValueCompositeMachine.runBranches m [embed c] := by
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
                haveValueCompositeMachine.successors (embed c) := by
            rw [step_successors c hhalt]
            simp
          have hone :
              embed (M.step c) ∈
                haveValueCompositeMachine.runBranches 1 [embed c] := by
            have h :=
              mem_runBranches_succ_of_successor
                haveValueCompositeMachine 0 [embed c]
                (embed c) (embed (M.step c))
                (by simp [NTM.runBranches])
                (embed_not_halted c) hsucc
            simpa using h
          have htrans :=
            mem_runBranches_trans haveValueCompositeMachine
              1 m [embed c]
              (embed (M.step c))
              (embed (M.run n (M.step c)))
              hone hmem
          refine ⟨1 + m, by omega, ?_⟩
          simpa [TM.run, hhalt] using htrans

theorem pop_run_reachable
    (v : Bool) (n : Nat)
    (c : Configuration FramePopState (Option Bool)) :
    ∃ m ≤ n,
      popConfig v (framePopMachine.run n c) ∈
        haveValueCompositeMachine.runBranches m [popConfig v c] :=
  tm_phase_run_reachable
    framePopMachine (popConfig v)
    (popConfig_not_halted v)
    (pop_successors_active v) n c

theorem push_run_reachable
    (frame : EvalFrame) (n : Nat)
    (c : Configuration FramePushState (Option Bool)) :
    ∃ m ≤ n,
      pushConfig frame (framePushMachine.run n c) ∈
        haveValueCompositeMachine.runBranches m [pushConfig frame c] :=
  tm_phase_run_reachable
    framePushMachine (pushConfig frame)
    (pushConfig_not_halted frame)
    (push_successors_active frame) n c

private theorem one_step_of_successor
    (a b : HaveValueConfig)
    (ha : ¬ Halted haveValueCompositeMachine a)
    (hs : b ∈ haveValueCompositeMachine.successors a) :
    b ∈ haveValueCompositeMachine.runBranches 1 [a] := by
  have h :=
    mem_runBranches_succ_of_successor
      haveValueCompositeMachine 0 [a] a b
      (by simp [NTM.runBranches]) ha hs
  simpa using h

/-- A semantic terminal value with an empty continuation stack is physically
stable: two finite-control steps inspect the empty stack and restore the
canonical stack-end head. -/
theorem empty_frames_reaches_doneValue
    (witness unread : BitString)
    (consumed padding : Nat)
    (v : Bool) :
    ∃ m ≤ 2,
      ({ state := .doneValue v,
         tape :=
           evalCursorStackEndTape witness consumed unread [] padding } :
        HaveValueConfig) ∈
      haveValueCompositeMachine.runBranches m
        [{ state := .start v,
           tape :=
             evalCursorStackEndTape witness consumed unread [] padding }] := by
  let t0 :=
    evalCursorStackEndTape witness consumed unread [] padding
  let tPeek := Tape.move none .left t0
  let c0 : HaveValueConfig := { state := .start v, tape := t0 }
  let cPeek : HaveValueConfig := { state := .peek v, tape := tPeek }
  let cDone : HaveValueConfig := { state := .doneValue v, tape := t0 }

  have hStartSucc :
      cPeek ∈ haveValueCompositeMachine.successors c0 := by
    dsimp [c0, cPeek, tPeek]
    rw [start_successors v t0 rfl]
    simp

  have hStart :
      cPeek ∈ haveValueCompositeMachine.runBranches 1 [c0] :=
    one_step_of_successor c0 cPeek (start_not_halted v t0) hStartSucc

  have hPeekBlank : tPeek.head = none := by
    dsimp [tPeek, t0]
    simp [evalCursorStackEndTape, Tape.move]

  have hPeekSucc :
      cDone ∈ haveValueCompositeMachine.successors cPeek := by
    dsimp [cPeek, cDone]
    rw [empty_handoff_successors v tPeek hPeekBlank]
    simp [tPeek, t0, evalCursorStackEndTape, Tape.move]

  have hPeek :
      cDone ∈ haveValueCompositeMachine.runBranches 1 [cPeek] :=
    one_step_of_successor cPeek cDone
      (peek_not_halted v tPeek) hPeekSucc

  have hAll :=
    mem_runBranches_trans haveValueCompositeMachine
      1 1 [c0] cPeek cDone hStart hPeek
  refine ⟨2, by omega, ?_⟩
  dsimp [c0, cDone, t0] at hAll ⊢
  simpa using hAll

/-- Common prefix for every nonempty continuation frame:
start → peek → six-step physical frame pop. -/
theorem frame_reaches_popped
    (witness unread frameStack : BitString)
    (consumed padding : Nat)
    (v : Bool) (frame : EvalFrame) :
    ∃ m ≤ 8,
      popConfig v
        { state := .halt frame,
          tape :=
            evalCursorStackEndTape witness consumed unread
              frameStack (padding + 3) } ∈
        haveValueCompositeMachine.runBranches m
          [{ state := .start v,
             tape :=
               evalCursorStackEndTape witness consumed unread
                 (encodeEvalFrame frame ++ frameStack) padding }] := by
  let t0 :=
    evalCursorStackEndTape witness consumed unread
      (encodeEvalFrame frame ++ frameStack) padding
  let tPeek := Tape.move none .left t0
  let c0 : HaveValueConfig := { state := .start v, tape := t0 }
  let cPeek : HaveValueConfig := { state := .peek v, tape := tPeek }
  let cPop0 : Configuration FramePopState (Option Bool) :=
    framePopConfig t0
  let cPopH : Configuration FramePopState (Option Bool) :=
    { state := .halt frame,
      tape :=
        evalCursorStackEndTape witness consumed unread
          frameStack (padding + 3) }

  have hStartSucc :
      cPeek ∈ haveValueCompositeMachine.successors c0 := by
    dsimp [c0, cPeek, tPeek]
    rw [start_successors v t0 rfl]
    simp
  have hStart :
      cPeek ∈ haveValueCompositeMachine.runBranches 1 [c0] :=
    one_step_of_successor c0 cPeek (start_not_halted v t0) hStartSucc

  have hPeekHead : tPeek.head = some (frameBit0 frame) := by
    dsimp [tPeek, t0]
    rw [encodeEvalFrame_eq_bits]
    simp [evalCursorStackEndTape, Tape.move]

  have hPeekSucc :
      popConfig v cPop0 ∈
        haveValueCompositeMachine.successors cPeek := by
    dsimp [cPeek, cPop0, popConfig]
    rw [nonempty_handoff_successors v (frameBit0 frame) tPeek hPeekHead]
    simp [framePopConfig, framePopMachine, tPeek, t0,
      encodeEvalFrame_eq_bits, evalCursorStackEndTape,
      Tape.move, List.append_assoc]

  have hPeek :
      popConfig v cPop0 ∈
        haveValueCompositeMachine.runBranches 1 [cPeek] :=
    one_step_of_successor cPeek (popConfig v cPop0)
      (peek_not_halted v tPeek) hPeekSucc

  have hToPop :=
    mem_runBranches_trans haveValueCompositeMachine
      1 1 [c0] cPeek (popConfig v cPop0) hStart hPeek

  have hPopExact :
      framePopMachine.run 6 cPop0 = cPopH := by
    dsimp [cPop0, cPopH, t0]
    exact framePop_run_six_cursor
      witness unread consumed frameStack padding frame

  obtain ⟨mP, hmP, hP⟩ := pop_run_reachable v 6 cPop0
  have hP' :
      popConfig v cPopH ∈
        haveValueCompositeMachine.runBranches mP [popConfig v cPop0] := by
    rw [hPopExact] at hP
    exact hP

  have hAll :=
    mem_runBranches_trans haveValueCompositeMachine
      2 mP [c0] (popConfig v cPop0) (popConfig v cPopH)
      hToPop hP'
  refine ⟨2 + mP, by omega, ?_⟩
  dsimp [c0, cPopH, t0] at hAll ⊢
  simpa [popConfig] using hAll

/-- Negation continuation. -/
theorem neg_reaches_doneValue
    (witness unread frameStack : BitString)
    (consumed padding : Nat)
    (v : Bool) :
    ∃ m ≤ 9,
      ({ state := .doneValue (!v),
         tape :=
           evalCursorStackEndTape witness consumed unread
             frameStack (padding + 3) } : HaveValueConfig) ∈
        haveValueCompositeMachine.runBranches m
          [{ state := .start v,
             tape :=
               evalCursorStackEndTape witness consumed unread
                 (encodeEvalFrame .neg ++ frameStack) padding }] := by
  obtain ⟨m, hm, hmem⟩ :=
    frame_reaches_popped
      witness unread frameStack consumed padding v .neg
  let cPop : HaveValueConfig :=
    popConfig v
      { state := FramePopState.halt .neg,
        tape :=
          evalCursorStackEndTape witness consumed unread
            frameStack (padding + 3) }
  let cDone : HaveValueConfig :=
    { state := .doneValue (!v),
      tape :=
        evalCursorStackEndTape witness consumed unread
          frameStack (padding + 3) }
  have hSucc :
      cDone ∈ haveValueCompositeMachine.successors cPop := by
    dsimp [cPop, cDone, popConfig]
    rw [pop_neg_handoff_successors]
    simp
  have hOne :
      cDone ∈ haveValueCompositeMachine.runBranches 1 [cPop] :=
    one_step_of_successor cPop cDone
      (popConfig_not_halted v
        { state := FramePopState.halt .neg,
          tape :=
            evalCursorStackEndTape witness consumed unread
              frameStack (padding + 3) }) hSucc
  have hAll :=
    mem_runBranches_trans haveValueCompositeMachine
      m 1
      [{ state := .start v,
         tape :=
           evalCursorStackEndTape witness consumed unread
             (encodeEvalFrame .neg ++ frameStack) padding }]
      cPop cDone hmem hOne
  refine ⟨m + 1, by omega, ?_⟩
  dsimp [cPop, cDone] at hAll ⊢
  simpa using hAll

/-- Right-hand conjunction continuation. -/
theorem andRight_reaches_doneValue
    (witness unread frameStack : BitString)
    (consumed padding : Nat)
    (l v : Bool) :
    ∃ m ≤ 9,
      ({ state := .doneValue (Bool.and l v),
         tape :=
           evalCursorStackEndTape witness consumed unread
             frameStack (padding + 3) } : HaveValueConfig) ∈
        haveValueCompositeMachine.runBranches m
          [{ state := .start v,
             tape :=
               evalCursorStackEndTape witness consumed unread
                 (encodeEvalFrame (.andRight l) ++ frameStack) padding }] := by
  obtain ⟨m, hm, hmem⟩ :=
    frame_reaches_popped
      witness unread frameStack consumed padding v (.andRight l)
  let cPop : HaveValueConfig :=
    popConfig v
      { state := FramePopState.halt (.andRight l),
        tape :=
          evalCursorStackEndTape witness consumed unread
            frameStack (padding + 3) }
  let cDone : HaveValueConfig :=
    { state := .doneValue (Bool.and l v),
      tape :=
        evalCursorStackEndTape witness consumed unread
          frameStack (padding + 3) }
  have hSucc :
      cDone ∈ haveValueCompositeMachine.successors cPop := by
    dsimp [cPop, cDone, popConfig]
    rw [pop_andRight_handoff_successors]
    simp
  have hOne :
      cDone ∈ haveValueCompositeMachine.runBranches 1 [cPop] :=
    one_step_of_successor cPop cDone
      (popConfig_not_halted v
        { state := FramePopState.halt (.andRight l),
          tape :=
            evalCursorStackEndTape witness consumed unread
              frameStack (padding + 3) }) hSucc
  have hAll :=
    mem_runBranches_trans haveValueCompositeMachine
      m 1
      [{ state := .start v,
         tape :=
           evalCursorStackEndTape witness consumed unread
             (encodeEvalFrame (.andRight l) ++ frameStack) padding }]
      cPop cDone hmem hOne
  refine ⟨m + 1, by omega, ?_⟩
  dsimp [cPop, cDone] at hAll ⊢
  simpa using hAll

/-- Right-hand disjunction continuation. -/
theorem orRight_reaches_doneValue
    (witness unread frameStack : BitString)
    (consumed padding : Nat)
    (l v : Bool) :
    ∃ m ≤ 9,
      ({ state := .doneValue (Bool.or l v),
         tape :=
           evalCursorStackEndTape witness consumed unread
             frameStack (padding + 3) } : HaveValueConfig) ∈
        haveValueCompositeMachine.runBranches m
          [{ state := .start v,
             tape :=
               evalCursorStackEndTape witness consumed unread
                 (encodeEvalFrame (.orRight l) ++ frameStack) padding }] := by
  obtain ⟨m, hm, hmem⟩ :=
    frame_reaches_popped
      witness unread frameStack consumed padding v (.orRight l)
  let cPop : HaveValueConfig :=
    popConfig v
      { state := FramePopState.halt (.orRight l),
        tape :=
          evalCursorStackEndTape witness consumed unread
            frameStack (padding + 3) }
  let cDone : HaveValueConfig :=
    { state := .doneValue (Bool.or l v),
      tape :=
        evalCursorStackEndTape witness consumed unread
          frameStack (padding + 3) }
  have hSucc :
      cDone ∈ haveValueCompositeMachine.successors cPop := by
    dsimp [cPop, cDone, popConfig]
    rw [pop_orRight_handoff_successors]
    simp
  have hOne :
      cDone ∈ haveValueCompositeMachine.runBranches 1 [cPop] :=
    one_step_of_successor cPop cDone
      (popConfig_not_halted v
        { state := FramePopState.halt (.orRight l),
          tape :=
            evalCursorStackEndTape witness consumed unread
              frameStack (padding + 3) }) hSucc
  have hAll :=
    mem_runBranches_trans haveValueCompositeMachine
      m 1
      [{ state := .start v,
         tape :=
           evalCursorStackEndTape witness consumed unread
             (encodeEvalFrame (.orRight l) ++ frameStack) padding }]
      cPop cDone hmem hOne
  refine ⟨m + 1, by omega, ?_⟩
  dsimp [cPop, cDone] at hAll ⊢
  simpa using hAll

/-- Generic left-frame route: pop the old frame, push the derived right frame,
and return to a physical need-expression state. -/
theorem leftFrame_reaches_doneNeed
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
      ({ state := .doneNeed,
         tape :=
           evalCursorStackEndTape witness consumed unread
             (encodeEvalFrame newFrame ++ frameStack)
             ((((padding + 3) - 1) - 1) - 1) } : HaveValueConfig) ∈
        haveValueCompositeMachine.runBranches m
          [{ state := .start v,
             tape :=
               evalCursorStackEndTape witness consumed unread
                 (encodeEvalFrame oldFrame ++ frameStack) padding }] := by
  obtain ⟨m0, hm0, h0⟩ :=
    frame_reaches_popped
      witness unread frameStack consumed padding v oldFrame

  let tRest :=
    evalCursorStackEndTape witness consumed unread
      frameStack (padding + 3)
  let tPushed :=
    evalCursorStackEndTape witness consumed unread
      (encodeEvalFrame newFrame ++ frameStack)
      ((((padding + 3) - 1) - 1) - 1)
  let cPop : HaveValueConfig :=
    popConfig v { state := .halt oldFrame, tape := tRest }
  let cPush0 : Configuration FramePushState (Option Bool) :=
    framePushConfig newFrame tRest
  let cPushH : Configuration FramePushState (Option Bool) :=
    { state := .halt, tape := tPushed }
  let cDone : HaveValueConfig := { state := .doneNeed, tape := tPushed }

  have hHandSucc :
      pushConfig newFrame cPush0 ∈
        haveValueCompositeMachine.successors cPop := by
    change
      ({ state := .push newFrame (.start newFrame), tape := tRest } :
        HaveValueConfig) ∈
      haveValueCompositeMachine.successors
        ({ state := .pop v (.halt oldFrame), tape := tRest } :
          HaveValueConfig)
    rw [hhandoff tRest]
    simp
  have hHand :
      pushConfig newFrame cPush0 ∈
        haveValueCompositeMachine.runBranches 1 [cPop] :=
    one_step_of_successor cPop (pushConfig newFrame cPush0)
      (popConfig_not_halted v
        { state := .halt oldFrame, tape := tRest }) hHandSucc

  have hToPush :=
    mem_runBranches_trans haveValueCompositeMachine
      m0 1
      [{ state := .start v,
         tape :=
           evalCursorStackEndTape witness consumed unread
             (encodeEvalFrame oldFrame ++ frameStack) padding }]
      cPop (pushConfig newFrame cPush0) h0 hHand

  have hPushExact :
      framePushMachine.run 3 cPush0 = cPushH := by
    dsimp [cPush0, cPushH, tRest, tPushed]
    exact framePush_run_three_cursor_exact
      witness unread frameStack consumed (padding + 3) newFrame

  obtain ⟨mP, hmP, hP⟩ :=
    push_run_reachable newFrame 3 cPush0
  have hP' :
      pushConfig newFrame cPushH ∈
        haveValueCompositeMachine.runBranches mP
          [pushConfig newFrame cPush0] := by
    rw [hPushExact] at hP
    exact hP

  have hThroughPush :=
    mem_runBranches_trans haveValueCompositeMachine
      (m0 + 1) mP
      [{ state := .start v,
         tape :=
           evalCursorStackEndTape witness consumed unread
             (encodeEvalFrame oldFrame ++ frameStack) padding }]
      (pushConfig newFrame cPush0) (pushConfig newFrame cPushH)
      hToPush hP'

  have hFinalSucc :
      cDone ∈
        haveValueCompositeMachine.successors
          (pushConfig newFrame cPushH) := by
    dsimp [cDone, pushConfig, cPushH]
    rw [push_handoff_successors newFrame tPushed]
    simp
  have hFinal :
      cDone ∈
        haveValueCompositeMachine.runBranches 1
          [pushConfig newFrame cPushH] :=
    one_step_of_successor
      (pushConfig newFrame cPushH) cDone
      (pushConfig_not_halted newFrame cPushH) hFinalSucc

  have hAll :=
    mem_runBranches_trans haveValueCompositeMachine
      ((m0 + 1) + mP) 1
      [{ state := .start v,
         tape :=
           evalCursorStackEndTape witness consumed unread
             (encodeEvalFrame oldFrame ++ frameStack) padding }]
      (pushConfig newFrame cPushH) cDone hThroughPush hFinal

  refine ⟨((m0 + 1) + mP) + 1, by omega, ?_⟩
  dsimp [cDone, tPushed] at hAll ⊢
  simpa using hAll

theorem andLeft_reaches_doneNeed
    (witness unread frameStack : BitString)
    (consumed padding : Nat)
    (v : Bool) :
    ∃ m ≤ 13,
      ({ state := .doneNeed,
         tape :=
           evalCursorStackEndTape witness consumed unread
             (encodeEvalFrame (.andRight v) ++ frameStack)
             ((((padding + 3) - 1) - 1) - 1) } : HaveValueConfig) ∈
        haveValueCompositeMachine.runBranches m
          [{ state := .start v,
             tape :=
               evalCursorStackEndTape witness consumed unread
                 (encodeEvalFrame .andLeft ++ frameStack) padding }] := by
  apply leftFrame_reaches_doneNeed
    witness unread frameStack consumed padding v
      .andLeft (.andRight v)
  exact pop_andLeft_handoff_successors v

theorem orLeft_reaches_doneNeed
    (witness unread frameStack : BitString)
    (consumed padding : Nat)
    (v : Bool) :
    ∃ m ≤ 13,
      ({ state := .doneNeed,
         tape :=
           evalCursorStackEndTape witness consumed unread
             (encodeEvalFrame (.orRight v) ++ frameStack)
             ((((padding + 3) - 1) - 1) - 1) } : HaveValueConfig) ∈
        haveValueCompositeMachine.runBranches m
          [{ state := .start v,
             tape :=
               evalCursorStackEndTape witness consumed unread
                 (encodeEvalFrame .orLeft ++ frameStack) padding }] := by
  apply leftFrame_reaches_doneNeed
    witness unread frameStack consumed padding v
      .orLeft (.orRight v)
  exact pop_orLeft_handoff_successors v

#print axioms MCore.Real.P01HaveValueCompositeRun.empty_frames_reaches_doneValue
#print axioms MCore.Real.P01HaveValueCompositeRun.frame_reaches_popped
#print axioms MCore.Real.P01HaveValueCompositeRun.neg_reaches_doneValue
#print axioms MCore.Real.P01HaveValueCompositeRun.andRight_reaches_doneValue
#print axioms MCore.Real.P01HaveValueCompositeRun.orRight_reaches_doneValue
#print axioms MCore.Real.P01HaveValueCompositeRun.leftFrame_reaches_doneNeed
#print axioms MCore.Real.P01HaveValueCompositeRun.andLeft_reaches_doneNeed
#print axioms MCore.Real.P01HaveValueCompositeRun.orLeft_reaches_doneNeed

end P01HaveValueCompositeRun
end Real
end MCore
