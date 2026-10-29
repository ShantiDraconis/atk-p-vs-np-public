import MCore.Real.P01EvalRunLoopNTM
import MCore.Real.P01NTMRunLaws

namespace MCore
namespace Real
namespace P01EvalRunLoopRun

open CanonicalFinalProof
open CanonicalCircuitBits
open P01NTMRunLaws
open P01EncodedStackEvaluator
open P01EncodedFrameTape
open P01EvalCursorMachine
open P01EvalCursorRoundTrip
open P01NeedExprTagDecode
open P01NeedExprCompositeNTM
open P01InputNodeCompositeNTM
open P01InputNodeCompositeRun
open P01InputNodeRoundTrip
open P01EvalFramePushMachine
open P01EvalCursorFramePush
open P01EvalRunLoopNTM

abbrev LoopConfig :=
  Configuration EvalRunLoopState (Option Bool)

def seekLoopConfig
    (c : Configuration CursorSeekState (Option Bool)) : LoopConfig :=
  { state := .need (.seek c.state), tape := c.tape }

def decodeLoopConfig
    (c : Configuration TagDecodeState (Option Bool)) : LoopConfig :=
  { state := .need (.decode c.state), tape := c.tape }

def retValueLoopConfig
    (value : Bool)
    (c : Configuration CursorReturnState (Option Bool)) : LoopConfig :=
  { state := .need (.retValue value c.state), tape := c.tape }


def retPushLoopConfig
    (frame : EvalFrame)
    (c : Configuration CursorReturnState (Option Bool)) : LoopConfig :=
  { state := .need (.retPush frame c.state), tape := c.tape }

def pushLoopConfig
    (frame : EvalFrame)
    (c : Configuration FramePushState (Option Bool)) : LoopConfig :=
  { state := .need (.push frame c.state), tape := c.tape }


def inputLoopConfig
    (c : Configuration InputNodeCompositeState (Option Bool)) : LoopConfig :=
  { state := inputLoopEmbed c.state, tape := c.tape }

@[simp] theorem seekLoop_not_halted
    (c : Configuration CursorSeekState (Option Bool)) :
    ¬ Halted evalRunLoopMachine (seekLoopConfig c) := by
  simp [Halted, seekLoopConfig, evalRunLoopMachine]

@[simp] theorem decodeLoop_not_halted
    (c : Configuration TagDecodeState (Option Bool)) :
    ¬ Halted evalRunLoopMachine (decodeLoopConfig c) := by
  simp [Halted, decodeLoopConfig, evalRunLoopMachine]

@[simp] theorem retValueLoop_not_halted
    (value : Bool)
    (c : Configuration CursorReturnState (Option Bool)) :
    ¬ Halted evalRunLoopMachine (retValueLoopConfig value c) := by
  simp [Halted, retValueLoopConfig, evalRunLoopMachine]


@[simp] theorem retPushLoop_not_halted
    (frame : EvalFrame)
    (c : Configuration CursorReturnState (Option Bool)) :
    ¬ Halted evalRunLoopMachine (retPushLoopConfig frame c) := by
  simp [Halted, retPushLoopConfig, evalRunLoopMachine]

@[simp] theorem pushLoop_not_halted
    (frame : EvalFrame)
    (c : Configuration FramePushState (Option Bool)) :
    ¬ Halted evalRunLoopMachine (pushLoopConfig frame c) := by
  simp [Halted, pushLoopConfig, evalRunLoopMachine]

theorem seekLoop_successors_active
    (c : Configuration CursorSeekState (Option Bool))
    (h : cursorSeekMachine.halting c.state = false) :
    evalRunLoopMachine.successors (seekLoopConfig c) =
      [seekLoopConfig (cursorSeekMachine.step c)] := by
  rcases c with ⟨q, tape⟩
  unfold NTM.successors
  simp only [seekLoopConfig]
  cases q <;>
    simp [evalRunLoopMachine, needExprCompositeMachine,
      needLoopEmbed, cursorSeekMachine, NTM.stepBranch, TM.step,
      Tape.write, Tape.move] at h ⊢

theorem decodeLoop_successors_active
    (c : Configuration TagDecodeState (Option Bool))
    (h : tagDecodeMachine.halting c.state = false) :
    evalRunLoopMachine.successors (decodeLoopConfig c) =
      [decodeLoopConfig (tagDecodeMachine.step c)] := by
  rcases c with ⟨q, tape⟩
  unfold NTM.successors
  simp only [decodeLoopConfig]
  cases q <;>
    simp [evalRunLoopMachine, needExprCompositeMachine,
      needLoopEmbed, tagDecodeMachine, NTM.stepBranch, TM.step,
      Tape.write, Tape.move] at h ⊢

theorem retValueLoop_successors_active
    (value : Bool)
    (c : Configuration CursorReturnState (Option Bool))
    (h : cursorReturnMachine.halting c.state = false) :
    evalRunLoopMachine.successors (retValueLoopConfig value c) =
      [retValueLoopConfig value (cursorReturnMachine.step c)] := by
  rcases c with ⟨q, tape⟩
  unfold NTM.successors
  simp only [retValueLoopConfig]
  cases q <;>
    simp [evalRunLoopMachine, needExprCompositeMachine,
      needLoopEmbed, cursorReturnMachine, NTM.stepBranch, TM.step,
      Tape.write, Tape.move] at h ⊢


theorem retPushLoop_successors_active
    (frame : EvalFrame)
    (c : Configuration CursorReturnState (Option Bool))
    (h : cursorReturnMachine.halting c.state = false) :
    evalRunLoopMachine.successors (retPushLoopConfig frame c) =
      [retPushLoopConfig frame (cursorReturnMachine.step c)] := by
  rcases c with ⟨q, tape⟩
  unfold NTM.successors
  simp only [retPushLoopConfig]
  cases q <;>
    simp [evalRunLoopMachine, needExprCompositeMachine,
      needLoopEmbed, cursorReturnMachine, NTM.stepBranch, TM.step,
      Tape.write, Tape.move] at h ⊢

theorem pushLoop_successors_active
    (frame : EvalFrame)
    (c : Configuration FramePushState (Option Bool))
    (h : framePushMachine.halting c.state = false) :
    evalRunLoopMachine.successors (pushLoopConfig frame c) =
      [pushLoopConfig frame (framePushMachine.step c)] := by
  rcases c with ⟨q, tape⟩
  unfold NTM.successors
  simp only [pushLoopConfig]
  cases q <;>
    simp [evalRunLoopMachine, needExprCompositeMachine,
      needLoopEmbed, framePushMachine, NTM.stepBranch, TM.step,
      Tape.write, Tape.move] at h ⊢


/-- Active input-node configurations embed exactly into the repeated evaluator
loop; terminal input states are handled by `inputLoopEmbed` itself. -/
theorem inputLoop_successors_active
    (c : Configuration InputNodeCompositeState (Option Bool))
    (h : ¬ Halted inputNodeCompositeMachine c) :
    evalRunLoopMachine.successors (inputLoopConfig c) =
      (inputNodeCompositeMachine.successors c).map inputLoopConfig := by
  rcases c with ⟨q, tape⟩
  cases q <;>
    simp [Halted, inputLoopConfig, inputLoopEmbed,
      evalRunLoopMachine, inputNodeCompositeMachine,
      NTM.successors, NTM.stepBranch, List.map_map,
      Function.comp_def, Tape.write, Tape.move] at h ⊢

theorem inputLoop_active
    (c : Configuration InputNodeCompositeState (Option Bool))
    (h : ¬ Halted inputNodeCompositeMachine c) :
    ¬ Halted evalRunLoopMachine (inputLoopConfig c) := by
  rcases c with ⟨q, tape⟩
  cases q <;>
    simp [Halted, inputLoopConfig, inputLoopEmbed,
      evalRunLoopMachine, inputNodeCompositeMachine] at h ⊢

/-- Terminal-aware reachability lift for the indexed-input primitive.

The source primitive halts at `.done selected mode`; the target loop maps that
same terminal directly to either `.final selected` or `.have (.start selected)`
according to the retained return mode. -/
theorem input_terminal_reachable_lift :
    ∀ (n : Nat)
      (a b : Configuration InputNodeCompositeState (Option Bool)),
      ¬ Halted inputNodeCompositeMachine a →
      Halted inputNodeCompositeMachine b →
      b ∈ inputNodeCompositeMachine.runBranches n [a] →
      ∃ m ≤ n,
        inputLoopConfig b ∈
          evalRunLoopMachine.runBranches m [inputLoopConfig a] := by
  intro n
  induction n with
  | zero =>
      intro a b ha hb hreach
      simp [NTM.runBranches] at hreach
      subst b
      exact False.elim (ha hb)
  | succ n ih =>
      intro a b ha hb hreach
      have hreach' :
          b ∈ inputNodeCompositeMachine.runBranches n
            (inputNodeCompositeMachine.successors a) := by
        change b ∈ inputNodeCompositeMachine.runBranches (n + 1) [a] at hreach
        rw [runBranches_singleton_active
          inputNodeCompositeMachine n a ha] at hreach
        exact hreach
      rw [mem_runBranches_iff] at hreach'
      rcases hreach' with ⟨c, hca, hcb⟩

      have hstepSucc :
          inputLoopConfig c ∈
            evalRunLoopMachine.successors (inputLoopConfig a) := by
        rw [inputLoop_successors_active a ha]
        exact List.mem_map.mpr ⟨c, hca, rfl⟩
      have hstep :
          inputLoopConfig c ∈
            evalRunLoopMachine.runBranches 1 [inputLoopConfig a] := by
        have h :=
          mem_runBranches_succ_of_successor
            evalRunLoopMachine 0 [inputLoopConfig a]
            (inputLoopConfig a) (inputLoopConfig c)
            (by simp [NTM.runBranches])
            (inputLoop_active a ha) hstepSucc
        simpa using h

      by_cases hc : Halted inputNodeCompositeMachine c
      · have hcb' : b = c := by
          rw [runBranches_singleton_halted
            inputNodeCompositeMachine n c hc] at hcb
          simpa using hcb
        subst b
        exact ⟨1, by omega, hstep⟩
      · obtain ⟨m, hm, htail⟩ := ih c b hc hb hcb
        have htrans :=
          mem_runBranches_trans evalRunLoopMachine
            1 m [inputLoopConfig a]
            (inputLoopConfig c) (inputLoopConfig b)
            hstep htail
        exact ⟨1 + m, by omega, htrans⟩

/-- The complete indexed-input primitive, starting after the 000 tag decoder,
lifts to the mode-aware repeated evaluator loop with the same majorant. -/
theorem inputNode_loop_from_read
    (witness tail frameStack : BitString)
    (consumed padding i : Nat)
    (hi : i < witness.length) :
    ∃ m ≤ inputNodeCompositeFuel consumed i tail frameStack,
      inputLoopConfig
        ({ state :=
             .done (witness.getD i false)
               (inputNodeFinalMode tail frameStack),
           tape :=
             (inputAfterReadTarget witness
               (consumedAfterInputIndex consumed i)
               tail frameStack padding).tape } :
          Configuration InputNodeCompositeState (Option Bool)) ∈
        evalRunLoopMachine.runBranches m
          [inputLoopConfig
            ({ state := inputNodeCompositeMachine.initial,
               tape :=
                 evalCursorReadTape witness consumed
                   (encodeNat i ++ tail) frameStack padding } :
              Configuration InputNodeCompositeState (Option Bool))] := by
  obtain ⟨m, hm, hsrc⟩ :=
    inputNodeComposite_reaches_done
      witness tail frameStack consumed padding i hi
  let a : Configuration InputNodeCompositeState (Option Bool) :=
    { state := inputNodeCompositeMachine.initial,
      tape :=
        evalCursorReadTape witness consumed
          (encodeNat i ++ tail) frameStack padding }
  let b : Configuration InputNodeCompositeState (Option Bool) :=
    { state :=
        .done (witness.getD i false)
          (inputNodeFinalMode tail frameStack),
      tape :=
        (inputAfterReadTarget witness
          (consumedAfterInputIndex consumed i)
          tail frameStack padding).tape }
  have ha : ¬ Halted inputNodeCompositeMachine a := by
    simp [Halted, a, inputNodeCompositeMachine]
  have hb : Halted inputNodeCompositeMachine b := by
    simp [Halted, b, inputNodeCompositeMachine]
  obtain ⟨k, hk, hlift⟩ :=
    input_terminal_reachable_lift m a b ha hb (by
      simpa [a, b] using hsrc)
  exact ⟨k, Nat.le_trans hk hm, by simpa [a, b] using hlift⟩

#print axioms MCore.Real.P01EvalRunLoopRun.inputLoop_successors_active
#print axioms MCore.Real.P01EvalRunLoopRun.input_terminal_reachable_lift
#print axioms MCore.Real.P01EvalRunLoopRun.inputNode_loop_from_read

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

theorem seekLoop_run_reachable
    (n : Nat)
    (c : Configuration CursorSeekState (Option Bool)) :
    ∃ m ≤ n,
      seekLoopConfig (cursorSeekMachine.run n c) ∈
        evalRunLoopMachine.runBranches m [seekLoopConfig c] :=
  tm_phase_run_reachable
    cursorSeekMachine seekLoopConfig
    seekLoop_not_halted seekLoop_successors_active n c

theorem decodeLoop_run_reachable
    (n : Nat)
    (c : Configuration TagDecodeState (Option Bool)) :
    ∃ m ≤ n,
      decodeLoopConfig (tagDecodeMachine.run n c) ∈
        evalRunLoopMachine.runBranches m [decodeLoopConfig c] :=
  tm_phase_run_reachable
    tagDecodeMachine decodeLoopConfig
    decodeLoop_not_halted decodeLoop_successors_active n c

theorem retValueLoop_run_reachable
    (value : Bool) (n : Nat)
    (c : Configuration CursorReturnState (Option Bool)) :
    ∃ m ≤ n,
      retValueLoopConfig value (cursorReturnMachine.run n c) ∈
        evalRunLoopMachine.runBranches m [retValueLoopConfig value c] :=
  tm_phase_run_reachable
    cursorReturnMachine (retValueLoopConfig value)
    (retValueLoop_not_halted value)
    (retValueLoop_successors_active value) n c


theorem retPushLoop_run_reachable
    (frame : EvalFrame) (n : Nat)
    (c : Configuration CursorReturnState (Option Bool)) :
    ∃ m ≤ n,
      retPushLoopConfig frame (cursorReturnMachine.run n c) ∈
        evalRunLoopMachine.runBranches m [retPushLoopConfig frame c] :=
  tm_phase_run_reachable
    cursorReturnMachine (retPushLoopConfig frame)
    (retPushLoop_not_halted frame)
    (retPushLoop_successors_active frame) n c

theorem pushLoop_run_reachable
    (frame : EvalFrame) (n : Nat)
    (c : Configuration FramePushState (Option Bool)) :
    ∃ m ≤ n,
      pushLoopConfig frame (framePushMachine.run n c) ∈
        evalRunLoopMachine.runBranches m [pushLoopConfig frame c] :=
  tm_phase_run_reachable
    framePushMachine (pushLoopConfig frame)
    (pushLoop_not_halted frame)
    (pushLoop_successors_active frame) n c

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

def constLoopFuel
    (frameStack rest : BitString) : Nat :=
  (frameStack.length + (rest.length + 3) + 3) +
    1 + 3 + 1 +
    (rest.length + frameStack.length + 2) + 1

/-- Generic physical loop route for constant tags 001/010. -/
theorem constTag_loop_reaches_have
    (witness rest frameStack : BitString)
    (consumed padding : Nat)
    (b0 b1 b2 value : Bool)
    (tag : NeedExprTag)
    (hdecode : decodeTagBits b0 b1 b2 = tag)
    (hhandoff :
      ∀ tape : Tape (Option Bool),
        needExprCompositeMachine.successors
          { state := .decode (.halt tag), tape := tape } =
          [{ state := .retValue value .scanUnread, tape := tape }]) :
    ∃ m ≤ constLoopFuel frameStack rest,
      ({ state := .have (.start value),
         tape :=
           evalCursorStackEndTape witness (consumed + 3)
             rest frameStack padding } : LoopConfig) ∈
        evalRunLoopMachine.runBranches m
          [{ state := .need needExprCompositeMachine.initial,
             tape :=
               evalCursorStackEndTape witness consumed
                 (b0 :: b1 :: b2 :: rest)
                 frameStack padding }] := by
  let nSeek := frameStack.length + (rest.length + 3) + 3
  let nRet := rest.length + frameStack.length + 2
  let t0 :=
    evalCursorStackEndTape witness consumed
      (b0 :: b1 :: b2 :: rest) frameStack padding
  let tRead :=
    evalCursorReadTape witness consumed
      (b0 :: b1 :: b2 :: rest) frameStack padding
  let tAfterTag :=
    evalCursorReadTape witness (consumed + 3)
      rest frameStack padding
  let tDone :=
    evalCursorStackEndTape witness (consumed + 3)
      rest frameStack padding

  let cSeek0 : Configuration CursorSeekState (Option Bool) :=
    { state := cursorSeekMachine.initial, tape := t0 }
  let cSeekH : Configuration CursorSeekState (Option Bool) :=
    { state := .halt, tape := tRead }
  let cDec0 : Configuration TagDecodeState (Option Bool) :=
    { state := tagDecodeMachine.initial, tape := tRead }
  let cDecH : Configuration TagDecodeState (Option Bool) :=
    { state := .halt tag, tape := tAfterTag }
  let cRet0 : Configuration CursorReturnState (Option Bool) :=
    { state := .scanUnread, tape := tAfterTag }
  let cRetH : Configuration CursorReturnState (Option Bool) :=
    { state := .halt, tape := tDone }

  have hSeekExact :
      cursorSeekMachine.run nSeek cSeek0 = cSeekH := by
    dsimp [nSeek, cSeek0, cSeekH, t0, tRead]
    simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
      cursorSeek_run witness consumed
        (b0 :: b1 :: b2 :: rest) frameStack padding
  obtain ⟨mS, hmS, hS⟩ := seekLoop_run_reachable nSeek cSeek0
  have hS' :
      seekLoopConfig cSeekH ∈
        evalRunLoopMachine.runBranches mS [seekLoopConfig cSeek0] := by
    rw [hSeekExact] at hS
    exact hS

  have hSeekHandSucc :
      decodeLoopConfig cDec0 ∈
        evalRunLoopMachine.successors (seekLoopConfig cSeekH) := by
    dsimp [seekLoopConfig, decodeLoopConfig, cSeekH, cDec0]
    simp [evalRunLoopMachine, needExprCompositeMachine, needLoopEmbed,
      NTM.successors, NTM.stepBranch, Tape.write, Tape.move]
  have hSeekHand :
      decodeLoopConfig cDec0 ∈
        evalRunLoopMachine.runBranches 1 [seekLoopConfig cSeekH] :=
    one_step_of_successor
      (seekLoopConfig cSeekH) (decodeLoopConfig cDec0)
      (seekLoop_not_halted cSeekH) hSeekHandSucc
  have hToDec :=
    mem_runBranches_trans evalRunLoopMachine
      mS 1 [seekLoopConfig cSeek0]
      (seekLoopConfig cSeekH) (decodeLoopConfig cDec0)
      hS' hSeekHand

  have hDecExact :
      tagDecodeMachine.run 3 cDec0 = cDecH := by
    dsimp [cDec0, cDecH, tRead, tAfterTag]
    simpa [hdecode] using
      tagDecode_run_three witness rest frameStack consumed padding
        b0 b1 b2
  obtain ⟨mD, hmD, hD⟩ := decodeLoop_run_reachable 3 cDec0
  have hD' :
      decodeLoopConfig cDecH ∈
        evalRunLoopMachine.runBranches mD [decodeLoopConfig cDec0] := by
    rw [hDecExact] at hD
    exact hD
  have hThroughDec :=
    mem_runBranches_trans evalRunLoopMachine
      (mS + 1) mD [seekLoopConfig cSeek0]
      (decodeLoopConfig cDec0) (decodeLoopConfig cDecH)
      hToDec hD'

  have hDecHandSucc :
      retValueLoopConfig value cRet0 ∈
        evalRunLoopMachine.successors (decodeLoopConfig cDecH) := by
    change
      ({ state := .need (.retValue value .scanUnread), tape := tAfterTag } :
        LoopConfig) ∈
      evalRunLoopMachine.successors
        ({ state := .need (.decode (.halt tag)), tape := tAfterTag } :
          LoopConfig)
    have hsrc := hhandoff tAfterTag
    rw [show evalRunLoopMachine.successors
        ({ state := .need (.decode (.halt tag)), tape := tAfterTag } :
          LoopConfig) =
      (needExprCompositeMachine.successors
        ({ state := .decode (.halt tag), tape := tAfterTag } :
          Configuration NeedExprCompositeState (Option Bool))).map
        (fun d => ({ state := needLoopEmbed d.state, tape := d.tape } :
          LoopConfig)) by
        simp [evalRunLoopMachine, needExprCompositeMachine,
          NTM.successors, NTM.stepBranch, needLoopEmbed,
          Tape.write, Tape.move]]
    rw [hsrc]
    simp [needLoopEmbed]
  have hDecHand :
      retValueLoopConfig value cRet0 ∈
        evalRunLoopMachine.runBranches 1 [decodeLoopConfig cDecH] :=
    one_step_of_successor
      (decodeLoopConfig cDecH) (retValueLoopConfig value cRet0)
      (decodeLoop_not_halted cDecH) hDecHandSucc
  have hToRet :=
    mem_runBranches_trans evalRunLoopMachine
      ((mS + 1) + mD) 1 [seekLoopConfig cSeek0]
      (decodeLoopConfig cDecH) (retValueLoopConfig value cRet0)
      hThroughDec hDecHand

  have hRetExact :
      cursorReturnMachine.run nRet cRet0 = cRetH := by
    dsimp [nRet, cRet0, cRetH, tAfterTag, tDone]
    exact cursorReturn_preserve_run
      witness (consumed + 3) rest frameStack padding
  obtain ⟨mR, hmR, hR⟩ :=
    retValueLoop_run_reachable value nRet cRet0
  have hR' :
      retValueLoopConfig value cRetH ∈
        evalRunLoopMachine.runBranches mR
          [retValueLoopConfig value cRet0] := by
    rw [hRetExact] at hR
    exact hR
  have hThroughRet :=
    mem_runBranches_trans evalRunLoopMachine
      (((mS + 1) + mD) + 1) mR [seekLoopConfig cSeek0]
      (retValueLoopConfig value cRet0)
      (retValueLoopConfig value cRetH)
      hToRet hR'

  let cHave : LoopConfig :=
    { state := .have (.start value), tape := tDone }
  have hFinalSucc :
      cHave ∈
        evalRunLoopMachine.successors
          (retValueLoopConfig value cRetH) := by
    dsimp [cHave, retValueLoopConfig, cRetH]
    simp [needLoopEmbed, evalRunLoopMachine, needExprCompositeMachine,
      NTM.successors, NTM.stepBranch, Tape.write, Tape.move]
  have hFinal :
      cHave ∈
        evalRunLoopMachine.runBranches 1
          [retValueLoopConfig value cRetH] :=
    one_step_of_successor
      (retValueLoopConfig value cRetH) cHave
      (retValueLoop_not_halted value cRetH) hFinalSucc

  have hAll :=
    mem_runBranches_trans evalRunLoopMachine
      ((((mS + 1) + mD) + 1) + mR) 1
      [seekLoopConfig cSeek0]
      (retValueLoopConfig value cRetH) cHave
      hThroughRet hFinal

  refine ⟨(((((mS + 1) + mD) + 1) + mR) + 1), ?_, ?_⟩
  · dsimp [constLoopFuel, nSeek, nRet] at *
    omega
  · dsimp [cHave, tDone, cSeek0, t0] at hAll ⊢
    simpa [seekLoopConfig, needExprCompositeMachine] using hAll

theorem constFalse_loop_reaches_have
    (witness rest frameStack : BitString)
    (consumed padding : Nat) :
    ∃ m ≤ constLoopFuel frameStack rest,
      ({ state := .have (.start false),
         tape :=
           evalCursorStackEndTape witness (consumed + 3)
             rest frameStack padding } : LoopConfig) ∈
        evalRunLoopMachine.runBranches m
          [{ state := .need needExprCompositeMachine.initial,
             tape :=
               evalCursorStackEndTape witness consumed
                 (false :: false :: true :: rest)
                 frameStack padding }] := by
  apply constTag_loop_reaches_have
    witness rest frameStack consumed padding
      false false true false .constFalse
  · rfl
  · exact constFalse_handoff_successors

theorem constTrue_loop_reaches_have
    (witness rest frameStack : BitString)
    (consumed padding : Nat) :
    ∃ m ≤ constLoopFuel frameStack rest,
      ({ state := .have (.start true),
         tape :=
           evalCursorStackEndTape witness (consumed + 3)
             rest frameStack padding } : LoopConfig) ∈
        evalRunLoopMachine.runBranches m
          [{ state := .need needExprCompositeMachine.initial,
             tape :=
               evalCursorStackEndTape witness consumed
                 (false :: true :: false :: rest)
                 frameStack padding }] := by
  apply constTag_loop_reaches_have
    witness rest frameStack consumed padding
      false true false true .constTrue
  · rfl
  · exact constTrue_handoff_successors


/-- Same polynomial majorant as the already-certified physical continuation
tag route, now with the terminal `doneNeed` immediately restarted by the
global evalRun loop. -/
def pushLoopFuel
    (frameStack rest : BitString) : Nat :=
  P01NeedExprCompositeRun.pushTagCompositeFuel frameStack rest

/-- Generic repeated-evaluator route for the continuation tags 011/100/101. -/
theorem pushTag_loop_reaches_need
    (witness rest frameStack : BitString)
    (consumed padding : Nat)
    (b0 b1 b2 : Bool)
    (tag : NeedExprTag)
    (frame : EvalFrame)
    (hTag : decodeTagBits b0 b1 b2 = tag)
    (hHandoff :
      ∀ tape : Tape (Option Bool),
        needExprCompositeMachine.successors
          { state := .decode (.halt tag), tape := tape } =
        [{ state := .retPush frame .scanUnread, tape := tape }]) :
    ∃ m ≤ pushLoopFuel frameStack rest,
      ({ state := .need needExprCompositeMachine.initial,
         tape :=
           evalCursorStackEndTape witness (consumed + 3)
             rest (encodeEvalFrame frame ++ frameStack)
             (((padding - 1) - 1) - 1) } : LoopConfig) ∈
        evalRunLoopMachine.runBranches m
          [{ state := .need needExprCompositeMachine.initial,
             tape :=
               evalCursorStackEndTape witness consumed
                 (b0 :: b1 :: b2 :: rest) frameStack padding }] := by
  let nSeek := frameStack.length + (rest.length + 3) + 3
  let nRet := rest.length + frameStack.length + 2
  let t0 :=
    evalCursorStackEndTape witness consumed
      (b0 :: b1 :: b2 :: rest) frameStack padding
  let tRead :=
    evalCursorReadTape witness consumed
      (b0 :: b1 :: b2 :: rest) frameStack padding
  let tAfterTag :=
    evalCursorReadTape witness (consumed + 3)
      rest frameStack padding
  let tStack :=
    evalCursorStackEndTape witness (consumed + 3)
      rest frameStack padding
  let tPushed :=
    evalCursorStackEndTape witness (consumed + 3)
      rest (encodeEvalFrame frame ++ frameStack)
      (((padding - 1) - 1) - 1)

  let cSeek0 : Configuration CursorSeekState (Option Bool) :=
    { state := cursorSeekMachine.initial, tape := t0 }
  let cSeekH : Configuration CursorSeekState (Option Bool) :=
    { state := .halt, tape := tRead }
  let cDec0 : Configuration TagDecodeState (Option Bool) :=
    { state := tagDecodeMachine.initial, tape := tRead }
  let cDecH : Configuration TagDecodeState (Option Bool) :=
    { state := .halt tag, tape := tAfterTag }
  let cRet0 : Configuration CursorReturnState (Option Bool) :=
    { state := .scanUnread, tape := tAfterTag }
  let cRetH : Configuration CursorReturnState (Option Bool) :=
    { state := .halt, tape := tStack }
  let cPush0 : Configuration FramePushState (Option Bool) :=
    framePushConfig frame tStack
  let cPushH : Configuration FramePushState (Option Bool) :=
    { state := .halt, tape := tPushed }

  obtain ⟨mS, hmS, hS⟩ := seekLoop_run_reachable nSeek cSeek0
  have hSeekExact :
      cursorSeekMachine.run nSeek cSeek0 = cSeekH := by
    dsimp [nSeek, cSeek0, cSeekH, t0, tRead]
    simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
      cursorSeek_run witness consumed
        (b0 :: b1 :: b2 :: rest) frameStack padding
  have hS' :
      seekLoopConfig cSeekH ∈
        evalRunLoopMachine.runBranches mS [seekLoopConfig cSeek0] := by
    rw [hSeekExact] at hS
    exact hS

  have hSeekHandSucc :
      decodeLoopConfig cDec0 ∈
        evalRunLoopMachine.successors (seekLoopConfig cSeekH) := by
    dsimp [seekLoopConfig, decodeLoopConfig, cSeekH, cDec0]
    simp [evalRunLoopMachine, needExprCompositeMachine, needLoopEmbed,
      NTM.successors, NTM.stepBranch, Tape.write, Tape.move]
  have hSeekHand :
      decodeLoopConfig cDec0 ∈
        evalRunLoopMachine.runBranches 1 [seekLoopConfig cSeekH] :=
    one_step_of_successor
      (seekLoopConfig cSeekH) (decodeLoopConfig cDec0)
      (seekLoop_not_halted cSeekH) hSeekHandSucc
  have hToDec :=
    mem_runBranches_trans evalRunLoopMachine
      mS 1 [seekLoopConfig cSeek0]
      (seekLoopConfig cSeekH) (decodeLoopConfig cDec0)
      hS' hSeekHand

  obtain ⟨mD, hmD, hD⟩ := decodeLoop_run_reachable 3 cDec0
  have hDecExact :
      tagDecodeMachine.run 3 cDec0 = cDecH := by
    dsimp [cDec0, cDecH, tRead, tAfterTag]
    simpa [hTag] using
      tagDecode_run_three witness rest frameStack consumed padding
        b0 b1 b2
  have hD' :
      decodeLoopConfig cDecH ∈
        evalRunLoopMachine.runBranches mD [decodeLoopConfig cDec0] := by
    rw [hDecExact] at hD
    exact hD
  have hThroughDec :=
    mem_runBranches_trans evalRunLoopMachine
      (mS + 1) mD [seekLoopConfig cSeek0]
      (decodeLoopConfig cDec0) (decodeLoopConfig cDecH)
      hToDec hD'

  have hDecHandSucc :
      retPushLoopConfig frame cRet0 ∈
        evalRunLoopMachine.successors (decodeLoopConfig cDecH) := by
    change
      ({ state := .need (.retPush frame .scanUnread), tape := tAfterTag } :
        LoopConfig) ∈
      evalRunLoopMachine.successors
        ({ state := .need (.decode (.halt tag)), tape := tAfterTag } :
          LoopConfig)
    have hsrc := hHandoff tAfterTag
    rw [show evalRunLoopMachine.successors
        ({ state := .need (.decode (.halt tag)), tape := tAfterTag } :
          LoopConfig) =
      (needExprCompositeMachine.successors
        ({ state := .decode (.halt tag), tape := tAfterTag } :
          Configuration NeedExprCompositeState (Option Bool))).map
        (fun d => ({ state := needLoopEmbed d.state, tape := d.tape } :
          LoopConfig)) by
        simp [evalRunLoopMachine, needExprCompositeMachine,
          NTM.successors, NTM.stepBranch, needLoopEmbed,
          Tape.write, Tape.move]]
    rw [hsrc]
    simp [needLoopEmbed]
  have hDecHand :
      retPushLoopConfig frame cRet0 ∈
        evalRunLoopMachine.runBranches 1 [decodeLoopConfig cDecH] :=
    one_step_of_successor
      (decodeLoopConfig cDecH) (retPushLoopConfig frame cRet0)
      (decodeLoop_not_halted cDecH) hDecHandSucc
  have hToRet :=
    mem_runBranches_trans evalRunLoopMachine
      ((mS + 1) + mD) 1 [seekLoopConfig cSeek0]
      (decodeLoopConfig cDecH) (retPushLoopConfig frame cRet0)
      hThroughDec hDecHand

  obtain ⟨mR, hmR, hR⟩ :=
    retPushLoop_run_reachable frame nRet cRet0
  have hRetExact :
      cursorReturnMachine.run nRet cRet0 = cRetH := by
    dsimp [nRet, cRet0, cRetH, tAfterTag, tStack]
    exact cursorReturn_preserve_run
      witness (consumed + 3) rest frameStack padding
  have hR' :
      retPushLoopConfig frame cRetH ∈
        evalRunLoopMachine.runBranches mR [retPushLoopConfig frame cRet0] := by
    rw [hRetExact] at hR
    exact hR
  have hThroughRet :=
    mem_runBranches_trans evalRunLoopMachine
      (((mS + 1) + mD) + 1) mR [seekLoopConfig cSeek0]
      (retPushLoopConfig frame cRet0)
      (retPushLoopConfig frame cRetH)
      hToRet hR'

  have hRetHandSucc :
      pushLoopConfig frame cPush0 ∈
        evalRunLoopMachine.successors (retPushLoopConfig frame cRetH) := by
    change
      ({ state := .need (.push frame (.start frame)), tape := tStack } :
        LoopConfig) ∈
      evalRunLoopMachine.successors
        ({ state := .need (.retPush frame .halt), tape := tStack } :
          LoopConfig)
    simp [evalRunLoopMachine, needExprCompositeMachine, needLoopEmbed,
      framePushConfig, NTM.successors, NTM.stepBranch,
      Tape.write, Tape.move]
  have hRetHand :
      pushLoopConfig frame cPush0 ∈
        evalRunLoopMachine.runBranches 1 [retPushLoopConfig frame cRetH] :=
    one_step_of_successor
      (retPushLoopConfig frame cRetH) (pushLoopConfig frame cPush0)
      (retPushLoop_not_halted frame cRetH) hRetHandSucc
  have hToPush :=
    mem_runBranches_trans evalRunLoopMachine
      ((((mS + 1) + mD) + 1) + mR) 1 [seekLoopConfig cSeek0]
      (retPushLoopConfig frame cRetH) (pushLoopConfig frame cPush0)
      hThroughRet hRetHand

  obtain ⟨mP, hmP, hP⟩ :=
    pushLoop_run_reachable frame 3 cPush0
  have hPushExact :
      framePushMachine.run 3 cPush0 = cPushH := by
    dsimp [cPush0, cPushH, tStack, tPushed]
    exact framePush_run_three_cursor_exact
      witness rest frameStack (consumed + 3) padding frame
  have hP' :
      pushLoopConfig frame cPushH ∈
        evalRunLoopMachine.runBranches mP [pushLoopConfig frame cPush0] := by
    rw [hPushExact] at hP
    exact hP
  have hThroughPush :=
    mem_runBranches_trans evalRunLoopMachine
      (((((mS + 1) + mD) + 1) + mR) + 1) mP
      [seekLoopConfig cSeek0]
      (pushLoopConfig frame cPush0) (pushLoopConfig frame cPushH)
      hToPush hP'

  let cNeed : LoopConfig :=
    { state := .need needExprCompositeMachine.initial, tape := tPushed }
  have hFinalSucc :
      cNeed ∈ evalRunLoopMachine.successors (pushLoopConfig frame cPushH) := by
    dsimp [cNeed, pushLoopConfig, cPushH]
    simp [evalRunLoopMachine, needExprCompositeMachine, needLoopEmbed,
      NTM.successors, NTM.stepBranch, Tape.write, Tape.move]
  have hFinal :
      cNeed ∈ evalRunLoopMachine.runBranches 1 [pushLoopConfig frame cPushH] :=
    one_step_of_successor
      (pushLoopConfig frame cPushH) cNeed
      (pushLoop_not_halted frame cPushH) hFinalSucc

  have hAll :=
    mem_runBranches_trans evalRunLoopMachine
      ((((((mS + 1) + mD) + 1) + mR) + 1) + mP) 1
      [seekLoopConfig cSeek0]
      (pushLoopConfig frame cPushH) cNeed
      hThroughPush hFinal

  refine ⟨((((((mS + 1) + mD) + 1) + mR) + 1) + mP) + 1, ?_, ?_⟩
  · dsimp [pushLoopFuel, P01NeedExprCompositeRun.pushTagCompositeFuel,
      nSeek, nRet] at *
    omega
  · dsimp [cNeed, tPushed, cSeek0, t0] at hAll ⊢
    simpa [seekLoopConfig, needExprCompositeMachine] using hAll

theorem neg_loop_reaches_need
    (witness rest frameStack : BitString)
    (consumed padding : Nat) :
    ∃ m ≤ pushLoopFuel frameStack rest,
      ({ state := .need needExprCompositeMachine.initial,
         tape := evalCursorStackEndTape witness (consumed + 3) rest
           (encodeEvalFrame .neg ++ frameStack)
           (((padding - 1) - 1) - 1) } : LoopConfig) ∈
        evalRunLoopMachine.runBranches m
          [{ state := .need needExprCompositeMachine.initial,
             tape := evalCursorStackEndTape witness consumed
               (false :: true :: true :: rest) frameStack padding }] := by
  apply pushTag_loop_reaches_need witness rest frameStack consumed padding
    false true true .neg .neg
  · rfl
  · exact P01NeedExprCompositeNTM.neg_handoff_successors

theorem and_loop_reaches_need
    (witness rest frameStack : BitString)
    (consumed padding : Nat) :
    ∃ m ≤ pushLoopFuel frameStack rest,
      ({ state := .need needExprCompositeMachine.initial,
         tape := evalCursorStackEndTape witness (consumed + 3) rest
           (encodeEvalFrame .andLeft ++ frameStack)
           (((padding - 1) - 1) - 1) } : LoopConfig) ∈
        evalRunLoopMachine.runBranches m
          [{ state := .need needExprCompositeMachine.initial,
             tape := evalCursorStackEndTape witness consumed
               (true :: false :: false :: rest) frameStack padding }] := by
  apply pushTag_loop_reaches_need witness rest frameStack consumed padding
    true false false .and .andLeft
  · rfl
  · exact P01NeedExprCompositeNTM.and_handoff_successors

theorem or_loop_reaches_need
    (witness rest frameStack : BitString)
    (consumed padding : Nat) :
    ∃ m ≤ pushLoopFuel frameStack rest,
      ({ state := .need needExprCompositeMachine.initial,
         tape := evalCursorStackEndTape witness (consumed + 3) rest
           (encodeEvalFrame .orLeft ++ frameStack)
           (((padding - 1) - 1) - 1) } : LoopConfig) ∈
        evalRunLoopMachine.runBranches m
          [{ state := .need needExprCompositeMachine.initial,
             tape := evalCursorStackEndTape witness consumed
               (true :: false :: true :: rest) frameStack padding }] := by
  apply pushTag_loop_reaches_need witness rest frameStack consumed padding
    true false true .or .orLeft
  · rfl
  · exact P01NeedExprCompositeNTM.or_handoff_successors

#print axioms MCore.Real.P01EvalRunLoopRun.pushTag_loop_reaches_need
#print axioms MCore.Real.P01EvalRunLoopRun.neg_loop_reaches_need
#print axioms MCore.Real.P01EvalRunLoopRun.and_loop_reaches_need
#print axioms MCore.Real.P01EvalRunLoopRun.or_loop_reaches_need

#print axioms MCore.Real.P01EvalRunLoopRun.retPushLoop_run_reachable
#print axioms MCore.Real.P01EvalRunLoopRun.pushLoop_run_reachable
#print axioms MCore.Real.P01EvalRunLoopRun.constTag_loop_reaches_have
#print axioms MCore.Real.P01EvalRunLoopRun.constFalse_loop_reaches_have
#print axioms MCore.Real.P01EvalRunLoopRun.constTrue_loop_reaches_have

end P01EvalRunLoopRun
end Real
end MCore
