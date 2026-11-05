import MCore.Real.P01NeedExprCompositeNTM
import MCore.Real.P01NTMRunLaws
import MCore.Real.P01EvalCursorFramePush
import MCore.Real.P01InputNodeCompositeRun

namespace MCore
namespace Real
namespace P01NeedExprCompositeRun

open CanonicalFinalProof
open CanonicalCircuitBits
open P01NTMRunLaws
open P01EvalCursorMachine
open P01EvalCursorRoundTrip
open P01EvalFramePushMachine
open P01EvalCursorFramePush
open P01EncodedStackEvaluator
open P01EncodedFrameTape
open P01NeedExprTagDecode
open P01InputNodeCompositeNTM
open P01InputNodeCompositeRun
open P01InputNodeRoundTrip
open P01NeedExprCompositeNTM

abbrev NeedExprConfig :=
  Configuration NeedExprCompositeState (Option Bool)

/-- Exact simulation of the already-certified indexed-input NTM inside the
global needExpr NTM.  Accepting/rejecting terminals are mapped directly to the
global terminals, so runBranches can be transported without an extra fake
terminal phase. -/
def inputSimulation :
    P01NTMRunLaws.Simulation
      inputNodeCompositeMachine needExprCompositeMachine inputStateEmbed where
  accepting := by
    intro s
    cases s <;> rfl
  rejecting := by
    intro s
    cases s <;> rfl
  successors := by
    intro c hactive
    rcases c with ⟨q, tape⟩
    cases q with
    | done selected mode =>
        simp [Halted, inputNodeCompositeMachine] at hactive
    | reject =>
        simp [Halted, inputNodeCompositeMachine] at hactive
    | look ql =>
        unfold NTM.successors
        simp [P01NTMRunLaws.liftConfig, inputStateEmbed,
          needExprCompositeMachine, inputNodeCompositeMachine,
          NTM.stepBranch, Tape.write, Tape.move]
    | read mode qr =>
        unfold NTM.successors
        simp [P01NTMRunLaws.liftConfig, inputStateEmbed,
          needExprCompositeMachine, inputNodeCompositeMachine,
          NTM.stepBranch, Tape.write, Tape.move]
    | ret mode selected qt =>
        unfold NTM.successors
        cases qt <;>
          simp [P01NTMRunLaws.liftConfig, inputStateEmbed,
            needExprCompositeMachine, inputNodeCompositeMachine,
            NTM.stepBranch, Tape.write, Tape.move]

#print axioms MCore.Real.P01NeedExprCompositeRun.inputSimulation

def seekConfig
    (c : Configuration CursorSeekState (Option Bool)) :
    NeedExprConfig :=
  { state := .seek c.state, tape := c.tape }

def decodeConfig
    (c : Configuration TagDecodeState (Option Bool)) :
    NeedExprConfig :=
  { state := .decode c.state, tape := c.tape }

def retValueConfig
    (value : Bool)
    (c : Configuration CursorReturnState (Option Bool)) :
    NeedExprConfig :=
  { state := .retValue value c.state, tape := c.tape }

def retPushConfig
    (frame : P01EncodedStackEvaluator.EvalFrame)
    (c : Configuration CursorReturnState (Option Bool)) :
    NeedExprConfig :=
  { state := .retPush frame c.state, tape := c.tape }

def pushConfig
    (frame : P01EncodedStackEvaluator.EvalFrame)
    (c : Configuration FramePushState (Option Bool)) :
    NeedExprConfig :=
  { state := .push frame c.state, tape := c.tape }

@[simp] theorem seekConfig_not_halted
    (c : Configuration CursorSeekState (Option Bool)) :
    ¬ Halted needExprCompositeMachine (seekConfig c) := by
  simp [Halted, seekConfig, needExprCompositeMachine]

@[simp] theorem decodeConfig_not_halted
    (c : Configuration TagDecodeState (Option Bool)) :
    ¬ Halted needExprCompositeMachine (decodeConfig c) := by
  simp [Halted, decodeConfig, needExprCompositeMachine]

@[simp] theorem retValueConfig_not_halted
    (value : Bool)
    (c : Configuration CursorReturnState (Option Bool)) :
    ¬ Halted needExprCompositeMachine (retValueConfig value c) := by
  simp [Halted, retValueConfig, needExprCompositeMachine]

@[simp] theorem retPushConfig_not_halted
    (frame : P01EncodedStackEvaluator.EvalFrame)
    (c : Configuration CursorReturnState (Option Bool)) :
    ¬ Halted needExprCompositeMachine (retPushConfig frame c) := by
  simp [Halted, retPushConfig, needExprCompositeMachine]

@[simp] theorem pushConfig_not_halted
    (frame : P01EncodedStackEvaluator.EvalFrame)
    (c : Configuration FramePushState (Option Bool)) :
    ¬ Halted needExprCompositeMachine (pushConfig frame c) := by
  simp [Halted, pushConfig, needExprCompositeMachine]

theorem seek_successors_active
    (c : Configuration CursorSeekState (Option Bool))
    (h : cursorSeekMachine.halting c.state = false) :
    needExprCompositeMachine.successors (seekConfig c) =
      [seekConfig (cursorSeekMachine.step c)] := by
  unfold NTM.successors
  simp only [seekConfig]
  rw [seek_transition_active c.state c.tape.head h]
  simp [seekConfig, NTM.stepBranch, TM.step,
    cursorSeekMachine, needExprCompositeMachine,
    Tape.write, Tape.move]

theorem decode_successors_active
    (c : Configuration TagDecodeState (Option Bool))
    (h : tagDecodeMachine.halting c.state = false) :
    needExprCompositeMachine.successors (decodeConfig c) =
      [decodeConfig (tagDecodeMachine.step c)] := by
  unfold NTM.successors
  simp only [decodeConfig]
  rw [decode_transition_active c.state c.tape.head h]
  simp [decodeConfig, NTM.stepBranch, TM.step,
    tagDecodeMachine, needExprCompositeMachine,
    Tape.write, Tape.move]

theorem retValue_successors_active
    (value : Bool)
    (c : Configuration CursorReturnState (Option Bool))
    (h : cursorReturnMachine.halting c.state = false) :
    needExprCompositeMachine.successors (retValueConfig value c) =
      [retValueConfig value (cursorReturnMachine.step c)] := by
  unfold NTM.successors
  simp only [retValueConfig]
  rw [retValue_transition_active value c.state c.tape.head h]
  simp [retValueConfig, NTM.stepBranch, TM.step,
    cursorReturnMachine, needExprCompositeMachine,
    Tape.write, Tape.move]

theorem retPush_successors_active
    (frame : P01EncodedStackEvaluator.EvalFrame)
    (c : Configuration CursorReturnState (Option Bool))
    (h : cursorReturnMachine.halting c.state = false) :
    needExprCompositeMachine.successors (retPushConfig frame c) =
      [retPushConfig frame (cursorReturnMachine.step c)] := by
  unfold NTM.successors
  simp only [retPushConfig]
  rw [retPush_transition_active frame c.state c.tape.head h]
  simp only [List.map_singleton]
  simp [retPushConfig, NTM.stepBranch, TM.step,
    needExprCompositeMachine, cursorReturnMachine]

theorem push_successors_active
    (frame : P01EncodedStackEvaluator.EvalFrame)
    (c : Configuration FramePushState (Option Bool))
    (h : framePushMachine.halting c.state = false) :
    needExprCompositeMachine.successors (pushConfig frame c) =
      [pushConfig frame (framePushMachine.step c)] := by
  unfold NTM.successors
  simp only [pushConfig]
  rw [push_transition_active frame c.state c.tape.head h]
  simp [pushConfig, NTM.stepBranch, TM.step,
    framePushMachine, needExprCompositeMachine,
    Tape.write, Tape.move]

/-- Generic deterministic phase reachability, specialized by an injection and
a one-step successor theorem. -/
private theorem tm_phase_run_reachable
    {S : Type}
    (M : TM S (Option Bool))
    (embed : Configuration S (Option Bool) → NeedExprConfig)
    (embed_not_halted :
      ∀ c, ¬ Halted needExprCompositeMachine (embed c))
    (step_successors :
      ∀ c, M.halting c.state = false →
        needExprCompositeMachine.successors (embed c) =
          [embed (M.step c)]) :
    ∀ (n : Nat) (c : Configuration S (Option Bool)),
      ∃ m ≤ n,
        embed (M.run n c) ∈
          needExprCompositeMachine.runBranches m [embed c] := by
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
                needExprCompositeMachine.successors (embed c) := by
            rw [step_successors c hhalt]
            simp
          have hone :
              embed (M.step c) ∈
                needExprCompositeMachine.runBranches 1 [embed c] := by
            have h :=
              mem_runBranches_succ_of_successor
                needExprCompositeMachine 0 [embed c]
                (embed c) (embed (M.step c))
                (by simp [NTM.runBranches])
                (embed_not_halted c) hsucc
            simpa using h
          have htrans :=
            mem_runBranches_trans needExprCompositeMachine
              1 m [embed c]
              (embed (M.step c))
              (embed (M.run n (M.step c)))
              hone hmem
          refine ⟨1 + m, by omega, ?_⟩
          simpa [TM.run, hhalt] using htrans

theorem seek_run_reachable
    (n : Nat)
    (c : Configuration CursorSeekState (Option Bool)) :
    ∃ m ≤ n,
      seekConfig (cursorSeekMachine.run n c) ∈
        needExprCompositeMachine.runBranches m [seekConfig c] :=
  tm_phase_run_reachable
    cursorSeekMachine seekConfig
    seekConfig_not_halted seek_successors_active n c

theorem decode_run_reachable
    (n : Nat)
    (c : Configuration TagDecodeState (Option Bool)) :
    ∃ m ≤ n,
      decodeConfig (tagDecodeMachine.run n c) ∈
        needExprCompositeMachine.runBranches m [decodeConfig c] :=
  tm_phase_run_reachable
    tagDecodeMachine decodeConfig
    decodeConfig_not_halted decode_successors_active n c

theorem retValue_run_reachable
    (value : Bool) (n : Nat)
    (c : Configuration CursorReturnState (Option Bool)) :
    ∃ m ≤ n,
      retValueConfig value (cursorReturnMachine.run n c) ∈
        needExprCompositeMachine.runBranches m [retValueConfig value c] :=
  tm_phase_run_reachable
    cursorReturnMachine (retValueConfig value)
    (retValueConfig_not_halted value)
    (retValue_successors_active value) n c

theorem retPush_run_reachable
    (frame : P01EncodedStackEvaluator.EvalFrame) (n : Nat)
    (c : Configuration CursorReturnState (Option Bool)) :
    ∃ m ≤ n,
      retPushConfig frame (cursorReturnMachine.run n c) ∈
        needExprCompositeMachine.runBranches m [retPushConfig frame c] :=
  tm_phase_run_reachable
    cursorReturnMachine (retPushConfig frame)
    (retPushConfig_not_halted frame)
    (retPush_successors_active frame) n c

theorem push_run_reachable
    (frame : P01EncodedStackEvaluator.EvalFrame) (n : Nat)
    (c : Configuration FramePushState (Option Bool)) :
    ∃ m ≤ n,
      pushConfig frame (framePushMachine.run n c) ∈
        needExprCompositeMachine.runBranches m [pushConfig frame c] :=
  tm_phase_run_reachable
    framePushMachine (pushConfig frame)
    (pushConfig_not_halted frame)
    (push_successors_active frame) n c

/-- One active successor is reachable in one composite step. -/
private theorem one_step_of_successor
    (a b : NeedExprConfig)
    (ha : ¬ Halted needExprCompositeMachine a)
    (hs : b ∈ needExprCompositeMachine.successors a) :
    b ∈ needExprCompositeMachine.runBranches 1 [a] := by
  have h :=
    mem_runBranches_succ_of_successor
      needExprCompositeMachine 0 [a] a b
      (by simp [NTM.runBranches]) ha hs
  simpa using h

/-- The certified input-node NTM transports exactly into the global needExpr
machine through `inputStateEmbed`.  Its accepting terminal becomes
`.doneValue selected` with the same physical tape and without an extra phase. -/
theorem inputNode_reaches_doneValue_from_read
    (witness tail frameStack : BitString)
    (consumed padding i : Nat)
    (hi : i < witness.length) :
    ∃ m ≤ inputNodeCompositeFuel consumed i tail frameStack,
      ({ state := .doneValue (witness.getD i false),
         tape :=
           (inputAfterReadTarget witness
             (consumedAfterInputIndex consumed i)
             tail frameStack padding).tape } : NeedExprConfig) ∈
        needExprCompositeMachine.runBranches m
          [{ state := .input inputNodeCompositeMachine.initial,
             tape :=
               evalCursorReadTape witness consumed
                 (encodeNat i ++ tail) frameStack padding }] := by
  obtain ⟨m, hm, hmem⟩ :=
    inputNodeComposite_reaches_done
      witness tail frameStack consumed padding i hi
  let c0 : Configuration InputNodeCompositeState (Option Bool) :=
    { state := inputNodeCompositeMachine.initial,
      tape :=
        evalCursorReadTape witness consumed
          (encodeNat i ++ tail) frameStack padding }
  let done : Configuration InputNodeCompositeState (Option Bool) :=
    { state :=
        .done (witness.getD i false)
          (inputNodeFinalMode tail frameStack),
      tape :=
        (inputAfterReadTarget witness
          (consumedAfterInputIndex consumed i)
          tail frameStack padding).tape }
  have hmem' :
      done ∈ inputNodeCompositeMachine.runBranches m [c0] := by
    simpa [c0, done] using hmem
  have hmap :=
    P01NTMRunLaws.runBranches_map
      inputNodeCompositeMachine needExprCompositeMachine inputStateEmbed
      inputSimulation m [c0]
  have hlift :
      P01NTMRunLaws.liftConfig inputStateEmbed done ∈
        needExprCompositeMachine.runBranches m
          ([c0].map (P01NTMRunLaws.liftConfig inputStateEmbed)) := by
    rw [hmap]
    exact List.mem_map.mpr ⟨done, hmem', rfl⟩
  refine ⟨m, hm, ?_⟩
  simpa [c0, done, P01NTMRunLaws.liftConfig, inputStateEmbed,
    inputNodeCompositeMachine] using hlift

#print axioms MCore.Real.P01NeedExprCompositeRun.inputNode_reaches_doneValue_from_read

/-- Uniform majorant for the fused constant-tag route. -/
def constTagCompositeFuel
    (frameStack rest : BitString) : Nat :=
  (frameStack.length + (rest.length + 3) + 3) +
    1 + 3 + 1 +
    (rest.length + frameStack.length + 2) + 1

/-- Complete physical `001` route in the single fused `needExpr` NTM. -/
theorem constFalse_reaches_done
    (witness rest frameStack : BitString)
    (consumed padding : Nat) :
    ∃ m ≤ constTagCompositeFuel frameStack rest,
      ({ state := .doneValue false,
         tape :=
           evalCursorStackEndTape witness (consumed + 3)
             rest frameStack padding } : NeedExprConfig) ∈
        needExprCompositeMachine.runBranches m
          [{ state := needExprCompositeMachine.initial,
             tape :=
               evalCursorStackEndTape witness consumed
                 (false :: false :: true :: rest)
                 frameStack padding }] := by
  let nSeek := frameStack.length + (rest.length + 3) + 3
  let nRet := rest.length + frameStack.length + 2
  let t0 :=
    evalCursorStackEndTape witness consumed
      (false :: false :: true :: rest) frameStack padding
  let tRead :=
    evalCursorReadTape witness consumed
      (false :: false :: true :: rest) frameStack padding
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
    { state := .halt .constFalse, tape := tAfterTag }
  let cRet0 : Configuration CursorReturnState (Option Bool) :=
    { state := .scanUnread, tape := tAfterTag }
  let cRetH : Configuration CursorReturnState (Option Bool) :=
    { state := .halt, tape := tDone }
  let cDone : NeedExprConfig :=
    { state := .doneValue false, tape := tDone }

  have hSeekExact :
      cursorSeekMachine.run nSeek cSeek0 = cSeekH := by
    dsimp [nSeek, cSeek0, cSeekH, t0, tRead]
    simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
      cursorSeek_run witness consumed
        (false :: false :: true :: rest) frameStack padding

  obtain ⟨mS, hmS, hS⟩ := seek_run_reachable nSeek cSeek0
  have hS' :
      seekConfig cSeekH ∈
        needExprCompositeMachine.runBranches mS [seekConfig cSeek0] := by
    rw [hSeekExact] at hS
    exact hS

  have hSeekHandSucc :
      decodeConfig cDec0 ∈
        needExprCompositeMachine.successors (seekConfig cSeekH) := by
    dsimp [seekConfig, decodeConfig, cSeekH, cDec0]
    rw [seek_handoff_successors tRead]
    simp
  have hSeekHand :
      decodeConfig cDec0 ∈
        needExprCompositeMachine.runBranches 1 [seekConfig cSeekH] :=
    one_step_of_successor
      (seekConfig cSeekH) (decodeConfig cDec0)
      (seekConfig_not_halted cSeekH) hSeekHandSucc

  have hToDec :=
    mem_runBranches_trans needExprCompositeMachine
      mS 1 [seekConfig cSeek0]
      (seekConfig cSeekH) (decodeConfig cDec0)
      hS' hSeekHand

  have hDecExact :
      tagDecodeMachine.run 3 cDec0 = cDecH := by
    dsimp [cDec0, cDecH, tRead, tAfterTag]
    simpa [decodeTagBits] using
      tagDecode_run_three witness rest frameStack consumed padding
        false false true

  obtain ⟨mD, hmD, hD⟩ := decode_run_reachable 3 cDec0
  have hD' :
      decodeConfig cDecH ∈
        needExprCompositeMachine.runBranches mD [decodeConfig cDec0] := by
    rw [hDecExact] at hD
    exact hD
  have hThroughDec :=
    mem_runBranches_trans needExprCompositeMachine
      (mS + 1) mD [seekConfig cSeek0]
      (decodeConfig cDec0) (decodeConfig cDecH)
      hToDec hD'

  have hDecHandSucc :
      retValueConfig false cRet0 ∈
        needExprCompositeMachine.successors (decodeConfig cDecH) := by
    dsimp [decodeConfig, retValueConfig, cDecH, cRet0]
    rw [constFalse_handoff_successors tAfterTag]
    simp
  have hDecHand :
      retValueConfig false cRet0 ∈
        needExprCompositeMachine.runBranches 1 [decodeConfig cDecH] :=
    one_step_of_successor
      (decodeConfig cDecH) (retValueConfig false cRet0)
      (decodeConfig_not_halted cDecH) hDecHandSucc
  have hToRet :=
    mem_runBranches_trans needExprCompositeMachine
      ((mS + 1) + mD) 1 [seekConfig cSeek0]
      (decodeConfig cDecH) (retValueConfig false cRet0)
      hThroughDec hDecHand

  have hRetExact :
      cursorReturnMachine.run nRet cRet0 = cRetH := by
    dsimp [nRet, cRet0, cRetH, tAfterTag, tDone]
    exact cursorReturn_preserve_run
      witness (consumed + 3) rest frameStack padding

  obtain ⟨mR, hmR, hR⟩ :=
    retValue_run_reachable false nRet cRet0
  have hR' :
      retValueConfig false cRetH ∈
        needExprCompositeMachine.runBranches mR
          [retValueConfig false cRet0] := by
    rw [hRetExact] at hR
    exact hR
  have hThroughRet :=
    mem_runBranches_trans needExprCompositeMachine
      (((mS + 1) + mD) + 1) mR [seekConfig cSeek0]
      (retValueConfig false cRet0)
      (retValueConfig false cRetH)
      hToRet hR'

  have hFinalSucc :
      cDone ∈
        needExprCompositeMachine.successors
          (retValueConfig false cRetH) := by
    dsimp [cDone, retValueConfig, cRetH]
    rw [retValue_handoff_successors false tDone]
    simp
  have hFinal :
      cDone ∈
        needExprCompositeMachine.runBranches 1
          [retValueConfig false cRetH] :=
    one_step_of_successor
      (retValueConfig false cRetH) cDone
      (retValueConfig_not_halted false cRetH) hFinalSucc

  have hAll :=
    mem_runBranches_trans needExprCompositeMachine
      ((((mS + 1) + mD) + 1) + mR) 1 [seekConfig cSeek0]
      (retValueConfig false cRetH) cDone
      hThroughRet hFinal

  refine ⟨((((mS + 1) + mD) + 1) + mR) + 1, ?_, ?_⟩
  · dsimp [constTagCompositeFuel, nSeek, nRet] at *
    omega
  · dsimp [cDone, tDone, cSeek0, t0] at hAll ⊢
    simpa [seekConfig, needExprCompositeMachine] using hAll

/-- Complete physical `010` route in the single fused `needExpr` NTM. -/
theorem constTrue_reaches_done
    (witness rest frameStack : BitString)
    (consumed padding : Nat) :
    ∃ m ≤ constTagCompositeFuel frameStack rest,
      ({ state := .doneValue true,
         tape :=
           evalCursorStackEndTape witness (consumed + 3)
             rest frameStack padding } : NeedExprConfig) ∈
        needExprCompositeMachine.runBranches m
          [{ state := needExprCompositeMachine.initial,
             tape :=
               evalCursorStackEndTape witness consumed
                 (false :: true :: false :: rest)
                 frameStack padding }] := by
  let nSeek := frameStack.length + (rest.length + 3) + 3
  let nRet := rest.length + frameStack.length + 2
  let t0 :=
    evalCursorStackEndTape witness consumed
      (false :: true :: false :: rest) frameStack padding
  let tRead :=
    evalCursorReadTape witness consumed
      (false :: true :: false :: rest) frameStack padding
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
    { state := .halt .constTrue, tape := tAfterTag }
  let cRet0 : Configuration CursorReturnState (Option Bool) :=
    { state := .scanUnread, tape := tAfterTag }
  let cRetH : Configuration CursorReturnState (Option Bool) :=
    { state := .halt, tape := tDone }
  let cDone : NeedExprConfig :=
    { state := .doneValue true, tape := tDone }

  have hSeekExact :
      cursorSeekMachine.run nSeek cSeek0 = cSeekH := by
    dsimp [nSeek, cSeek0, cSeekH, t0, tRead]
    simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
      cursorSeek_run witness consumed
        (false :: true :: false :: rest) frameStack padding

  obtain ⟨mS, hmS, hS⟩ := seek_run_reachable nSeek cSeek0
  have hS' :
      seekConfig cSeekH ∈
        needExprCompositeMachine.runBranches mS [seekConfig cSeek0] := by
    rw [hSeekExact] at hS
    exact hS

  have hSeekHandSucc :
      decodeConfig cDec0 ∈
        needExprCompositeMachine.successors (seekConfig cSeekH) := by
    dsimp [seekConfig, decodeConfig, cSeekH, cDec0]
    rw [seek_handoff_successors tRead]
    simp
  have hSeekHand :
      decodeConfig cDec0 ∈
        needExprCompositeMachine.runBranches 1 [seekConfig cSeekH] :=
    one_step_of_successor
      (seekConfig cSeekH) (decodeConfig cDec0)
      (seekConfig_not_halted cSeekH) hSeekHandSucc

  have hToDec :=
    mem_runBranches_trans needExprCompositeMachine
      mS 1 [seekConfig cSeek0]
      (seekConfig cSeekH) (decodeConfig cDec0)
      hS' hSeekHand

  have hDecExact :
      tagDecodeMachine.run 3 cDec0 = cDecH := by
    dsimp [cDec0, cDecH, tRead, tAfterTag]
    simpa [decodeTagBits] using
      tagDecode_run_three witness rest frameStack consumed padding
        false true false

  obtain ⟨mD, hmD, hD⟩ := decode_run_reachable 3 cDec0
  have hD' :
      decodeConfig cDecH ∈
        needExprCompositeMachine.runBranches mD [decodeConfig cDec0] := by
    rw [hDecExact] at hD
    exact hD
  have hThroughDec :=
    mem_runBranches_trans needExprCompositeMachine
      (mS + 1) mD [seekConfig cSeek0]
      (decodeConfig cDec0) (decodeConfig cDecH)
      hToDec hD'

  have hDecHandSucc :
      retValueConfig true cRet0 ∈
        needExprCompositeMachine.successors (decodeConfig cDecH) := by
    dsimp [decodeConfig, retValueConfig, cDecH, cRet0]
    rw [constTrue_handoff_successors tAfterTag]
    simp
  have hDecHand :
      retValueConfig true cRet0 ∈
        needExprCompositeMachine.runBranches 1 [decodeConfig cDecH] :=
    one_step_of_successor
      (decodeConfig cDecH) (retValueConfig true cRet0)
      (decodeConfig_not_halted cDecH) hDecHandSucc
  have hToRet :=
    mem_runBranches_trans needExprCompositeMachine
      ((mS + 1) + mD) 1 [seekConfig cSeek0]
      (decodeConfig cDecH) (retValueConfig true cRet0)
      hThroughDec hDecHand

  have hRetExact :
      cursorReturnMachine.run nRet cRet0 = cRetH := by
    dsimp [nRet, cRet0, cRetH, tAfterTag, tDone]
    exact cursorReturn_preserve_run
      witness (consumed + 3) rest frameStack padding

  obtain ⟨mR, hmR, hR⟩ :=
    retValue_run_reachable true nRet cRet0
  have hR' :
      retValueConfig true cRetH ∈
        needExprCompositeMachine.runBranches mR
          [retValueConfig true cRet0] := by
    rw [hRetExact] at hR
    exact hR
  have hThroughRet :=
    mem_runBranches_trans needExprCompositeMachine
      (((mS + 1) + mD) + 1) mR [seekConfig cSeek0]
      (retValueConfig true cRet0)
      (retValueConfig true cRetH)
      hToRet hR'

  have hFinalSucc :
      cDone ∈
        needExprCompositeMachine.successors
          (retValueConfig true cRetH) := by
    dsimp [cDone, retValueConfig, cRetH]
    rw [retValue_handoff_successors true tDone]
    simp
  have hFinal :
      cDone ∈
        needExprCompositeMachine.runBranches 1
          [retValueConfig true cRetH] :=
    one_step_of_successor
      (retValueConfig true cRetH) cDone
      (retValueConfig_not_halted true cRetH) hFinalSucc

  have hAll :=
    mem_runBranches_trans needExprCompositeMachine
      ((((mS + 1) + mD) + 1) + mR) 1 [seekConfig cSeek0]
      (retValueConfig true cRetH) cDone
      hThroughRet hFinal

  refine ⟨((((mS + 1) + mD) + 1) + mR) + 1, ?_, ?_⟩
  · dsimp [constTagCompositeFuel, nSeek, nRet] at *
    omega
  · dsimp [cDone, tDone, cSeek0, t0] at hAll ⊢
    simpa [seekConfig, needExprCompositeMachine] using hAll



/-- Uniform majorant for the three continuation-tag routes 011/100/101. -/
def pushTagCompositeFuel
    (frameStack rest : BitString) : Nat :=
  (frameStack.length + (rest.length + 3) + 3) +
    1 + 3 + 1 +
    (rest.length + frameStack.length + 2) +
    1 + 3 + 1

/-- Generic physical route for a decoded continuation tag.

The hypotheses mention only the finite tag decoder result and the corresponding
finite-control handoff.  The source/witness/frame data remain entirely on tape.
-/
theorem pushTag_reaches_done
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
    ∃ m ≤ pushTagCompositeFuel frameStack rest,
      ({ state := .doneNeed,
         tape :=
           evalCursorStackEndTape witness (consumed + 3)
             rest (encodeEvalFrame frame ++ frameStack)
             (((padding - 1) - 1) - 1) } : NeedExprConfig) ∈
        needExprCompositeMachine.runBranches m
          [{ state := needExprCompositeMachine.initial,
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
  let cDone : NeedExprConfig :=
    { state := .doneNeed, tape := tPushed }

  have hSeekExact :
      cursorSeekMachine.run nSeek cSeek0 = cSeekH := by
    dsimp [nSeek, cSeek0, cSeekH, t0, tRead]
    simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
      cursorSeek_run witness consumed
        (b0 :: b1 :: b2 :: rest) frameStack padding

  obtain ⟨mS, hmS, hS⟩ := seek_run_reachable nSeek cSeek0
  have hS' :
      seekConfig cSeekH ∈
        needExprCompositeMachine.runBranches mS [seekConfig cSeek0] := by
    rw [hSeekExact] at hS
    exact hS

  have hSeekHandSucc :
      decodeConfig cDec0 ∈
        needExprCompositeMachine.successors (seekConfig cSeekH) := by
    dsimp [seekConfig, decodeConfig, cSeekH, cDec0]
    rw [seek_handoff_successors tRead]
    simp
  have hSeekHand :
      decodeConfig cDec0 ∈
        needExprCompositeMachine.runBranches 1 [seekConfig cSeekH] :=
    one_step_of_successor
      (seekConfig cSeekH) (decodeConfig cDec0)
      (seekConfig_not_halted cSeekH) hSeekHandSucc
  have hToDec :=
    mem_runBranches_trans needExprCompositeMachine
      mS 1 [seekConfig cSeek0]
      (seekConfig cSeekH) (decodeConfig cDec0)
      hS' hSeekHand

  have hDecExact :
      tagDecodeMachine.run 3 cDec0 = cDecH := by
    dsimp [cDec0, cDecH, tRead, tAfterTag]
    simpa [hTag] using
      tagDecode_run_three witness rest frameStack consumed padding
        b0 b1 b2
  obtain ⟨mD, hmD, hD⟩ := decode_run_reachable 3 cDec0
  have hD' :
      decodeConfig cDecH ∈
        needExprCompositeMachine.runBranches mD [decodeConfig cDec0] := by
    rw [hDecExact] at hD
    exact hD
  have hThroughDec :=
    mem_runBranches_trans needExprCompositeMachine
      (mS + 1) mD [seekConfig cSeek0]
      (decodeConfig cDec0) (decodeConfig cDecH)
      hToDec hD'

  have hDecHandSucc :
      retPushConfig frame cRet0 ∈
        needExprCompositeMachine.successors (decodeConfig cDecH) := by
    dsimp [decodeConfig, retPushConfig, cDecH, cRet0]
    rw [hHandoff tAfterTag]
    simp
  have hDecHand :
      retPushConfig frame cRet0 ∈
        needExprCompositeMachine.runBranches 1 [decodeConfig cDecH] :=
    one_step_of_successor
      (decodeConfig cDecH) (retPushConfig frame cRet0)
      (decodeConfig_not_halted cDecH) hDecHandSucc
  have hToRet :=
    mem_runBranches_trans needExprCompositeMachine
      ((mS + 1) + mD) 1 [seekConfig cSeek0]
      (decodeConfig cDecH) (retPushConfig frame cRet0)
      hThroughDec hDecHand

  have hRetExact :
      cursorReturnMachine.run nRet cRet0 = cRetH := by
    dsimp [nRet, cRet0, cRetH, tAfterTag, tStack]
    exact cursorReturn_preserve_run
      witness (consumed + 3) rest frameStack padding
  obtain ⟨mR, hmR, hR⟩ :=
    retPush_run_reachable frame nRet cRet0
  have hR' :
      retPushConfig frame cRetH ∈
        needExprCompositeMachine.runBranches mR
          [retPushConfig frame cRet0] := by
    rw [hRetExact] at hR
    exact hR
  have hThroughRet :=
    mem_runBranches_trans needExprCompositeMachine
      (((mS + 1) + mD) + 1) mR [seekConfig cSeek0]
      (retPushConfig frame cRet0)
      (retPushConfig frame cRetH)
      hToRet hR'

  have hRetHandSucc :
      pushConfig frame cPush0 ∈
        needExprCompositeMachine.successors
          (retPushConfig frame cRetH) := by
    dsimp [retPushConfig, pushConfig, cRetH, cPush0]
    rw [retPush_handoff_successors frame tStack]
    simp [framePushConfig]
  have hRetHand :
      pushConfig frame cPush0 ∈
        needExprCompositeMachine.runBranches 1
          [retPushConfig frame cRetH] :=
    one_step_of_successor
      (retPushConfig frame cRetH) (pushConfig frame cPush0)
      (retPushConfig_not_halted frame cRetH) hRetHandSucc
  have hToPush :=
    mem_runBranches_trans needExprCompositeMachine
      ((((mS + 1) + mD) + 1) + mR) 1 [seekConfig cSeek0]
      (retPushConfig frame cRetH) (pushConfig frame cPush0)
      hThroughRet hRetHand

  have hPushExact :
      framePushMachine.run 3 cPush0 = cPushH := by
    dsimp [cPush0, cPushH, tStack, tPushed]
    exact framePush_run_three_cursor_exact
      witness rest frameStack (consumed + 3) padding frame
  obtain ⟨mP, hmP, hP⟩ :=
    push_run_reachable frame 3 cPush0
  have hP' :
      pushConfig frame cPushH ∈
        needExprCompositeMachine.runBranches mP
          [pushConfig frame cPush0] := by
    rw [hPushExact] at hP
    exact hP
  have hThroughPush :=
    mem_runBranches_trans needExprCompositeMachine
      (((((mS + 1) + mD) + 1) + mR) + 1) mP
      [seekConfig cSeek0]
      (pushConfig frame cPush0) (pushConfig frame cPushH)
      hToPush hP'

  have hFinalSucc :
      cDone ∈
        needExprCompositeMachine.successors
          (pushConfig frame cPushH) := by
    dsimp [cDone, pushConfig, cPushH]
    rw [push_handoff_successors frame tPushed]
    simp
  have hFinal :
      cDone ∈
        needExprCompositeMachine.runBranches 1
          [pushConfig frame cPushH] :=
    one_step_of_successor
      (pushConfig frame cPushH) cDone
      (pushConfig_not_halted frame cPushH) hFinalSucc

  have hAll :=
    mem_runBranches_trans needExprCompositeMachine
      ((((((mS + 1) + mD) + 1) + mR) + 1) + mP) 1
      [seekConfig cSeek0]
      (pushConfig frame cPushH) cDone
      hThroughPush hFinal

  refine ⟨((((((mS + 1) + mD) + 1) + mR) + 1) + mP) + 1, ?_, ?_⟩
  · dsimp [pushTagCompositeFuel, nSeek, nRet] at *
    omega
  · dsimp [cDone, tPushed, cSeek0, t0] at hAll ⊢
    simpa [seekConfig, needExprCompositeMachine] using hAll

theorem neg_reaches_done
    (witness rest frameStack : BitString)
    (consumed padding : Nat) :
    ∃ m ≤ pushTagCompositeFuel frameStack rest,
      ({ state := .doneNeed,
         tape :=
           evalCursorStackEndTape witness (consumed + 3) rest
             (encodeEvalFrame .neg ++ frameStack)
             (((padding - 1) - 1) - 1) } : NeedExprConfig) ∈
        needExprCompositeMachine.runBranches m
          [{ state := needExprCompositeMachine.initial,
             tape := evalCursorStackEndTape witness consumed
               (false :: true :: true :: rest) frameStack padding }] := by
  apply pushTag_reaches_done witness rest frameStack consumed padding
    false true true .neg .neg
  · rfl
  · exact neg_handoff_successors

theorem and_reaches_done
    (witness rest frameStack : BitString)
    (consumed padding : Nat) :
    ∃ m ≤ pushTagCompositeFuel frameStack rest,
      ({ state := .doneNeed,
         tape :=
           evalCursorStackEndTape witness (consumed + 3) rest
             (encodeEvalFrame .andLeft ++ frameStack)
             (((padding - 1) - 1) - 1) } : NeedExprConfig) ∈
        needExprCompositeMachine.runBranches m
          [{ state := needExprCompositeMachine.initial,
             tape := evalCursorStackEndTape witness consumed
               (true :: false :: false :: rest) frameStack padding }] := by
  apply pushTag_reaches_done witness rest frameStack consumed padding
    true false false .and .andLeft
  · rfl
  · exact and_handoff_successors

theorem or_reaches_done
    (witness rest frameStack : BitString)
    (consumed padding : Nat) :
    ∃ m ≤ pushTagCompositeFuel frameStack rest,
      ({ state := .doneNeed,
         tape :=
           evalCursorStackEndTape witness (consumed + 3) rest
             (encodeEvalFrame .orLeft ++ frameStack)
             (((padding - 1) - 1) - 1) } : NeedExprConfig) ∈
        needExprCompositeMachine.runBranches m
          [{ state := needExprCompositeMachine.initial,
             tape := evalCursorStackEndTape witness consumed
               (true :: false :: true :: rest) frameStack padding }] := by
  apply pushTag_reaches_done witness rest frameStack consumed padding
    true false true .or .orLeft
  · rfl
  · exact or_handoff_successors



/-- Uniform majorant for the full physical 000 input route. -/
def inputTagCompositeFuel
    (consumed i : Nat) (tail frameStack : BitString) : Nat :=
  (frameStack.length +
      (false :: false :: false :: (encodeNat i ++ tail)).length + 3) +
    1 + 3 + 1 +
    inputNodeCompositeFuel (consumed + 3) i tail frameStack

/-- Complete physical `000` route in the same fused `needExpr` NTM.

Only the common seek/decode prefix is proved here.  Once the 000 tag has been
erased, the already-certified input primitive is invoked through
`inputNode_reaches_doneValue_from_read`. -/
theorem input_reaches_done
    (witness tail frameStack : BitString)
    (consumed padding i : Nat)
    (hi : i < witness.length) :
    ∃ m ≤ inputTagCompositeFuel consumed i tail frameStack,
      ({ state := .doneValue (witness.getD i false),
         tape :=
           (inputAfterReadTarget witness
             (consumedAfterInputIndex (consumed + 3) i)
             tail frameStack padding).tape } : NeedExprConfig) ∈
        needExprCompositeMachine.runBranches m
          [{ state := needExprCompositeMachine.initial,
             tape :=
               evalCursorStackEndTape witness consumed
                 (false :: false :: false :: (encodeNat i ++ tail))
                 frameStack padding }] := by
  let source := false :: false :: false :: (encodeNat i ++ tail)
  let nSeek := frameStack.length + source.length + 3
  let t0 :=
    evalCursorStackEndTape witness consumed source frameStack padding
  let tRead :=
    evalCursorReadTape witness consumed source frameStack padding
  let tAfterTag :=
    evalCursorReadTape witness (consumed + 3)
      (encodeNat i ++ tail) frameStack padding

  let cSeek0 : Configuration CursorSeekState (Option Bool) :=
    { state := cursorSeekMachine.initial, tape := t0 }
  let cSeekH : Configuration CursorSeekState (Option Bool) :=
    { state := .halt, tape := tRead }
  let cDec0 : Configuration TagDecodeState (Option Bool) :=
    { state := tagDecodeMachine.initial, tape := tRead }
  let cDecH : Configuration TagDecodeState (Option Bool) :=
    { state := .halt .input, tape := tAfterTag }
  let cInput0 : NeedExprConfig :=
    { state := .input inputNodeCompositeMachine.initial, tape := tAfterTag }

  have hSeekExact :
      cursorSeekMachine.run nSeek cSeek0 = cSeekH := by
    dsimp [nSeek, cSeek0, cSeekH, t0, tRead, source]
    exact cursorSeek_run witness consumed
      (false :: false :: false :: (encodeNat i ++ tail))
      frameStack padding

  obtain ⟨mS, hmS, hS⟩ := seek_run_reachable nSeek cSeek0
  have hS' :
      seekConfig cSeekH ∈
        needExprCompositeMachine.runBranches mS [seekConfig cSeek0] := by
    rw [hSeekExact] at hS
    exact hS

  have hSeekHandSucc :
      decodeConfig cDec0 ∈
        needExprCompositeMachine.successors (seekConfig cSeekH) := by
    dsimp [seekConfig, decodeConfig, cSeekH, cDec0]
    rw [seek_handoff_successors tRead]
    simp
  have hSeekHand :
      decodeConfig cDec0 ∈
        needExprCompositeMachine.runBranches 1 [seekConfig cSeekH] :=
    one_step_of_successor
      (seekConfig cSeekH) (decodeConfig cDec0)
      (seekConfig_not_halted cSeekH) hSeekHandSucc
  have hToDec :=
    mem_runBranches_trans needExprCompositeMachine
      mS 1 [seekConfig cSeek0]
      (seekConfig cSeekH) (decodeConfig cDec0)
      hS' hSeekHand

  have hDecExact :
      tagDecodeMachine.run 3 cDec0 = cDecH := by
    dsimp [cDec0, cDecH, tRead, tAfterTag, source]
    simpa [decodeTagBits] using
      tagDecode_run_three witness (encodeNat i ++ tail)
        frameStack consumed padding false false false

  obtain ⟨mD, hmD, hD⟩ := decode_run_reachable 3 cDec0
  have hD' :
      decodeConfig cDecH ∈
        needExprCompositeMachine.runBranches mD [decodeConfig cDec0] := by
    rw [hDecExact] at hD
    exact hD
  have hThroughDec :=
    mem_runBranches_trans needExprCompositeMachine
      (mS + 1) mD [seekConfig cSeek0]
      (decodeConfig cDec0) (decodeConfig cDecH)
      hToDec hD'

  have hInputHandSucc :
      cInput0 ∈
        needExprCompositeMachine.successors (decodeConfig cDecH) := by
    dsimp [cInput0, decodeConfig, cDecH]
    rw [input_tag_handoff_successors tAfterTag]
    simp
  have hInputHand :
      cInput0 ∈
        needExprCompositeMachine.runBranches 1 [decodeConfig cDecH] :=
    one_step_of_successor
      (decodeConfig cDecH) cInput0
      (decodeConfig_not_halted cDecH) hInputHandSucc
  have hToInput :=
    mem_runBranches_trans needExprCompositeMachine
      ((mS + 1) + mD) 1 [seekConfig cSeek0]
      (decodeConfig cDecH) cInput0
      hThroughDec hInputHand

  obtain ⟨mI, hmI, hI⟩ :=
    inputNode_reaches_doneValue_from_read
      witness tail frameStack (consumed + 3) padding i hi

  have hI' :
      ({ state := .doneValue (witness.getD i false),
         tape :=
           (inputAfterReadTarget witness
             (consumedAfterInputIndex (consumed + 3) i)
             tail frameStack padding).tape } : NeedExprConfig) ∈
        needExprCompositeMachine.runBranches mI [cInput0] := by
    simpa [cInput0, tAfterTag] using hI

  have hAll :=
    mem_runBranches_trans needExprCompositeMachine
      (((mS + 1) + mD) + 1) mI [seekConfig cSeek0]
      cInput0
      ({ state := .doneValue (witness.getD i false),
         tape :=
           (inputAfterReadTarget witness
             (consumedAfterInputIndex (consumed + 3) i)
             tail frameStack padding).tape } : NeedExprConfig)
      hToInput hI'

  refine ⟨(((mS + 1) + mD) + 1) + mI, ?_, ?_⟩
  · dsimp [inputTagCompositeFuel, nSeek, source] at *
    omega
  · dsimp [cSeek0, t0, source] at hAll ⊢
    simpa [seekConfig, needExprCompositeMachine] using hAll

#print axioms MCore.Real.P01NeedExprCompositeRun.input_reaches_done

#print axioms MCore.Real.P01NeedExprCompositeRun.pushTag_reaches_done
#print axioms MCore.Real.P01NeedExprCompositeRun.neg_reaches_done
#print axioms MCore.Real.P01NeedExprCompositeRun.and_reaches_done
#print axioms MCore.Real.P01NeedExprCompositeRun.or_reaches_done

#print axioms MCore.Real.P01NeedExprCompositeRun.constTrue_reaches_done

#print axioms MCore.Real.P01NeedExprCompositeRun.constFalse_reaches_done


#print axioms MCore.Real.P01NeedExprCompositeRun.constTrue_reaches_done

#print axioms MCore.Real.P01NeedExprCompositeRun.seek_run_reachable
#print axioms MCore.Real.P01NeedExprCompositeRun.decode_run_reachable
#print axioms MCore.Real.P01NeedExprCompositeRun.retValue_run_reachable
#print axioms MCore.Real.P01NeedExprCompositeRun.retPush_run_reachable
#print axioms MCore.Real.P01NeedExprCompositeRun.push_run_reachable

end P01NeedExprCompositeRun
end Real
end MCore
