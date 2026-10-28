import MCore.Real.P01TagDecodeCompositeNTM
import MCore.Real.P01NTMRunLaws

namespace MCore
namespace Real
namespace P01TagDecodeCompositeRun

open CanonicalFinalProof
open P01NTMRunLaws
open P01EvalCursorMachine
open P01InputTagDecodeMachine
open P01TagDecodeCompositeNTM

abbrev CompositeConfig :=
  Configuration TagDecodeCompositeState (Option Bool)

def seekConfig
    (c : Configuration CursorSeekState (Option Bool)) :
    CompositeConfig :=
  { state := .seek c.state, tape := c.tape }

def decodeConfig
    (c : Configuration TagDecodeState (Option Bool)) :
    CompositeConfig :=
  { state := .decode c.state, tape := c.tape }

@[simp] theorem seekConfig_not_halted
    (c : Configuration CursorSeekState (Option Bool)) :
    ¬ Halted tagDecodeCompositeMachine (seekConfig c) := by
  simp [Halted, seekConfig, tagDecodeCompositeMachine]

@[simp] theorem decodeConfig_not_halted
    (c : Configuration TagDecodeState (Option Bool)) :
    ¬ Halted tagDecodeCompositeMachine (decodeConfig c) := by
  simp [Halted, decodeConfig, tagDecodeCompositeMachine]

theorem seek_successors_active
    (c : Configuration CursorSeekState (Option Bool))
    (h : cursorSeekMachine.halting c.state = false) :
    tagDecodeCompositeMachine.successors (seekConfig c) =
      [seekConfig (cursorSeekMachine.step c)] := by
  unfold NTM.successors
  simp only [seekConfig]
  rw [seek_transition_active c.state c.tape.head h]
  simp [seekConfig, NTM.stepBranch, TM.step,
    tagDecodeCompositeMachine, cursorSeekMachine,
    Tape.write, Tape.move]

theorem decode_successors_active
    (c : Configuration TagDecodeState (Option Bool))
    (h : tagDecodeMachine.halting c.state = false) :
    tagDecodeCompositeMachine.successors (decodeConfig c) =
      [decodeConfig (tagDecodeMachine.step c)] := by
  unfold NTM.successors
  simp only [decodeConfig]
  rw [decode_transition_active c.state c.tape.head h]
  simp [decodeConfig, NTM.stepBranch, TM.step,
    tagDecodeCompositeMachine, tagDecodeMachine,
    Tape.write, Tape.move]

theorem seek_run_reachable :
    ∀ (n : Nat) (c : Configuration CursorSeekState (Option Bool)),
      ∃ m ≤ n,
        seekConfig (cursorSeekMachine.run n c) ∈
          tagDecodeCompositeMachine.runBranches m [seekConfig c] := by
  intro n
  induction n with
  | zero =>
      intro c
      refine ⟨0, by omega, ?_⟩
      change seekConfig c ∈ [seekConfig c]
      simp
  | succ n ih =>
      intro c
      cases hhalt : cursorSeekMachine.halting c.state with
      | true =>
          have hr :=
            MachineRunLemmas.run_halted
              cursorSeekMachine c hhalt (n + 1)
          refine ⟨0, by omega, ?_⟩
          change
            seekConfig (cursorSeekMachine.run (n + 1) c) ∈ [seekConfig c]
          rw [hr]
          simp
      | false =>
          obtain ⟨m, hm, hmem⟩ := ih (cursorSeekMachine.step c)
          have hsucc :
              seekConfig (cursorSeekMachine.step c) ∈
                tagDecodeCompositeMachine.successors (seekConfig c) := by
            rw [seek_successors_active c hhalt]
            simp
          have hone :
              seekConfig (cursorSeekMachine.step c) ∈
                tagDecodeCompositeMachine.runBranches 1 [seekConfig c] := by
            have h :=
              mem_runBranches_succ_of_successor
                tagDecodeCompositeMachine 0 [seekConfig c]
                (seekConfig c)
                (seekConfig (cursorSeekMachine.step c))
                (by simp [NTM.runBranches])
                (seekConfig_not_halted c) hsucc
            simpa using h
          have htrans :=
            mem_runBranches_trans tagDecodeCompositeMachine
              1 m [seekConfig c]
              (seekConfig (cursorSeekMachine.step c))
              (seekConfig
                (cursorSeekMachine.run n (cursorSeekMachine.step c)))
              hone hmem
          refine ⟨1 + m, by omega, ?_⟩
          simpa [TM.run, hhalt] using htrans

theorem decode_run_reachable :
    ∀ (n : Nat) (c : Configuration TagDecodeState (Option Bool)),
      ∃ m ≤ n,
        decodeConfig (tagDecodeMachine.run n c) ∈
          tagDecodeCompositeMachine.runBranches m [decodeConfig c] := by
  intro n
  induction n with
  | zero =>
      intro c
      refine ⟨0, by omega, ?_⟩
      change decodeConfig c ∈ [decodeConfig c]
      simp
  | succ n ih =>
      intro c
      cases hhalt : tagDecodeMachine.halting c.state with
      | true =>
          have hr :=
            MachineRunLemmas.run_halted
              tagDecodeMachine c hhalt (n + 1)
          refine ⟨0, by omega, ?_⟩
          change
            decodeConfig (tagDecodeMachine.run (n + 1) c) ∈ [decodeConfig c]
          rw [hr]
          simp
      | false =>
          obtain ⟨m, hm, hmem⟩ := ih (tagDecodeMachine.step c)
          have hsucc :
              decodeConfig (tagDecodeMachine.step c) ∈
                tagDecodeCompositeMachine.successors (decodeConfig c) := by
            rw [decode_successors_active c hhalt]
            simp
          have hone :
              decodeConfig (tagDecodeMachine.step c) ∈
                tagDecodeCompositeMachine.runBranches 1 [decodeConfig c] := by
            have h :=
              mem_runBranches_succ_of_successor
                tagDecodeCompositeMachine 0 [decodeConfig c]
                (decodeConfig c)
                (decodeConfig (tagDecodeMachine.step c))
                (by simp [NTM.runBranches])
                (decodeConfig_not_halted c) hsucc
            simpa using h
          have htrans :=
            mem_runBranches_trans tagDecodeCompositeMachine
              1 m [decodeConfig c]
              (decodeConfig (tagDecodeMachine.step c))
              (decodeConfig
                (tagDecodeMachine.run n (tagDecodeMachine.step c)))
              hone hmem
          refine ⟨1 + m, by omega, ?_⟩
          simpa [TM.run, hhalt] using htrans

def tagDecodeCompositeFuel
    (tail frameStack : BitString) : Nat :=
  frameStack.length + tail.length + 11

/-- Full physical tag decoding in one fixed NTM.

Starting at the canonical stack-end cursor, the machine seeks to the source,
physically consumes exactly three tag bits, stores them in finite control, and
halts in an accepting `.done` state with the remaining source untouched. -/
theorem tagDecodeComposite_reaches_done
    (witness tail frameStack : BitString)
    (consumed padding : Nat)
    (b0 b1 b2 : Bool) :
    ∃ m ≤ tagDecodeCompositeFuel tail frameStack,
      ({ state := .done b0 b1 b2,
         tape :=
           evalCursorReadTape witness (consumed + 3)
             tail frameStack padding } : CompositeConfig) ∈
        tagDecodeCompositeMachine.runBranches m
          [{ state := tagDecodeCompositeMachine.initial,
             tape :=
               evalCursorStackEndTape witness consumed
                 (b0 :: b1 :: b2 :: tail) frameStack padding }] := by
  let seekFuel :=
    frameStack.length + (b0 :: b1 :: b2 :: tail).length + 3
  let startSeek : Configuration CursorSeekState (Option Bool) :=
    { state := cursorSeekMachine.initial,
      tape :=
        evalCursorStackEndTape witness consumed
          (b0 :: b1 :: b2 :: tail) frameStack padding }
  let haltSeek : Configuration CursorSeekState (Option Bool) :=
    { state := .halt,
      tape :=
        evalCursorReadTape witness consumed
          (b0 :: b1 :: b2 :: tail) frameStack padding }

  have hSeekExact :
      cursorSeekMachine.run seekFuel startSeek = haltSeek := by
    dsimp [seekFuel, startSeek, haltSeek]
    exact cursorSeek_run witness consumed
      (b0 :: b1 :: b2 :: tail) frameStack padding

  obtain ⟨mS, hmS, hS⟩ :=
    seek_run_reachable seekFuel startSeek
  have hSeekReached :
      seekConfig haltSeek ∈
        tagDecodeCompositeMachine.runBranches mS [seekConfig startSeek] := by
    rw [hSeekExact] at hS
    exact hS

  let startDecode : Configuration TagDecodeState (Option Bool) :=
    { state := tagDecodeMachine.initial,
      tape :=
        evalCursorReadTape witness consumed
          (b0 :: b1 :: b2 :: tail) frameStack padding }

  have hHandoff :
      decodeConfig startDecode ∈
        tagDecodeCompositeMachine.runBranches (mS + 1) [seekConfig startSeek] := by
    have hsucc :
        decodeConfig startDecode ∈
          tagDecodeCompositeMachine.successors (seekConfig haltSeek) := by
      rw [show seekConfig haltSeek =
          ({ state := .seek .halt, tape := haltSeek.tape } : CompositeConfig) by
            rfl]
      rw [seek_handoff_successors haltSeek.tape]
      simp [startDecode, haltSeek, decodeConfig]
    exact mem_runBranches_succ_of_successor
      tagDecodeCompositeMachine mS [seekConfig startSeek]
      (seekConfig haltSeek) (decodeConfig startDecode)
      hSeekReached (seekConfig_not_halted haltSeek) hsucc

  let haltDecode : Configuration TagDecodeState (Option Bool) :=
    { state := .halt b0 b1 b2,
      tape :=
        evalCursorReadTape witness (consumed + 3)
          tail frameStack padding }

  have hDecodeExact :
      tagDecodeMachine.run 3 startDecode = haltDecode := by
    dsimp [startDecode, haltDecode]
    exact tagDecode_run_three witness tail frameStack consumed padding b0 b1 b2

  obtain ⟨mD, hmD, hD⟩ := decode_run_reachable 3 startDecode
  have hDecodeReached :
      decodeConfig haltDecode ∈
        tagDecodeCompositeMachine.runBranches mD [decodeConfig startDecode] := by
    rw [hDecodeExact] at hD
    exact hD

  have hBoth :
      decodeConfig haltDecode ∈
        tagDecodeCompositeMachine.runBranches ((mS + 1) + mD)
          [seekConfig startSeek] :=
    mem_runBranches_trans tagDecodeCompositeMachine
      (mS + 1) mD [seekConfig startSeek]
      (decodeConfig startDecode) (decodeConfig haltDecode)
      hHandoff hDecodeReached

  let done : CompositeConfig :=
    { state := .done b0 b1 b2,
      tape :=
        evalCursorReadTape witness (consumed + 3)
          tail frameStack padding }

  have hDone :
      done ∈
        tagDecodeCompositeMachine.runBranches (((mS + 1) + mD) + 1)
          [seekConfig startSeek] := by
    have hsucc :
        done ∈
          tagDecodeCompositeMachine.successors (decodeConfig haltDecode) := by
      rw [show decodeConfig haltDecode =
          ({ state := .decode (.halt b0 b1 b2), tape := haltDecode.tape } :
            CompositeConfig) by
            rfl]
      rw [decode_handoff_successors b0 b1 b2 haltDecode.tape]
      simp [done, haltDecode]
    exact mem_runBranches_succ_of_successor
      tagDecodeCompositeMachine ((mS + 1) + mD) [seekConfig startSeek]
      (decodeConfig haltDecode) done hBoth
      (decodeConfig_not_halted haltDecode) hsucc

  refine ⟨((mS + 1) + mD) + 1, ?_, ?_⟩
  · dsimp [tagDecodeCompositeFuel, seekFuel] at hmS ⊢
    omega
  · dsimp [done, startSeek, seekConfig] at hDone ⊢
    simpa [tagDecodeCompositeMachine] using hDone

#print axioms MCore.Real.P01TagDecodeCompositeRun.seek_run_reachable
#print axioms MCore.Real.P01TagDecodeCompositeRun.decode_run_reachable
#print axioms MCore.Real.P01TagDecodeCompositeRun.tagDecodeComposite_reaches_done

end P01TagDecodeCompositeRun
end Real
end MCore
