import MCore.Real.P01CheckedEvalRunTagPrefix
import MCore.Real.P01CheckedEvalRunPhaseLift
import MCore.Real.CanonicalSATWitness

namespace MCore
namespace Real
namespace P01CheckedEvalRunBaseCases

open CanonicalFinalProof
open CircuitK1
open CanonicalCircuitBits
open CanonicalSATWitness
open P01NTMRunLaws
open P01EncodedStackEvaluator
open P01EncodedFrameTape
open P01EvalCursorMachine
open P01EvalCursorRoundTrip
open P01HaveValueCompositeNTM
open P01NeedExprCompositeNTM
open P01NeedExprTagDecode
open P01CheckedEvalRunLoopNTM
open P01CheckedEvalRunPhaseLift
open P01CheckedEvalRunTagPrefix
open P01CNFMode

abbrev CheckedConfig :=
  Configuration CheckedEvalRunState (Option Bool)

/-- Finite syntax mode carried after the current circuit has been evaluated. -/
def exitMode (mode : SyntaxMode) (c : Circuit) : SyntaxMode :=
  childMode mode (circuitTag c)

/-- Physical checked-loop outcome after one whole encoded circuit has been
evaluated, while preserving any external source tail and continuation stack. -/
def CheckedLoopOutcome
    (witness : BitString)
    (mode : SyntaxMode)
    (value : Bool)
    (tail : BitString)
    (frames : List EvalFrame)
    (cfg : CheckedConfig) : Prop :=
  match tail, frames with
  | [], [] =>
      ∃ tape : Tape (Option Bool),
        cfg = { state := .final value, tape := tape }
  | _, _ =>
      ∃ consumed padding : Nat,
        cfg =
          { state := .have mode (.start value),
            tape :=
              evalCursorStackEndTape witness consumed tail
                (encodeEvalFrames frames) padding }

/-- Producer-first checked circuit certificate.

The circuit must satisfy the finite syntax mode.  The physical checked loop
then evaluates its canonical prefix encoding to the semantic value while
preserving arbitrary external tail/frames. -/
def CheckedCircuitRunCertificate
    (sigma : Assignment)
    (witness : BitString)
    (mode : SyntaxMode)
    (phi : Circuit) : Prop :=
  modeCheck mode phi = true →
  ∀ (tail : BitString) (frames : List EvalFrame)
      (consumed padding : Nat),
    varBound phi ≤ witness.length →
    (∀ i, i < varBound phi →
      witness.getD i false = sigma i) →
    ∃ m cfg,
      cfg ∈
        checkedEvalRunLoopMachine.runBranches m
          [{ state := .need mode needExprCompositeMachine.initial,
             tape :=
               evalCursorStackEndTape witness consumed
                 (encodeCircuit phi ++ tail)
                 (encodeEvalFrames frames) padding }] ∧
      CheckedLoopOutcome witness (exitMode mode phi)
        (evalCircuit sigma phi) tail frames cfg

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

/-- A computed value with no unread source and no continuation frame reaches
the checked loop's global final state after the mandatory source-empty guard. -/
theorem checked_empty_frames_reaches_final
    (mode : SyntaxMode)
    (witness : BitString)
    (consumed padding : Nat)
    (v : Bool) :
    ∃ m ≤ 3,
      ({ state := .final v,
         tape :=
           Tape.move none .left
             (Tape.move none .left
               (evalCursorStackEndTape witness consumed [] [] padding)) } :
        CheckedConfig) ∈
      checkedEvalRunLoopMachine.runBranches m
        [{ state := .have mode (.start v),
           tape :=
             evalCursorStackEndTape witness consumed [] [] padding }] := by
  let t0 :=
    evalCursorStackEndTape witness consumed [] [] padding
  let tPeek := Tape.move none .left t0
  let tCheck := Tape.move none .left tPeek
  let c0 : CheckedConfig := { state := .have mode (.start v), tape := t0 }
  let cPeek : CheckedConfig := { state := .have mode (.peek v), tape := tPeek }
  let cCheck : CheckedConfig := { state := .checkSource v, tape := tCheck }
  let cFinal : CheckedConfig := { state := .final v, tape := tCheck }

  have hStartSucc :
      cPeek ∈ checkedEvalRunLoopMachine.successors c0 := by
    dsimp [c0, cPeek, tPeek, t0]
    simp [checkedEvalRunLoopMachine, haveValueCompositeMachine,
      haveCheckedEmbed, NTM.successors, NTM.stepBranch,
      evalCursorStackEndTape, Tape.write, Tape.move,
      List.append_assoc]

  have hStart :
      cPeek ∈ checkedEvalRunLoopMachine.runBranches 1 [c0] :=
    one_step_of_successor c0 cPeek
      (by
        dsimp [c0]
        simp [Halted, checkedEvalRunLoopMachine])
      hStartSucc

  have hPeekSucc :
      cCheck ∈ checkedEvalRunLoopMachine.successors cPeek := by
    dsimp [cPeek, cCheck, tPeek, tCheck, t0]
    simp [checkedEvalRunLoopMachine, evalCursorStackEndTape,
      NTM.successors, NTM.stepBranch, Tape.write, Tape.move,
      List.append_assoc]

  have hPeek :
      cCheck ∈ checkedEvalRunLoopMachine.runBranches 1 [cPeek] :=
    one_step_of_successor cPeek cCheck
      (by
        dsimp [cPeek]
        simp [Halted, checkedEvalRunLoopMachine])
      hPeekSucc

  have hCheckSucc :
      cFinal ∈ checkedEvalRunLoopMachine.successors cCheck := by
    dsimp [cCheck, cFinal, tCheck, tPeek, t0]
    cases consumed <;>
      simp [checkedEvalRunLoopMachine, evalCursorStackEndTape,
        NTM.successors, NTM.stepBranch, Tape.write, Tape.move,
        List.replicate_succ, List.append_assoc]

  have hCheck :
      cFinal ∈ checkedEvalRunLoopMachine.runBranches 1 [cCheck] :=
    one_step_of_successor cCheck cFinal
      (by
        dsimp [cCheck]
        simp [Halted, checkedEvalRunLoopMachine])
      hCheckSucc

  have h01 :=
    mem_runBranches_trans checkedEvalRunLoopMachine
      1 1 [c0] cPeek cCheck hStart hPeek
  have hAll :=
    mem_runBranches_trans checkedEvalRunLoopMachine
      2 1 [c0] cCheck cFinal h01 hCheck
  refine ⟨3, by omega, ?_⟩
  dsimp [c0, cFinal, t0, tPeek, tCheck] at hAll ⊢
  simpa using hAll

/-- Shared checked physical execution for a constant tag. -/
theorem const_checked_run
    (sigma : Assignment)
    (witness tail : BitString)
    (frames : List EvalFrame)
    (mode : SyntaxMode)
    (consumed padding : Nat)
    (v : Bool)
    (hmode : modeCheck mode (.const v) = true) :
    ∃ m cfg,
      cfg ∈
        checkedEvalRunLoopMachine.runBranches m
          [{ state := .need mode needExprCompositeMachine.initial,
             tape :=
               evalCursorStackEndTape witness consumed
                 (encodeCircuit (.const v) ++ tail)
                 (encodeEvalFrames frames) padding }] ∧
      CheckedLoopOutcome witness (exitMode mode (.const v))
        v tail frames cfg := by
  let b0 := false
  let b1 := v
  let b2 := !v
  have htag :
      decodeTagBits b0 b1 b2 =
        (if v then NeedExprTag.constTrue else NeedExprTag.constFalse) := by
    cases v <;> rfl
  have hallowed :
      tagAllowed mode
        (if v then NeedExprTag.constTrue else NeedExprTag.constFalse) = true := by
    cases v <;> simpa using hmode

  obtain ⟨m0, hm0, h0⟩ :=
    checked_tag_prefix_reaches
      mode witness tail (encodeEvalFrames frames)
      consumed padding b0 b1 b2
      (by simpa [htag] using hallowed)

  let tAfter :=
    evalCursorReadTape witness (consumed + 3)
      tail (encodeEvalFrames frames) padding
  let tDone :=
    evalCursorStackEndTape witness (consumed + 3)
      tail (encodeEvalFrames frames) padding
  let nRet := tail.length + (encodeEvalFrames frames).length + 2
  let cRet0 : Configuration CursorReturnState (Option Bool) :=
    { state := .scanUnread, tape := tAfter }
  let cRetH : Configuration CursorReturnState (Option Bool) :=
    { state := .halt, tape := tDone }
  let cCheckedRet0 : CheckedConfig :=
    { state := .need mode (.retValue v .scanUnread), tape := tAfter }
  let cCheckedRetH : CheckedConfig :=
    { state := .need mode (.retValue v .halt), tape := tDone }
  let cHave : CheckedConfig :=
    { state := .have mode (.start v), tape := tDone }

  have hPrefix :
      cCheckedRet0 ∈
        checkedEvalRunLoopMachine.runBranches m0
          [{ state := .need mode needExprCompositeMachine.initial,
             tape :=
               evalCursorStackEndTape witness consumed
                 (encodeCircuit (.const v) ++ tail)
                 (encodeEvalFrames frames) padding }] := by
    cases v <;>
      simpa [cCheckedRet0, tAfter, postTagState,
        childMode, circuitTag, encodeCircuit, b0, b1, b2,
        decodeTagBits] using h0

  have hRetExact :
      cursorReturnMachine.run nRet cRet0 = cRetH := by
    dsimp [nRet, cRet0, cRetH, tAfter, tDone]
    exact cursorReturn_preserve_run
      witness (consumed + 3) tail
        (encodeEvalFrames frames) padding

  obtain ⟨mR, hmR, hR⟩ :=
    retValue_run_reachable mode v nRet cRet0
  have hR' :
      cCheckedRetH ∈
        checkedEvalRunLoopMachine.runBranches mR [cCheckedRet0] := by
    rw [hRetExact] at hR
    simpa [cCheckedRet0, cCheckedRetH,
      retValueConfig, cRet0, cRetH] using hR

  have hThroughRet :=
    mem_runBranches_trans checkedEvalRunLoopMachine
      m0 mR
      [{ state := .need mode needExprCompositeMachine.initial,
         tape :=
           evalCursorStackEndTape witness consumed
             (encodeCircuit (.const v) ++ tail)
             (encodeEvalFrames frames) padding }]
      cCheckedRet0 cCheckedRetH hPrefix hR'

  have hHandSucc :
      cHave ∈ checkedEvalRunLoopMachine.successors cCheckedRetH := by
    dsimp [cHave, cCheckedRetH, tDone]
    simp [checkedEvalRunLoopMachine, needExprCompositeMachine,
      needCheckedEmbed, NTM.successors, NTM.stepBranch,
      Tape.write, Tape.move]

  have hHand :
      cHave ∈
        checkedEvalRunLoopMachine.runBranches 1 [cCheckedRetH] :=
    one_step_of_successor cCheckedRetH cHave
      (by
        dsimp [cCheckedRetH]
        simp [Halted, checkedEvalRunLoopMachine])
      hHandSucc

  have hToHave :=
    mem_runBranches_trans checkedEvalRunLoopMachine
      (m0 + mR) 1
      [{ state := .need mode needExprCompositeMachine.initial,
         tape :=
           evalCursorStackEndTape witness consumed
             (encodeCircuit (.const v) ++ tail)
             (encodeEvalFrames frames) padding }]
      cCheckedRetH cHave hThroughRet hHand

  cases tail with
  | cons x xs =>
      refine ⟨m0 + mR + 1, cHave, hToHave, ?_⟩
      change CheckedLoopOutcome witness (exitMode mode (.const v))
        v (x :: xs) frames cHave
      refine ⟨consumed + 3, padding, ?_⟩
      cases v <;> cases mode <;>
        simp [CheckedLoopOutcome, exitMode, circuitTag, childMode,
          cHave, tDone, modeCheck] at hmode ⊢
  | nil =>
      cases frames with
      | cons f fs =>
          refine ⟨m0 + mR + 1, cHave, hToHave, ?_⟩
          change CheckedLoopOutcome witness (exitMode mode (.const v))
            v [] (f :: fs) cHave
          refine ⟨consumed + 3, padding, ?_⟩
          cases v <;> cases mode <;>
            simp [CheckedLoopOutcome, exitMode, circuitTag, childMode,
              cHave, tDone, modeCheck] at hmode ⊢
      | nil =>
          obtain ⟨mF, hmF, hF⟩ :=
            checked_empty_frames_reaches_final
              mode witness (consumed + 3) padding v
          let cFinal : CheckedConfig :=
            { state := .final v,
              tape :=
                Tape.move none .left
                  (Tape.move none .left
                    (evalCursorStackEndTape witness (consumed + 3)
                      [] [] padding)) }
          have hToHaveNil :
              cHave ∈
                checkedEvalRunLoopMachine.runBranches (m0 + mR + 1)
                  [{ state := .need mode needExprCompositeMachine.initial,
                     tape :=
                       evalCursorStackEndTape witness consumed
                         (encodeCircuit (.const v))
                         (encodeEvalFrames []) padding }] := by
            simpa using hToHave
          have hAll :=
            mem_runBranches_trans checkedEvalRunLoopMachine
              (m0 + mR + 1) mF
              [{ state := .need mode needExprCompositeMachine.initial,
                 tape :=
                   evalCursorStackEndTape witness consumed
                     (encodeCircuit (.const v))
                     (encodeEvalFrames []) padding }]
              cHave cFinal hToHaveNil
              (by simpa [cFinal] using hF)
          refine ⟨m0 + mR + 1 + mF, cFinal, ?_, ?_⟩
          · simpa using hAll
          · exact ⟨cFinal.tape, rfl⟩

theorem constFalse_certificate
    (sigma : Assignment)
    (witness : BitString)
    (mode : SyntaxMode) :
    CheckedCircuitRunCertificate sigma witness mode (.const false) := by
  intro hmode tail frames consumed padding hlen hread
  exact const_checked_run sigma witness tail frames mode
    consumed padding false hmode

theorem constTrue_certificate
    (sigma : Assignment)
    (witness : BitString)
    (mode : SyntaxMode) :
    CheckedCircuitRunCertificate sigma witness mode (.const true) := by
  intro hmode tail frames consumed padding hlen hread
  exact const_checked_run sigma witness tail frames mode
    consumed padding true hmode

theorem const_certificate
    (sigma : Assignment)
    (witness : BitString)
    (mode : SyntaxMode)
    (v : Bool) :
    CheckedCircuitRunCertificate sigma witness mode (.const v) := by
  cases v
  · exact constFalse_certificate sigma witness mode
  · exact constTrue_certificate sigma witness mode

#print axioms MCore.Real.P01CheckedEvalRunBaseCases.checked_empty_frames_reaches_final
#print axioms MCore.Real.P01CheckedEvalRunBaseCases.const_checked_run
#print axioms MCore.Real.P01CheckedEvalRunBaseCases.constFalse_certificate
#print axioms MCore.Real.P01CheckedEvalRunBaseCases.constTrue_certificate
#print axioms MCore.Real.P01CheckedEvalRunBaseCases.const_certificate

end P01CheckedEvalRunBaseCases
end Real
end MCore
