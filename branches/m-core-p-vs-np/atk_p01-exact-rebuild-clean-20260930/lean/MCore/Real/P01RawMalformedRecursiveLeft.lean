import MCore.Real.P01RawTotalContract
import MCore.Real.P01RawMalformedBaseProducer
import MCore.Real.P01ExactBoundedReject
import MCore.Real.P01CheckedEvalRunBoundedHelpers

namespace MCore
namespace Real
namespace P01RawMalformedRecursiveLeft

open CanonicalFinalProof
open CanonicalCircuitBits
open P01CNFMode
open P01NeedExprTagDecode
open P01NeedExprCompositeNTM
open P01EncodedStackEvaluator
open P01EvalCursorMachine
open P01CheckedEvalRunLoopNTM
open P01CheckedEvalRunTagPrefix
open P01CheckedEvalRunBoundedHelpers
open P01CheckedVerifierInvariant
open P01CheckedVerifierGlobalBudget
open P01ExactBoundedReject
open P01RawTotalContract
open P01RawMalformedBaseProducer
open P01NTMRunLaws

abbrev EvalConfig :=
  Configuration CheckedEvalRunState (Option Bool)

theorem slice_add_child_budget
    (fuel n : Nat) :
    rawMalformedSlice n + rawMalformedBudget fuel n =
      rawMalformedBudget (fuel + 1) n := by
  unfold rawMalformedBudget
  ring

/-- A syntactically forbidden root tag is already an explicit physical reject,
and costs at most one raw budget slice. -/
theorem disallowed_root_fail_closed
    (witness rest : BitString)
    (frames : List EvalFrame)
    (mode : SyntaxMode)
    (consumed padding n fuel : Nat)
    (b0 b1 b2 : Bool)
    (hdis :
      tagAllowed mode (decodeTagBits b0 b1 b2) = false)
    (hLayout :
      CheckedLayoutBound n consumed
        (b0 :: b1 :: b2 :: rest) (encodeEvalFrames frames)) :
    ∃ m ≤ rawMalformedBudget (fuel + 1) n, ∃ cfg : EvalConfig,
      cfg ∈ checkedEvalRunLoopMachine.runBranches m
        [{ state := .need mode needExprCompositeMachine.initial,
           tape :=
             evalCursorStackEndTape witness consumed
               (b0 :: b1 :: b2 :: rest) (encodeEvalFrames frames) padding }] ∧
      EvalFailClosed cfg := by
  obtain ⟨m, hm, tape, hmem⟩ :=
    root_tag_reject_within_envelope
      n mode witness rest (encodeEvalFrames frames) consumed padding
      b0 b1 b2 hdis hLayout.source_le hLayout.frames_le
  have hmSlice :
      m ≤ rawMalformedSlice n :=
    Nat.le_trans hm (loopEnvelope_le_rawMalformedSlice n)
  have hmBudget :
      m ≤ rawMalformedBudget (fuel + 1) n :=
    Nat.le_trans hmSlice (slice_le_rawMalformedBudget (fuel + 1) n)
  let cfg : EvalConfig := { state := .reject, tape := tape }
  exact ⟨m, hmBudget, cfg, by simpa [cfg] using hmem, Or.inl rfl⟩

/-- Generic recursive malformed handoff.

A legal three-bit operator tag pushes one certified continuation frame and
enters its child.  If the child decoder fails with one less fuel, the child's
physical fail-closed state is also a fail-closed state of the whole operator.
-/
theorem push_tag_then_recursive_fail_closed
    (fuel n consumed padding : Nat)
    (witness rest : BitString)
    (frames : List EvalFrame)
    (mode : SyntaxMode)
    (b0 b1 b2 : Bool)
    (tag : NeedExprTag)
    (frame : EvalFrame)
    (hRec : RawMalformedAtFuel fuel)
    (hFuel :
      (b0 :: b1 :: b2 :: rest).length < fuel + 1)
    (hChildNone : decodeCircuitCore fuel rest = none)
    (hLayout :
      CheckedLayoutBound n consumed
        (b0 :: b1 :: b2 :: rest) (encodeEvalFrames frames)
    (hWitness :
      (b0 :: b1 :: b2 :: rest).length ≤ witness.length)
    (hTag : decodeTagBits b0 b1 b2 = tag)
    (hAllowed : tagAllowed mode tag = true)
    (hPost :
      postTagState mode tag =
        .need (childMode mode tag) (.retPush frame .scanUnread)) :
    ∃ m ≤ rawMalformedBudget (fuel + 1) n, ∃ cfg : EvalConfig,
      cfg ∈ checkedEvalRunLoopMachine.runBranches m
        [{ state := .need mode needExprCompositeMachine.initial,
           tape :=
             evalCursorStackEndTape witness consumed
               (b0 :: b1 :: b2 :: rest) (encodeEvalFrames frames) padding }] ∧
      EvalFailClosed cfg := by
  have hChildFuel : rest.length < fuel := by
    simp at hFuel
    omega
  have hChildWitness : rest.length ≤ witness.length := by
    simp at hWitness
    omega
  have hChildLayout :
      CheckedLayoutBound n (consumed + 3) rest
        (encodeEvalFrames (frame :: frames)) := by
    simpa [encodeEvalFrames, List.append_assoc] using
      (after_push_tag n consumed b0 b1 b2 rest
        (encodeEvalFrames frames) frame hLayout)

  obtain ⟨m0, hm0, h0⟩ :=
    pushTag_checked_reaches_need_within_envelope
      n mode witness rest (encodeEvalFrames frames) consumed padding
      b0 b1 b2 tag frame hTag hAllowed hPost
      hLayout.source_le hLayout.frames_le

  let padChild := ((padding - 1) - 1) - 1
  let cNeed : EvalConfig :=
    { state := .need (childMode mode tag) needExprCompositeMachine.initial,
      tape :=
        evalCursorStackEndTape witness (consumed + 3)
          rest (encodeEvalFrames (frame :: frames)) padChild }

  have h0' :
      cNeed ∈ checkedEvalRunLoopMachine.runBranches m0
        [{ state := .need mode needExprCompositeMachine.initial,
           tape :=
             evalCursorStackEndTape witness consumed
               (b0 :: b1 :: b2 :: rest) (encodeEvalFrames frames) padding }] := by
    simpa [cNeed, padChild] using h0

  obtain ⟨m1, hm1, cfg, h1, hfc⟩ :=
    hRec witness rest (frame :: frames)
      (childMode mode tag) (consumed + 3) padChild n
      hChildFuel hChildNone hChildLayout hChildWitness

  have h1' :
      cfg ∈ checkedEvalRunLoopMachine.runBranches m1 [cNeed] := by
    simpa [cNeed] using h1

  have hAll :=
    mem_runBranches_trans checkedEvalRunLoopMachine
      m0 m1
      [{ state := .need mode needExprCompositeMachine.initial,
         tape :=
           evalCursorStackEndTape witness consumed
             (b0 :: b1 :: b2 :: rest) (encodeEvalFrames frames) padding }]
      cNeed cfg h0' h1'

  have hm0Slice :
      m0 ≤ rawMalformedSlice n :=
    Nat.le_trans hm0 (loopEnvelope_le_rawMalformedSlice n)

  have hbudget :
      m0 + m1 ≤ rawMalformedBudget (fuel + 1) n := by
    calc
      m0 + m1 ≤ rawMalformedSlice n + rawMalformedBudget fuel n :=
        Nat.add_le_add hm0Slice hm1
      _ = rawMalformedBudget (fuel + 1) n :=
        slice_add_child_budget fuel n

  exact ⟨m0 + m1, hbudget, cfg, hAll, hfc⟩

theorem neg_child_failure
    (fuel n consumed padding : Nat)
    (witness rest : BitString)
    (frames : List EvalFrame)
    (mode : SyntaxMode)
    (hRec : RawMalformedAtFuel fuel)
    (hFuel :
      (false :: true :: true :: rest).length < fuel + 1)
    (hNone : decodeCircuitCore fuel rest = none)
    (hLayout :
      CheckedLayoutBound n consumed
        (false :: true :: true :: rest) (encodeEvalFrames frames))
    (hWitness :
      (false :: true :: true :: rest).length ≤ witness.length) :
    ∃ m ≤ rawMalformedBudget (fuel + 1) n, ∃ cfg : EvalConfig,
      cfg ∈ checkedEvalRunLoopMachine.runBranches m
        [{ state := .need mode needExprCompositeMachine.initial,
           tape :=
             evalCursorStackEndTape witness consumed
               (false :: true :: true :: rest) (encodeEvalFrames frames) padding }] ∧
      EvalFailClosed cfg := by
  cases hAllowed : tagAllowed mode .neg with
  | false =>
      exact disallowed_root_fail_closed
        witness rest frames mode consumed padding n fuel
        false true true (by simpa using hAllowed) hLayout
  | true =>
      exact push_tag_then_recursive_fail_closed
        fuel n consumed padding witness rest frames mode
        false true true .neg .neg hRec hFuel hNone hLayout hWitness
        rfl hAllowed
        (by simp [postTagState, childMode])

theorem and_left_failure
    (fuel n consumed padding : Nat)
    (witness rest : BitString)
    (frames : List EvalFrame)
    (mode : SyntaxMode)
    (hRec : RawMalformedAtFuel fuel)
    (hFuel :
      (true :: false :: false :: rest).length < fuel + 1)
    (hNone : decodeCircuitCore fuel rest = none)
    (hLayout :
      CheckedLayoutBound n consumed
        (true :: false :: false :: rest) (encodeEvalFrames frames))
    (hWitness :
      (true :: false :: false :: rest).length ≤ witness.length) :
    ∃ m ≤ rawMalformedBudget (fuel + 1) n, ∃ cfg : EvalConfig,
      cfg ∈ checkedEvalRunLoopMachine.runBranches m
        [{ state := .need mode needExprCompositeMachine.initial,
           tape :=
             evalCursorStackEndTape witness consumed
               (true :: false :: false :: rest) (encodeEvalFrames frames) padding }] ∧
      EvalFailClosed cfg := by
  cases hAllowed : tagAllowed mode .and with
  | false =>
      exact disallowed_root_fail_closed
        witness rest frames mode consumed padding n fuel
        true false false (by simpa using hAllowed) hLayout
  | true =>
      exact push_tag_then_recursive_fail_closed
        fuel n consumed padding witness rest frames mode
        true false false .and .andLeft hRec hFuel hNone hLayout hWitness
        rfl hAllowed
        (by
          cases mode <;>
            simp [tagAllowed] at hAllowed ⊢
          simp [postTagState, childMode])

theorem or_left_failure
    (fuel n consumed padding : Nat)
    (witness rest : BitString)
    (frames : List EvalFrame)
    (mode : SyntaxMode)
    (hRec : RawMalformedAtFuel fuel)
    (hFuel :
      (true :: false :: true :: rest).length < fuel + 1)
    (hNone : decodeCircuitCore fuel rest = none)
    (hLayout :
      CheckedLayoutBound n consumed
        (true :: false :: true :: rest) (encodeEvalFrames frames))
    (hWitness :
      (true :: false :: true :: rest).length ≤ witness.length) :
    ∃ m ≤ rawMalformedBudget (fuel + 1) n, ∃ cfg : EvalConfig,
      cfg ∈ checkedEvalRunLoopMachine.runBranches m
        [{ state := .need mode needExprCompositeMachine.initial,
           tape :=
             evalCursorStackEndTape witness consumed
               (true :: false :: true :: rest) (encodeEvalFrames frames) padding }] ∧
      EvalFailClosed cfg := by
  cases hAllowed : tagAllowed mode .or with
  | false =>
      exact disallowed_root_fail_closed
        witness rest frames mode consumed padding n fuel
        true false true (by simpa using hAllowed) hLayout
  | true =>
      exact push_tag_then_recursive_fail_closed
        fuel n consumed padding witness rest frames mode
        true false true .or .orLeft hRec hFuel hNone hLayout hWitness
        rfl hAllowed
        (by simp [postTagState, childMode])

#print axioms MCore.Real.P01RawMalformedRecursiveLeft.push_tag_then_recursive_fail_closed
#print axioms MCore.Real.P01RawMalformedRecursiveLeft.neg_child_failure
#print axioms MCore.Real.P01RawMalformedRecursiveLeft.and_left_failure
#print axioms MCore.Real.P01RawMalformedRecursiveLeft.or_left_failure

end P01RawMalformedRecursiveLeft
end Real
end MCore
