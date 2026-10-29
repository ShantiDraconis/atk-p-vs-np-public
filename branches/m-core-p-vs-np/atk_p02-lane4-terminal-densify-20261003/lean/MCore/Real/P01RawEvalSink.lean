import MCore.Real.P01RawBaseExact
import MCore.Real.P01RawRecursiveBudget
import MCore.Real.P01ExactBoundedReject

namespace MCore
namespace Real
namespace P01RawEvalSink

open CanonicalFinalProof
open CanonicalCircuitBits
open P01CNFMode
open P01NeedExprTagDecode
open P01NeedExprCompositeNTM
open P01EncodedStackEvaluator
open P01EvalCursorMachine
open P01EncodedFrameTape
open P01CheckedVerifierInvariant
open P01CheckedVerifierBudget
open P01CheckedEvalRunLoopNTM
open P01CheckedEvalRunTagPrefix
open P01CheckedEvalRunBoundedHelpers
open P01ExactBoundedReject
open P01RawMalformedTag
open P01RawMalformedUnary
open P01RawBaseExact
open P01RawRecursiveBudget
open P01NTMRunLaws

abbrev EvalConfig :=
  Configuration CheckedEvalRunState (Option Bool)

/-- A physical evaluator failure is either the explicit reject state or an
active dead-end with no successor.  Both are fail-closed after lifting to the
verifier. -/
inductive EvalFailureSink (cfg : EvalConfig) : Prop
  | reject (h : cfg.state = .reject) : EvalFailureSink cfg
  | dead
      (hactive : ¬ P01NTMRunLaws.Halted checkedEvalRunLoopMachine cfg)
      (hdead : checkedEvalRunLoopMachine.successors cfg = []) :
      EvalFailureSink cfg

theorem reject_is_sink (tape : Tape (Option Bool)) :
    EvalFailureSink
      ({ state := .reject, tape := tape } : EvalConfig) :=
  .reject rfl

/-- Reachability composition preserves the sink property. -/
theorem compose_reach_sink
    (a b : Nat)
    (start mid fin : EvalConfig)
    (h0 :
      mid ∈ checkedEvalRunLoopMachine.runBranches a [start])
    (h1 :
      fin ∈ checkedEvalRunLoopMachine.runBranches b [mid])
    (hsink : EvalFailureSink fin) :
    fin ∈ checkedEvalRunLoopMachine.runBranches (a + b) [start] ∧
      EvalFailureSink fin :=
  ⟨mem_runBranches_trans checkedEvalRunLoopMachine
      a b [start] mid fin h0 h1,
    hsink⟩

/-- Any three-bit tag forbidden in the current syntax mode reaches explicit
reject within one raw cubic chunk. -/
theorem disallowed_tag_reaches_sink
    (n : Nat)
    (mode : SyntaxMode)
    (witness rest : BitString)
    (frames : List EvalFrame)
    (consumed padding : Nat)
    (b0 b1 b2 : Bool)
    (hdis :
      tagAllowed mode (decodeTagBits b0 b1 b2) = false)
    (hLayout :
      CheckedLayoutBound n consumed
        (b0 :: b1 :: b2 :: rest)
        (encodeEvalFrames frames)) :
    ∃ m ≤ rawChunk n, ∃ cfg : EvalConfig,
      cfg ∈ checkedEvalRunLoopMachine.runBranches m
        [{ state := .need mode needExprCompositeMachine.initial,
           tape :=
             evalCursorStackEndTape witness consumed
               (b0 :: b1 :: b2 :: rest)
               (encodeEvalFrames frames) padding }] ∧
      EvalFailureSink cfg := by
  obtain ⟨m, hm, tape, hreach⟩ :=
    root_tag_reject_within_envelope
      n mode witness rest (encodeEvalFrames frames)
      consumed padding b0 b1 b2 hdis
      hLayout.source_le hLayout.frames_le
  refine ⟨m, Nat.le_trans hm (loopEnvelope_le_rawChunk n),
    { state := .reject, tape := tape }, hreach, ?_⟩
  exact reject_is_sink tape

/-- A truncated tag reaches a dead sink within one raw chunk. -/
theorem truncated_tag_reaches_sink
    (n : Nat)
    (mode : SyntaxMode)
    (witness source : BitString)
    (frames : List EvalFrame)
    (consumed padding : Nat)
    (hshort : source.length < 3)
    (hLayout :
      CheckedLayoutBound n consumed source
        (encodeEvalFrames frames)) :
    ∃ m ≤ rawChunk n, ∃ cfg : EvalConfig,
      cfg ∈ checkedEvalRunLoopMachine.runBranches m
        [{ state := .need mode needExprCompositeMachine.initial,
           tape :=
             evalCursorStackEndTape witness consumed
               source (encodeEvalFrames frames) padding }] ∧
      EvalFailureSink cfg := by
  obtain ⟨m, hm, dead, hreach, hactive, hdead⟩ :=
    checked_truncated_tag_reaches_dead
      mode witness source (encodeEvalFrames frames)
      consumed padding hshort
  have htag :
      (encodeEvalFrames frames).length + source.length + 7 ≤
        checkedTagPrefixFuel source (encodeEvalFrames frames) := by
    unfold checkedTagPrefixFuel
    omega
  have henv :
      checkedTagPrefixFuel source (encodeEvalFrames frames) ≤
        checkedStepEnvelope n :=
    checkedTagPrefixFuel_le_envelope
      n source (encodeEvalFrames frames)
      hLayout.source_le hLayout.frames_le
  have hm' : m ≤ rawChunk n :=
    Nat.le_trans hm
      (Nat.le_trans htag
        (Nat.le_trans henv (stepEnvelope_le_rawChunk n)))
  refine ⟨m, hm', dead, hreach, ?_⟩
  exact .dead hactive hdead

/-- Decoder failure in the unary input payload reaches a dead sink within one
raw chunk. -/
theorem unary_none_reaches_sink
    (n : Nat)
    (mode : SyntaxMode)
    (witness rest : BitString)
    (frames : List EvalFrame)
    (consumed padding : Nat)
    (hdec : decodeNat rest = none)
    (hLayout :
      CheckedLayoutBound n consumed
        (false :: false :: false :: rest)
        (encodeEvalFrames frames)) :
    ∃ m ≤ rawChunk n, ∃ cfg : EvalConfig,
      cfg ∈ checkedEvalRunLoopMachine.runBranches m
        [{ state := .need mode needExprCompositeMachine.initial,
           tape :=
             evalCursorStackEndTape witness consumed
               (false :: false :: false :: rest)
               (encodeEvalFrames frames) padding }] ∧
      EvalFailureSink cfg := by
  have hrest :=
    P01RawBaseExact.decodeNat_none_eq_replicate_true rest hdec
  obtain ⟨m, hm, dead, hreach, hactive, hdead⟩ :=
    checked_truncated_unary_reaches_dead
      mode witness (encodeEvalFrames frames)
      consumed padding rest.length
  have hsource :
      (false :: false :: false :: List.replicate rest.length true : BitString).length ≤ n := by
    simpa [← hrest] using hLayout.source_le
  have hframes :
      (encodeEvalFrames frames).length ≤ n :=
    hLayout.frames_le
  have htag :
      checkedTagPrefixFuel
          (false :: false :: false :: List.replicate rest.length true)
          (encodeEvalFrames frames) ≤
        checkedStepEnvelope n :=
    checkedTagPrefixFuel_le_envelope
      n
      (false :: false :: false :: List.replicate rest.length true)
      (encodeEvalFrames frames) hsource hframes
  have hk : rest.length + 1 ≤ n + 1 := by
    have hr : rest.length ≤ n := by
      have := hsource
      simp at this
      omega
    omega
  have hm' :
      m ≤ checkedStepEnvelope n + (n + 1) := by
    exact Nat.le_trans hm (Nat.add_le_add htag hk)
  have hbudget :
      m ≤ rawChunk n :=
    Nat.le_trans hm' (step_plus_linear_le_rawChunk n)
  have hreach' :
      dead ∈ checkedEvalRunLoopMachine.runBranches m
        [{ state := .need mode needExprCompositeMachine.initial,
           tape :=
             evalCursorStackEndTape witness consumed
               (false :: false :: false :: rest)
               (encodeEvalFrames frames) padding }] := by
    rw [hrest]
    exact hreach
  exact ⟨m, hbudget, dead, hreach', .dead hactive hdead⟩

/-- One already-bounded prefix plus a recursively reached sink composes without
changing the failure classification. -/
theorem prefix_then_sink
    (a b : Nat)
    (start mid fin : EvalConfig)
    (h0 : mid ∈ checkedEvalRunLoopMachine.runBranches a [start])
    (h1 : fin ∈ checkedEvalRunLoopMachine.runBranches b [mid])
    (hs : EvalFailureSink fin) :
    fin ∈ checkedEvalRunLoopMachine.runBranches (a + b) [start] ∧
      EvalFailureSink fin :=
  compose_reach_sink a b start mid fin h0 h1 hs

#print axioms MCore.Real.P01RawEvalSink.disallowed_tag_reaches_sink
#print axioms MCore.Real.P01RawEvalSink.truncated_tag_reaches_sink
#print axioms MCore.Real.P01RawEvalSink.unary_none_reaches_sink
#print axioms MCore.Real.P01RawEvalSink.prefix_then_sink

end P01RawEvalSink
end Real
end MCore
