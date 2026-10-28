import MCore.Real.P01RawEvalSink
import MCore.Real.P01ExactBoundedCircuitProducer
import MCore.Real.P01ExactBoundedReject
import MCore.Real.P01CheckedEvalRunBoundedHelpers
import MCore.Real.CanonicalSATWitness

namespace MCore
namespace Real
namespace P01RawRecursiveSteps

open CanonicalFinalProof
open CanonicalCircuitBits
open CanonicalSATWitness
open P01CNFMode
open P01NeedExprTagDecode
open P01NeedExprCompositeNTM
open P01EncodedStackEvaluator
open P01EvalCursorMachine
open P01EncodedFrameTape
open P01CheckedVerifierInvariant
open P01CheckedEvalRunLoopNTM
open P01CheckedEvalRunBaseCases
open P01CheckedEvalRunBoundedHelpers
open P01ExactBoundedCircuitProducer
open P01ExactBoundedReject
open P01RawEvalSink
open P01RawRecursiveBudget
open P01NTMRunLaws

abbrev EvalConfig :=
  Configuration CheckedEvalRunState (Option Bool)

def witnessAssignment (witness : BitString) : Assignment :=
  fun i => witness.getD i false

/-- Standard recursive sink certificate at a fixed global source bound n. -/
def RawSinkCertificate
    (fuel n : Nat)
    (mode : SyntaxMode)
    (witness bits : BitString)
    (frames : List EvalFrame)
    (consumed padding : Nat) : Prop :=
  ∃ m ≤ rawFailureBudget fuel n, ∃ cfg : EvalConfig,
    cfg ∈ checkedEvalRunLoopMachine.runBranches m
      [{ state := .need mode needExprCompositeMachine.initial,
         tape :=
           evalCursorStackEndTape witness consumed bits
             (encodeEvalFrames frames) padding }] ∧
    EvalFailureSink cfg

theorem chunk_sink_to_succ
    (fuel n : Nat)
    (mode : SyntaxMode)
    (witness bits : BitString)
    (frames : List EvalFrame)
    (consumed padding : Nat)
    (h :
      ∃ m ≤ rawChunk n, ∃ cfg : EvalConfig,
        cfg ∈ checkedEvalRunLoopMachine.runBranches m
          [{ state := .need mode needExprCompositeMachine.initial,
             tape :=
               evalCursorStackEndTape witness consumed bits
                 (encodeEvalFrames frames) padding }] ∧
        EvalFailureSink cfg) :
    RawSinkCertificate (fuel + 1) n mode witness bits frames
      consumed padding := by
  rcases h with ⟨m, hm, cfg, hreach, hsink⟩
  refine ⟨m, ?_, cfg, hreach, hsink⟩
  exact Nat.le_trans hm
    (rawChunk_le_failureBudget (fuel + 1) n (by omega))

/-- One cubic prefix followed by the recursive sink consumes exactly one fuel
level of the raw potential. -/
theorem prefix_chunk_then_recursive
    (fuel n : Nat)
    (start mid : EvalConfig)
    (a : Nat)
    (ha : a ≤ rawChunk n)
    (hprefix :
      mid ∈ checkedEvalRunLoopMachine.runBranches a [start])
    (hrec :
      ∃ b ≤ rawFailureBudget fuel n, ∃ fin : EvalConfig,
        fin ∈ checkedEvalRunLoopMachine.runBranches b [mid] ∧
        EvalFailureSink fin) :
    ∃ total ≤ rawFailureBudget (fuel + 1) n, ∃ fin : EvalConfig,
      fin ∈ checkedEvalRunLoopMachine.runBranches total [start] ∧
      EvalFailureSink fin := by
  rcases hrec with ⟨b, hb, fin, hfin, hsink⟩
  refine ⟨a + b, ?_, fin, ?_, hsink⟩
  · rw [rawFailureBudget_succ]
    omega
  · exact mem_runBranches_trans checkedEvalRunLoopMachine
      a b [start] mid fin hprefix hfin

private theorem not_allowed_post
    (mode : SyntaxMode)
    (_h : tagAllowed mode .neg = true) :
    P01CheckedEvalRunTagPrefix.postTagState mode .neg =
      .need (childMode mode .neg) (.retPush .neg .scanUnread) := by
  rfl

/-- Propagate a malformed NOT child. -/
theorem not_child_failure_step
    (fuel n : Nat)
    (mode : SyntaxMode)
    (witness rest : BitString)
    (frames : List EvalFrame)
    (consumed padding : Nat)
    (hLayout :
      CheckedLayoutBound n consumed
        (false :: true :: true :: rest)
        (encodeEvalFrames frames))
    (hrec :
      RawSinkCertificate fuel n (childMode mode .neg)
        witness rest (.neg :: frames) (consumed + 3)
        (((padding - 1) - 1) - 1)) :
    RawSinkCertificate (fuel + 1) n mode witness
      (false :: true :: true :: rest) frames consumed padding := by
  cases hallowed : tagAllowed mode .neg with
  | false =>
      apply chunk_sink_to_succ fuel n mode witness
        (false :: true :: true :: rest) frames consumed padding
      exact disallowed_tag_reaches_sink
        n mode witness rest frames consumed padding
        false true true (by simpa using hallowed) hLayout
  | true =>
      obtain ⟨m0, hm0, h0⟩ :=
        pushTag_checked_reaches_need_within_envelope
          n mode witness rest (encodeEvalFrames frames)
          consumed padding false true true .neg .neg rfl
          (by simpa using hallowed)
          (not_allowed_post mode (by simpa using hallowed))
          hLayout.source_le hLayout.frames_le
      let start : EvalConfig :=
        { state := .need mode needExprCompositeMachine.initial,
          tape :=
            evalCursorStackEndTape witness consumed
              (false :: true :: true :: rest)
              (encodeEvalFrames frames) padding }
      let mid : EvalConfig :=
        { state := .need (childMode mode .neg)
              needExprCompositeMachine.initial,
          tape :=
            evalCursorStackEndTape witness (consumed + 3) rest
              (encodeEvalFrame .neg ++ encodeEvalFrames frames)
              (((padding - 1) - 1) - 1) }
      have hprefix : mid ∈
          checkedEvalRunLoopMachine.runBranches m0 [start] := by
        simpa [start, mid, encodeEvalFrames, List.append_assoc, childMode] using h0
      have hrec' :
          ∃ b ≤ rawFailureBudget fuel n, ∃ fin : EvalConfig,
            fin ∈ checkedEvalRunLoopMachine.runBranches b [mid] ∧
            EvalFailureSink fin := by
        simpa [RawSinkCertificate, mid, encodeEvalFrames,
          List.append_assoc] using hrec
      exact prefix_chunk_then_recursive fuel n start mid m0
        (Nat.le_trans hm0 (loopEnvelope_le_rawChunk n))
        hprefix hrec'

/-- Propagate a malformed left child of AND. -/
theorem and_left_failure_step
    (fuel n : Nat)
    (mode : SyntaxMode)
    (witness rest : BitString)
    (frames : List EvalFrame)
    (consumed padding : Nat)
    (hLayout :
      CheckedLayoutBound n consumed
        (true :: false :: false :: rest)
        (encodeEvalFrames frames))
    (hrec :
      RawSinkCertificate fuel n .cnf
        witness rest (.andLeft :: frames) (consumed + 3)
        (((padding - 1) - 1) - 1)) :
    RawSinkCertificate (fuel + 1) n mode witness
      (true :: false :: false :: rest) frames consumed padding := by
  cases mode with
  | clause =>
      apply chunk_sink_to_succ fuel n .clause witness
        (true :: false :: false :: rest) frames consumed padding
      exact disallowed_tag_reaches_sink
        n .clause witness rest frames consumed padding
        true false false rfl hLayout
  | mustInput =>
      apply chunk_sink_to_succ fuel n .mustInput witness
        (true :: false :: false :: rest) frames consumed padding
      exact disallowed_tag_reaches_sink
        n .mustInput witness rest frames consumed padding
        true false false rfl hLayout
  | cnf =>
      obtain ⟨m0, hm0, h0⟩ :=
        pushTag_checked_reaches_need_within_envelope
          n .cnf witness rest (encodeEvalFrames frames)
          consumed padding true false false .and .andLeft
          rfl rfl rfl hLayout.source_le hLayout.frames_le
      let start : EvalConfig :=
        { state := .need .cnf needExprCompositeMachine.initial,
          tape :=
            evalCursorStackEndTape witness consumed
              (true :: false :: false :: rest)
              (encodeEvalFrames frames) padding }
      let mid : EvalConfig :=
        { state := .need .cnf needExprCompositeMachine.initial,
          tape :=
            evalCursorStackEndTape witness (consumed + 3) rest
              (encodeEvalFrame .andLeft ++ encodeEvalFrames frames)
              (((padding - 1) - 1) - 1) }
      have hprefix : mid ∈
          checkedEvalRunLoopMachine.runBranches m0 [start] := by
        simpa [start, mid, encodeEvalFrames, List.append_assoc, childMode] using h0
      have hrec' :
          ∃ b ≤ rawFailureBudget fuel n, ∃ fin : EvalConfig,
            fin ∈ checkedEvalRunLoopMachine.runBranches b [mid] ∧
            EvalFailureSink fin := by
        simpa [RawSinkCertificate, mid, encodeEvalFrames,
          List.append_assoc] using hrec
      exact prefix_chunk_then_recursive fuel n start mid m0
        (Nat.le_trans hm0 (loopEnvelope_le_rawChunk n))
        hprefix hrec'

private theorem or_left_allowed_step
    (fuel n : Nat)
    (mode : SyntaxMode)
    (witness rest : BitString)
    (frames : List EvalFrame)
    (consumed padding : Nat)
    (hallowed : tagAllowed mode .or = true)
    (hpost :
      P01CheckedEvalRunTagPrefix.postTagState mode .or =
        .need .clause (.retPush .orLeft .scanUnread))
    (hLayout :
      CheckedLayoutBound n consumed
        (true :: false :: true :: rest)
        (encodeEvalFrames frames))
    (hrec :
      RawSinkCertificate fuel n .clause
        witness rest (.orLeft :: frames) (consumed + 3)
        (((padding - 1) - 1) - 1)) :
    RawSinkCertificate (fuel + 1) n mode witness
      (true :: false :: true :: rest) frames consumed padding := by
  obtain ⟨m0, hm0, h0⟩ :=
    pushTag_checked_reaches_need_within_envelope
      n mode witness rest (encodeEvalFrames frames)
      consumed padding true false true .or .orLeft
      rfl hallowed (by simpa [childMode] using hpost)
      hLayout.source_le hLayout.frames_le
  let start : EvalConfig :=
    { state := .need mode needExprCompositeMachine.initial,
      tape :=
        evalCursorStackEndTape witness consumed
          (true :: false :: true :: rest)
          (encodeEvalFrames frames) padding }
  let mid : EvalConfig :=
    { state := .need .clause needExprCompositeMachine.initial,
      tape :=
        evalCursorStackEndTape witness (consumed + 3) rest
          (encodeEvalFrame .orLeft ++ encodeEvalFrames frames)
          (((padding - 1) - 1) - 1) }
  have hprefix : mid ∈
      checkedEvalRunLoopMachine.runBranches m0 [start] := by
    simpa [start, mid, encodeEvalFrames, List.append_assoc, childMode] using h0
  have hrec' :
      ∃ b ≤ rawFailureBudget fuel n, ∃ fin : EvalConfig,
        fin ∈ checkedEvalRunLoopMachine.runBranches b [mid] ∧
        EvalFailureSink fin := by
    simpa [RawSinkCertificate, mid, encodeEvalFrames,
      List.append_assoc] using hrec
  exact prefix_chunk_then_recursive fuel n start mid m0
    (Nat.le_trans hm0 (loopEnvelope_le_rawChunk n))
    hprefix hrec'

/-- Propagate a malformed left child of OR. -/
theorem or_left_failure_step
    (fuel n : Nat)
    (mode : SyntaxMode)
    (witness rest : BitString)
    (frames : List EvalFrame)
    (consumed padding : Nat)
    (hLayout :
      CheckedLayoutBound n consumed
        (true :: false :: true :: rest)
        (encodeEvalFrames frames))
    (hrec :
      RawSinkCertificate fuel n .clause
        witness rest (.orLeft :: frames) (consumed + 3)
        (((padding - 1) - 1) - 1)) :
    RawSinkCertificate (fuel + 1) n mode witness
      (true :: false :: true :: rest) frames consumed padding := by
  cases mode with
  | mustInput =>
      apply chunk_sink_to_succ fuel n .mustInput witness
        (true :: false :: true :: rest) frames consumed padding
      exact disallowed_tag_reaches_sink
        n .mustInput witness rest frames consumed padding
        true false true rfl hLayout
  | cnf =>
      exact or_left_allowed_step fuel n .cnf witness rest frames
        consumed padding rfl rfl hLayout hrec
  | clause =>
      exact or_left_allowed_step fuel n .clause witness rest frames
        consumed padding rfl rfl hLayout hrec

private theorem circuit_len_le_of_binary_layout
    (n consumed : Nat)
    (tag0 tag1 tag2 : Bool)
    (left : CircuitK1.Circuit)
    (rightSource frameStack : BitString)
    (h :
      CheckedLayoutBound n consumed
        (tag0 :: tag1 :: tag2 ::
          (encodeCircuit left ++ rightSource))
        frameStack) :
    (encodeCircuit left).length ≤ n := by
  have hs := h.source_budget
  simp [List.length_append] at hs
  omega

private theorem varBound_le_witness_of_binary_layout
    (n consumed : Nat)
    (tag0 tag1 tag2 : Bool)
    (witness : BitString)
    (left : CircuitK1.Circuit)
    (rightSource frameStack : BitString)
    (hw : witness.length = n)
    (h :
      CheckedLayoutBound n consumed
        (tag0 :: tag1 :: tag2 ::
          (encodeCircuit left ++ rightSource))
        frameStack) :
    varBound left ≤ witness.length := by
  rw [hw]
  exact Nat.le_trans
    (varBound_le_encoded_length left)
    (circuit_len_le_of_binary_layout
      n consumed tag0 tag1 tag2 left rightSource frameStack h)

private theorem witness_read_agrees
    (witness : BitString) :
    ∀ i, i < witness.length →
      witness.getD i false = witnessAssignment witness i := by
  intro i hi
  rfl

/-- AND-right structural decoder failure.  A syntactically invalid left child
rejects directly; a valid left child is evaluated exactly, its continuation
opens the right child, and the recursive sink is then propagated. -/
theorem and_right_failure_step
    (fuel n : Nat)
    (mode : SyntaxMode)
    (witness : BitString)
    (left : CircuitK1.Circuit)
    (rightSource : BitString)
    (frames : List EvalFrame)
    (consumed padding : Nat)
    (hw : witness.length = n)
    (hLayout :
      CheckedLayoutBound n consumed
        (true :: false :: false ::
          (encodeCircuit left ++ rightSource))
        (encodeEvalFrames frames))
    (hrec :
      ∀ (padRight : Nat),
        CheckedLayoutBound n
          (consumed + 3 + (encodeCircuit left).length)
          rightSource
          (encodeEvalFrames
            (.andRight
              (evalCircuit (witnessAssignment witness) left) :: frames)) →
        RawSinkCertificate fuel n .cnf witness rightSource
          (.andRight
            (evalCircuit (witnessAssignment witness) left) :: frames)
          (consumed + 3 + (encodeCircuit left).length)
          padRight) :
    RawSinkCertificate (fuel + 1) n mode witness
      (true :: false :: false ::
        (encodeCircuit left ++ rightSource))
      frames consumed padding := by
  cases mode with
  | clause =>
      apply chunk_sink_to_succ fuel n .clause witness
        (true :: false :: false ::
          (encodeCircuit left ++ rightSource))
        frames consumed padding
      exact disallowed_tag_reaches_sink
        n .clause witness (encodeCircuit left ++ rightSource)
        frames consumed padding true false false rfl hLayout
  | mustInput =>
      apply chunk_sink_to_succ fuel n .mustInput witness
        (true :: false :: false ::
          (encodeCircuit left ++ rightSource))
        frames consumed padding
      exact disallowed_tag_reaches_sink
        n .mustInput witness (encodeCircuit left ++ rightSource)
        frames consumed padding true false false rfl hLayout
  | cnf =>
      obtain ⟨m0, hm0, h0⟩ :=
        pushTag_checked_reaches_need_within_envelope
          n .cnf witness (encodeCircuit left ++ rightSource)
          (encodeEvalFrames frames) consumed padding
          true false false .and .andLeft rfl rfl rfl
          hLayout.source_le hLayout.frames_le
      let padLeft := (((padding - 1) - 1) - 1)
      let leftConsumed := consumed + 3
      let start : EvalConfig :=
        { state := .need .cnf needExprCompositeMachine.initial,
          tape :=
            evalCursorStackEndTape witness consumed
              (true :: false :: false ::
                (encodeCircuit left ++ rightSource))
              (encodeEvalFrames frames) padding }
      let cNeedLeft : EvalConfig :=
        { state := .need .cnf needExprCompositeMachine.initial,
          tape :=
            evalCursorStackEndTape witness leftConsumed
              (encodeCircuit left ++ rightSource)
              (encodeEvalFrame .andLeft ++ encodeEvalFrames frames)
              padLeft }
      have h0' : cNeedLeft ∈
          checkedEvalRunLoopMachine.runBranches m0 [start] := by
        simpa [start, cNeedLeft, padLeft, leftConsumed,
          encodeEvalFrames, List.append_assoc] using h0
      have hLayoutLeft :
          CheckedLayoutBound n leftConsumed
            (encodeCircuit left ++ rightSource)
            (encodeEvalFrame .andLeft ++ encodeEvalFrames frames) := by
        have h :=
          P01CheckedVerifierInvariant.after_push_tag
            n consumed true false false
            (encodeCircuit left ++ rightSource)
            (encodeEvalFrames frames) .andLeft hLayout
        simpa [leftConsumed] using h
      have hlen :
          varBound left ≤ witness.length :=
        varBound_le_witness_of_binary_layout
          n consumed true false false witness left rightSource
          (encodeEvalFrames frames) hw hLayout
      have henc :
          (encodeCircuit left).length ≤ n :=
        circuit_len_le_of_binary_layout
          n consumed true false false left rightSource
          (encodeEvalFrames frames) hLayout
      cases hmode : modeCheck .cnf left with
      | false =>
          have hreject :=
            circuit_exact_bounded_reject
              (witnessAssignment witness) witness left .cnf
          obtain ⟨m1, hm1, cfg, h1, hstate⟩ :=
            hreject hmode rightSource (.andLeft :: frames)
              leftConsumed padLeft n
              (by simpa [encodeEvalFrames, List.append_assoc] using hLayoutLeft)
              hlen (by
                intro i hi
                exact witness_read_agrees witness i
                  (Nat.lt_of_lt_of_le hi hlen))
          have h1' : cfg ∈
              checkedEvalRunLoopMachine.runBranches m1 [cNeedLeft] := by
            simpa [cNeedLeft, encodeEvalFrames,
              List.append_assoc] using h1
          have hAll :=
            mem_runBranches_trans checkedEvalRunLoopMachine
              m0 m1 [start] cNeedLeft cfg h0' h1'
          refine ⟨m0 + m1, ?_, cfg, hAll, ?_⟩
          · have hcost :
                m0 + m1 ≤ rawChunk n := by
              have hc :=
                circuit_plus_loop_le_rawChunk n left henc
              omega
            exact Nat.le_trans hcost
              (rawChunk_le_failureBudget (fuel + 1) n (by omega))
          · exact .reject hstate
      | true =>
          have hpositive :=
            circuit_exact_bounded_certificate
              (witnessAssignment witness) witness left .cnf
          obtain ⟨m1, hm1, cfgLeft, h1, hout1⟩ :=
            hpositive hmode rightSource (.andLeft :: frames)
              leftConsumed padLeft n
              (by simpa [encodeEvalFrames, List.append_assoc] using hLayoutLeft)
              hlen (by
                intro i hi
                exact witness_read_agrees witness i
                  (Nat.lt_of_lt_of_le hi hlen))
          have h1' : cfgLeft ∈
              checkedEvalRunLoopMachine.runBranches m1 [cNeedLeft] := by
            simpa [cNeedLeft, encodeEvalFrames,
              List.append_assoc] using h1
          let afterLeft :=
            leftConsumed + (encodeCircuit left).length
          obtain ⟨padding1, hcfgLeft⟩ :=
            exact_outcome_have_of_frames_ne_nil
              witness (exitMode .cnf left)
              (evalCircuit (witnessAssignment witness) left)
              rightSource (.andLeft :: frames)
              afterLeft cfgLeft (by simp)
              (by simpa [afterLeft] using hout1)
          subst cfgLeft
          obtain ⟨m2, hm2, h2⟩ :=
            andLeftReturn_checked_reaches_need_within_envelope
              n (exitMode .cnf left)
              witness rightSource (encodeEvalFrames frames)
              afterLeft padding1
              (evalCircuit (witnessAssignment witness) left)
          let padRight := ((((padding1 + 3) - 1) - 1) - 1)
          let cHaveLeft : EvalConfig :=
            { state := .have (exitMode .cnf left)
                (.start (evalCircuit (witnessAssignment witness) left))
              tape :=
                evalCursorStackEndTape witness afterLeft rightSource
                  (encodeEvalFrames (.andLeft :: frames)) padding1 }
          let cNeedRight : EvalConfig :=
            { state := .need .cnf needExprCompositeMachine.initial,
              tape :=
                evalCursorStackEndTape witness afterLeft rightSource
                  (encodeEvalFrame
                    (.andRight
                      (evalCircuit (witnessAssignment witness) left)) ++
                    encodeEvalFrames frames)
                  padRight }
          have h01 :=
            mem_runBranches_trans checkedEvalRunLoopMachine
              m0 m1 [start] cNeedLeft cHaveLeft
              h0' (by simpa [cHaveLeft, afterLeft, encodeEvalFrames,
                List.append_assoc] using h1')
          have h2' : cNeedRight ∈
              checkedEvalRunLoopMachine.runBranches m2 [cHaveLeft] := by
            simpa [cHaveLeft, cNeedRight, padRight, encodeEvalFrames,
              List.append_assoc] using h2
          have hpre :=
            mem_runBranches_trans checkedEvalRunLoopMachine
              (m0 + m1) m2 [start]
              cHaveLeft cNeedRight h01 h2'
          have hLayoutRight :
              CheckedLayoutBound n afterLeft rightSource
                (encodeEvalFrames
                  (.andRight
                    (evalCircuit (witnessAssignment witness) left) :: frames)) := by
            have hp :
                CheckedLayoutBound n
                  (consumed +
                    (true :: false :: false :: encodeCircuit left).length)
                  rightSource
                  (encodeEvalFrame
                    (.andRight
                      (evalCircuit (witnessAssignment witness) left)) ++
                    encodeEvalFrames frames) := by
              apply layout_after_prefix_with_frame
                n consumed
                (true :: false :: false :: encodeCircuit left)
                rightSource (encodeEvalFrames frames)
                (.andRight
                  (evalCircuit (witnessAssignment witness) left))
              · simp
              · simpa [List.append_assoc] using hLayout
            have hoff :
                consumed +
                    (true :: false :: false :: encodeCircuit left).length =
                  afterLeft := by
              simp [afterLeft, leftConsumed]
              omega
            rw [← hoff]
            simpa [encodeEvalFrames, List.append_assoc] using hp
          have hrec' := hrec padRight hLayoutRight
          have hprefixBudget :
              m0 + m1 + m2 ≤ rawChunk n := by
            have hc :=
              circuit_plus_two_loops_le_rawChunk n left henc
            omega
          have hrecMid :
              ∃ b ≤ rawFailureBudget fuel n, ∃ fin : EvalConfig,
                fin ∈ checkedEvalRunLoopMachine.runBranches b [cNeedRight] ∧
                EvalFailureSink fin := by
            simpa [RawSinkCertificate, cNeedRight, padRight,
              encodeEvalFrames, List.append_assoc] using hrec'
          exact prefix_chunk_then_recursive fuel n start cNeedRight
            (m0 + m1 + m2) hprefixBudget hpre hrecMid

private theorem or_right_allowed_step
    (fuel n : Nat)
    (mode : SyntaxMode)
    (witness : BitString)
    (left : CircuitK1.Circuit)
    (rightSource : BitString)
    (frames : List EvalFrame)
    (consumed padding : Nat)
    (hw : witness.length = n)
    (hallowed : tagAllowed mode .or = true)
    (hLayout :
      CheckedLayoutBound n consumed
        (true :: false :: true ::
          (encodeCircuit left ++ rightSource))
        (encodeEvalFrames frames))
    (hrec :
      ∀ (padRight : Nat),
        CheckedLayoutBound n
          (consumed + 3 + (encodeCircuit left).length)
          rightSource
          (encodeEvalFrames
            (.orRight
              (evalCircuit (witnessAssignment witness) left) :: frames)) →
        RawSinkCertificate fuel n .clause witness rightSource
          (.orRight
            (evalCircuit (witnessAssignment witness) left) :: frames)
          (consumed + 3 + (encodeCircuit left).length)
          padRight) :
    RawSinkCertificate (fuel + 1) n mode witness
      (true :: false :: true ::
        (encodeCircuit left ++ rightSource))
      frames consumed padding := by
  obtain ⟨m0, hm0, h0⟩ :=
    pushTag_checked_reaches_need_within_envelope
      n mode witness (encodeCircuit left ++ rightSource)
      (encodeEvalFrames frames) consumed padding
      true false true .or .orLeft rfl hallowed rfl
      hLayout.source_le hLayout.frames_le
  let padLeft := (((padding - 1) - 1) - 1)
  let leftConsumed := consumed + 3
  let start : EvalConfig :=
    { state := .need mode needExprCompositeMachine.initial,
      tape :=
        evalCursorStackEndTape witness consumed
          (true :: false :: true ::
            (encodeCircuit left ++ rightSource))
          (encodeEvalFrames frames) padding }
  let cNeedLeft : EvalConfig :=
    { state := .need .clause needExprCompositeMachine.initial,
      tape :=
        evalCursorStackEndTape witness leftConsumed
          (encodeCircuit left ++ rightSource)
          (encodeEvalFrame .orLeft ++ encodeEvalFrames frames)
          padLeft }
  have h0' : cNeedLeft ∈
      checkedEvalRunLoopMachine.runBranches m0 [start] := by
    simpa [start, cNeedLeft, padLeft, leftConsumed,
      encodeEvalFrames, List.append_assoc, childMode] using h0
  have hLayoutLeft :
      CheckedLayoutBound n leftConsumed
        (encodeCircuit left ++ rightSource)
        (encodeEvalFrame .orLeft ++ encodeEvalFrames frames) := by
    have h :=
      P01CheckedVerifierInvariant.after_push_tag
        n consumed true false true
        (encodeCircuit left ++ rightSource)
        (encodeEvalFrames frames) .orLeft hLayout
    simpa [leftConsumed] using h
  have hlen :
      varBound left ≤ witness.length :=
    varBound_le_witness_of_binary_layout
      n consumed true false true witness left rightSource
      (encodeEvalFrames frames) hw hLayout
  have henc :
      (encodeCircuit left).length ≤ n :=
    circuit_len_le_of_binary_layout
      n consumed true false true left rightSource
      (encodeEvalFrames frames) hLayout
  cases hmode : modeCheck .clause left with
  | false =>
      have hreject :=
        circuit_exact_bounded_reject
          (witnessAssignment witness) witness left .clause
      obtain ⟨m1, hm1, cfg, h1, hstate⟩ :=
        hreject hmode rightSource (.orLeft :: frames)
          leftConsumed padLeft n
          (by simpa [encodeEvalFrames, List.append_assoc] using hLayoutLeft)
          hlen (by
            intro i hi
            exact witness_read_agrees witness i
              (Nat.lt_of_lt_of_le hi hlen))
      have h1' : cfg ∈
          checkedEvalRunLoopMachine.runBranches m1 [cNeedLeft] := by
        simpa [cNeedLeft, encodeEvalFrames, List.append_assoc] using h1
      have hAll :=
        mem_runBranches_trans checkedEvalRunLoopMachine
          m0 m1 [start] cNeedLeft cfg h0' h1'
      refine ⟨m0 + m1, ?_, cfg, hAll, ?_⟩
      · have hcost :
            m0 + m1 ≤ rawChunk n := by
          have hc :=
            circuit_plus_loop_le_rawChunk n left henc
          omega
        exact Nat.le_trans hcost
          (rawChunk_le_failureBudget (fuel + 1) n (by omega))
      · exact .reject hstate
  | true =>
      have hpositive :=
        circuit_exact_bounded_certificate
          (witnessAssignment witness) witness left .clause
      obtain ⟨m1, hm1, cfgLeft, h1, hout1⟩ :=
        hpositive hmode rightSource (.orLeft :: frames)
          leftConsumed padLeft n
          (by simpa [encodeEvalFrames, List.append_assoc] using hLayoutLeft)
          hlen (by
            intro i hi
            exact witness_read_agrees witness i
              (Nat.lt_of_lt_of_le hi hlen))
      have h1' : cfgLeft ∈
          checkedEvalRunLoopMachine.runBranches m1 [cNeedLeft] := by
        simpa [cNeedLeft, encodeEvalFrames, List.append_assoc] using h1
      let afterLeft :=
        leftConsumed + (encodeCircuit left).length
      obtain ⟨padding1, hcfgLeft⟩ :=
        exact_outcome_have_of_frames_ne_nil
          witness (exitMode .clause left)
          (evalCircuit (witnessAssignment witness) left)
          rightSource (.orLeft :: frames)
          afterLeft cfgLeft (by simp)
          (by simpa [afterLeft] using hout1)
      subst cfgLeft
      obtain ⟨m2, hm2, h2⟩ :=
        orLeftReturn_checked_reaches_need_within_envelope
          n (exitMode .clause left)
          witness rightSource (encodeEvalFrames frames)
          afterLeft padding1
          (evalCircuit (witnessAssignment witness) left)
      let padRight := ((((padding1 + 3) - 1) - 1) - 1)
      let cHaveLeft : EvalConfig :=
        { state := .have (exitMode .clause left)
            (.start (evalCircuit (witnessAssignment witness) left))
          tape :=
            evalCursorStackEndTape witness afterLeft rightSource
              (encodeEvalFrames (.orLeft :: frames)) padding1 }
      let cNeedRight : EvalConfig :=
        { state := .need .clause needExprCompositeMachine.initial,
          tape :=
            evalCursorStackEndTape witness afterLeft rightSource
              (encodeEvalFrame
                (.orRight
                  (evalCircuit (witnessAssignment witness) left)) ++
                encodeEvalFrames frames)
              padRight }
      have h01 :=
        mem_runBranches_trans checkedEvalRunLoopMachine
          m0 m1 [start] cNeedLeft cHaveLeft
          h0' (by simpa [cHaveLeft, afterLeft, encodeEvalFrames,
            List.append_assoc] using h1')
      have h2' : cNeedRight ∈
          checkedEvalRunLoopMachine.runBranches m2 [cHaveLeft] := by
        simpa [cHaveLeft, cNeedRight, padRight, encodeEvalFrames,
          List.append_assoc] using h2
      have hpre :=
        mem_runBranches_trans checkedEvalRunLoopMachine
          (m0 + m1) m2 [start]
          cHaveLeft cNeedRight h01 h2'
      have hLayoutRight :
          CheckedLayoutBound n afterLeft rightSource
            (encodeEvalFrames
              (.orRight
                (evalCircuit (witnessAssignment witness) left) :: frames)) := by
        have hp :
            CheckedLayoutBound n
              (consumed +
                (true :: false :: true :: encodeCircuit left).length)
              rightSource
              (encodeEvalFrame
                (.orRight
                  (evalCircuit (witnessAssignment witness) left)) ++
                encodeEvalFrames frames) := by
          apply layout_after_prefix_with_frame
            n consumed
            (true :: false :: true :: encodeCircuit left)
            rightSource (encodeEvalFrames frames)
            (.orRight
              (evalCircuit (witnessAssignment witness) left))
          · simp
          · simpa [List.append_assoc] using hLayout
        have hoff :
            consumed +
                (true :: false :: true :: encodeCircuit left).length =
              afterLeft := by
          simp [afterLeft, leftConsumed]
          omega
        rw [← hoff]
        simpa [encodeEvalFrames, List.append_assoc] using hp
      have hrec' := hrec padRight hLayoutRight
      have hprefixBudget :
          m0 + m1 + m2 ≤ rawChunk n := by
        have hc :=
          circuit_plus_two_loops_le_rawChunk n left henc
        omega
      have hrecMid :
          ∃ b ≤ rawFailureBudget fuel n, ∃ fin : EvalConfig,
            fin ∈ checkedEvalRunLoopMachine.runBranches b [cNeedRight] ∧
            EvalFailureSink fin := by
        simpa [RawSinkCertificate, cNeedRight, padRight,
          encodeEvalFrames, List.append_assoc] using hrec'
      exact prefix_chunk_then_recursive fuel n start cNeedRight
        (m0 + m1 + m2) hprefixBudget hpre hrecMid

/-- OR-right structural decoder failure. -/
theorem or_right_failure_step
    (fuel n : Nat)
    (mode : SyntaxMode)
    (witness : BitString)
    (left : CircuitK1.Circuit)
    (rightSource : BitString)
    (frames : List EvalFrame)
    (consumed padding : Nat)
    (hw : witness.length = n)
    (hLayout :
      CheckedLayoutBound n consumed
        (true :: false :: true ::
          (encodeCircuit left ++ rightSource))
        (encodeEvalFrames frames))
    (hrec :
      ∀ (padRight : Nat),
        CheckedLayoutBound n
          (consumed + 3 + (encodeCircuit left).length)
          rightSource
          (encodeEvalFrames
            (.orRight
              (evalCircuit (witnessAssignment witness) left) :: frames)) →
        RawSinkCertificate fuel n .clause witness rightSource
          (.orRight
            (evalCircuit (witnessAssignment witness) left) :: frames)
          (consumed + 3 + (encodeCircuit left).length)
          padRight) :
    RawSinkCertificate (fuel + 1) n mode witness
      (true :: false :: true ::
        (encodeCircuit left ++ rightSource))
      frames consumed padding := by
  cases mode with
  | mustInput =>
      apply chunk_sink_to_succ fuel n .mustInput witness
        (true :: false :: true ::
          (encodeCircuit left ++ rightSource))
        frames consumed padding
      exact disallowed_tag_reaches_sink
        n .mustInput witness (encodeCircuit left ++ rightSource)
        frames consumed padding true false true rfl hLayout
  | cnf =>
      exact or_right_allowed_step fuel n .cnf witness left rightSource
        frames consumed padding hw rfl hLayout hrec
  | clause =>
      exact or_right_allowed_step fuel n .clause witness left rightSource
        frames consumed padding hw rfl hLayout hrec

#print axioms MCore.Real.P01RawRecursiveSteps.not_child_failure_step
#print axioms MCore.Real.P01RawRecursiveSteps.and_left_failure_step
#print axioms MCore.Real.P01RawRecursiveSteps.or_left_failure_step
#print axioms MCore.Real.P01RawRecursiveSteps.and_right_failure_step
#print axioms MCore.Real.P01RawRecursiveSteps.or_right_failure_step

end P01RawRecursiveSteps
end Real
end MCore
