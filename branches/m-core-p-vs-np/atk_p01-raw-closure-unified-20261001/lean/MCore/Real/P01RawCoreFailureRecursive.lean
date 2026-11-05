import MCore.Real.P01RawCoreFailure

namespace MCore
namespace Real
namespace P01RawCoreFailureRecursive

open CanonicalFinalProof
open CircuitK1
open CanonicalCircuitBits
open P01GuessedWitnessRelation
open P01EncodedStackEvaluator
open P01EncodedFrameTape
open P01EvalCursorMachine
open P01NeedExprCompositeNTM
open P01NeedExprTagDecode
open P01CheckedEvalRunLoopNTM
open P01CheckedEvalRunTagPrefix
open P01CheckedEvalRunBoundedHelpers
open P01CheckedEvalRunBoundedCertificate
open P01ExactBoundedCircuitProducer
open P01ExactBoundedReject
open P01CheckedVerifierInvariant
open P01CheckedVerifierGlobalBudget
open P01CNFMode
open P01NTMRunLaws
open P01RawCoreFailure

abbrev CheckedConfig :=
  Configuration CheckedEvalRunState (Option Bool)

def rawAssignment (witness : BitString) : Assignment :=
  fun i => witness.getD i false

@[simp] theorem rawAssignment_apply (witness : BitString) (i : Nat) :
    rawAssignment witness i = witness.getD i false := rfl

theorem checkedCircuitBudget_le_raw_local
    (phi : Circuit) (n : Nat) :
    checkedCircuitBudget phi n ≤
      32 * ((encodeCircuit phi).length + 1) *
        checkedLoopStepEnvelope n := by
  have hs := evalStepCount_le_three_mul_encoding phi
  have hc :
      8 * (evalStepCount phi + 1) ≤
        32 * ((encodeCircuit phi).length + 1) := by
    omega
  unfold checkedCircuitBudget
  exact Nat.mul_le_mul_right (checkedLoopStepEnvelope n) hc

theorem tag_then_raw_budget
    (restLen n : Nat) :
    checkedLoopStepEnvelope n + rawCoreBudget restLen n ≤
      rawCoreBudget (restLen + 3) n := by
  unfold rawCoreBudget
  let E := checkedLoopStepEnvelope n
  have hc :
      1 + 64 * (restLen + 1) ≤
        64 * (restLen + 3 + 1) := by omega
  have hm := Nat.mul_le_mul_right E hc
  dsimp [E] at hm
  convert hm using 1 <;> ring

theorem binary_prefix_then_raw_budget
    (phi : Circuit) (restLen n : Nat) :
    checkedLoopStepEnvelope n +
        checkedCircuitBudget phi n +
        checkedLoopStepEnvelope n +
        rawCoreBudget restLen n ≤
      rawCoreBudget
        (3 + (encodeCircuit phi).length + restLen) n := by
  have hcb := checkedCircuitBudget_le_raw_local phi n
  let E := checkedLoopStepEnvelope n
  have hc :
      1 + 32 * ((encodeCircuit phi).length + 1) +
          1 + 64 * (restLen + 1) ≤
        64 * (3 + (encodeCircuit phi).length + restLen + 1) := by
    omega
  have hm := Nat.mul_le_mul_right E hc
  dsimp [E] at hm
  calc
    checkedLoopStepEnvelope n +
          checkedCircuitBudget phi n +
          checkedLoopStepEnvelope n +
          rawCoreBudget restLen n
        ≤ checkedLoopStepEnvelope n +
            (32 * ((encodeCircuit phi).length + 1) *
              checkedLoopStepEnvelope n) +
            checkedLoopStepEnvelope n +
            rawCoreBudget restLen n := by
              omega
    _ ≤ rawCoreBudget
          (3 + (encodeCircuit phi).length + restLen) n := by
      unfold rawCoreBudget
      convert hm using 1 <;> ring

theorem tag_then_circuit_budget
    (phi : Circuit) (tailLen n : Nat) :
    checkedLoopStepEnvelope n + checkedCircuitBudget phi n ≤
      rawCoreBudget
        (3 + (encodeCircuit phi).length + tailLen) n := by
  have hcb := checkedCircuitBudget_le_raw_local phi n
  let E := checkedLoopStepEnvelope n
  have hc :
      1 + 32 * ((encodeCircuit phi).length + 1) ≤
        64 * (3 + (encodeCircuit phi).length + tailLen + 1) := by
    omega
  have hm := Nat.mul_le_mul_right E hc
  dsimp [E] at hm
  calc
    checkedLoopStepEnvelope n + checkedCircuitBudget phi n
        ≤ checkedLoopStepEnvelope n +
            32 * ((encodeCircuit phi).length + 1) *
              checkedLoopStepEnvelope n := by omega
    _ ≤ rawCoreBudget
          (3 + (encodeCircuit phi).length + tailLen) n := by
      unfold rawCoreBudget
      convert hm using 1 <;> ring

/--
Recursive physical fail-closed theorem mirroring the actual bounded decoder.

The fuel side condition is preserved because every recursive syntax descent
consumes a three-bit tag.  No SAT endpoint fact is assumed.  A successful
decoded child is executed with the already-certified exact bounded producer;
recursion is used only on the suffix whose decoder actually returned none.
-/
theorem decodeCore_none_reaches_raw_failure :
    ∀ (fuel : Nat) (bits : BitString),
      bits.length < 3 * fuel →
      ∀ (n : Nat) (mode : SyntaxMode)
        (witness : BitString) (frames : List EvalFrame)
        (consumed padding : Nat),
        witness.length = n →
        CheckedLayoutBound n consumed bits (encodeEvalFrames frames) →
        decodeCircuitCore fuel bits = none →
        ∃ m ≤ rawCoreBudget bits.length n, ∃ cfg : CheckedConfig,
          cfg ∈ checkedEvalRunLoopMachine.runBranches m
            [{ state := .need mode needExprCompositeMachine.initial,
               tape :=
                 evalCursorStackEndTape witness consumed bits
                   (encodeEvalFrames frames) padding }] ∧
          RawFailEndpoint cfg := by
  intro fuel
  induction fuel with
  | zero =>
      intro bits hfuel
      simp at hfuel
  | succ fuel ih =>
      intro bits hfuel n mode witness frames consumed padding
        hw hLayout hdec
      rcases bits with _ | ⟨b0, rest0⟩
      · exact truncated_tag_reaches_raw_failure
          n mode witness [] frames consumed padding (by simp) hLayout
      · rcases rest0 with _ | ⟨b1, rest1⟩
        · exact truncated_tag_reaches_raw_failure
            n mode witness [b0] frames consumed padding (by simp) hLayout
        · rcases rest1 with _ | ⟨b2, rest⟩
          · exact truncated_tag_reaches_raw_failure
              n mode witness [b0, b1] frames consumed padding (by simp) hLayout
          · cases b0 <;> cases b1 <;> cases b2
            · -- 000 input; decoder failure means unterminated unary index.
              simp only [decodeCircuitCore] at hdec
              cases hnat : decodeNat rest with
              | none =>
                  exact truncated_unary_reaches_raw_failure
                    n mode witness rest frames consumed padding
                    hnat hLayout
              | some p =>
                  simp [hnat] at hdec
            · -- 001 const false always decodes.
              simp [decodeCircuitCore] at hdec
            · -- 010 const true always decodes.
              simp [decodeCircuitCore] at hdec
            · -- 011 negation.
              simp only [decodeCircuitCore] at hdec
              cases hchild : decodeCircuitCore fuel rest with
              | some p =>
                  simp [hchild] at hdec
              | none =>
                  cases hallowed : tagAllowed mode .neg with
                  | false =>
                      exact disallowed_tag_reaches_raw_failure
                        n mode witness rest frames consumed padding
                        false true true hallowed hLayout
                  | true =>
                      have hrestFuel : rest.length < 3 * fuel := by
                        simp at hfuel
                        omega
                      obtain ⟨m0, hm0, h0⟩ :=
                        pushTag_checked_reaches_need_within_envelope
                          n mode witness rest (encodeEvalFrames frames)
                          consumed padding
                          false true true .neg .neg rfl hallowed rfl
                          hLayout.source_le hLayout.frames_le
                      let padChild := ((padding - 1) - 1) - 1
                      have hLayoutChild :
                          CheckedLayoutBound n (consumed + 3) rest
                            (encodeEvalFrame .neg ++ encodeEvalFrames frames) :=
                        after_push_tag n consumed false true true
                          rest (encodeEvalFrames frames) .neg hLayout
                      obtain ⟨m1, hm1, cfg, h1, hend⟩ :=
                        ih rest hrestFuel n (childMode mode .neg)
                          witness (.neg :: frames) (consumed + 3)
                          padChild hw
                          (by simpa [encodeEvalFrames, List.append_assoc]
                            using hLayoutChild)
                          hchild
                      let cNeed : CheckedConfig :=
                        { state := .need (childMode mode .neg)
                            needExprCompositeMachine.initial,
                          tape :=
                            evalCursorStackEndTape witness (consumed + 3)
                              rest
                              (encodeEvalFrame .neg ++
                                encodeEvalFrames frames)
                              padChild }
                      have h0' :
                          cNeed ∈
                            checkedEvalRunLoopMachine.runBranches m0
                              [{ state := .need mode
                                   needExprCompositeMachine.initial,
                                 tape :=
                                   evalCursorStackEndTape witness consumed
                                     (false :: true :: true :: rest)
                                     (encodeEvalFrames frames) padding }] := by
                        simpa [cNeed, padChild, encodeEvalFrames,
                          List.append_assoc] using h0
                      have h1' :
                          cfg ∈ checkedEvalRunLoopMachine.runBranches m1
                            [cNeed] := by
                        simpa [cNeed, encodeEvalFrames,
                          List.append_assoc] using h1
                      have hAll :=
                        mem_runBranches_trans checkedEvalRunLoopMachine
                          m0 m1
                          [{ state := .need mode
                               needExprCompositeMachine.initial,
                             tape :=
                               evalCursorStackEndTape witness consumed
                                 (false :: true :: true :: rest)
                                 (encodeEvalFrames frames) padding }]
                          cNeed cfg h0' h1'
                      refine ⟨m0 + m1, ?_, cfg, hAll, hend⟩
                      have hsum :
                          m0 + m1 ≤
                            checkedLoopStepEnvelope n +
                              rawCoreBudget rest.length n := by omega
                      exact Nat.le_trans hsum
                        (by
                          simpa using tag_then_raw_budget rest.length n)
            · -- 100 conjunction.
              cases hallowed : tagAllowed mode .and with
              | false =>
                  exact disallowed_tag_reaches_raw_failure
                    n mode witness rest frames consumed padding
                    true false false hallowed hLayout
              | true =>
                  have hmode : mode = .cnf := by
                    cases mode <;> simp [tagAllowed] at hallowed ⊢
                  subst mode
                  simp only [decodeCircuitCore] at hdec
                  cases hleftCore : decodeCircuitCore fuel rest with
                  | none =>
                      have hrestFuel : rest.length < 3 * fuel := by
                        simp at hfuel
                        omega
                      obtain ⟨m0, hm0, h0⟩ :=
                        pushTag_checked_reaches_need_within_envelope
                          n .cnf witness rest (encodeEvalFrames frames)
                          consumed padding
                          true false false .and .andLeft rfl rfl
                          (by simp [P01CheckedEvalRunTagPrefix.postTagState,
                            childMode])
                          hLayout.source_le hLayout.frames_le
                      let padLeft := ((padding - 1) - 1) - 1
                      have hLayoutLeft :
                          CheckedLayoutBound n (consumed + 3) rest
                            (encodeEvalFrame .andLeft ++
                              encodeEvalFrames frames) :=
                        after_push_tag n consumed true false false rest
                          (encodeEvalFrames frames) .andLeft hLayout
                      obtain ⟨m1, hm1, cfg, h1, hend⟩ :=
                        ih rest hrestFuel n .cnf witness
                          (.andLeft :: frames) (consumed + 3) padLeft
                          hw
                          (by simpa [encodeEvalFrames, List.append_assoc]
                            using hLayoutLeft)
                          hleftCore
                      let cNeed : CheckedConfig :=
                        { state := .need .cnf needExprCompositeMachine.initial,
                          tape :=
                            evalCursorStackEndTape witness (consumed + 3)
                              rest
                              (encodeEvalFrame .andLeft ++
                                encodeEvalFrames frames)
                              padLeft }
                      have h0' :
                          cNeed ∈
                            checkedEvalRunLoopMachine.runBranches m0
                              [{ state := .need .cnf
                                   needExprCompositeMachine.initial,
                                 tape :=
                                   evalCursorStackEndTape witness consumed
                                     (true :: false :: false :: rest)
                                     (encodeEvalFrames frames) padding }] := by
                        simpa [cNeed, padLeft, encodeEvalFrames,
                          List.append_assoc] using h0
                      have h1' :
                          cfg ∈ checkedEvalRunLoopMachine.runBranches m1
                            [cNeed] := by
                        simpa [cNeed, encodeEvalFrames,
                          List.append_assoc] using h1
                      have hAll :=
                        mem_runBranches_trans checkedEvalRunLoopMachine
                          m0 m1
                          [{ state := .need .cnf
                               needExprCompositeMachine.initial,
                             tape :=
                               evalCursorStackEndTape witness consumed
                                 (true :: false :: false :: rest)
                                 (encodeEvalFrames frames) padding }]
                          cNeed cfg h0' h1'
                      refine ⟨m0 + m1, ?_, cfg, hAll, hend⟩
                      have hsum :
                          m0 + m1 ≤ checkedLoopStepEnvelope n +
                            rawCoreBudget rest.length n := by omega
                      exact Nat.le_trans hsum
                        (by simpa using tag_then_raw_budget rest.length n)
                  | some p =>
                      rcases p with ⟨left, rest'⟩
                      cases hrightCore : decodeCircuitCore fuel rest' with
                      | some q =>
                          simp [hleftCore, hrightCore] at hdec
                      | none =>
                          have hsound :
                              rest = encodeCircuit left ++ rest' :=
                            decodeCircuitCore_sound fuel rest left rest'
                              hleftCore
                          have hrightFuel : rest'.length < 3 * fuel := by
                            simp at hfuel
                            have hrlen :
                                (encodeCircuit left).length + rest'.length =
                                  rest.length := by
                              rw [hsound, List.length_append]
                            omega
                          have hLayout0 :
                              CheckedLayoutBound n consumed
                                (true :: false :: false ::
                                  (encodeCircuit left ++ rest'))
                                (encodeEvalFrames frames) := by
                            simpa [hsound, List.append_assoc] using hLayout
                          obtain ⟨m0, hm0, h0⟩ :=
                            pushTag_checked_reaches_need_within_envelope
                              n .cnf witness
                              (encodeCircuit left ++ rest')
                              (encodeEvalFrames frames)
                              consumed padding true false false
                              .and .andLeft rfl rfl
                              (by simp
                                [P01CheckedEvalRunTagPrefix.postTagState,
                                  childMode])
                              hLayout0.source_le hLayout0.frames_le
                          let padLeft := ((padding - 1) - 1) - 1
                          let leftConsumed := consumed + 3
                          let cNeedLeft : CheckedConfig :=
                            { state := .need .cnf
                                needExprCompositeMachine.initial,
                              tape :=
                                evalCursorStackEndTape witness leftConsumed
                                  (encodeCircuit left ++ rest')
                                  (encodeEvalFrame .andLeft ++
                                    encodeEvalFrames frames)
                                  padLeft }
                          have h0' :
                              cNeedLeft ∈
                                checkedEvalRunLoopMachine.runBranches m0
                                  [{ state := .need .cnf
                                       needExprCompositeMachine.initial,
                                     tape :=
                                       evalCursorStackEndTape witness consumed
                                         (true :: false :: false ::
                                           (encodeCircuit left ++ rest'))
                                         (encodeEvalFrames frames) padding }] := by
                            simpa [cNeedLeft, leftConsumed, padLeft,
                              encodeEvalFrames, List.append_assoc] using h0
                          have hLayoutLeft :
                              CheckedLayoutBound n leftConsumed
                                (encodeCircuit left ++ rest')
                                (encodeEvalFrame .andLeft ++
                                  encodeEvalFrames frames) := by
                            simpa [leftConsumed, List.append_assoc] using
                              (after_push_tag n consumed true false false
                                (encodeCircuit left ++ rest')
                                (encodeEvalFrames frames) .andLeft hLayout0)
                          have hEncLeft :
                              (encodeCircuit left).length ≤ n := by
                            have hs := hLayout0.source_le
                            simp at hs
                            omega
                          have hlenLeft :
                              varBound left ≤ witness.length := by
                            rw [hw]
                            exact Nat.le_trans
                              (varBound_le_encoded_length left) hEncLeft
                          cases hleftMode : modeCheck .cnf left with
                          | false =>
                              have hrej :=
                                circuit_exact_bounded_reject
                                  (rawAssignment witness) witness left .cnf
                              obtain ⟨m1, hm1, cfg, h1, hrejState⟩ :=
                                hrej hleftMode rest' (.andLeft :: frames)
                                  leftConsumed padLeft n
                                  (by simpa [encodeEvalFrames,
                                    List.append_assoc] using hLayoutLeft)
                                  hlenLeft (by intro i hi; rfl)
                              have h1' :
                                  cfg ∈
                                    checkedEvalRunLoopMachine.runBranches m1
                                      [cNeedLeft] := by
                                simpa [cNeedLeft, encodeEvalFrames,
                                  List.append_assoc] using h1
                              have hAll :=
                                mem_runBranches_trans
                                  checkedEvalRunLoopMachine m0 m1
                                  [{ state := .need .cnf
                                       needExprCompositeMachine.initial,
                                     tape :=
                                       evalCursorStackEndTape witness consumed
                                         (true :: false :: false ::
                                           (encodeCircuit left ++ rest'))
                                         (encodeEvalFrames frames) padding }]
                                  cNeedLeft cfg h0' h1'
                              refine ⟨m0 + m1, ?_, cfg, hAll, ?_⟩
                              · have hsum :
                                    m0 + m1 ≤
                                      checkedLoopStepEnvelope n +
                                        checkedCircuitBudget left n := by omega
                                have hb :=
                                  tag_then_circuit_budget left rest'.length n
                                exact Nat.le_trans hsum
                                  (by simpa [hsound] using hb)
                              · exact Or.inl hrejState
                          | true =>
                              have hpos :=
                                circuit_exact_bounded_certificate
                                  (rawAssignment witness) witness left .cnf
                              obtain ⟨m1, hm1, cfgLeft, h1, hout1⟩ :=
                                hpos hleftMode rest' (.andLeft :: frames)
                                  leftConsumed padLeft n
                                  (by simpa [encodeEvalFrames,
                                    List.append_assoc] using hLayoutLeft)
                                  hlenLeft (by intro i hi; rfl)
                              have h1' :
                                  cfgLeft ∈
                                    checkedEvalRunLoopMachine.runBranches m1
                                      [cNeedLeft] := by
                                simpa [cNeedLeft, encodeEvalFrames,
                                  List.append_assoc] using h1
                              have h01 :=
                                mem_runBranches_trans
                                  checkedEvalRunLoopMachine m0 m1
                                  [{ state := .need .cnf
                                       needExprCompositeMachine.initial,
                                     tape :=
                                       evalCursorStackEndTape witness consumed
                                         (true :: false :: false ::
                                           (encodeCircuit left ++ rest'))
                                         (encodeEvalFrames frames) padding }]
                                  cNeedLeft cfgLeft h0' h1'
                              let afterLeft :=
                                leftConsumed + (encodeCircuit left).length
                              obtain ⟨padding1, hcfgLeft⟩ :=
                                exact_outcome_have_of_frames_ne_nil
                                  witness (exitMode .cnf left)
                                  (evalCircuit (rawAssignment witness) left)
                                  rest' (.andLeft :: frames)
                                  afterLeft cfgLeft (by simp)
                                  (by simpa [afterLeft] using hout1)
                              subst cfgLeft
                              obtain ⟨m2, hm2, h2⟩ :=
                                andLeftReturn_checked_reaches_need_within_envelope
                                  n (exitMode .cnf left)
                                  witness rest' (encodeEvalFrames frames)
                                  afterLeft padding1
                                  (evalCircuit (rawAssignment witness) left)
                              let padRight :=
                                (((padding1 + 3) - 1) - 1) - 1
                              let value :=
                                evalCircuit (rawAssignment witness) left
                              let cNeedRight : CheckedConfig :=
                                { state := .need .cnf
                                    needExprCompositeMachine.initial,
                                  tape :=
                                    evalCursorStackEndTape witness afterLeft
                                      rest'
                                      (encodeEvalFrame (.andRight value) ++
                                        encodeEvalFrames frames)
                                      padRight }
                              have h2' :
                                  cNeedRight ∈
                                    checkedEvalRunLoopMachine.runBranches m2
                                      [{ state := .have (exitMode .cnf left)
                                           (.start value),
                                         tape :=
                                           evalCursorStackEndTape witness
                                             afterLeft rest'
                                             (encodeEvalFrames
                                               (.andLeft :: frames))
                                             padding1 }] := by
                                simpa [cNeedRight, value, padRight,
                                  encodeEvalFrames, List.append_assoc] using h2
                              have h012 :=
                                mem_runBranches_trans
                                  checkedEvalRunLoopMachine (m0 + m1) m2
                                  [{ state := .need .cnf
                                       needExprCompositeMachine.initial,
                                     tape :=
                                       evalCursorStackEndTape witness consumed
                                         (true :: false :: false ::
                                           (encodeCircuit left ++ rest'))
                                         (encodeEvalFrames frames) padding }]
                                  ({ state := .have (exitMode .cnf left)
                                       (.start value),
                                     tape :=
                                       evalCursorStackEndTape witness afterLeft
                                         rest'
                                         (encodeEvalFrames
                                           (.andLeft :: frames))
                                         padding1 } : CheckedConfig)
                                  cNeedRight h01 h2'
                              have hLayoutRight :
                                  CheckedLayoutBound n afterLeft rest'
                                    (encodeEvalFrame (.andRight value) ++
                                      encodeEvalFrames frames) := by
                                have hp :=
                                  layout_after_prefix_with_frame
                                    n consumed
                                    (true :: false :: false ::
                                      encodeCircuit left)
                                    rest' (encodeEvalFrames frames)
                                    (.andRight value)
                                    (by simpa [List.append_assoc]
                                      using hLayout0)
                                simpa [afterLeft, leftConsumed, value] using hp
                              obtain ⟨m3, hm3, cfg, h3, hend⟩ :=
                                ih rest' hrightFuel n .cnf witness
                                  (.andRight value :: frames) afterLeft
                                  padRight hw
                                  (by simpa [encodeEvalFrames,
                                    List.append_assoc] using hLayoutRight)
                                  hrightCore
                              have h3' :
                                  cfg ∈
                                    checkedEvalRunLoopMachine.runBranches m3
                                      [cNeedRight] := by
                                simpa [cNeedRight, encodeEvalFrames,
                                  List.append_assoc] using h3
                              have hAll :=
                                mem_runBranches_trans
                                  checkedEvalRunLoopMachine
                                  (m0 + m1 + m2) m3
                                  [{ state := .need .cnf
                                       needExprCompositeMachine.initial,
                                     tape :=
                                       evalCursorStackEndTape witness consumed
                                         (true :: false :: false ::
                                           (encodeCircuit left ++ rest'))
                                         (encodeEvalFrames frames) padding }]
                                  cNeedRight cfg h012 h3'
                              refine ⟨m0 + m1 + m2 + m3, ?_,
                                cfg, hAll, hend⟩
                              have hsum :
                                  m0 + m1 + m2 + m3 ≤
                                    checkedLoopStepEnvelope n +
                                      checkedCircuitBudget left n +
                                      checkedLoopStepEnvelope n +
                                      rawCoreBudget rest'.length n := by
                                omega
                              exact Nat.le_trans hsum
                                (by
                                  simpa [hsound, List.length_append]
                                    using
                                      binary_prefix_then_raw_budget
                                        left rest'.length n)
            · -- 101 disjunction.
              cases hallowed : tagAllowed mode .or with
              | false =>
                  exact disallowed_tag_reaches_raw_failure
                    n mode witness rest frames consumed padding
                    true false true hallowed hLayout
              | true =>
                  simp only [decodeCircuitCore] at hdec
                  cases hleftCore : decodeCircuitCore fuel rest with
                  | none =>
                      have hrestFuel : rest.length < 3 * fuel := by
                        simp at hfuel
                        omega
                      obtain ⟨m0, hm0, h0⟩ :=
                        pushTag_checked_reaches_need_within_envelope
                          n mode witness rest (encodeEvalFrames frames)
                          consumed padding true false true
                          .or .orLeft rfl hallowed
                          (by simp
                            [P01CheckedEvalRunTagPrefix.postTagState,
                              childMode])
                          hLayout.source_le hLayout.frames_le
                      let padLeft := ((padding - 1) - 1) - 1
                      have hLayoutLeft :
                          CheckedLayoutBound n (consumed + 3) rest
                            (encodeEvalFrame .orLeft ++
                              encodeEvalFrames frames) :=
                        after_push_tag n consumed true false true rest
                          (encodeEvalFrames frames) .orLeft hLayout
                      obtain ⟨m1, hm1, cfg, h1, hend⟩ :=
                        ih rest hrestFuel n .clause witness
                          (.orLeft :: frames) (consumed + 3) padLeft hw
                          (by simpa [encodeEvalFrames, List.append_assoc]
                            using hLayoutLeft)
                          hleftCore
                      let cNeed : CheckedConfig :=
                        { state := .need .clause
                            needExprCompositeMachine.initial,
                          tape :=
                            evalCursorStackEndTape witness (consumed + 3)
                              rest
                              (encodeEvalFrame .orLeft ++
                                encodeEvalFrames frames)
                              padLeft }
                      have h0' :
                          cNeed ∈
                            checkedEvalRunLoopMachine.runBranches m0
                              [{ state := .need mode
                                   needExprCompositeMachine.initial,
                                 tape :=
                                   evalCursorStackEndTape witness consumed
                                     (true :: false :: true :: rest)
                                     (encodeEvalFrames frames) padding }] := by
                        simpa [cNeed, padLeft, encodeEvalFrames,
                          List.append_assoc] using h0
                      have h1' :
                          cfg ∈ checkedEvalRunLoopMachine.runBranches m1
                            [cNeed] := by
                        simpa [cNeed, encodeEvalFrames,
                          List.append_assoc] using h1
                      have hAll :=
                        mem_runBranches_trans checkedEvalRunLoopMachine
                          m0 m1
                          [{ state := .need mode
                               needExprCompositeMachine.initial,
                             tape :=
                               evalCursorStackEndTape witness consumed
                                 (true :: false :: true :: rest)
                                 (encodeEvalFrames frames) padding }]
                          cNeed cfg h0' h1'
                      refine ⟨m0 + m1, ?_, cfg, hAll, hend⟩
                      have hsum :
                          m0 + m1 ≤ checkedLoopStepEnvelope n +
                            rawCoreBudget rest.length n := by omega
                      exact Nat.le_trans hsum
                        (by simpa using tag_then_raw_budget rest.length n)
                  | some p =>
                      rcases p with ⟨left, rest'⟩
                      cases hrightCore : decodeCircuitCore fuel rest' with
                      | some q =>
                          simp [hleftCore, hrightCore] at hdec
                      | none =>
                          have hsound :
                              rest = encodeCircuit left ++ rest' :=
                            decodeCircuitCore_sound fuel rest left rest'
                              hleftCore
                          have hrightFuel : rest'.length < 3 * fuel := by
                            simp at hfuel
                            have hrlen :
                                (encodeCircuit left).length + rest'.length =
                                  rest.length := by
                              rw [hsound, List.length_append]
                            omega
                          have hLayout0 :
                              CheckedLayoutBound n consumed
                                (true :: false :: true ::
                                  (encodeCircuit left ++ rest'))
                                (encodeEvalFrames frames) := by
                            simpa [hsound, List.append_assoc] using hLayout
                          obtain ⟨m0, hm0, h0⟩ :=
                            pushTag_checked_reaches_need_within_envelope
                              n mode witness
                              (encodeCircuit left ++ rest')
                              (encodeEvalFrames frames)
                              consumed padding true false true
                              .or .orLeft rfl hallowed
                              (by simp
                                [P01CheckedEvalRunTagPrefix.postTagState,
                                  childMode])
                              hLayout0.source_le hLayout0.frames_le
                          let padLeft := ((padding - 1) - 1) - 1
                          let leftConsumed := consumed + 3
                          let cNeedLeft : CheckedConfig :=
                            { state := .need .clause
                                needExprCompositeMachine.initial,
                              tape :=
                                evalCursorStackEndTape witness leftConsumed
                                  (encodeCircuit left ++ rest')
                                  (encodeEvalFrame .orLeft ++
                                    encodeEvalFrames frames)
                                  padLeft }
                          have h0' :
                              cNeedLeft ∈
                                checkedEvalRunLoopMachine.runBranches m0
                                  [{ state := .need mode
                                       needExprCompositeMachine.initial,
                                     tape :=
                                       evalCursorStackEndTape witness consumed
                                         (true :: false :: true ::
                                           (encodeCircuit left ++ rest'))
                                         (encodeEvalFrames frames) padding }] := by
                            simpa [cNeedLeft, leftConsumed, padLeft,
                              encodeEvalFrames, List.append_assoc] using h0
                          have hLayoutLeft :
                              CheckedLayoutBound n leftConsumed
                                (encodeCircuit left ++ rest')
                                (encodeEvalFrame .orLeft ++
                                  encodeEvalFrames frames) := by
                            simpa [leftConsumed, List.append_assoc] using
                              (after_push_tag n consumed true false true
                                (encodeCircuit left ++ rest')
                                (encodeEvalFrames frames) .orLeft hLayout0)
                          have hEncLeft :
                              (encodeCircuit left).length ≤ n := by
                            have hs := hLayout0.source_le
                            simp at hs
                            omega
                          have hlenLeft :
                              varBound left ≤ witness.length := by
                            rw [hw]
                            exact Nat.le_trans
                              (varBound_le_encoded_length left) hEncLeft
                          cases hleftMode : modeCheck .clause left with
                          | false =>
                              have hrej :=
                                circuit_exact_bounded_reject
                                  (rawAssignment witness) witness left .clause
                              obtain ⟨m1, hm1, cfg, h1, hrejState⟩ :=
                                hrej hleftMode rest' (.orLeft :: frames)
                                  leftConsumed padLeft n
                                  (by simpa [encodeEvalFrames,
                                    List.append_assoc] using hLayoutLeft)
                                  hlenLeft (by intro i hi; rfl)
                              have h1' :
                                  cfg ∈
                                    checkedEvalRunLoopMachine.runBranches m1
                                      [cNeedLeft] := by
                                simpa [cNeedLeft, encodeEvalFrames,
                                  List.append_assoc] using h1
                              have hAll :=
                                mem_runBranches_trans
                                  checkedEvalRunLoopMachine m0 m1
                                  [{ state := .need mode
                                       needExprCompositeMachine.initial,
                                     tape :=
                                       evalCursorStackEndTape witness consumed
                                         (true :: false :: true ::
                                           (encodeCircuit left ++ rest'))
                                         (encodeEvalFrames frames) padding }]
                                  cNeedLeft cfg h0' h1'
                              refine ⟨m0 + m1, ?_, cfg, hAll, ?_⟩
                              · have hsum :
                                    m0 + m1 ≤
                                      checkedLoopStepEnvelope n +
                                        checkedCircuitBudget left n := by omega
                                exact Nat.le_trans hsum
                                  (by
                                    simpa [hsound, List.length_append]
                                      using
                                        tag_then_circuit_budget
                                          left rest'.length n)
                              · exact Or.inl hrejState
                          | true =>
                              have hpos :=
                                circuit_exact_bounded_certificate
                                  (rawAssignment witness) witness left .clause
                              obtain ⟨m1, hm1, cfgLeft, h1, hout1⟩ :=
                                hpos hleftMode rest' (.orLeft :: frames)
                                  leftConsumed padLeft n
                                  (by simpa [encodeEvalFrames,
                                    List.append_assoc] using hLayoutLeft)
                                  hlenLeft (by intro i hi; rfl)
                              have h1' :
                                  cfgLeft ∈
                                    checkedEvalRunLoopMachine.runBranches m1
                                      [cNeedLeft] := by
                                simpa [cNeedLeft, encodeEvalFrames,
                                  List.append_assoc] using h1
                              have h01 :=
                                mem_runBranches_trans
                                  checkedEvalRunLoopMachine m0 m1
                                  [{ state := .need mode
                                       needExprCompositeMachine.initial,
                                     tape :=
                                       evalCursorStackEndTape witness consumed
                                         (true :: false :: true ::
                                           (encodeCircuit left ++ rest'))
                                         (encodeEvalFrames frames) padding }]
                                  cNeedLeft cfgLeft h0' h1'
                              let afterLeft :=
                                leftConsumed + (encodeCircuit left).length
                              obtain ⟨padding1, hcfgLeft⟩ :=
                                exact_outcome_have_of_frames_ne_nil
                                  witness (exitMode .clause left)
                                  (evalCircuit (rawAssignment witness) left)
                                  rest' (.orLeft :: frames)
                                  afterLeft cfgLeft (by simp)
                                  (by simpa [afterLeft] using hout1)
                              subst cfgLeft
                              obtain ⟨m2, hm2, h2⟩ :=
                                orLeftReturn_checked_reaches_need_within_envelope
                                  n (exitMode .clause left)
                                  witness rest' (encodeEvalFrames frames)
                                  afterLeft padding1
                                  (evalCircuit (rawAssignment witness) left)
                              let padRight :=
                                (((padding1 + 3) - 1) - 1) - 1
                              let value :=
                                evalCircuit (rawAssignment witness) left
                              let cNeedRight : CheckedConfig :=
                                { state := .need .clause
                                    needExprCompositeMachine.initial,
                                  tape :=
                                    evalCursorStackEndTape witness afterLeft
                                      rest'
                                      (encodeEvalFrame (.orRight value) ++
                                        encodeEvalFrames frames)
                                      padRight }
                              have h2' :
                                  cNeedRight ∈
                                    checkedEvalRunLoopMachine.runBranches m2
                                      [{ state := .have (exitMode .clause left)
                                           (.start value),
                                         tape :=
                                           evalCursorStackEndTape witness
                                             afterLeft rest'
                                             (encodeEvalFrames
                                               (.orLeft :: frames))
                                             padding1 }] := by
                                simpa [cNeedRight, value, padRight,
                                  encodeEvalFrames, List.append_assoc] using h2
                              have h012 :=
                                mem_runBranches_trans
                                  checkedEvalRunLoopMachine (m0 + m1) m2
                                  [{ state := .need mode
                                       needExprCompositeMachine.initial,
                                     tape :=
                                       evalCursorStackEndTape witness consumed
                                         (true :: false :: true ::
                                           (encodeCircuit left ++ rest'))
                                         (encodeEvalFrames frames) padding }]
                                  ({ state := .have (exitMode .clause left)
                                       (.start value),
                                     tape :=
                                       evalCursorStackEndTape witness afterLeft
                                         rest'
                                         (encodeEvalFrames
                                           (.orLeft :: frames))
                                         padding1 } : CheckedConfig)
                                  cNeedRight h01 h2'
                              have hLayoutRight :
                                  CheckedLayoutBound n afterLeft rest'
                                    (encodeEvalFrame (.orRight value) ++
                                      encodeEvalFrames frames) := by
                                have hp :=
                                  layout_after_prefix_with_frame
                                    n consumed
                                    (true :: false :: true ::
                                      encodeCircuit left)
                                    rest' (encodeEvalFrames frames)
                                    (.orRight value)
                                    (by simpa [List.append_assoc]
                                      using hLayout0)
                                simpa [afterLeft, leftConsumed, value] using hp
                              obtain ⟨m3, hm3, cfg, h3, hend⟩ :=
                                ih rest' hrightFuel n .clause witness
                                  (.orRight value :: frames) afterLeft
                                  padRight hw
                                  (by simpa [encodeEvalFrames,
                                    List.append_assoc] using hLayoutRight)
                                  hrightCore
                              have h3' :
                                  cfg ∈
                                    checkedEvalRunLoopMachine.runBranches m3
                                      [cNeedRight] := by
                                simpa [cNeedRight, encodeEvalFrames,
                                  List.append_assoc] using h3
                              have hAll :=
                                mem_runBranches_trans
                                  checkedEvalRunLoopMachine
                                  (m0 + m1 + m2) m3
                                  [{ state := .need mode
                                       needExprCompositeMachine.initial,
                                     tape :=
                                       evalCursorStackEndTape witness consumed
                                         (true :: false :: true ::
                                           (encodeCircuit left ++ rest'))
                                         (encodeEvalFrames frames) padding }]
                                  cNeedRight cfg h012 h3'
                              refine ⟨m0 + m1 + m2 + m3, ?_,
                                cfg, hAll, hend⟩
                              have hsum :
                                  m0 + m1 + m2 + m3 ≤
                                    checkedLoopStepEnvelope n +
                                      checkedCircuitBudget left n +
                                      checkedLoopStepEnvelope n +
                                      rawCoreBudget rest'.length n := by
                                omega
                              exact Nat.le_trans hsum
                                (by
                                  simpa [hsound, List.length_append]
                                    using
                                      binary_prefix_then_raw_budget
                                        left rest'.length n)
            · -- 110 is not an encoding tag.
              exact disallowed_tag_reaches_raw_failure
                n mode witness rest frames consumed padding
                true true false (by cases mode <;> rfl) hLayout
            · -- 111 is not an encoding tag.
              exact disallowed_tag_reaches_raw_failure
                n mode witness rest frames consumed padding
                true true true (by cases mode <;> rfl) hLayout

#print axioms MCore.Real.P01RawCoreFailureRecursive.decodeCore_none_reaches_raw_failure

end P01RawCoreFailureRecursive
end Real
end MCore
