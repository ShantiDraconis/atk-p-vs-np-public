import MCore.Real.P01RawMalformedRecursiveLeft
import MCore.Real.P01ExactBoundedCircuitProducer
import MCore.Real.P01ExactBoundedReject
import MCore.Real.P01CheckedEvalRunBoundedHelpers
import MCore.Real.P01CheckedVerifierGlobalBudget

namespace MCore
namespace Real
namespace P01RawMalformedRecursiveRight

open CanonicalFinalProof
open CanonicalCircuitBits
open P01CNFMode
open P01NeedExprTagDecode
open P01NeedExprCompositeNTM
open P01EncodedStackEvaluator
open P01EvalCursorMachine
open P01CheckedEvalRunLoopNTM
open P01CheckedEvalRunBoundedHelpers
open P01CheckedVerifierInvariant
open P01CheckedVerifierGlobalBudget
open P01CheckedEvalRunBoundedCertificate
open P01ExactBoundedCircuitProducer
open P01ExactBoundedReject
open P01RawTotalContract
open P01RawMalformedBaseProducer
open P01RawMalformedRecursiveLeft
open P01NTMRunLaws

abbrev EvalConfig :=
  Configuration CheckedEvalRunState (Option Bool)

theorem checkedCircuitBudget_plus_two_loops_le_slice
    (phi : CircuitK1.Circuit)
    (n : Nat)
    (henc : (encodeCircuit phi).length ≤ n) :
    checkedCircuitBudget phi n +
        2 * checkedLoopStepEnvelope n ≤
      rawMalformedSlice n := by
  have hsteps0 :
      evalStepCount phi ≤ 3 * n := by
    exact Nat.le_trans
      (evalStepCount_le_three_mul_encoding phi)
      (Nat.mul_le_mul_left 3 henc)
  have hsteps :
      evalStepCount phi + 1 ≤ 3 * (n + 1) := by
    omega
  have hbudget :
      checkedCircuitBudget phi n ≤
        6144 * (n + 1) ^ 3 := by
    unfold checkedCircuitBudget checkedLoopStepEnvelope
    have hmul :=
      Nat.mul_le_mul_right (256 * (n + 1) ^ 2)
        (Nat.mul_le_mul_left 8 hsteps)
    calc
      8 * (evalStepCount phi + 1) * (256 * (n + 1) ^ 2)
          ≤ (8 * (3 * (n + 1))) * (256 * (n + 1) ^ 2) := hmul
      _ = 6144 * (n + 1) ^ 3 := by ring
  have hloops :
      2 * checkedLoopStepEnvelope n ≤
        512 * (n + 1) ^ 3 := by
    unfold checkedLoopStepEnvelope
    have hp :
        (n + 1) ^ 2 ≤ (n + 1) ^ 3 :=
      Nat.pow_le_pow_right (by omega) (by omega)
    calc
      2 * (256 * (n + 1) ^ 2)
          = 512 * (n + 1) ^ 2 := by ring
      _ ≤ 512 * (n + 1) ^ 3 :=
        Nat.mul_le_mul_left 512 hp
  unfold rawMalformedSlice
  calc
    checkedCircuitBudget phi n + 2 * checkedLoopStepEnvelope n
        ≤ 6144 * (n + 1) ^ 3 + 512 * (n + 1) ^ 3 :=
          Nat.add_le_add hbudget hloops
    _ ≤ 8192 * (n + 1) ^ 3 := by
      exact Nat.mul_le_mul_right ((n + 1) ^ 3) (by omega)

theorem checkedCircuitBudget_plus_one_loop_le_slice
    (phi : CircuitK1.Circuit)
    (n : Nat)
    (henc : (encodeCircuit phi).length ≤ n) :
    checkedCircuitBudget phi n +
        checkedLoopStepEnvelope n ≤
      rawMalformedSlice n := by
  have htwo :=
    checkedCircuitBudget_plus_two_loops_le_slice phi n henc
  omega

theorem local_slice_plus_child_budget
    (fuel n : Nat) :
    rawMalformedSlice n + rawMalformedBudget fuel n =
      rawMalformedBudget (fuel + 1) n :=
  slice_add_child_budget fuel n

/-- AND whose left raw subtree decodes successfully but whose right subtree is
malformed.  If the decoded left circuit violates CNF mode, the exact negative
producer rejects immediately.  Otherwise the exact positive producer evaluates
the left child, performs the certified and-left handoff, then recursion handles
the malformed right child. -/
theorem and_right_failure
    (fuel n consumed padding : Nat)
    (witness rest rest' : BitString)
    (frames : List EvalFrame)
    (mode : SyntaxMode)
    (left : CircuitK1.Circuit)
    (hRec : RawMalformedAtFuel fuel)
    (hFuel :
      (true :: false :: false :: rest).length < fuel + 1)
    (hLeft :
      decodeCircuitCore fuel rest = some (left, rest'))
    (hRight :
      decodeCircuitCore fuel rest' = none)
    (hLayout :
      CheckedLayoutBound n consumed
        (true :: false :: false :: rest)
        (encodeEvalFrames frames))
    (hWitness :
      (true :: false :: false :: rest).length ≤ witness.length) :
    ∃ m ≤ rawMalformedBudget (fuel + 1) n, ∃ cfg : EvalConfig,
      cfg ∈ checkedEvalRunLoopMachine.runBranches m
        [{ state := .need mode needExprCompositeMachine.initial,
           tape :=
             evalCursorStackEndTape witness consumed
               (true :: false :: false :: rest)
               (encodeEvalFrames frames) padding }] ∧
      EvalFailClosed cfg := by
  cases mode with
  | clause =>
      exact disallowed_root_fail_closed
        witness rest frames .clause consumed padding n fuel
        true false false (by rfl) hLayout
  | mustInput =>
      exact disallowed_root_fail_closed
        witness rest frames .mustInput consumed padding n fuel
        true false false (by rfl) hLayout
  | cnf =>
      have hRest : rest = encodeCircuit left ++ rest' :=
        decodeCore_success_prefix hLeft
      have hRestWitness : rest.length ≤ witness.length := by
        simp at hWitness
        omega
      have hLeftLen :
          varBound left ≤ witness.length :=
        decoded_varBound_le_witness hLeft hRestWitness
      have hRead :
          ∀ i, i < varBound left →
            witness.getD i false = witnessAssignment witness i :=
        witnessAssignment_agrees witness left hLeftLen

      have hLayoutAfterTag :
          CheckedLayoutBound n (consumed + 3) rest
            (encodeEvalFrame .andLeft ++ encodeEvalFrames frames) :=
        after_push_tag n consumed true false false rest
          (encodeEvalFrames frames) .andLeft hLayout

      have hLayoutLeft :
          CheckedLayoutBound n (consumed + 3)
            (encodeCircuit left ++ rest')
            (encodeEvalFrames (.andLeft :: frames)) := by
        rw [hRest] at hLayoutAfterTag
        simpa [encodeEvalFrames, List.append_assoc] using hLayoutAfterTag

      obtain ⟨m0, hm0, h0⟩ :=
        pushTag_checked_reaches_need_within_envelope
          n .cnf witness rest (encodeEvalFrames frames)
          consumed padding true false false .and .andLeft
          rfl rfl (by simp [P01CheckedEvalRunTagPrefix.postTagState, childMode])
          hLayout.source_le hLayout.frames_le

      let padLeft := ((padding - 1) - 1) - 1
      let leftConsumed := consumed + 3
      let cNeedLeft : EvalConfig :=
        { state := .need .cnf needExprCompositeMachine.initial,
          tape :=
            evalCursorStackEndTape witness leftConsumed
              (encodeCircuit left ++ rest')
              (encodeEvalFrames (.andLeft :: frames)) padLeft }

      have h0' :
          cNeedLeft ∈ checkedEvalRunLoopMachine.runBranches m0
            [{ state := .need .cnf needExprCompositeMachine.initial,
               tape :=
                 evalCursorStackEndTape witness consumed
                   (true :: false :: false :: rest)
                   (encodeEvalFrames frames) padding }] := by
        simpa [cNeedLeft, leftConsumed, padLeft, hRest,
          encodeEvalFrames, List.append_assoc] using h0

      have hencLeft : (encodeCircuit left).length ≤ n := by
        have hs := hLayoutLeft.source_le
        simp at hs
        omega

      cases hLeftMode : modeCheck .cnf left with
      | false =>
          have hNeg :=
            circuit_exact_bounded_reject
              (witnessAssignment witness) witness left .cnf
          obtain ⟨m1, hm1, cfg, h1, hrej⟩ :=
            hNeg hLeftMode rest' (.andLeft :: frames)
              leftConsumed padLeft n hLayoutLeft hLeftLen hRead
          have h1' :
              cfg ∈ checkedEvalRunLoopMachine.runBranches m1 [cNeedLeft] := by
            simpa [cNeedLeft] using h1
          have hAll :=
            mem_runBranches_trans checkedEvalRunLoopMachine
              m0 m1
              [{ state := .need .cnf needExprCompositeMachine.initial,
                 tape :=
                   evalCursorStackEndTape witness consumed
                     (true :: false :: false :: rest)
                     (encodeEvalFrames frames) padding }]
              cNeedLeft cfg h0' h1'
          have hlocal :
              m0 + m1 ≤ rawMalformedSlice n := by
            have hcap :=
              checkedCircuitBudget_plus_one_loop_le_slice left n hencLeft
            omega
          exact ⟨m0 + m1,
            Nat.le_trans hlocal
              (slice_le_rawMalformedBudget (fuel + 1) n),
            cfg, hAll, Or.inl hrej⟩

      | true =>
          have hPos :=
            circuit_exact_bounded_certificate
              (witnessAssignment witness) witness left .cnf
          obtain ⟨m1, hm1, cfgLeft, h1, hout1⟩ :=
            hPos hLeftMode rest' (.andLeft :: frames)
              leftConsumed padLeft n hLayoutLeft hLeftLen hRead
          have h1' :
              cfgLeft ∈ checkedEvalRunLoopMachine.runBranches m1 [cNeedLeft] := by
            simpa [cNeedLeft] using h1
          have h01 :=
            mem_runBranches_trans checkedEvalRunLoopMachine
              m0 m1
              [{ state := .need .cnf needExprCompositeMachine.initial,
                 tape :=
                   evalCursorStackEndTape witness consumed
                     (true :: false :: false :: rest)
                     (encodeEvalFrames frames) padding }]
              cNeedLeft cfgLeft h0' h1'

          let afterLeft := leftConsumed + (encodeCircuit left).length
          obtain ⟨padding1, hcfgLeft⟩ :=
            exact_outcome_have_of_frames_ne_nil
              witness (exitMode .cnf left)
              (evalCircuit (witnessAssignment witness) left)
              rest' (.andLeft :: frames) afterLeft cfgLeft
              (by simp)
              (by simpa [afterLeft] using hout1)
          subst cfgLeft

          obtain ⟨m2, hm2, h2⟩ :=
            andLeftReturn_checked_reaches_need_within_envelope
              n (exitMode .cnf left) witness rest'
              (encodeEvalFrames frames)
              afterLeft padding1
              (evalCircuit (witnessAssignment witness) left)

          let value := evalCircuit (witnessAssignment witness) left
          let padRight := (((padding1 + 3) - 1) - 1) - 1
          let cNeedRight : EvalConfig :=
            { state := .need .cnf needExprCompositeMachine.initial,
              tape :=
                evalCursorStackEndTape witness afterLeft rest'
                  (encodeEvalFrames (.andRight value :: frames)) padRight }

          have h2' :
              cNeedRight ∈ checkedEvalRunLoopMachine.runBranches m2
                [{ state := .have (exitMode .cnf left)
                     (.start (evalCircuit (witnessAssignment witness) left)),
                   tape :=
                     evalCursorStackEndTape witness afterLeft rest'
                       (encodeEvalFrames (.andLeft :: frames)) padding1 }] := by
            simpa [cNeedRight, value, padRight, encodeEvalFrames,
              List.append_assoc] using h2

          have h012 :=
            mem_runBranches_trans checkedEvalRunLoopMachine
              (m0 + m1) m2
              [{ state := .need .cnf needExprCompositeMachine.initial,
                 tape :=
                   evalCursorStackEndTape witness consumed
                     (true :: false :: false :: rest)
                     (encodeEvalFrames frames) padding }]
              ({ state := .have (exitMode .cnf left)
                   (.start (evalCircuit (witnessAssignment witness) left)),
                 tape :=
                   evalCursorStackEndTape witness afterLeft rest'
                     (encodeEvalFrames (.andLeft :: frames)) padding1 } :
                EvalConfig)
              cNeedRight h01 h2'

          have hAfterLeft :
              CheckedLayoutBound n afterLeft rest'
                (encodeEvalFrames (.andLeft :: frames)) := by
            have hp :=
              layout_consume_prefix n leftConsumed
                (encodeCircuit left) rest'
                (encodeEvalFrames (.andLeft :: frames)) hLayoutLeft
            simpa [afterLeft] using hp

          have hRightLayout :
              CheckedLayoutBound n afterLeft rest'
                (encodeEvalFrames (.andRight value :: frames)) := by
            have hp :=
              replace_top_frame n afterLeft rest'
                (encodeEvalFrames frames)
                .andLeft (.andRight value)
                (by simpa [encodeEvalFrames, List.append_assoc] using hAfterLeft)
            simpa [encodeEvalFrames, List.append_assoc] using hp

          have hRightFuel : rest'.length < fuel := by
            rw [hRest] at hFuel
            simp at hFuel
            omega
          have hRightWitness : rest'.length ≤ witness.length := by
            rw [hRest] at hRestWitness
            simp at hRestWitness
            omega

          obtain ⟨m3, hm3, cfg, h3, hfc⟩ :=
            hRec witness rest' (.andRight value :: frames) .cnf
              afterLeft padRight n
              hRightFuel hRight hRightLayout hRightWitness

          have h3' :
              cfg ∈ checkedEvalRunLoopMachine.runBranches m3 [cNeedRight] := by
            simpa [cNeedRight] using h3

          have hAll :=
            mem_runBranches_trans checkedEvalRunLoopMachine
              (m0 + m1 + m2) m3
              [{ state := .need .cnf needExprCompositeMachine.initial,
                 tape :=
                   evalCursorStackEndTape witness consumed
                     (true :: false :: false :: rest)
                     (encodeEvalFrames frames) padding }]
              cNeedRight cfg h012 h3'

          have hlocal :
              m0 + m1 + m2 ≤ rawMalformedSlice n := by
            have hcap :=
              checkedCircuitBudget_plus_two_loops_le_slice left n hencLeft
            omega
          have hbudget :
              m0 + m1 + m2 + m3 ≤
                rawMalformedBudget (fuel + 1) n := by
            calc
              m0 + m1 + m2 + m3
                  ≤ rawMalformedSlice n + rawMalformedBudget fuel n :=
                    Nat.add_le_add hlocal hm3
              _ = rawMalformedBudget (fuel + 1) n :=
                    local_slice_plus_child_budget fuel n
          exact ⟨m0 + m1 + m2 + m3, hbudget, cfg, hAll, hfc⟩

/-- OR analogue of and_right_failure. -/
theorem or_right_failure
    (fuel n consumed padding : Nat)
    (witness rest rest' : BitString)
    (frames : List EvalFrame)
    (mode : SyntaxMode)
    (left : CircuitK1.Circuit)
    (hRec : RawMalformedAtFuel fuel)
    (hFuel :
      (true :: false :: true :: rest).length < fuel + 1)
    (hLeft :
      decodeCircuitCore fuel rest = some (left, rest'))
    (hRight :
      decodeCircuitCore fuel rest' = none)
    (hLayout :
      CheckedLayoutBound n consumed
        (true :: false :: true :: rest)
        (encodeEvalFrames frames))
    (hWitness :
      (true :: false :: true :: rest).length ≤ witness.length) :
    ∃ m ≤ rawMalformedBudget (fuel + 1) n, ∃ cfg : EvalConfig,
      cfg ∈ checkedEvalRunLoopMachine.runBranches m
        [{ state := .need mode needExprCompositeMachine.initial,
           tape :=
             evalCursorStackEndTape witness consumed
               (true :: false :: true :: rest)
               (encodeEvalFrames frames) padding }] ∧
      EvalFailClosed cfg := by
  cases hAllowed : tagAllowed mode .or with
  | false =>
      exact disallowed_root_fail_closed
        witness rest frames mode consumed padding n fuel
        true false true (by simpa using hAllowed) hLayout
  | true =>
      have hRest : rest = encodeCircuit left ++ rest' :=
        decodeCore_success_prefix hLeft
      have hRestWitness : rest.length ≤ witness.length := by
        simp at hWitness
        omega
      have hLeftLen :
          varBound left ≤ witness.length :=
        decoded_varBound_le_witness hLeft hRestWitness
      have hRead :
          ∀ i, i < varBound left →
            witness.getD i false = witnessAssignment witness i :=
        witnessAssignment_agrees witness left hLeftLen

      have hLayoutAfterTag :
          CheckedLayoutBound n (consumed + 3) rest
            (encodeEvalFrame .orLeft ++ encodeEvalFrames frames) :=
        after_push_tag n consumed true false true rest
          (encodeEvalFrames frames) .orLeft hLayout
      have hLayoutLeft :
          CheckedLayoutBound n (consumed + 3)
            (encodeCircuit left ++ rest')
            (encodeEvalFrames (.orLeft :: frames)) := by
        rw [hRest] at hLayoutAfterTag
        simpa [encodeEvalFrames, List.append_assoc] using hLayoutAfterTag

      obtain ⟨m0, hm0, h0⟩ :=
        pushTag_checked_reaches_need_within_envelope
          n mode witness rest (encodeEvalFrames frames)
          consumed padding true false true .or .orLeft
          rfl hAllowed (by simp [P01CheckedEvalRunTagPrefix.postTagState, childMode])
          hLayout.source_le hLayout.frames_le

      let padLeft := ((padding - 1) - 1) - 1
      let leftConsumed := consumed + 3
      let cNeedLeft : EvalConfig :=
        { state := .need .clause needExprCompositeMachine.initial,
          tape :=
            evalCursorStackEndTape witness leftConsumed
              (encodeCircuit left ++ rest')
              (encodeEvalFrames (.orLeft :: frames)) padLeft }

      have h0' :
          cNeedLeft ∈ checkedEvalRunLoopMachine.runBranches m0
            [{ state := .need mode needExprCompositeMachine.initial,
               tape :=
                 evalCursorStackEndTape witness consumed
                   (true :: false :: true :: rest)
                   (encodeEvalFrames frames) padding }] := by
        simpa [cNeedLeft, leftConsumed, padLeft, hRest,
          encodeEvalFrames, List.append_assoc] using h0

      have hencLeft : (encodeCircuit left).length ≤ n := by
        have hs := hLayoutLeft.source_le
        simp at hs
        omega

      cases hLeftMode : modeCheck .clause left with
      | false =>
          have hNeg :=
            circuit_exact_bounded_reject
              (witnessAssignment witness) witness left .clause
          obtain ⟨m1, hm1, cfg, h1, hrej⟩ :=
            hNeg hLeftMode rest' (.orLeft :: frames)
              leftConsumed padLeft n hLayoutLeft hLeftLen hRead
          have h1' :
              cfg ∈ checkedEvalRunLoopMachine.runBranches m1 [cNeedLeft] := by
            simpa [cNeedLeft] using h1
          have hAll :=
            mem_runBranches_trans checkedEvalRunLoopMachine
              m0 m1
              [{ state := .need mode needExprCompositeMachine.initial,
                 tape :=
                   evalCursorStackEndTape witness consumed
                     (true :: false :: true :: rest)
                     (encodeEvalFrames frames) padding }]
              cNeedLeft cfg h0' h1'
          have hlocal :
              m0 + m1 ≤ rawMalformedSlice n := by
            have hcap :=
              checkedCircuitBudget_plus_one_loop_le_slice left n hencLeft
            omega
          exact ⟨m0 + m1,
            Nat.le_trans hlocal
              (slice_le_rawMalformedBudget (fuel + 1) n),
            cfg, hAll, Or.inl hrej⟩
      | true =>
          have hPos :=
            circuit_exact_bounded_certificate
              (witnessAssignment witness) witness left .clause
          obtain ⟨m1, hm1, cfgLeft, h1, hout1⟩ :=
            hPos hLeftMode rest' (.orLeft :: frames)
              leftConsumed padLeft n hLayoutLeft hLeftLen hRead
          have h1' :
              cfgLeft ∈ checkedEvalRunLoopMachine.runBranches m1 [cNeedLeft] := by
            simpa [cNeedLeft] using h1
          have h01 :=
            mem_runBranches_trans checkedEvalRunLoopMachine
              m0 m1
              [{ state := .need mode needExprCompositeMachine.initial,
                 tape :=
                   evalCursorStackEndTape witness consumed
                     (true :: false :: true :: rest)
                     (encodeEvalFrames frames) padding }]
              cNeedLeft cfgLeft h0' h1'

          let afterLeft := leftConsumed + (encodeCircuit left).length
          obtain ⟨padding1, hcfgLeft⟩ :=
            exact_outcome_have_of_frames_ne_nil
              witness (exitMode .clause left)
              (evalCircuit (witnessAssignment witness) left)
              rest' (.orLeft :: frames) afterLeft cfgLeft
              (by simp)
              (by simpa [afterLeft] using hout1)
          subst cfgLeft

          obtain ⟨m2, hm2, h2⟩ :=
            orLeftReturn_checked_reaches_need_within_envelope
              n (exitMode .clause left) witness rest'
              (encodeEvalFrames frames)
              afterLeft padding1
              (evalCircuit (witnessAssignment witness) left)

          let value := evalCircuit (witnessAssignment witness) left
          let padRight := (((padding1 + 3) - 1) - 1) - 1
          let cNeedRight : EvalConfig :=
            { state := .need .clause needExprCompositeMachine.initial,
              tape :=
                evalCursorStackEndTape witness afterLeft rest'
                  (encodeEvalFrames (.orRight value :: frames)) padRight }

          have h2' :
              cNeedRight ∈ checkedEvalRunLoopMachine.runBranches m2
                [{ state := .have (exitMode .clause left)
                     (.start (evalCircuit (witnessAssignment witness) left)),
                   tape :=
                     evalCursorStackEndTape witness afterLeft rest'
                       (encodeEvalFrames (.orLeft :: frames)) padding1 }] := by
            simpa [cNeedRight, value, padRight, encodeEvalFrames,
              List.append_assoc] using h2

          have h012 :=
            mem_runBranches_trans checkedEvalRunLoopMachine
              (m0 + m1) m2
              [{ state := .need mode needExprCompositeMachine.initial,
                 tape :=
                   evalCursorStackEndTape witness consumed
                     (true :: false :: true :: rest)
                     (encodeEvalFrames frames) padding }]
              ({ state := .have (exitMode .clause left)
                   (.start (evalCircuit (witnessAssignment witness) left)),
                 tape :=
                   evalCursorStackEndTape witness afterLeft rest'
                     (encodeEvalFrames (.orLeft :: frames)) padding1 } :
                EvalConfig)
              cNeedRight h01 h2'

          have hAfterLeft :
              CheckedLayoutBound n afterLeft rest'
                (encodeEvalFrames (.orLeft :: frames)) := by
            have hp :=
              layout_consume_prefix n leftConsumed
                (encodeCircuit left) rest'
                (encodeEvalFrames (.orLeft :: frames)) hLayoutLeft
            simpa [afterLeft] using hp
          have hRightLayout :
              CheckedLayoutBound n afterLeft rest'
                (encodeEvalFrames (.orRight value :: frames)) := by
            have hp :=
              replace_top_frame n afterLeft rest'
                (encodeEvalFrames frames)
                .orLeft (.orRight value)
                (by simpa [encodeEvalFrames, List.append_assoc] using hAfterLeft)
            simpa [encodeEvalFrames, List.append_assoc] using hp

          have hRightFuel : rest'.length < fuel := by
            rw [hRest] at hFuel
            simp at hFuel
            omega
          have hRightWitness : rest'.length ≤ witness.length := by
            rw [hRest] at hRestWitness
            simp at hRestWitness
            omega

          obtain ⟨m3, hm3, cfg, h3, hfc⟩ :=
            hRec witness rest' (.orRight value :: frames) .clause
              afterLeft padRight n
              hRightFuel hRight hRightLayout hRightWitness
          have h3' :
              cfg ∈ checkedEvalRunLoopMachine.runBranches m3 [cNeedRight] := by
            simpa [cNeedRight] using h3
          have hAll :=
            mem_runBranches_trans checkedEvalRunLoopMachine
              (m0 + m1 + m2) m3
              [{ state := .need mode needExprCompositeMachine.initial,
                 tape :=
                   evalCursorStackEndTape witness consumed
                     (true :: false :: true :: rest)
                     (encodeEvalFrames frames) padding }]
              cNeedRight cfg h012 h3'

          have hlocal :
              m0 + m1 + m2 ≤ rawMalformedSlice n := by
            have hcap :=
              checkedCircuitBudget_plus_two_loops_le_slice left n hencLeft
            omega
          have hbudget :
              m0 + m1 + m2 + m3 ≤
                rawMalformedBudget (fuel + 1) n := by
            calc
              m0 + m1 + m2 + m3
                  ≤ rawMalformedSlice n + rawMalformedBudget fuel n :=
                    Nat.add_le_add hlocal hm3
              _ = rawMalformedBudget (fuel + 1) n :=
                    local_slice_plus_child_budget fuel n
          exact ⟨m0 + m1 + m2 + m3, hbudget, cfg, hAll, hfc⟩

#print axioms MCore.Real.P01RawMalformedRecursiveRight.and_right_failure
#print axioms MCore.Real.P01RawMalformedRecursiveRight.or_right_failure

end P01RawMalformedRecursiveRight
end Real
end MCore
