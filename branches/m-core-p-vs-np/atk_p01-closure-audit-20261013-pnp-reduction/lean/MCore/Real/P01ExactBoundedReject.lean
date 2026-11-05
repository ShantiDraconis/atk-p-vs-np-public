import MCore.Real.P01ExactBoundedCircuitProducer
import MCore.Real.P01CheckedEvalReject

namespace MCore
namespace Real
namespace P01ExactBoundedReject

open CanonicalFinalProof
open CanonicalCircuitBits
open CanonicalSATWitness
open P01EncodedStackEvaluator
open P01EncodedFrameTape
open P01EvalCursorMachine
open P01NeedExprCompositeNTM
open P01CheckedEvalRunLoopNTM
open P01CheckedEvalRunBaseCases
open P01CheckedEvalRunBoundedHelpers
open P01CheckedEvalRunBoundedCertificate
open P01CheckedEvalReject
open P01CheckedVerifierInvariant
open P01CheckedVerifierBudget
open P01CheckedVerifierGlobalBudget
open P01ExactBoundedCircuitProducer
open P01CNFMode
open P01NTMRunLaws

abbrev CheckedConfig :=
  Configuration CheckedEvalRunState (Option Bool)

/-- Bounded negative counterpart of the exact positive circuit certificate. -/
def ExactBoundedCheckedCircuitRejectCertificate
    (sigma : Assignment)
    (witness : BitString)
    (mode : SyntaxMode)
    (phi : CircuitK1.Circuit) : Prop :=
  modeCheck mode phi = false →
  ∀ (tail : BitString) (frames : List EvalFrame)
      (consumed padding n : Nat),
    CheckedLayoutBound n consumed
      (encodeCircuit phi ++ tail) (encodeEvalFrames frames) →
    varBound phi ≤ witness.length →
    (∀ i, i < varBound phi →
      witness.getD i false = sigma i) →
    ∃ m ≤ checkedCircuitBudget phi n, ∃ cfg,
      cfg ∈
        checkedEvalRunLoopMachine.runBranches m
          [{ state := .need mode needExprCompositeMachine.initial,
             tape :=
               evalCursorStackEndTape witness consumed
                 (encodeCircuit phi ++ tail)
                 (encodeEvalFrames frames) padding }] ∧
      cfg.state = .reject

/-- A syntactically forbidden physical tag rejects within one common loop
envelope. -/
theorem root_tag_reject_within_envelope
    (n : Nat)
    (mode : SyntaxMode)
    (witness rest frameStack : BitString)
    (consumed padding : Nat)
    (b0 b1 b2 : Bool)
    (hdisallowed :
      tagAllowed mode
        (P01NeedExprTagDecode.decodeTagBits b0 b1 b2) = false)
    (hsource : (b0 :: b1 :: b2 :: rest).length ≤ n)
    (hframes : frameStack.length ≤ n) :
    ∃ m ≤ checkedLoopStepEnvelope n, ∃ tape,
      ({ state := .reject, tape := tape } : CheckedConfig) ∈
        checkedEvalRunLoopMachine.runBranches m
          [{ state := .need mode needExprCompositeMachine.initial,
             tape :=
               evalCursorStackEndTape witness consumed
                 (b0 :: b1 :: b2 :: rest)
                 frameStack padding }] := by
  obtain ⟨m, hm, hrun⟩ :=
    P01CheckedEvalRunTagPrefix.disallowed_tag_prefix_reaches_reject
      mode witness rest frameStack consumed padding
      b0 b1 b2 hdisallowed
  have hfuel :
      P01CheckedEvalRunTagPrefix.checkedTagPrefixFuel
          (b0 :: b1 :: b2 :: rest) frameStack ≤
        checkedStepEnvelope n :=
    checkedTagPrefixFuel_le_envelope
      n (b0 :: b1 :: b2 :: rest) frameStack hsource hframes
  refine ⟨m, Nat.le_trans hm
      (Nat.le_trans hfuel (checkedStepEnvelope_le_loopEnvelope n)),
    evalCursorReadTape witness (consumed + 3) rest frameStack padding,
    ?_⟩
  simpa using hrun

/-- Input nodes are valid in every syntax mode, so their negative certificate
is vacuous. -/
theorem input_exact_bounded_reject
    (sigma : Assignment)
    (witness : BitString)
    (mode : SyntaxMode)
    (i : Nat) :
    ExactBoundedCheckedCircuitRejectCertificate
      sigma witness mode (.input i) := by
  intro hinvalid
  cases mode <;>
    simp [modeCheck, tagAllowed, isCNFBool, isClauseBool] at hinvalid

/-- Invalid constants reject at their root tag under the exact circuit budget. -/
theorem const_exact_bounded_reject
    (sigma : Assignment)
    (witness : BitString)
    (mode : SyntaxMode)
    (v : Bool) :
    ExactBoundedCheckedCircuitRejectCertificate
      sigma witness mode (.const v) := by
  intro hinvalid tail frames consumed padding n hLayout hlen hread
  have hroot :
      tagAllowed mode (circuitTag (.const v)) = false := by
    cases v <;> cases mode <;>
      simp [modeCheck, tagAllowed, circuitTag,
        isCNFBool, isClauseBool] at hinvalid ⊢
  cases v with
  | false =>
      obtain ⟨m, hm, tape, hrun⟩ :=
        root_tag_reject_within_envelope
          n mode witness tail (encodeEvalFrames frames)
          consumed padding false false true
          (by simpa [circuitTag] using hroot)
          (by simpa [encodeCircuit] using hLayout.source_le)
          hLayout.frames_le
      refine ⟨m,
        Nat.le_trans hm
          (loopEnvelope_le_checkedCircuitBudget (.const false) n),
        { state := .reject, tape := tape }, ?_, rfl⟩
      simpa [encodeCircuit] using hrun
  | true =>
      obtain ⟨m, hm, tape, hrun⟩ :=
        root_tag_reject_within_envelope
          n mode witness tail (encodeEvalFrames frames)
          consumed padding false true false
          (by simpa [circuitTag] using hroot)
          (by simpa [encodeCircuit] using hLayout.source_le)
          hLayout.frames_le
      refine ⟨m,
        Nat.le_trans hm
          (loopEnvelope_le_checkedCircuitBudget (.const true) n),
        { state := .reject, tape := tape }, ?_, rfl⟩
      simpa [encodeCircuit] using hrun

/-- Bounded negative producer for negation.  If the root negation tag is
forbidden, rejection is immediate.  Otherwise the child is entered in
must-input mode and its bounded negative certificate is composed. -/
theorem neg_exact_bounded_reject
    (sigma : Assignment)
    (witness : BitString)
    (mode : SyntaxMode)
    (child : CircuitK1.Circuit)
    (hchild :
      ExactBoundedCheckedCircuitRejectCertificate
        sigma witness (childMode mode .neg) child) :
    ExactBoundedCheckedCircuitRejectCertificate
      sigma witness mode (.not child) := by
  intro hinvalid tail frames consumed padding n hLayout hlen hread
  cases hroot : tagAllowed mode .neg with
  | false =>
      have hLayout0 :
          CheckedLayoutBound n consumed
            (false :: true :: true :: (encodeCircuit child ++ tail))
            (encodeEvalFrames frames) := by
        simpa [encodeCircuit, List.append_assoc] using hLayout
      obtain ⟨m, hm, tape, hrun⟩ :=
        root_tag_reject_within_envelope
          n mode witness (encodeCircuit child ++ tail)
          (encodeEvalFrames frames) consumed padding
          false true true
          (by simpa using hroot)
          hLayout0.source_le hLayout0.frames_le
      refine ⟨m,
        Nat.le_trans hm
          (loopEnvelope_le_checkedCircuitBudget (.not child) n),
        { state := .reject, tape := tape }, ?_, rfl⟩
      simpa [encodeCircuit, List.append_assoc] using hrun
  | true =>
      have hchildInvalid :
          modeCheck (childMode mode .neg) child = false := by
        rw [modeCheck_not] at hinvalid
        simpa [hroot] using hinvalid

      have hlenChild : varBound child ≤ witness.length := by
        simpa [varBound] using hlen
      have hreadChild :
          ∀ i, i < varBound child →
            witness.getD i false = sigma i := by
        intro i hi
        exact hread i (by simpa [varBound] using hi)

      have hLayout0 :
          CheckedLayoutBound n consumed
            (false :: true :: true :: (encodeCircuit child ++ tail))
            (encodeEvalFrames frames) := by
        simpa [encodeCircuit, List.append_assoc] using hLayout

      have hLayoutChild :
          CheckedLayoutBound n (consumed + 3)
            (encodeCircuit child ++ tail)
            (encodeEvalFrame .neg ++ encodeEvalFrames frames) :=
        after_push_tag n consumed false true true
          (encodeCircuit child ++ tail) (encodeEvalFrames frames) .neg hLayout0

      obtain ⟨m0, hm0, h0⟩ :=
        pushTag_checked_reaches_need_within_envelope
          n mode witness (encodeCircuit child ++ tail)
          (encodeEvalFrames frames) consumed padding
          false true true .neg .neg rfl hroot rfl
          hLayout0.source_le hLayout0.frames_le

      let padChild := ((padding - 1) - 1) - 1
      let cNeed : CheckedConfig :=
        { state := .need (childMode mode .neg)
            needExprCompositeMachine.initial,
          tape :=
            evalCursorStackEndTape witness (consumed + 3)
              (encodeCircuit child ++ tail)
              (encodeEvalFrame .neg ++ encodeEvalFrames frames)
              padChild }

      have h0' :
          cNeed ∈
            checkedEvalRunLoopMachine.runBranches m0
              [{ state := .need mode needExprCompositeMachine.initial,
                 tape :=
                   evalCursorStackEndTape witness consumed
                     (encodeCircuit (.not child) ++ tail)
                     (encodeEvalFrames frames) padding }] := by
        simpa [cNeed, padChild, encodeCircuit, List.append_assoc] using h0

      obtain ⟨m1, hm1, cfg1, h1, hrej⟩ :=
        hchild hchildInvalid tail (.neg :: frames)
          (consumed + 3) padChild n
          (by simpa [encodeEvalFrames, List.append_assoc] using hLayoutChild)
          hlenChild hreadChild

      have h1' :
          cfg1 ∈ checkedEvalRunLoopMachine.runBranches m1 [cNeed] := by
        simpa [cNeed, encodeEvalFrames, List.append_assoc] using h1

      have hAll :=
        mem_runBranches_trans checkedEvalRunLoopMachine
          m0 m1
          [{ state := .need mode needExprCompositeMachine.initial,
             tape :=
               evalCursorStackEndTape witness consumed
                 (encodeCircuit (.not child) ++ tail)
                 (encodeEvalFrames frames) padding }]
          cNeed cfg1 h0' h1'

      have hbudget :
          m0 + m1 ≤ checkedCircuitBudget (.not child) n := by
        have hraw :
            m0 + m1 ≤
              checkedLoopStepEnvelope n +
                checkedCircuitBudget child n := by
          omega
        let E := checkedLoopStepEnvelope n
        have hcoef :
            1 + 8 * (evalStepCount child + 1) ≤
              8 * (evalStepCount (.not child) + 1) := by
          simp [evalStepCount]
          omega
        have hmul := Nat.mul_le_mul_right E hcoef
        have hcap :
            checkedLoopStepEnvelope n +
                checkedCircuitBudget child n ≤
              checkedCircuitBudget (.not child) n := by
          unfold checkedCircuitBudget
          dsimp [E] at hmul ⊢
          calc
            checkedLoopStepEnvelope n +
                8 * (evalStepCount child + 1) * checkedLoopStepEnvelope n
                =
              (1 + 8 * (evalStepCount child + 1)) *
                checkedLoopStepEnvelope n := by
                  simp only [Nat.add_mul, Nat.one_mul]
            _ ≤
              8 * (evalStepCount child.not + 1) *
                checkedLoopStepEnvelope n := hmul
        exact Nat.le_trans hraw hcap

      exact ⟨m0 + m1, hbudget, cfg1, hAll, hrej⟩


/-- Exact bounded negative producer for conjunction. -/
theorem and_exact_bounded_reject
    (sigma : Assignment)
    (witness : BitString)
    (left right : CircuitK1.Circuit)
    (hleftReject :
      ExactBoundedCheckedCircuitRejectCertificate
        sigma witness .cnf left)
    (hrightReject :
      ExactBoundedCheckedCircuitRejectCertificate
        sigma witness .cnf right) :
    ∀ mode : SyntaxMode,
      ExactBoundedCheckedCircuitRejectCertificate
        sigma witness mode (.and left right) := by
  intro mode hinvalid tail frames consumed padding n hLayout hlen hread
  cases mode with
  | clause =>
      have hLayout0 :
          CheckedLayoutBound n consumed
            (true :: false :: false ::
              (encodeCircuit left ++ encodeCircuit right ++ tail))
            (encodeEvalFrames frames) := by
        simpa [encodeCircuit, List.append_assoc] using hLayout
      obtain ⟨m, hm, tape, hrun⟩ :=
        root_tag_reject_within_envelope
          n .clause witness
          (encodeCircuit left ++ encodeCircuit right ++ tail)
          (encodeEvalFrames frames) consumed padding
          true false false (by rfl)
          hLayout0.source_le hLayout0.frames_le
      refine ⟨m,
        Nat.le_trans hm
          (loopEnvelope_le_checkedCircuitBudget (.and left right) n),
        { state := .reject, tape := tape }, ?_, rfl⟩
      simpa [encodeCircuit, List.append_assoc] using hrun
  | mustInput =>
      have hLayout0 :
          CheckedLayoutBound n consumed
            (true :: false :: false ::
              (encodeCircuit left ++ encodeCircuit right ++ tail))
            (encodeEvalFrames frames) := by
        simpa [encodeCircuit, List.append_assoc] using hLayout
      obtain ⟨m, hm, tape, hrun⟩ :=
        root_tag_reject_within_envelope
          n .mustInput witness
          (encodeCircuit left ++ encodeCircuit right ++ tail)
          (encodeEvalFrames frames) consumed padding
          true false false (by rfl)
          hLayout0.source_le hLayout0.frames_le
      refine ⟨m,
        Nat.le_trans hm
          (loopEnvelope_le_checkedCircuitBudget (.and left right) n),
        { state := .reject, tape := tape }, ?_, rfl⟩
      simpa [encodeCircuit, List.append_assoc] using hrun
  | cnf =>
      have hlenMax :
          max (varBound left) (varBound right) ≤ witness.length := by
        simpa [varBound] using hlen
      have hlenLeft : varBound left ≤ witness.length :=
        Nat.le_trans (Nat.le_max_left _ _) hlenMax
      have hlenRight : varBound right ≤ witness.length :=
        Nat.le_trans (Nat.le_max_right _ _) hlenMax
      have hreadLeft :
          ∀ i, i < varBound left →
            witness.getD i false = sigma i := by
        intro i hi
        exact hread i (by
          simpa [varBound] using
            Nat.lt_of_lt_of_le hi (Nat.le_max_left _ _))
      have hreadRight :
          ∀ i, i < varBound right →
            witness.getD i false = sigma i := by
        intro i hi
        exact hread i (by
          simpa [varBound] using
            Nat.lt_of_lt_of_le hi (Nat.le_max_right _ _))

      have hLayout0 :
          CheckedLayoutBound n consumed
            (true :: false :: false ::
              (encodeCircuit left ++ encodeCircuit right ++ tail))
            (encodeEvalFrames frames) := by
        simpa [encodeCircuit, List.append_assoc] using hLayout

      obtain ⟨m0, hm0, h0⟩ :=
        pushTag_checked_reaches_need_within_envelope
          n .cnf witness
          (encodeCircuit left ++ encodeCircuit right ++ tail)
          (encodeEvalFrames frames) consumed padding
          true false false .and .andLeft rfl rfl (by
            simp [P01CheckedEvalRunTagPrefix.postTagState, childMode])
          hLayout0.source_le hLayout0.frames_le

      let padLeft := ((padding - 1) - 1) - 1
      let leftConsumed := consumed + 3
      let cNeedLeft : CheckedConfig :=
        { state := .need .cnf needExprCompositeMachine.initial,
          tape :=
            evalCursorStackEndTape witness leftConsumed
              (encodeCircuit left ++ encodeCircuit right ++ tail)
              (encodeEvalFrame .andLeft ++ encodeEvalFrames frames)
              padLeft }

      have h0' :
          cNeedLeft ∈
            checkedEvalRunLoopMachine.runBranches m0
              [{ state := .need .cnf needExprCompositeMachine.initial,
                 tape :=
                   evalCursorStackEndTape witness consumed
                     (encodeCircuit (.and left right) ++ tail)
                     (encodeEvalFrames frames) padding }] := by
        simpa [cNeedLeft, leftConsumed, padLeft, encodeCircuit,
          childMode, List.append_assoc] using h0

      have hLayoutLeft :
          CheckedLayoutBound n leftConsumed
            (encodeCircuit left ++ (encodeCircuit right ++ tail))
            (encodeEvalFrame .andLeft ++ encodeEvalFrames frames) := by
        simpa [leftConsumed, List.append_assoc] using
          (after_push_tag n consumed true false false
            (encodeCircuit left ++ encodeCircuit right ++ tail)
            (encodeEvalFrames frames) .andLeft hLayout0)

      cases hleftMode : modeCheck .cnf left with
      | false =>
          obtain ⟨m1, hm1, cfgReject, h1, hrej⟩ :=
            hleftReject hleftMode
              (encodeCircuit right ++ tail) (.andLeft :: frames)
              leftConsumed padLeft n
              (by simpa [encodeEvalFrames, List.append_assoc] using hLayoutLeft)
              hlenLeft hreadLeft
          have h1' :
              cfgReject ∈
                checkedEvalRunLoopMachine.runBranches m1 [cNeedLeft] := by
            simpa [cNeedLeft, encodeEvalFrames, List.append_assoc] using h1
          have hAll :=
            mem_runBranches_trans checkedEvalRunLoopMachine
              m0 m1
              [{ state := .need .cnf needExprCompositeMachine.initial,
                 tape :=
                   evalCursorStackEndTape witness consumed
                     (encodeCircuit (.and left right) ++ tail)
                     (encodeEvalFrames frames) padding }]
              cNeedLeft cfgReject h0' h1'
          have hbudget :
              m0 + m1 ≤ checkedCircuitBudget (.and left right) n := by
            have hraw :
                m0 + m1 ≤
                  checkedLoopStepEnvelope n +
                    checkedCircuitBudget left n := by
              omega
            let E := checkedLoopStepEnvelope n
            have hcoef :
                1 + 8 * (evalStepCount left + 1) ≤
                  8 * (evalStepCount (.and left right) + 1) := by
              simp [evalStepCount]
              omega
            have hmul := Nat.mul_le_mul_right E hcoef
            unfold checkedCircuitBudget at hraw ⊢
            dsimp [E] at hmul
            have hshape :
                checkedLoopStepEnvelope n +
                    8 * (evalStepCount left + 1) * checkedLoopStepEnvelope n =
                  (1 + 8 * (evalStepCount left + 1)) *
                    checkedLoopStepEnvelope n := by
              simp only [Nat.add_mul, Nat.one_mul]
            rw [hshape] at hraw
            exact Nat.le_trans hraw hmul
          exact ⟨m0 + m1, hbudget, cfgReject, hAll, hrej⟩
      | true =>
          have hrightMode : modeCheck .cnf right = false := by
            have h := hinvalid
            rw [modeCheck_and] at h
            simpa [tagAllowed, hleftMode] using h

          have hleftPositive :=
            circuit_exact_bounded_certificate sigma witness left .cnf
          obtain ⟨m1, hm1, cfgLeft, h1, hout1⟩ :=
            hleftPositive hleftMode
              (encodeCircuit right ++ tail) (.andLeft :: frames)
              leftConsumed padLeft n
              (by simpa [encodeEvalFrames, List.append_assoc] using hLayoutLeft)
              hlenLeft hreadLeft

          have h1' :
              cfgLeft ∈
                checkedEvalRunLoopMachine.runBranches m1 [cNeedLeft] := by
            simpa [cNeedLeft, encodeEvalFrames, List.append_assoc] using h1
          have h01 :=
            mem_runBranches_trans checkedEvalRunLoopMachine
              m0 m1
              [{ state := .need .cnf needExprCompositeMachine.initial,
                 tape :=
                   evalCursorStackEndTape witness consumed
                     (encodeCircuit (.and left right) ++ tail)
                     (encodeEvalFrames frames) padding }]
              cNeedLeft cfgLeft h0' h1'

          let afterLeft :=
            leftConsumed + (encodeCircuit left).length
          have hRightTail : encodeCircuit right ++ tail ≠ [] := by
            intro hnil
            have henc : encodeCircuit right = [] :=
              (List.append_eq_nil_iff.mp hnil).1
            cases right with
            | input i => simp [encodeCircuit] at henc
            | const b => cases b <;> simp [encodeCircuit] at henc
            | not child => simp [encodeCircuit] at henc
            | and a b => simp [encodeCircuit] at henc
            | or a b => simp [encodeCircuit] at henc

          obtain ⟨padding1, hcfgLeft⟩ :=
            exact_outcome_have_of_tail_ne_nil
              witness (exitMode .cnf left) (evalCircuit sigma left)
              (encodeCircuit right ++ tail) (.andLeft :: frames)
              afterLeft cfgLeft hRightTail
              (by simpa [afterLeft] using hout1)
          subst cfgLeft

          obtain ⟨m2, hm2, h2⟩ :=
            andLeftReturn_checked_reaches_need_within_envelope
              n (exitMode .cnf left)
              witness (encodeCircuit right ++ tail)
              (encodeEvalFrames frames)
              afterLeft padding1 (evalCircuit sigma left)

          let padRight := (((padding1 + 3) - 1) - 1) - 1
          let cNeedRight : CheckedConfig :=
            { state := .need .cnf needExprCompositeMachine.initial,
              tape :=
                evalCursorStackEndTape witness afterLeft
                  (encodeCircuit right ++ tail)
                  (encodeEvalFrame (.andRight (evalCircuit sigma left)) ++
                    encodeEvalFrames frames)
                  padRight }

          have h2' :
              cNeedRight ∈
                checkedEvalRunLoopMachine.runBranches m2
                  [{ state := .have (exitMode .cnf left)
                       (.start (evalCircuit sigma left)),
                     tape :=
                       evalCursorStackEndTape witness afterLeft
                         (encodeCircuit right ++ tail)
                         (encodeEvalFrames (.andLeft :: frames))
                         padding1 }] := by
            simpa [cNeedRight, padRight, encodeEvalFrames,
              List.append_assoc] using h2

          have h012 :=
            mem_runBranches_trans checkedEvalRunLoopMachine
              (m0 + m1) m2
              [{ state := .need .cnf needExprCompositeMachine.initial,
                 tape :=
                   evalCursorStackEndTape witness consumed
                     (encodeCircuit (.and left right) ++ tail)
                     (encodeEvalFrames frames) padding }]
              ({ state := .have (exitMode .cnf left)
                   (.start (evalCircuit sigma left)),
                 tape :=
                   evalCursorStackEndTape witness afterLeft
                     (encodeCircuit right ++ tail)
                     (encodeEvalFrames (.andLeft :: frames))
                     padding1 } : CheckedConfig)
              cNeedRight h01 h2'

          have hLayoutRight :
              CheckedLayoutBound n afterLeft
                (encodeCircuit right ++ tail)
                (encodeEvalFrame (.andRight (evalCircuit sigma left)) ++
                  encodeEvalFrames frames) := by
            have hp :
                CheckedLayoutBound n
                  (consumed +
                    (true :: false :: false :: encodeCircuit left).length)
                  (encodeCircuit right ++ tail)
                  (encodeEvalFrame (.andRight (evalCircuit sigma left)) ++
                    encodeEvalFrames frames) := by
              apply layout_after_prefix_with_frame
                n consumed
                (true :: false :: false :: encodeCircuit left)
                (encodeCircuit right ++ tail)
                (encodeEvalFrames frames)
                (.andRight (evalCircuit sigma left))
              · simp
              · simpa [encodeCircuit, List.append_assoc] using hLayout
            have hoff :
                consumed + (true :: false :: false :: encodeCircuit left).length =
                  afterLeft := by
              simp [afterLeft, leftConsumed]
              omega
            rw [← hoff]
            exact hp

          obtain ⟨m3, hm3, cfgReject, h3, hrej⟩ :=
            hrightReject hrightMode tail
              (.andRight (evalCircuit sigma left) :: frames)
              afterLeft padRight n
              (by simpa [encodeEvalFrames, List.append_assoc] using hLayoutRight)
              hlenRight hreadRight

          have h3' :
              cfgReject ∈
                checkedEvalRunLoopMachine.runBranches m3 [cNeedRight] := by
            simpa [cNeedRight, encodeEvalFrames, List.append_assoc] using h3

          have hAll :=
            mem_runBranches_trans checkedEvalRunLoopMachine
              (m0 + m1 + m2) m3
              [{ state := .need .cnf needExprCompositeMachine.initial,
                 tape :=
                   evalCursorStackEndTape witness consumed
                     (encodeCircuit (.and left right) ++ tail)
                     (encodeEvalFrames frames) padding }]
              cNeedRight cfgReject h012 h3'

          have hbudget :
              m0 + m1 + m2 + m3 ≤
                checkedCircuitBudget (.and left right) n := by
            have hraw :
                m0 + m1 + m2 + m3 ≤
                  checkedLoopStepEnvelope n +
                    checkedCircuitBudget left n +
                    checkedLoopStepEnvelope n +
                    checkedCircuitBudget right n := by
              omega
            let E := checkedLoopStepEnvelope n
            have hcoef :
                8 * (evalStepCount left + 1) +
                    8 * (evalStepCount right + 1) + 2 ≤
                  8 * (evalStepCount (.and left right) + 1) := by
              simp [evalStepCount]
              omega
            have hmul := Nat.mul_le_mul_right E hcoef
            unfold checkedCircuitBudget at hraw ⊢
            dsimp [E] at hmul
            have hshape :
                checkedLoopStepEnvelope n +
                    8 * (evalStepCount left + 1) * checkedLoopStepEnvelope n +
                    checkedLoopStepEnvelope n +
                    8 * (evalStepCount right + 1) * checkedLoopStepEnvelope n =
                  (8 * (evalStepCount left + 1) +
                    8 * (evalStepCount right + 1) + 2) *
                    checkedLoopStepEnvelope n := by
              simp only [Nat.add_mul, Nat.one_mul]
              omega
            rw [hshape] at hraw
            exact Nat.le_trans hraw hmul
          exact ⟨m0 + m1 + m2 + m3, hbudget, cfgReject, hAll, hrej⟩


/-- Exact bounded negative producer for disjunction. -/
theorem or_exact_bounded_reject
    (sigma : Assignment)
    (witness : BitString)
    (left right : CircuitK1.Circuit)
    (hleftReject :
      ExactBoundedCheckedCircuitRejectCertificate
        sigma witness .clause left)
    (hrightReject :
      ExactBoundedCheckedCircuitRejectCertificate
        sigma witness .clause right) :
    ∀ mode : SyntaxMode,
      ExactBoundedCheckedCircuitRejectCertificate
        sigma witness mode (.or left right) := by
  intro mode hinvalid tail frames consumed padding n hLayout hlen hread
  cases hroot : tagAllowed mode .or with
  | false =>
      have hLayout0 :
          CheckedLayoutBound n consumed
            (true :: false :: true ::
              (encodeCircuit left ++ encodeCircuit right ++ tail))
            (encodeEvalFrames frames) := by
        simpa [encodeCircuit, List.append_assoc] using hLayout
      obtain ⟨m, hm, tape, hrun⟩ :=
        root_tag_reject_within_envelope
          n mode witness
          (encodeCircuit left ++ encodeCircuit right ++ tail)
          (encodeEvalFrames frames) consumed padding
          true false true (by simpa using hroot)
          hLayout0.source_le hLayout0.frames_le
      refine ⟨m,
        Nat.le_trans hm
          (loopEnvelope_le_checkedCircuitBudget (.or left right) n),
        { state := .reject, tape := tape }, ?_, rfl⟩
      simpa [encodeCircuit, List.append_assoc] using hrun
  | true =>
      have hlenMax :
          max (varBound left) (varBound right) ≤ witness.length := by
        simpa [varBound] using hlen
      have hlenLeft : varBound left ≤ witness.length :=
        Nat.le_trans (Nat.le_max_left _ _) hlenMax
      have hlenRight : varBound right ≤ witness.length :=
        Nat.le_trans (Nat.le_max_right _ _) hlenMax
      have hreadLeft :
          ∀ i, i < varBound left →
            witness.getD i false = sigma i := by
        intro i hi
        exact hread i (by
          simpa [varBound] using
            Nat.lt_of_lt_of_le hi (Nat.le_max_left _ _))
      have hreadRight :
          ∀ i, i < varBound right →
            witness.getD i false = sigma i := by
        intro i hi
        exact hread i (by
          simpa [varBound] using
            Nat.lt_of_lt_of_le hi (Nat.le_max_right _ _))

      have hLayout0 :
          CheckedLayoutBound n consumed
            (true :: false :: true ::
              (encodeCircuit left ++ encodeCircuit right ++ tail))
            (encodeEvalFrames frames) := by
        simpa [encodeCircuit, List.append_assoc] using hLayout

      obtain ⟨m0, hm0, h0⟩ :=
        pushTag_checked_reaches_need_within_envelope
          n mode witness
          (encodeCircuit left ++ encodeCircuit right ++ tail)
          (encodeEvalFrames frames) consumed padding
          true false true .or .orLeft rfl hroot (by
            simp [P01CheckedEvalRunTagPrefix.postTagState, childMode])
          hLayout0.source_le hLayout0.frames_le

      let padLeft := ((padding - 1) - 1) - 1
      let leftConsumed := consumed + 3
      let cNeedLeft : CheckedConfig :=
        { state := .need .clause needExprCompositeMachine.initial,
          tape :=
            evalCursorStackEndTape witness leftConsumed
              (encodeCircuit left ++ encodeCircuit right ++ tail)
              (encodeEvalFrame .orLeft ++ encodeEvalFrames frames)
              padLeft }

      have h0' :
          cNeedLeft ∈
            checkedEvalRunLoopMachine.runBranches m0
              [{ state := .need mode needExprCompositeMachine.initial,
                 tape :=
                   evalCursorStackEndTape witness consumed
                     (encodeCircuit (.or left right) ++ tail)
                     (encodeEvalFrames frames) padding }] := by
        simpa [cNeedLeft, leftConsumed, padLeft, encodeCircuit,
          childMode, List.append_assoc] using h0

      have hLayoutLeft :
          CheckedLayoutBound n leftConsumed
            (encodeCircuit left ++ (encodeCircuit right ++ tail))
            (encodeEvalFrame .orLeft ++ encodeEvalFrames frames) := by
        simpa [leftConsumed, List.append_assoc] using
          (after_push_tag n consumed true false true
            (encodeCircuit left ++ encodeCircuit right ++ tail)
            (encodeEvalFrames frames) .orLeft hLayout0)

      cases hleftMode : modeCheck .clause left with
      | false =>
          obtain ⟨m1, hm1, cfgReject, h1, hrej⟩ :=
            hleftReject hleftMode
              (encodeCircuit right ++ tail) (.orLeft :: frames)
              leftConsumed padLeft n
              (by simpa [encodeEvalFrames, List.append_assoc] using hLayoutLeft)
              hlenLeft hreadLeft
          have h1' :
              cfgReject ∈
                checkedEvalRunLoopMachine.runBranches m1 [cNeedLeft] := by
            simpa [cNeedLeft, encodeEvalFrames, List.append_assoc] using h1
          have hAll :=
            mem_runBranches_trans checkedEvalRunLoopMachine
              m0 m1
              [{ state := .need mode needExprCompositeMachine.initial,
                 tape :=
                   evalCursorStackEndTape witness consumed
                     (encodeCircuit (.or left right) ++ tail)
                     (encodeEvalFrames frames) padding }]
              cNeedLeft cfgReject h0' h1'
          have hbudget :
              m0 + m1 ≤ checkedCircuitBudget (.or left right) n := by
            have hraw :
                m0 + m1 ≤
                  checkedLoopStepEnvelope n +
                    checkedCircuitBudget left n := by
              omega
            let E := checkedLoopStepEnvelope n
            have hcoef :
                1 + 8 * (evalStepCount left + 1) ≤
                  8 * (evalStepCount (.or left right) + 1) := by
              simp [evalStepCount]
              omega
            have hmul := Nat.mul_le_mul_right E hcoef
            unfold checkedCircuitBudget at hraw ⊢
            dsimp [E] at hmul
            have hshape :
                checkedLoopStepEnvelope n +
                    8 * (evalStepCount left + 1) * checkedLoopStepEnvelope n =
                  (1 + 8 * (evalStepCount left + 1)) *
                    checkedLoopStepEnvelope n := by
              simp only [Nat.add_mul, Nat.one_mul]
            rw [hshape] at hraw
            exact Nat.le_trans hraw hmul
          exact ⟨m0 + m1, hbudget, cfgReject, hAll, hrej⟩
      | true =>
          have hrightMode : modeCheck .clause right = false := by
            have h := hinvalid
            rw [modeCheck_or] at h
            simpa [hroot, hleftMode] using h

          have hleftPositive :=
            circuit_exact_bounded_certificate sigma witness left .clause
          obtain ⟨m1, hm1, cfgLeft, h1, hout1⟩ :=
            hleftPositive hleftMode
              (encodeCircuit right ++ tail) (.orLeft :: frames)
              leftConsumed padLeft n
              (by simpa [encodeEvalFrames, List.append_assoc] using hLayoutLeft)
              hlenLeft hreadLeft

          have h1' :
              cfgLeft ∈
                checkedEvalRunLoopMachine.runBranches m1 [cNeedLeft] := by
            simpa [cNeedLeft, encodeEvalFrames, List.append_assoc] using h1
          have h01 :=
            mem_runBranches_trans checkedEvalRunLoopMachine
              m0 m1
              [{ state := .need mode needExprCompositeMachine.initial,
                 tape :=
                   evalCursorStackEndTape witness consumed
                     (encodeCircuit (.or left right) ++ tail)
                     (encodeEvalFrames frames) padding }]
              cNeedLeft cfgLeft h0' h1'

          let afterLeft :=
            leftConsumed + (encodeCircuit left).length
          have hRightTail : encodeCircuit right ++ tail ≠ [] := by
            intro hnil
            have henc : encodeCircuit right = [] :=
              (List.append_eq_nil_iff.mp hnil).1
            cases right with
            | input i => simp [encodeCircuit] at henc
            | const b => cases b <;> simp [encodeCircuit] at henc
            | not child => simp [encodeCircuit] at henc
            | and a b => simp [encodeCircuit] at henc
            | or a b => simp [encodeCircuit] at henc

          obtain ⟨padding1, hcfgLeft⟩ :=
            exact_outcome_have_of_tail_ne_nil
              witness (exitMode .clause left) (evalCircuit sigma left)
              (encodeCircuit right ++ tail) (.orLeft :: frames)
              afterLeft cfgLeft hRightTail
              (by simpa [afterLeft] using hout1)
          subst cfgLeft

          obtain ⟨m2, hm2, h2⟩ :=
            orLeftReturn_checked_reaches_need_within_envelope
              n (exitMode .clause left)
              witness (encodeCircuit right ++ tail)
              (encodeEvalFrames frames)
              afterLeft padding1 (evalCircuit sigma left)

          let padRight := (((padding1 + 3) - 1) - 1) - 1
          let cNeedRight : CheckedConfig :=
            { state := .need .clause needExprCompositeMachine.initial,
              tape :=
                evalCursorStackEndTape witness afterLeft
                  (encodeCircuit right ++ tail)
                  (encodeEvalFrame (.orRight (evalCircuit sigma left)) ++
                    encodeEvalFrames frames)
                  padRight }

          have h2' :
              cNeedRight ∈
                checkedEvalRunLoopMachine.runBranches m2
                  [{ state := .have (exitMode .clause left)
                       (.start (evalCircuit sigma left)),
                     tape :=
                       evalCursorStackEndTape witness afterLeft
                         (encodeCircuit right ++ tail)
                         (encodeEvalFrames (.orLeft :: frames))
                         padding1 }] := by
            simpa [cNeedRight, padRight, encodeEvalFrames,
              List.append_assoc] using h2

          have h012 :=
            mem_runBranches_trans checkedEvalRunLoopMachine
              (m0 + m1) m2
              [{ state := .need mode needExprCompositeMachine.initial,
                 tape :=
                   evalCursorStackEndTape witness consumed
                     (encodeCircuit (.or left right) ++ tail)
                     (encodeEvalFrames frames) padding }]
              ({ state := .have (exitMode .clause left)
                   (.start (evalCircuit sigma left)),
                 tape :=
                   evalCursorStackEndTape witness afterLeft
                     (encodeCircuit right ++ tail)
                     (encodeEvalFrames (.orLeft :: frames))
                     padding1 } : CheckedConfig)
              cNeedRight h01 h2'

          have hLayoutRight :
              CheckedLayoutBound n afterLeft
                (encodeCircuit right ++ tail)
                (encodeEvalFrame (.orRight (evalCircuit sigma left)) ++
                  encodeEvalFrames frames) := by
            have hp :
                CheckedLayoutBound n
                  (consumed +
                    (true :: false :: true :: encodeCircuit left).length)
                  (encodeCircuit right ++ tail)
                  (encodeEvalFrame (.orRight (evalCircuit sigma left)) ++
                    encodeEvalFrames frames) := by
              apply layout_after_prefix_with_frame
                n consumed
                (true :: false :: true :: encodeCircuit left)
                (encodeCircuit right ++ tail)
                (encodeEvalFrames frames)
                (.orRight (evalCircuit sigma left))
              · simp
              · simpa [encodeCircuit, List.append_assoc] using hLayout
            have hoff :
                consumed + (true :: false :: false :: encodeCircuit left).length =
                  afterLeft := by
              simp [afterLeft, leftConsumed]
              omega
            rw [← hoff]
            exact hp

          obtain ⟨m3, hm3, cfgReject, h3, hrej⟩ :=
            hrightReject hrightMode tail
              (.orRight (evalCircuit sigma left) :: frames)
              afterLeft padRight n
              (by simpa [encodeEvalFrames, List.append_assoc] using hLayoutRight)
              hlenRight hreadRight

          have h3' :
              cfgReject ∈
                checkedEvalRunLoopMachine.runBranches m3 [cNeedRight] := by
            simpa [cNeedRight, encodeEvalFrames, List.append_assoc] using h3

          have hAll :=
            mem_runBranches_trans checkedEvalRunLoopMachine
              (m0 + m1 + m2) m3
              [{ state := .need mode needExprCompositeMachine.initial,
                 tape :=
                   evalCursorStackEndTape witness consumed
                     (encodeCircuit (.or left right) ++ tail)
                     (encodeEvalFrames frames) padding }]
              cNeedRight cfgReject h012 h3'

          have hbudget :
              m0 + m1 + m2 + m3 ≤
                checkedCircuitBudget (.or left right) n := by
            have hraw :
                m0 + m1 + m2 + m3 ≤
                  checkedLoopStepEnvelope n +
                    checkedCircuitBudget left n +
                    checkedLoopStepEnvelope n +
                    checkedCircuitBudget right n := by
              omega
            let E := checkedLoopStepEnvelope n
            have hcoef :
                8 * (evalStepCount left + 1) +
                    8 * (evalStepCount right + 1) + 2 ≤
                  8 * (evalStepCount (.or left right) + 1) := by
              simp [evalStepCount]
              omega
            have hmul := Nat.mul_le_mul_right E hcoef
            unfold checkedCircuitBudget at hraw ⊢
            dsimp [E] at hmul
            have hshape :
                checkedLoopStepEnvelope n +
                    8 * (evalStepCount left + 1) * checkedLoopStepEnvelope n +
                    checkedLoopStepEnvelope n +
                    8 * (evalStepCount right + 1) * checkedLoopStepEnvelope n =
                  (8 * (evalStepCount left + 1) +
                    8 * (evalStepCount right + 1) + 2) *
                    checkedLoopStepEnvelope n := by
              simp only [Nat.add_mul, Nat.one_mul]
              omega
            rw [hshape] at hraw
            exact Nat.le_trans hraw hmul
          exact ⟨m0 + m1 + m2 + m3, hbudget, cfgReject, hAll, hrej⟩

/-- Exact bounded negative structural producer for every canonical circuit. -/
theorem circuit_exact_bounded_reject
    (sigma : Assignment)
    (witness : BitString) :
    ∀ (phi : CircuitK1.Circuit) (mode : SyntaxMode),
      ExactBoundedCheckedCircuitRejectCertificate sigma witness mode phi := by
  intro phi
  induction phi with
  | input i =>
      intro mode
      exact input_exact_bounded_reject sigma witness mode i
  | const v =>
      intro mode
      exact const_exact_bounded_reject sigma witness mode v
  | not child ih =>
      intro mode
      exact neg_exact_bounded_reject
        sigma witness mode child (ih (childMode mode .neg))
  | and left right ihLeft ihRight =>
      intro mode
      exact and_exact_bounded_reject
        sigma witness left right (ihLeft .cnf) (ihRight .cnf) mode
  | or left right ihLeft ihRight =>
      intro mode
      exact or_exact_bounded_reject
        sigma witness left right (ihLeft .clause) (ihRight .clause) mode

#print axioms MCore.Real.P01ExactBoundedReject.root_tag_reject_within_envelope
#print axioms MCore.Real.P01ExactBoundedReject.input_exact_bounded_reject
#print axioms MCore.Real.P01ExactBoundedReject.const_exact_bounded_reject
#print axioms MCore.Real.P01ExactBoundedReject.neg_exact_bounded_reject

end P01ExactBoundedReject
end Real
end MCore
