import MCore.Real.P01ExactBoundedCircuitProducer

namespace MCore
namespace Real
namespace P01ExactOrBounded

open CanonicalFinalProof
open CanonicalCircuitBits
open CanonicalSATWitness
open P01EncodedStackEvaluator
open P01EncodedFrameTape
open P01EvalCursorMachine
open P01NeedExprCompositeNTM
open P01CheckedEvalRunLoopNTM
open P01CheckedEvalRunBoundedCertificate
open P01CheckedEvalRunBoundedHelpers
open P01CheckedVerifierInvariant
open P01CheckedVerifierGlobalBudget
open P01CNFMode
open P01NTMRunLaws
open P01ExactBoundedCircuitProducer

theorem or_exact_bounded_certificate
    (sigma : Assignment)
    (witness : BitString)
    (mode : SyntaxMode)
    (left right : CircuitK1.Circuit)
    (hleft :
      ExactBoundedCheckedCircuitRunCertificate
        sigma witness .clause left)
    (hright :
      ExactBoundedCheckedCircuitRunCertificate
        sigma witness .clause right) :
    ExactBoundedCheckedCircuitRunCertificate
      sigma witness mode (.or left right) := by
  intro hmode tail frames consumed padding n hLayout hlen hread

  have hparts :
      (tagAllowed mode .or = true ∧ modeCheck .clause left = true) ∧
        modeCheck .clause right = true := by
    have h := hmode
    rw [modeCheck_or] at h
    simpa using h
  have hAllowed : tagAllowed mode .or = true := hparts.1.1
  have hleftMode : modeCheck .clause left = true := hparts.1.2
  have hrightMode : modeCheck .clause right = true := hparts.2

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
    intro j hj
    exact hread j (by
      simpa [varBound] using
        Nat.lt_of_lt_of_le hj (Nat.le_max_left _ _))
  have hreadRight :
      ∀ i, i < varBound right →
        witness.getD i false = sigma i := by
    intro j hj
    exact hread j (by
      simpa [varBound] using
        Nat.lt_of_lt_of_le hj (Nat.le_max_right _ _))

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
      true false true .or .orLeft rfl hAllowed (by
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
      List.append_assoc] using h0

  have hLayoutLeft :
      CheckedLayoutBound n leftConsumed
        (encodeCircuit left ++ (encodeCircuit right ++ tail))
        (encodeEvalFrame .orLeft ++ encodeEvalFrames frames) := by
    simpa [leftConsumed, List.append_assoc] using
      (after_push_tag n consumed true false true
        (encodeCircuit left ++ encodeCircuit right ++ tail)
        (encodeEvalFrames frames) .orLeft hLayout0)

  obtain ⟨m1, hm1, cfgLeft, h1, hout1⟩ :=
    hleft hleftMode
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
    cases right <;> simp [encodeCircuit] at henc

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
      simpa [encodeCircuit, List.append_assoc] using hLayout
    simpa [afterLeft, leftConsumed] using hp

  obtain ⟨m3, hm3, cfgRight, h3, hout3⟩ :=
    hright hrightMode tail
      (.orRight (evalCircuit sigma left) :: frames)
      afterLeft padRight n
      (by simpa [encodeEvalFrames, List.append_assoc] using hLayoutRight)
      hlenRight hreadRight

  have h3' :
      cfgRight ∈
        checkedEvalRunLoopMachine.runBranches m3 [cNeedRight] := by
    simpa [cNeedRight, encodeEvalFrames, List.append_assoc] using h3

  have h0123 :=
    mem_runBranches_trans checkedEvalRunLoopMachine
      (m0 + m1 + m2) m3
      [{ state := .need mode needExprCompositeMachine.initial,
         tape :=
           evalCursorStackEndTape witness consumed
             (encodeCircuit (.or left right) ++ tail)
             (encodeEvalFrames frames) padding }]
      cNeedRight cfgRight h012 h3'

  let finalConsumed :=
    afterLeft + (encodeCircuit right).length

  obtain ⟨padding2, hcfgRight⟩ :=
    exact_outcome_have_of_frames_ne_nil
      witness (exitMode .clause right) (evalCircuit sigma right)
      tail (.orRight (evalCircuit sigma left) :: frames)
      finalConsumed cfgRight (by simp)
      (by simpa [finalConsumed] using hout3)
  subst cfgRight

  obtain ⟨m4, hm4, h4⟩ :=
    orRightReturn_checked_reaches_have_within_envelope
      n (exitMode .clause right)
      witness tail (encodeEvalFrames frames)
      finalConsumed padding2
      (evalCircuit sigma left) (evalCircuit sigma right)

  let finalValue :=
    Bool.or (evalCircuit sigma left) (evalCircuit sigma right)
  let cHave : CheckedConfig :=
    { state := .have .clause (.start finalValue),
      tape :=
        evalCursorStackEndTape witness finalConsumed tail
          (encodeEvalFrames frames) (padding2 + 3) }

  have h4' :
      cHave ∈
        checkedEvalRunLoopMachine.runBranches m4
          [{ state := .have (exitMode .clause right)
               (.start (evalCircuit sigma right)),
             tape :=
               evalCursorStackEndTape witness finalConsumed tail
                 (encodeEvalFrames
                   (.orRight (evalCircuit sigma left) :: frames))
                 padding2 }] := by
    simpa [cHave, finalValue, encodeEvalFrames,
      List.append_assoc] using h4

  have h01234 :=
    mem_runBranches_trans checkedEvalRunLoopMachine
      (m0 + m1 + m2 + m3) m4
      [{ state := .need mode needExprCompositeMachine.initial,
         tape :=
           evalCursorStackEndTape witness consumed
             (encodeCircuit (.or left right) ++ tail)
             (encodeEvalFrames frames) padding }]
      ({ state := .have (exitMode .clause right)
           (.start (evalCircuit sigma right)),
         tape :=
           evalCursorStackEndTape witness finalConsumed tail
             (encodeEvalFrames
               (.orRight (evalCircuit sigma left) :: frames))
             padding2 } : CheckedConfig)
      cHave h0123 h4'

  have hConsumed :
      finalConsumed =
        consumed + (encodeCircuit (.or left right)).length := by
    unfold finalConsumed afterLeft leftConsumed
    simp [encodeCircuit]
    omega

  have hPrefixBudget :
      m0 + m1 + m2 + m3 + m4 ≤
        checkedCircuitBudget (.or left right) n := by
    have hraw :
        m0 + m1 + m2 + m3 + m4 ≤
          checkedLoopStepEnvelope n +
            checkedCircuitBudget left n +
            checkedLoopStepEnvelope n +
            checkedCircuitBudget right n +
            checkedLoopStepEnvelope n := by
      omega
    let E := checkedLoopStepEnvelope n
    have hcoef :
        8 * (evalStepCount left + 1) +
            8 * (evalStepCount right + 1) + 3 ≤
          8 * (evalStepCount left + evalStepCount right + 4) := by
      omega
    have hmul :=
      Nat.mul_le_mul_right E hcoef
    have hcount :
        evalStepCount (.or left right) + 1 =
          evalStepCount left + evalStepCount right + 4 := by
      simp [evalStepCount]
      omega
    have hcap :
        checkedLoopStepEnvelope n +
            checkedCircuitBudget left n +
            checkedLoopStepEnvelope n +
            checkedCircuitBudget right n +
            checkedLoopStepEnvelope n ≤
          checkedCircuitBudget (.or left right) n := by
      calc
        checkedLoopStepEnvelope n +
              checkedCircuitBudget left n +
              checkedLoopStepEnvelope n +
              checkedCircuitBudget right n +
              checkedLoopStepEnvelope n
            =
          (8 * (evalStepCount left + 1) +
            8 * (evalStepCount right + 1) + 3) * E := by
              unfold checkedCircuitBudget
              dsimp [E]
              omega
        _ ≤
          8 * (evalStepCount left + evalStepCount right + 4) * E :=
            hmul
        _ = checkedCircuitBudget (.or left right) n := by
              unfold checkedCircuitBudget
              rw [hcount]
    exact Nat.le_trans hraw hcap

  cases tail with
  | cons b bs =>
      refine ⟨m0 + m1 + m2 + m3 + m4,
        hPrefixBudget, cHave, h01234, ?_⟩
      change ExactCheckedLoopOutcome witness
        (exitMode mode (.or left right))
        (evalCircuit sigma (.or left right))
        (b :: bs) frames
        (consumed + (encodeCircuit (.or left right)).length) cHave
      rw [← hConsumed]
      refine ⟨padding2 + 3, ?_⟩
      simp [ExactCheckedLoopOutcome, exitMode, childMode, circuitTag,
        cHave, finalValue, evalCircuit]
  | nil =>
      cases frames with
      | cons f fs =>
          refine ⟨m0 + m1 + m2 + m3 + m4,
            hPrefixBudget, cHave, h01234, ?_⟩
          change ExactCheckedLoopOutcome witness
            (exitMode mode (.or left right))
            (evalCircuit sigma (.or left right))
            [] (f :: fs)
            (consumed + (encodeCircuit (.or left right)).length) cHave
          rw [← hConsumed]
          refine ⟨padding2 + 3, ?_⟩
          simp [ExactCheckedLoopOutcome, exitMode, childMode, circuitTag,
            cHave, finalValue, evalCircuit]
      | nil =>
          obtain ⟨m5, hm5, cfgFinal, h5, hout5⟩ :=
            have_reaches_outcome_within_envelope
              n mode witness finalValue [] []
              finalConsumed (padding2 + 3)
          have hAll :=
            mem_runBranches_trans checkedEvalRunLoopMachine
              (m0 + m1 + m2 + m3 + m4) m5
              [{ state := .need mode needExprCompositeMachine.initial,
                 tape :=
                   evalCursorStackEndTape witness consumed
                     (encodeCircuit (.or left right))
                     (encodeEvalFrames []) padding }]
              cHave cfgFinal (by simpa using h01234)
              (by simpa [cHave] using h5)
          have hFinalBudget :
              m0 + m1 + m2 + m3 + m4 + m5 ≤
                checkedCircuitBudget (.or left right) n := by
            have hraw :
                m0 + m1 + m2 + m3 + m4 + m5 ≤
                  checkedLoopStepEnvelope n +
                    checkedCircuitBudget left n +
                    checkedLoopStepEnvelope n +
                    checkedCircuitBudget right n +
                    checkedLoopStepEnvelope n +
                    checkedLoopStepEnvelope n := by
              omega
            let E := checkedLoopStepEnvelope n
            have hcoef :
                8 * (evalStepCount left + 1) +
                    8 * (evalStepCount right + 1) + 4 ≤
                  8 * (evalStepCount left + evalStepCount right + 4) := by
              omega
            have hmul := Nat.mul_le_mul_right E hcoef
            have hcount :
                evalStepCount (.or left right) + 1 =
                  evalStepCount left + evalStepCount right + 4 := by
              simp [evalStepCount]
              omega
            have hcap :
                checkedLoopStepEnvelope n +
                    checkedCircuitBudget left n +
                    checkedLoopStepEnvelope n +
                    checkedCircuitBudget right n +
                    checkedLoopStepEnvelope n +
                    checkedLoopStepEnvelope n ≤
                  checkedCircuitBudget (.or left right) n := by
              calc
                checkedLoopStepEnvelope n +
                      checkedCircuitBudget left n +
                      checkedLoopStepEnvelope n +
                      checkedCircuitBudget right n +
                      checkedLoopStepEnvelope n +
                      checkedLoopStepEnvelope n
                    =
                  (8 * (evalStepCount left + 1) +
                    8 * (evalStepCount right + 1) + 4) * E := by
                      unfold checkedCircuitBudget
                      dsimp [E]
                      omega
                _ ≤
                  8 * (evalStepCount left + evalStepCount right + 4) * E :=
                    hmul
                _ = checkedCircuitBudget (.or left right) n := by
                      unfold checkedCircuitBudget
                      rw [hcount]
            exact Nat.le_trans hraw hcap
          refine ⟨m0 + m1 + m2 + m3 + m4 + m5,
            hFinalBudget, cfgFinal, ?_, ?_⟩
          · simpa using hAll
          · change ExactCheckedLoopOutcome witness
              (exitMode mode (.or left right))
              (evalCircuit sigma (.or left right)) [] []
              (consumed + (encodeCircuit (.or left right)).length)
              cfgFinal
            simp [ExactCheckedLoopOutcome] at hout5 ⊢
            simpa [exitMode, childMode, circuitTag, finalValue,
              evalCircuit] using hout5




/-- Complete bounded structural producer for every circuit. -/
theorem circuit_exact_bounded_certificate
    (sigma : Assignment)
    (witness : BitString) :
    ∀ (phi : CircuitK1.Circuit) (mode : SyntaxMode),
      ExactBoundedCheckedCircuitRunCertificate
        sigma witness mode phi := by
  intro phi
  induction phi with
  | input i =>
      intro mode
      exact input_exact_bounded_certificate sigma witness mode i
  | const v =>
      intro mode
      exact const_exact_bounded_certificate sigma witness mode v
  | not child ih =>
      intro mode
      exact neg_exact_bounded_certificate
        sigma witness mode child (ih (childMode mode .neg))
  | and left right ihLeft ihRight =>
      intro mode
      exact and_exact_bounded_certificate
        sigma witness mode left right
        (ihLeft .cnf) (ihRight .cnf)
  | or left right ihLeft ihRight =>
      intro mode
      exact or_exact_bounded_certificate
        sigma witness mode left right
        (ihLeft .clause) (ihRight .clause)

#print axioms MCore.Real.P01ExactOrBounded.or_exact_bounded_certificate
#print axioms MCore.Real.P01ExactOrBounded.circuit_exact_bounded_certificate


end P01ExactOrBounded
end Real
end MCore
